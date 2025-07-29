use vstd::{
    hash_map::HashMapWithView,
    prelude::*,
    simple_pptr::{PPtr, PointsTo},
};

use crate::{
    insert_view::OpInsertChild,
    lemmas::{
        lemma_siblings_none_empty, lemma_siblings_unfold, lemma_transitive_children_empty,
        lemma_view_well_formed,
    },
    revoke_view::{
        lemma_revoke_spec, lemma_revoke_transitive_changes, lemma_revoke_transitive_non_changes,
    },
    state::{LinkSystem, SysState, Token},
    tcb::{
        child_of, get_parent, revoke_single_parent_update, siblings, transitive_child_of,
        transitive_children, view, weak_child_link_condition, CapKey, LinkMap,
    },
};

verus! {

struct Node {
    next: usize,
    child: usize,
    back: usize,
    first_child: bool,
    key: CapKey,
}

impl Token for PointsTo<Node> {
    closed spec fn addr(&self) -> usize {
        self.pptr().addr()
    }

    proof fn is_nonnull(tracked &self)
        ensures
            self.addr() != 0,
    {
        self.is_nonnull()
    }

    closed spec fn cond(&self, next: usize, child: usize, back: usize, first_child: bool) -> bool {
        self.is_init() && self.value().back == back && self.value().child == child
            && self.value().next == next && self.value().first_child == first_child
    }
}

struct Meta {
    map: HashMapWithView<CapKey, PPtr<Node>>,
    instance: Tracked<LinkSystem::Instance<PointsTo<Node>>>,
    spec: Tracked<LinkSystem::map<PointsTo<Node>>>,
    tokens: Tracked<LinkSystem::all_tokens<PointsTo<Node>>>,
    state: Tracked<LinkSystem::state<PointsTo<Node>>>,
    generation: Tracked<LinkSystem::depth<PointsTo<Node>>>,
}

impl Meta {
    spec fn ties(&self) -> bool {
        &&& self.spec@.instance_id() == self.instance@.id()
        &&& self.state@.instance_id() == self.instance@.id()
        &&& self.tokens@.instance_id() == self.instance@.id()
        &&& self.generation@.instance_id() == self.instance@.id()
    }

    spec fn wf(&self) -> bool {
        &&& self.ties()
        &&& self.state@.value() == SysState::Clean
        &&& self.dom() == self.map@.dom()
        &&& forall|key: CapKey| #[trigger]
            self.map@.contains_key(key) ==> self.tokens@.value()[key].addr()
                == self.map@[key].addr() && self.get(key).key == key
    }

    fn insert_root(&mut self, key: CapKey)
        requires
            !old(self).contains_key(key),
            old(self).wf(),
        ensures
            self.wf(),
    {
        let node = Node { next: 0, child: 0, back: 0, first_child: false, key };
        let (ptr, Tracked(token)) = PPtr::new(node);

        let tracked _ = token.is_nonnull();
        let tracked _ = self.instance.borrow_mut().insert_root(
            key,
            token,
            self.spec.borrow_mut(),
            self.tokens.borrow_mut(),
            token,
        );

        self.map.insert(key, ptr);
    }

    fn insert_child(&mut self, parent: CapKey, child: CapKey)
        requires
            old(self).contains_key(parent),
            !old(self).contains_key(child),
            old(self).wf(),
        ensures
            self.wf(),
            self.spec() == (OpInsertChild { parent, child }).update(old(self).spec()),
    {
        proof!{
            // needed later to show parent.next != child && parent.back != child
            self.instance.borrow().contains_back(parent, self.spec.borrow());
            self.instance.borrow().contains_next(parent, self.spec.borrow());
        };

        let parent_ptr = *self.map.get(&parent).unwrap();
        let next = self.borrow_node(parent).child;

        let node = Node { key: child, next, child: 0, back: parent_ptr.addr(), first_child: true };

        let (ptr, Tracked(token)) = PPtr::new(node);

        self.map.insert(child, ptr);

        proof!{
            token.is_nonnull();
            self.instance.borrow().contains_child(parent, self.spec.borrow());
            self.instance.borrow().token_invariant(parent, self.spec.borrow(), self.tokens.borrow());
        };

        let tracked parent_token = self.instance.borrow_mut().insert_child(
            token,
            child,
            parent,
            self.spec.borrow_mut(),
            self.tokens.borrow_mut(),
            self.state.borrow_mut(),
            self.generation.borrow_mut(),
            token,
        );

        assert(parent_ptr.addr() == parent_token.addr());
        let mut parent_node = parent_ptr.take(Tracked(&mut parent_token));

        if parent_node.child == 0 {
            proof!{
                self.lemma_child_null_imp_none(&parent_node);
            };
        } else {
            let tracked next_perm = self.instance.borrow_mut().insert_child_fix_next(
                child,
                parent,
                self.spec.borrow(),
                self.tokens.borrow_mut(),
                self.state.borrow_mut(),
            );

            let next_ptr = PPtr::<Node>::from_addr(parent_node.child);
            assert(next_ptr.addr() == next_perm.addr());

            let mut next_node = next_ptr.take(Tracked(&mut next_perm));
            next_node.back = ptr.addr();
            next_node.first_child = false;
            next_ptr.put(Tracked(&mut next_perm), next_node);

            let ghost next = self.spec()[parent].child.unwrap();
            let tracked _ = self.instance.borrow_mut().insert_child_finish_next(
                next_perm,
                child,
                parent,
                next,
                self.spec.borrow_mut(),
                self.tokens.borrow_mut(),
                self.state.borrow_mut(),
                next_perm,
            );
        }

        parent_node.child = ptr.addr();
        parent_ptr.put(Tracked(&mut parent_token), parent_node);

        proof! {
            self.instance.borrow_mut().finish_insert(
                parent_token, child, parent,
                self.spec.borrow_mut(),
                self.tokens.borrow_mut(),
                self.state.borrow_mut(),
                parent_token
            );

            assert(self.spec().dom() == self.map@.dom());
        };
    }

    fn revoke_single(&mut self, key: CapKey)
        requires
            old(self).wf(),
            old(self).contains_key(key),
            old(self).spec()[key].child.is_none(),
        ensures
            self.wf(),
            self.spec().dom() == old(self).spec().dom().remove(key),
            view(self.spec()) == revoke_single_parent_update(old(self).spec(), key).remove(key),
    {
        let tracked _ = self.instance.borrow().clean_links(self.spec.borrow(), self.state.borrow());
        let tracked token = self.instance.borrow_mut().revoke_single(
            key,
            self.spec.borrow(),
            self.tokens.borrow(),
            self.state.borrow_mut(),
        );

        let ptr = *self.map.get(&key).unwrap();
        let node = ptr.take(Tracked(&mut token));

        if node.back == 0 {
            proof!{ self.lemma_back_null_imp_none(&node); }
        } else {
            let tracked tok = self.instance.borrow_mut().revoke_take_back(
                self.spec.borrow(),
                self.tokens.borrow(),
                self.state.borrow_mut(),
            );

            let back_ptr = PPtr::from_addr(node.back);
            let mut back_node: Node = back_ptr.take(Tracked(&mut tok));

            match node.first_child {
                true => back_node.child = node.next,
                false => back_node.next = node.next,
            }

            back_ptr.put(Tracked(&mut tok), back_node);
            let tracked _ = self.instance.borrow_mut().revoke_put_back(
                tok,
                self.spec.borrow_mut(),
                self.tokens.borrow_mut(),
                self.state.borrow_mut(),
                tok,
            );
        }

        if node.next == 0 {
            proof!{ self.lemma_next_null_imp_none(&node); }
        } else {
            let tracked tok = self.instance.borrow_mut().revoke_take_next(
                self.spec.borrow(),
                self.tokens.borrow(),
                self.state.borrow_mut(),
            );

            let next_ptr = PPtr::<Node>::from_addr(node.next);
            let mut next_node = next_ptr.take(Tracked(&mut tok));

            next_node.back = node.back;
            next_node.first_child = node.first_child;

            next_ptr.put(Tracked(&mut tok), next_node);
            let tracked _ = self.instance.borrow_mut().revoke_put_next(
                tok,
                self.spec.borrow_mut(),
                self.tokens.borrow_mut(),
                self.state.borrow_mut(),
                tok,
            );
        }

        self.map.remove(&key);
        ptr.free(Tracked(token));

        assert(self.spec().dom() == old(self).spec().dom());

        let tracked _ = self.instance.borrow_mut().finish_revoke_single(
            key,
            self.spec.borrow_mut(),
            self.tokens.borrow_mut(),
            self.state.borrow_mut(),
        );

        let tracked _ = lemma_revoke_spec(old(self).spec(), self.spec(), key);

        assert(self.spec().dom() == self.map@.dom());
    }

    fn revoke_children(&mut self, key: CapKey)
        requires
            old(self).wf(),
            old(self).contains_key(key),
        ensures
            self.wf(),
            self.contains_key(key),
            self.spec()[key].child.is_none(),
            self.dom() == old(self).dom().difference(transitive_children(view(old(self).spec()), key)).insert(key),
            view(self.spec()).remove(key) == view(old(self).spec()).remove_keys(transitive_children(view(old(self).spec()), key)),
    {
        broadcast use vstd::set::group_set_axioms;

        let tracked _ = self.instance.borrow().weak_connections(self.spec.borrow());
        let tracked _ = lemma_view_well_formed(self.spec());
        assert(transitive_child_of(view(self.spec()), key, key));
        let ghost subtree = transitive_children(view(self.spec()), key);
        let ghost revoked_keys = Set::<CapKey>::empty();

        assert(self.dom().disjoint(revoked_keys));
        assert(old(self).dom() == self.dom().union(revoked_keys));
        assert(subtree == transitive_children(view(self.spec()), key).union(revoked_keys));

        loop
            invariant
                self.wf(),
                self.contains_key(key),
                self.dom().disjoint(revoked_keys),
                old(self).dom() == self.dom().union(revoked_keys),
                subtree == transitive_children(view(self.spec()), key).union(revoked_keys),
                view(old(self).spec()).remove_keys(subtree) == view(self.spec()).remove_keys(
                    subtree,
                ),
            ensures
                self.spec()[key].child.is_none(),
        {
            let child = self.first_child(key);
            let tracked _ = self.lemma_child_null_imp_none(child);

            if child.key.0 == key.0 && child.key.1 == key.1 {
                break
            }

            let tracked _ = self.instance.borrow().weak_connections(self.spec.borrow());
            let tracked _ = lemma_view_well_formed(self.spec());
            let tracked _ = self.instance.borrow().clean_links(self.spec.borrow(), self.state.borrow());
            let ghost pre = self.spec();
            self.revoke_single(child.key);
            let tracked _ = self.instance.borrow().weak_connections(self.spec.borrow());
            let tracked _ = lemma_view_well_formed(self.spec());
            let tracked _ = lemma_revoke_transitive_changes(pre, child.key, key);
            let tracked _ = lemma_revoke_transitive_non_changes(
                pre,
                child.key,
                key,
                subtree,
            );

            proof! {
                revoked_keys = revoked_keys.insert(child.key);
                assert(old(self).dom() == self.dom().union(revoked_keys));

                assert(subtree == transitive_children(view(self.spec()), key).union(revoked_keys));
                assert(subtree.contains(child.key));

                if let Some(parent) = get_parent(self.spec(), child.key) {
                    assume(transitive_child_of(view(self.spec()), parent, key));
                }

                assert(view(old(self).spec()).remove_keys(subtree) == view(self.spec()).remove_keys(subtree));
            };
        }

        let tracked _ = self.instance.borrow().weak_connections(self.spec.borrow());
        let tracked _ = lemma_view_well_formed(self.spec());

        assert forall|child: CapKey|
            transitive_child_of(view(self.spec()), child, key) implies child == key by {
            lemma_transitive_children_empty(view(self.spec()), key, child)
        };

        assert(revoked_keys.insert(key) == subtree);
        assert(view(self.spec()).remove_keys(subtree) == view(old(self).spec()).remove_keys(
            subtree,
        ));
        assert(view(self.spec()).remove(key) ==
            view(old(self).spec()).remove_keys(transitive_children(view(old(self).spec()), key)));

        let tracked _ = lemma_siblings_none_empty(self.spec());
        assert(view(self.spec())[key].children.len() == 0);
        assert(self.dom() == old(self).dom().difference(revoked_keys));
        assert(self.dom() ==
            old(self).dom().difference(transitive_children(view(old(self).spec()), key)).insert(key));
    }

    fn borrow_node(&self, key: CapKey) -> (res: &Node)
        requires
            self.wf(),
            self.contains_key(key),
        ensures
            self.get(key) == res,
    {
        let ptr = self.map.get(&key).unwrap();
        let tracked borrow = self.instance.borrow().borrow_token(
            key,
            self.spec.borrow(),
            self.tokens.borrow(),
            self.state.borrow(),
        );
        assert(ptr.addr() == borrow.addr());
        ptr.borrow(Tracked(borrow))
    }

    spec fn contains(&self, node: &Node) -> bool {
        &&& self.contains_key(node.key)
        &&& self.get(node.key) == node
    }

    spec fn contains_key(&self, key: CapKey) -> bool {
        self.spec().contains_key(key)
    }

    spec fn get(&self, key: CapKey) -> Node {
        self.tokens@.value()[key].value()
    }

    spec fn dom(&self) -> Set<CapKey> {
        self.spec().dom()
    }

    spec fn spec(&self) -> LinkMap {
        self.spec@.value()
    }

    fn first_child(&self, parent: CapKey) -> (res: &Node)
        requires
            self.wf(),
            self.contains_key(parent),
        ensures
            res.child == 0,
            self.contains(res),
            transitive_child_of(view(self.spec()), res.key, parent),
    {
        let mut res = self.borrow_node(parent);
        let mut ptr = *self.map.get(&parent).unwrap();
        let ghost mut current = parent;
        let tracked _ = self.instance.borrow().weak_connections(self.spec.borrow());
        let tracked _ = lemma_view_well_formed(self.spec());
        assert(transitive_child_of(view(self.spec()), current, parent));

        while res.child != 0
            invariant
                self.wf(),
                self.contains_key(current),
                self.contains_key(parent),
                self.get(current) == *res,
                self.tokens@.value()[current].addr() == ptr.addr(),
                transitive_child_of(view(self.spec()), current, parent),
        {
            proof! {
                self.instance.borrow().contains_child(current, self.spec.borrow());
                self.instance.borrow().token_invariant(current, self.spec.borrow(), self.tokens.borrow());

                let next_current = self.spec()[current].child.unwrap();
                self.instance.borrow().weak_connections(self.spec.borrow());
                lemma_siblings_unfold(self.spec(), next_current);
                assert(weak_child_link_condition(self.spec(), current));
                assert(siblings(self.spec(), Some(next_current)).last() == next_current);
                assert(child_of(self.spec(), next_current, current));
                assert(view(self.spec())[current].children.contains(next_current));

                current = next_current;

                let tracked _ = lemma_view_well_formed(self.spec());
                assert(transitive_child_of(view(self.spec()), current, parent));
                self.instance.borrow().token_invariant(current, self.spec.borrow(), self.tokens.borrow());
            };
            let tracked token = self.instance.borrow().borrow_token(
                current,
                self.spec.borrow(),
                self.tokens.borrow(),
                self.state.borrow(),
            );

            ptr = PPtr::from_addr(res.child);
            res = ptr.borrow(Tracked(token));
        }

        res
    }

    proof fn lemma_next_null_imp_none(tracked &self, node: &Node)
        requires
            node.next == 0,
            self.contains(node),
            self.ties(),
        ensures
            self.spec()[node.key].next.is_none(),
    {
        let next_key = self.spec()[node.key].next;
        if next_key.is_some() {
            self.instance.borrow().token_invariant(
                node.key,
                self.spec.borrow(),
                self.tokens.borrow(),
            );
            self.instance.borrow().contains_next(node.key, self.spec.borrow());
            self.instance.borrow().addr_nonnull(
                next_key.unwrap(),
                self.spec.borrow(),
                self.tokens.borrow(),
            );
            assert(node.child != 0);
        }
    }

    proof fn lemma_child_null_imp_none(tracked &self, node: &Node)
        requires
            node.child == 0,
            self.contains(node),
            self.ties(),
        ensures
            self.spec()[node.key].child.is_none(),
    {
        // prove that key.child == None in this case
        let child_key = self.spec()[node.key].child;
        if child_key.is_some() {
            self.instance.borrow().token_invariant(
                node.key,
                self.spec.borrow(),
                self.tokens.borrow(),
            );
            self.instance.borrow().contains_child(node.key, self.spec.borrow());
            self.instance.borrow().addr_nonnull(
                child_key.unwrap(),
                self.spec.borrow(),
                self.tokens.borrow(),
            );
            assert(node.child != 0);
        }
    }

    proof fn lemma_back_null_imp_none(tracked &self, node: &Node)
        requires
            node.back == 0,
            self.contains(node),
            self.ties(),
        ensures
            self.spec()[node.key].back.is_none(),
    {
        // prove that key.back == None in this case
        let back_key = self.spec()[node.key].back;
        if back_key.is_some() {
            self.instance.borrow().token_invariant(
                node.key,
                self.spec.borrow(),
                self.tokens.borrow(),
            );
            self.instance.borrow().contains_back(node.key, self.spec.borrow());
            self.instance.borrow().addr_nonnull(
                back_key.unwrap(),
                self.spec.borrow(),
                self.tokens.borrow(),
            );
            assert(node.back != 0);
        }
    }
}

} // verus!
