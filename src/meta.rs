//! This module ties together all specifications, proofs and tokens
//! and provides a single `Meta` structure that acts as
//! a map of CapabilityTables:
//!
//! it supports
//! - `insert_root`
//! - `insert_child`
//! - `revoke_leaf`
//! - `revoke_children`
//! - `revoke_all`

use vstd::{
    prelude::*,
    simple_pptr::{PPtr, PointsTo},
};

verus! {

#[cfg(verus_keep_ghost)]
use vstd::set_lib::lemma_len_subset;

#[cfg(verus_keep_ghost)]
use crate::{
    lemmas::{
        insert_view::OpInsertChild,
        lemma_depth_increase, lemma_siblings_none_empty, lemma_siblings_unfold,
        lemma_transitive_child_parent, lemma_transitive_children_empty, lemma_view_acyclic,
        lemma_view_tree_ish,
        revoke_view::{
            lemma_revoke_spec, lemma_revoke_transitive_changes,
            lemma_revoke_transitive_non_changes, lemma_still_transitive_child,
        },
    },
    specs::{
        cap_map::{
            get_parent, insert_child, revoke_single_parent_update, transitive_child_of,
            transitive_children, CapMap
        },
        link_map::{decreasing_condition, siblings, view, Child, LinkMap},
    },
    state::SysState,
};

use crate::{
    specs::cap_map::{ActId, CapKey},
    state::{LinkSystem, Token},
    tables::{HashMetaCapTable, MetaCapTable},
};

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
    table: HashMetaCapTable<PPtr<Node>>,
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

    pub closed spec fn wf(&self) -> bool {
        &&& self.ties()
        &&& self.dom().finite()
        &&& self.table.wf()
        &&& self.state@.value() == SysState::Clean
        &&& self.dom() == self.table@.dom()
        &&& forall|key: CapKey| self.table@.contains_key(key) ==> {
            &&& #[trigger] self.tokens@.value()[key].addr() == self.table@[key].addr()
            &&& self.get(key).key == key
        }
    }

    pub closed spec fn view(&self) -> CapMap {
        view(self.spec())
    }

    pub fn insert_root(&mut self, key: CapKey)
        requires
            !old(self)@.contains_key(key),
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

        self.table.insert(key, ptr);
    }

    pub fn insert_child(&mut self, parent: CapKey, child: CapKey)
        requires
            old(self)@.contains_key(parent),
            !old(self)@.contains_key(child),
            old(self).wf(),
        ensures
            self.wf(),
            self@ == insert_child(old(self)@, parent, child),
    {
        proof!{
            // needed later to show parent.next != child && parent.back != child
            self.instance.borrow().contains_back(parent, self.spec.borrow());
            self.instance.borrow().contains_next(parent, self.spec.borrow());

            self.instance.borrow().weak_connections(self.spec.borrow());
        };

        let parent_ptr = *self.table.get(parent).unwrap();
        let next = self.borrow_node(parent).child;

        let node = Node { key: child, next, child: 0, back: parent_ptr.addr(), first_child: true };

        let (ptr, Tracked(token)) = PPtr::new(node);

        self.table.insert(child, ptr);

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

            assert(self.spec().dom() == self.table@.dom());

            // for well-formedness: show tokens and physical addresses agree
            assert forall|key: CapKey| #[trigger] self.table@.contains_key(key)
            implies {
                &&& self.tokens@.value()[key].addr() == self.table@[key].addr()
                &&& self.get(key).key == key
            }
            by {
                assert(self.tokens@.value()[key].addr() == self.table@[key].addr());
            };
            assert(self.wf());

            assert(self.spec() == (OpInsertChild { parent, child }).update(old(self).spec()));

            assert(self@.dom() == old(self)@.dom().insert(child));

            (OpInsertChild{parent, child}).lemma_view_update(old(self).spec());
            assert(self@ == insert_child(old(self)@, parent, child));
        };
    }

    pub fn revoke_single(&mut self, key: CapKey)
        requires
            old(self).wf(),
            old(self)@.contains_key(key),
            old(self)@[key].children.len() == 0,
        ensures
            self.wf(),
            self@.dom() == old(self)@.dom().remove(key),
            self@ == revoke_single_parent_update(old(self)@, key).remove(key),
    {
        let tracked _ = self.instance.borrow().clean_links(self.spec.borrow(), self.state.borrow());
        let tracked token = self.instance.borrow_mut().revoke_single(
            key,
            self.spec.borrow(),
            self.tokens.borrow(),
            self.state.borrow_mut(),
        );

        let ptr = *self.table.get(key).unwrap();
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

        self.table.remove(key);
        ptr.free(Tracked(token));

        assert(self.spec().dom() == old(self).spec().dom());

        let tracked _ = self.instance.borrow_mut().finish_revoke_single(
            key,
            self.spec.borrow_mut(),
            self.tokens.borrow_mut(),
            self.state.borrow_mut(),
        );

        let tracked _ = lemma_revoke_spec(old(self).spec(), self.spec(), key);

        assert(self.spec().dom() == self.table@.dom());

        let tracked _ = {
            // for well-formedness: show tokens and physical addresses agree
            assert forall|key: CapKey| #[trigger] self.table@.contains_key(key)
            implies {
                &&& self.tokens@.value()[key].addr() == self.table@[key].addr()
                &&& self.get(key).key == key
            }
            by {
                assert(self.tokens@.value()[key].addr() == self.table@[key].addr());
            };

            assert(self.dom() == old(self).dom().remove(key));
            assert(self@.dom() == old(self)@.dom().remove(key));
        };
    }

    pub fn revoke_children(&mut self, key: CapKey)
        requires
            old(self).wf(),
            old(self)@.contains_key(key),
        ensures
            self.wf(),
            self@.contains_key(key),
            self@[key].children.len() == 0,
            self@.dom() == old(self)@.dom().difference(transitive_children(old(self)@, key)).insert(key),
            self@.remove(key) == old(self)@.remove_keys(transitive_children(old(self)@, key)),
    {
        broadcast use vstd::set::group_set_axioms;

        let tracked _ = self.instance.borrow().weak_connections(self.spec.borrow());
        let tracked _ = lemma_view_acyclic(self.spec());
        assert(transitive_child_of(view(self.spec()), key, key));
        let ghost subtree = transitive_children(view(self.spec()), key);
        let ghost revoked_keys = Set::<CapKey>::empty();

        assert(self.dom().disjoint(revoked_keys));
        assert(subtree == transitive_children(view(self.spec()), key).union(revoked_keys));

        loop
            invariant
                self.wf(),
                self@.contains_key(key),
                self.dom().disjoint(revoked_keys),
                old(self).dom() == self.dom().union(revoked_keys),
                subtree == transitive_children(view(self.spec()), key).union(revoked_keys),
                view(old(self).spec()).remove_keys(subtree) == view(self.spec()).remove_keys(
                    subtree,
                ),
            ensures
                self.spec()[key].child.is_none(),
            decreases
                self.dom().len()
        {
            let child = self.first_child(key);
            let tracked _ = self.lemma_child_null_imp_none(child);

            if child.key.0 == key.0 && child.key.1 == key.1 {
                break
            }

            let tracked _ = {
                self.instance.borrow().weak_connections(self.spec.borrow());
                lemma_view_acyclic(self.spec());
                self.instance.borrow().clean_links(self.spec.borrow(), self.state.borrow());
            };

            let ghost pre = self.spec();
            assert(self@ == view(pre));
            self.revoke_single(child.key);
            assert(view(pre).dom() == pre.dom());
            assert(self.dom() == pre.dom().remove(child.key));

            let tracked _ = {
                self.instance.borrow().weak_connections(self.spec.borrow());
                lemma_view_acyclic(self.spec());
                lemma_revoke_transitive_changes(pre, child.key, key);
                lemma_revoke_transitive_non_changes(pre, child.key, key, subtree);

                revoked_keys = revoked_keys.insert(child.key);
                assert(old(self).dom() == self.dom().union(revoked_keys));

                assert(subtree == transitive_children(view(self.spec()), key).union(revoked_keys));
                assert(subtree.contains(child.key));

                if let Some(parent) = get_parent(view(self.spec()), child.key) {
                    assert(transitive_child_of(view(pre), child.key, key));
                    lemma_view_tree_ish(pre);
                    lemma_transitive_child_parent(view(pre), key, parent, child.key);
                    lemma_depth_increase(view(pre), parent, child.key);
                    assert(transitive_child_of(view(pre), parent, parent));
                    lemma_still_transitive_child(view(pre), key, parent, child.key);
                    assert(transitive_child_of(view(self.spec()), parent, key));
                }

                assert(view(old(self).spec()).remove_keys(subtree) == view(self.spec()).remove_keys(subtree));
            };
        }

        let tracked _ = self.instance.borrow().clean_links(self.spec.borrow(), self.state.borrow());
        let tracked _ = lemma_view_acyclic(self.spec());
        let tracked _ = lemma_view_tree_ish(self.spec());

        assert forall |child: CapKey| {
            &&& self@.contains_key(child)
            &&& #[trigger] transitive_child_of(view(self.spec()), child, key)
        }
        implies child == key by {
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

        assert(
            self@.dom() == old(self)@.dom().difference(transitive_children(view(old(self).spec()), key)).insert(key)
        );
    }

    fn borrow_node(&self, key: CapKey) -> (res: &Node)
        requires
            self.wf(),
            self@.contains_key(key),
        ensures
            self.get(key) == res,
            self.contains(res),
            res.key == key,
    {
        let ptr = self.table.get(key).unwrap();
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
        &&& self@.contains_key(node.key)
        &&& self.get(node.key) == node
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
            self@.contains_key(parent),
        ensures
            res.child == 0,
            self.contains(res),
            transitive_child_of(view(self.spec()), res.key, parent),
    {
        let mut res = self.borrow_node(parent);
        let tracked _ = self.instance.borrow().weak_connections(self.spec.borrow());
        let tracked _ = lemma_view_acyclic(self.spec());
        assert(transitive_child_of(view(self.spec()), res.key, parent));

        while res.child != 0
            invariant
                self.wf(),
                self@.contains_key(parent),
                self.contains(res),
                transitive_child_of(view(self.spec()), res.key, parent),
            decreases
                self.generation@.value() - self.spec()[res.key].depth
        {
            let tracked token = {
                self.instance.borrow().contains_child(res.key, self.spec.borrow());
                self.instance.borrow().token_invariant(res.key, self.spec.borrow(), self.tokens.borrow());
                let ghost next = self.spec()[res.key].child.unwrap();

                self.instance.borrow().weak_connections(self.spec.borrow());
                lemma_siblings_unfold(self.spec(), next);
                assert(self.spec()[res.key].depth < self.spec()[next].depth) by {
                    assert(decreasing_condition::<Child>(self.spec(), res.key));
                };
                assert(siblings(self.spec(), Some(next)).last() == next);
                assert(view(self.spec())[res.key].children.contains(next));
                self.instance.borrow().depth_bound(next, self.spec.borrow(), self.generation.borrow());

                lemma_view_acyclic(self.spec());
                assert(transitive_child_of(view(self.spec()), next, parent));
                self.instance.borrow().token_invariant(next, self.spec.borrow(), self.tokens.borrow());
                self.instance.borrow().borrow_token(
                    next,
                    self.spec.borrow(),
                    self.tokens.borrow(),
                    self.state.borrow(),
                )
            };

            res = PPtr::from_addr(res.child).borrow(Tracked(token));
        }

        res
    }

    fn cap_in(&self, activity: ActId) -> (res: Option<CapKey>)
    requires self.wf()
    ensures
        res matches Some(key) ==> key.0 == activity && self.dom().contains(key),
        res matches None ==> self.dom().filter(|key: CapKey| key.0 == activity).is_empty()
    {
        let act_table = self.table.get_act_table(activity)?;
        act_table.get_element()
    }

    pub fn revoke_all(&mut self, activity: ActId)
        requires
            old(self).wf(),
        ensures
            self.wf(),
            self@.dom().filter(|key: CapKey| key.0 == activity).is_empty()
    {
        broadcast use vstd::set::group_set_axioms;

        loop
            invariant self.wf()
            ensures self@.dom().filter(|key: CapKey| key.0 == activity).is_empty()
            decreases self.dom().len()
        {
            let Some(cap) = self.cap_in(activity) else { break; };
            let ghost before = self.dom();
            assert(before.finite());

            self.revoke_children(cap);
            let ghost here = self.dom();
            assert(self@.dom().subset_of(before));
            let tracked _ = lemma_len_subset(self.dom(), before);
            assert(self.dom().len() <= before.len());

            self.revoke_single(cap);
            assert(self@.dom() =~= here.remove(cap));
            assert(self.dom() == here.remove(cap));
            assert(self.dom().len() == here.len() - 1);
        }
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
