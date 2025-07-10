use vstd::{
    hash_map::HashMapWithView,
    prelude::*,
    simple_pptr::{PPtr, PointsTo},
};

use crate::{
    state::{CapKey, LinkSystem, SysState, Token},
    view::{CapNode, OpInsertChild},
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
    state: Tracked<LinkSystem::state<PointsTo<Node>>>,
    generation: Tracked<LinkSystem::depth<PointsTo<Node>>>,
}

impl Meta {
    spec fn ties(&self) -> bool {
        &&& self.spec@.instance_id() == self.instance@.id()
        &&& self.state@.instance_id() == self.instance@.id()
        &&& self.generation@.instance_id() == self.instance@.id()
    }

    spec fn wf(&self) -> bool {
        &&& self.ties()
        &&& self.state@.value() == SysState::Clean
        &&& self.spec@.value().dom() == self.map@.dom()
        &&& forall|key: CapKey| #[trigger]
            self.map@.contains_key(key) ==>
                self.spec@.value()[key].0.addr() == self.map@[key].addr() &&
                self.get(key).key == key
    }

    fn insert_child(&mut self, parent: CapKey, child: CapKey)
        requires
            old(self).contains_key(parent),
            !old(self).contains_key(child),
            old(self).wf(),
        ensures
            self.wf(),
            self.spec@.value().dom() == old(self).spec@.value().dom().insert(child)
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
        let ghost op = OpInsertChild { parent, child, token };

        self.map.insert(child, ptr);

        proof!{
            token.is_nonnull();
            self.instance.borrow().contains_child(parent, self.spec.borrow());
            self.instance.borrow().token_invariant(parent, self.spec.borrow());
        };

        let tracked parent_token = self.instance.borrow_mut().insert_child(
            token,
            child,
            parent,
            self.spec.borrow_mut(),
            self.state.borrow_mut(),
            self.generation.borrow_mut(),
            token,
        );

        assert(self.spec@.value() == op.child_update(old(self).spec@.value()));

        assert(parent_ptr.addr() == parent_token.addr());
        let mut parent_node = parent_ptr.take(Tracked(&mut parent_token));

        if parent_node.child == 0 {
            proof!{
                self.lemma_child_null_imp_none(&parent_node);
            }
        } else {
            let tracked next_perm = self.instance.borrow_mut().insert_child_fix_next(
                child,
                parent,
                self.spec.borrow(),
                self.state.borrow_mut(),
            );

            let next_ptr = PPtr::<Node>::from_addr(parent_node.child);
            assert(next_ptr.addr() == next_perm.addr());

            let mut next_node = next_ptr.take(Tracked(&mut next_perm));
            next_node.back = ptr.addr();
            next_node.first_child = false;
            next_ptr.put(Tracked(&mut next_perm), next_node);

            let ghost next = self.spec@.value()[parent].1.child.unwrap();
            let tracked _ = self.instance.borrow_mut().insert_child_finish_next(
                next_perm,
                child,
                parent,
                next,
                self.spec.borrow_mut(),
                self.state.borrow_mut(),
                next_perm,
            );
        }

        parent_node.child = ptr.addr();
        parent_ptr.put(Tracked(&mut parent_token), parent_node);

        proof! {
            self.instance.borrow_mut().finish_insert(
                parent_token, child, parent, self.spec.borrow_mut(), self.state.borrow_mut(), parent_token);

            assert(self.spec@.value().dom() == self.map@.dom());
        };
    }

    fn revoke_single(&mut self, key: CapKey)
    requires
        old(self).wf(),
        old(self).contains_key(key),
        old(self).spec@.value()[key].1.child.is_none()
    ensures
        self.wf(),
        self.spec@.value().dom() == old(self).spec@.value().dom().remove(key)
    {
        let tracked token = self.instance.borrow_mut().revoke_single(key, self.spec.borrow(), self.state.borrow_mut());

        let ptr = self.map.get(&key).unwrap();
        let node = ptr.take(Tracked(&mut token));

        if node.back == 0 {
            proof!{ self.lemma_back_null_imp_none(&node); }
        }
        else {
            let tracked tok = self.instance.borrow_mut().revoke_take_back(self.spec.borrow(), self.state.borrow_mut());
            let back_ptr = PPtr::from_addr(node.back);
            let mut back_node: Node = back_ptr.take(Tracked(&mut tok));

            match node.first_child {
                true => back_node.child = node.next,
                false => back_node.next = node.next,
            }

            back_ptr.put(Tracked(&mut tok), back_node);
            let tracked _ = self.instance.borrow_mut().revoke_put_back(tok, self.spec.borrow_mut(), self.state.borrow_mut(), tok);
        }

        if node.next == 0 {
            proof!{ self.lemma_next_null_imp_none(&node); }
        }
        else {
            let tracked tok = self.instance.borrow_mut().revoke_take_next(self.spec.borrow(), self.state.borrow_mut());
            let next_ptr = PPtr::<Node>::from_addr(node.next);
            let mut next_node = next_ptr.take(Tracked(&mut tok));

            next_node.back = node.back;
            next_node.first_child = node.first_child;

            next_ptr.put(Tracked(&mut tok), next_node);
            let tracked _ = self.instance.borrow_mut().revoke_put_next(
                tok, self.spec.borrow_mut(), self.state.borrow_mut(), tok);
        }

        self.map.remove(&key);

        let tracked _ = self.instance.borrow_mut().finish_revoke_single(
            key, self.spec.borrow_mut(), self.state.borrow_mut());
        assert(self.spec@.value().dom() == self.map@.dom());
    }

    fn revoke_children(&mut self, key: CapKey)
    requires
        old(self).wf(),
        old(self).contains_key(key)
    ensures
        self.wf(),
        self.contains_key(key),
        self.spec@.value()[key].1.child.is_none()
    {
        loop invariant
            self.wf(),
            self.contains_key(key)
        {
            let child = self.first_child(key);
            let tracked _ = self.lemma_child_null_imp_none(child);

            if child.key == key {
                return
            }

            self.revoke_single(child.key);
        }
    }

    fn borrow_node(&self, key: CapKey) -> (res: &Node)
    requires
        self.wf(),
        self.contains_key(key)
    ensures
        self.get(key) == res,
    {
        let ptr = self.map.get(&key).unwrap();
        let tracked borrow = self.instance.borrow().borrow_token(
            key,
            self.spec.borrow(),
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
        self.spec@.value().contains_key(key)
    }

    spec fn get(&self, key: CapKey) -> Node {
        self.spec@.value()[key].0.value()
    }

    fn first_child(&self, key: CapKey) -> (res: &Node)
    requires
        self.wf(),
        self.contains_key(key),
    ensures
        res.child == 0,
        self.contains(res)
    {
        let mut res = self.borrow_node(key);
        let mut ptr = *self.map.get(&key).unwrap();
        let ghost mut key = key;

        while res.child != 0
        invariant
            self.contains_key(key),
            self.get(key) == *res,
            self.spec@.value()[key].0.addr() == ptr.addr(),
            self.wf()
        {
            proof! {
                self.instance.borrow().contains_child(key, self.spec.borrow());
                self.instance.borrow().token_invariant(key, self.spec.borrow());

                key = self.spec@.value()[key].1.child.unwrap();
                self.instance.borrow().token_invariant(key, self.spec.borrow());
            };
            let tracked token = self.instance.borrow().borrow_token(
                key,
                self.spec.borrow(),
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
        self.ties()
    ensures
        self.spec@.value()[node.key].1.next.is_none()
    {
        let next_key = self.spec@.value()[node.key].1.next;
        if next_key.is_some() {
            self.instance.borrow().token_invariant(node.key, self.spec.borrow());
            self.instance.borrow().contains_next(node.key, self.spec.borrow());
            self.instance.borrow().addr_nonnull(next_key.unwrap(), self.spec.borrow());
            assert(node.child != 0);
        }
    }

    proof fn lemma_child_null_imp_none(tracked &self, node: &Node)
    requires
        node.child == 0,
        self.contains(node),
        self.ties()
    ensures
        self.spec@.value()[node.key].1.child.is_none()
    {
        // prove that key.child == None in this case
        let child_key = self.spec@.value()[node.key].1.child;
        if child_key.is_some() {
            self.instance.borrow().token_invariant(node.key, self.spec.borrow());
            self.instance.borrow().contains_child(node.key, self.spec.borrow());
            self.instance.borrow().addr_nonnull(child_key.unwrap(), self.spec.borrow());
            assert(node.child != 0);
        }
    }

    proof fn lemma_back_null_imp_none(tracked &self, node: &Node)
    requires
        node.back == 0,
        self.contains(node),
        self.ties()
    ensures
        self.spec@.value()[node.key].1.back.is_none()
    {
        // prove that key.back == None in this case
        let back_key = self.spec@.value()[node.key].1.back;
        if back_key.is_some() {
            self.instance.borrow().token_invariant(node.key, self.spec.borrow());
            self.instance.borrow().contains_back(node.key, self.spec.borrow());
            self.instance.borrow().addr_nonnull(back_key.unwrap(), self.spec.borrow());
            assert(node.back != 0);
        }
    }
}

} // verus!
