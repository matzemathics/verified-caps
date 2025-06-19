use vstd::{
    hash_map::HashMapWithView,
    prelude::*,
    simple_pptr::{PPtr, PointsTo},
};

use crate::state::{token_invariant, CapKey, LinkSystem, LinkedNode, SysState, Token};

verus! {

struct Node {
    next: usize,
    child: usize,
    back: usize,
    first_child: bool,
}

impl Token for PointsTo<Node> {
    closed spec fn addr(&self) -> usize {
        self.pptr().addr()
    }

    proof fn is_nonnull(tracked &self)
    ensures self.addr() != 0
    {
        self.is_nonnull()
    }

    closed spec fn cond(&self, next: usize, child: usize, back: usize, first_child: bool) -> bool {
        self.is_init() &&
        self.value().back == back &&
        self.value().child == child &&
        self.value().next == next &&
        self.value().first_child == first_child
    }
}

struct Meta {
    map: HashMapWithView<CapKey, PPtr<Node>>,

    instance: Tracked<LinkSystem::Instance<PointsTo<Node>>>,
    spec: Tracked<LinkSystem::map<PointsTo<Node>>>,
    state: Tracked<LinkSystem::state<PointsTo<Node>>>,
}

impl Meta {
    spec fn wf(&self) -> bool {
        self.state@.value() == SysState::Clean &&
        self.spec@.instance_id() == self.instance@.id() &&
        self.state@.instance_id() == self.instance@.id() &&
        self.spec@.value().dom() == self.map@.dom() &&
        forall |key: CapKey| #[trigger] self.map@.contains_key(key) ==>
            self.spec@.value()[key].0.addr() == self.map@[key].addr()
    }

    fn insert_child(&mut self, parent: CapKey, child: CapKey)
    requires
        old(self).spec@.value().contains_key(parent),
        !old(self).spec@.value().contains_key(child),
        old(self).wf()
    ensures
        self.wf()
    {
        proof!{
            // needed later to show parent.next != child && parent.back != child
            self.instance.borrow().contains_back(parent, self.spec.borrow());
            self.instance.borrow().contains_next(parent, self.spec.borrow());
        };

        let parent_ptr = self.map.get(&parent).unwrap();

        let node = Node {
            next: 0,
            child: 0,
            back: parent_ptr.addr(),
            first_child: true
        };

        let (ptr, Tracked(token)) = PPtr::new(node);
        self.map.insert(child, ptr);

        proof!{
            token.is_nonnull();
            let inserted = LinkedNode { first_child: true, back: Some(parent), next: None, child: None };
            let new_map = self.spec@.value().insert(child, (token, inserted));

            assert(self.spec@.value()[parent].0.addr() == parent_ptr.addr());
            assert(token_invariant(new_map, child));

            self.instance.borrow().token_invariant(parent, self.spec.borrow());
            assert(token_invariant(self.spec@.value(), parent));
        };

        let tracked parent_token = self.instance.borrow_mut().insert_first_child(
            token, child, parent, self.spec.borrow_mut(), self.state.borrow_mut(), token);

        let parent_ptr = self.map.get(&parent).unwrap();
        assert(parent_ptr.addr() == parent_token.addr());

        let mut parent_node = parent_ptr.take(Tracked(&mut parent_token));

        if parent_node.child == 0 {
            proof!{
                let child_key = self.spec@.value()[parent].1.child;
                if child_key.is_some() {
                    self.instance.borrow().token_invariant(parent, self.spec.borrow());
                    self.instance.borrow().contains_child(parent, child_key.unwrap(), self.spec.borrow());
                    self.instance.borrow().addr_nonnull(child_key.unwrap(), self.spec.borrow());
                    assert(parent_node.child != 0);
                }
            }
        }
        else {
            proof!{ admit(); };
        }

        parent_node.child = ptr.addr();
        parent_ptr.put(Tracked(&mut parent_token), parent_node);

        proof! {
            let (_, old_parent_node) = self.spec@.value()[parent];

            let new_map = self.spec@.value()
                .insert(parent, (parent_token, LinkedNode { child: Some(child), ..old_parent_node }));

            assert(token_invariant(new_map, parent));

            self.instance.borrow_mut().finish_insert_first(
                parent_token, child, parent, self.spec.borrow_mut(), self.state.borrow_mut(), parent_token);

            assert(self.spec@.value().dom() == self.map@.dom());
        };
    }
}

}
