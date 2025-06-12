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
    fn insert_child(&mut self, parent: CapKey, child: CapKey)
    requires
        old(self).map@.contains_key(parent),
        old(self).state@.value() == SysState::Clean,
        old(self).spec@.value().contains_key(parent),
        !old(self).spec@.value().contains_key(child),
        old(self).spec@.instance_id() == old(self).instance@.id(),
        old(self).state@.instance_id() == old(self).instance@.id(),
    {
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
            assume(self.spec@.value()[parent].1.child == Option::<CapKey>::None);

            let inserted = LinkedNode { first_child: true, back: Some(parent), next: None, child: None };
            let new_map = self.spec@.value().insert(child, (token, inserted));

            assume(new_map[parent].0.addr() == parent_ptr.addr());
            assert(token_invariant(new_map, child));

            self.instance.borrow().token_invariant(parent, self.spec.borrow());
        };

        let tracked parent_token = self.instance.borrow_mut().insert_first_child(
            token, child, parent, self.spec.borrow_mut(), self.state.borrow_mut(), token);

        let parent_ptr = self.map.get(&parent).unwrap();
        assert(parent_ptr.addr() == parent_token.addr());

        let mut parent_node = parent_ptr.take(Tracked(&mut parent_token));
        parent_node.child = ptr.addr();
        parent_ptr.put(Tracked(&mut parent_token), parent_node);

        proof! {
            let (_, old_parent_node) = self.spec@.value()[parent];
            let new_map = self.spec@.value()
                .insert(parent, (parent_token, LinkedNode { child: Some(child), ..old_parent_node }));

            assume(old_parent_node.next != Some(parent));
            assume(old_parent_node.next != Some(child));
            assume(old_parent_node.back != Some(parent));
            assume(old_parent_node.back != Some(child));

            assert(token_invariant(new_map, parent));

            self.instance.borrow_mut().finish_insert_first(
                parent_token, child, parent, self.spec.borrow_mut(), self.state.borrow_mut(), parent_token);
        };
    }
}

}
