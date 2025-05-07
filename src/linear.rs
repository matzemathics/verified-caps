use alloc::string::String;
use vstd::{prelude::*, simple_pptr::PPtr};

use crate::ptr_map::MutPointerMap;

verus! {

struct LinNode {
    data: u64,
    generation: Ghost<nat>,
    child: LinLink,
    parent: LinLink,
    next: LinLink,
    prev: LinLink,
}

type LinKey = String;

#[derive(Clone, Copy)]
struct LinLink {
    inner: usize,
    key: Ghost<Option<LinKey>>,
}

impl LinLink {
    spec fn spec_null() -> Self {
        LinLink { inner: 0, key: Ghost(None) }
    }

    #[verifier::when_used_as_spec(spec_null)]
    fn null() -> Self
    returns Self::null()
    {
        LinLink {
            inner: 0,
            key: Ghost(None)
        }
    }

    #[verifier::type_invariant]
    spec fn wf(&self) -> bool {
        self.inner == 0 <==> self.key@ == Option::<LinKey>::None
    }
}

struct LinSystem {
    map: MutPointerMap<LinKey, LinNode>,
    generation: Ghost<nat>,
}

impl LinSystem {
    spec fn valid(&self, link: LinLink) -> bool {
        link.inner == 0 ||
        self.map@.contains_key(link.key@.unwrap()@) && self.map@[link.key@.unwrap()@].addr() == link.inner
    }

    spec fn follow(&self, link: LinLink) -> LinNode
    recommends self.valid(link) && link.inner != 0
    {
        self.map@[link.key@.unwrap()@].value()
    }

    spec fn contains_node(&self, node: LinNode) -> bool {
        exists |k: LinKey| #[trigger] self.map@.dom().contains(k@) && self.map@[k@].value() == node
    }

    spec fn node_conditions(&self, node: LinNode) -> bool {
        &&& node.generation@ < self.generation@
        &&& self.valid(node.parent)
        &&& (node.parent.inner != 0 ==> self.follow(node.parent).generation@ < node.generation@)
        &&& self.valid(node.child)
        &&& (node.child.inner != 0 ==> self.follow(node.child).generation@ > node.generation@)
        &&& self.valid(node.next)
        &&& (node.next.inner != 0 ==> self.follow(node.next).generation@ < node.generation@)
        &&& self.valid(node.prev)
        &&& (node.prev.inner != 0 ==> self.follow(node.prev).generation@ > node.generation@)
    }

    spec fn wf(&self) -> bool {
        &&& self.map.wf()
        &&& forall |key: LinKey| self.map@.contains_key(key@) ==> self.node_conditions(#[trigger] self.map@[key@].value())
    }

    spec fn view(&self) -> Map<LinKey, Seq<LinNode>> {
        Map::new(|k: LinKey| self.map@.dom().contains(k@), |k: LinKey| {
            let v = self.map@[k@].value();
            Seq::insert(children(self, v), 0, v)
        })
    }

    proof fn addr_nonnull(tracked &self, key: LinKey)
    requires self.map@.dom().contains(key@)
    ensures self.map@[key@].addr() != 0
    {
        self.map.tracked_borrow().tracked_borrow(key@).is_nonnull()
    }

    fn insert(&mut self, data: u64, parent: LinKey, new: LinKey)
    requires
        new@ != parent@,
        old(self).wf(),
        old(self).map@.contains_key(parent@),
        !old(self).map@.contains_key(new@),
    ensures
        self.wf()
    {
        let parent_ptr = self.map.get_ptr(&parent).unwrap();

        proof!{ self.addr_nonnull(parent) };
        let parent_link = LinLink { inner: parent_ptr.addr(), key: ghost_exec(Some(parent)) };
        let next_link = self.map.read(parent_ptr, Ghost(parent)).child;

        let node = LinNode {
            data,
            generation: self.generation,
            child: LinLink::null(),
            parent: parent_link,
            next: next_link,
            prev: LinLink::null(),
        };

        assert(self.node_conditions(self.map@[parent@].value()));
        assert(self.follow(node.parent).generation@ < node.generation@);

        self.generation = Ghost(self.generation@ + 1);

        assert(node.generation@ < self.generation@);
        assert(self.node_conditions(node));
        assert(
            forall |key: LinKey|
            self.map@.contains_key(key@) ==> self.node_conditions(#[trigger] self.map@[key@].value()));

        let ghost old_map = self.map@;
        let (_, child_ptr) = self.map.insert(new, node);

        proof! {
            assert forall |key: LinKey|
            self.map@.contains_key(key@) && key@ != new@
            implies #[trigger] self.map@[key@] == old(self).map@[key@] by {};

            assert forall |key: LinKey|
            self.map@.contains_key(key@) && key@ != new@
            implies self.node_conditions(#[trigger] self.map@[key@].value()) by {};
        };

        assert(self.node_conditions(self.follow(node.parent)));
        assert(self.follow(node.parent).child.inner != 0 ==>
            self.node_conditions( self.follow(self.follow(node.parent).child)));
        let ghost old_self = *self;

        let mut parent_node = self.map.take(parent_ptr, Ghost(parent), Ghost(Set::empty()));

        proof!{ self.addr_nonnull(new) };
        let child_link = LinLink { inner: child_ptr.addr(), key: Ghost(Some(new)) };
        assert(self.valid(child_link));

        if parent_node.child.inner != 0 {
            assert(self.follow(child_link).generation@ == node.generation@);
            assert(self.follow(parent_node.child).generation@ < node.generation@);

            let ghost vacated = Set::empty().insert(parent@);
            let mut next_child = self.map.take(PPtr::from_addr(parent_node.child.inner), Ghost(parent_node.child.key@.unwrap()), Ghost(vacated));
            assert(old_self.node_conditions(next_child));

            assert(next_child.generation@ < node.generation@ == self.follow(child_link).generation@);
            assert(self.valid(child_link));

            next_child.prev = child_link;
            assert(old_self.node_conditions(next_child));

            self.map.untake(PPtr::from_addr(parent_node.child.inner), Ghost(parent_node.child.key@.unwrap()), next_child, Ghost(vacated));
        }

        parent_node.child = child_link;
        assert(self.node_conditions(parent_node));

        self.map.untake(parent_ptr, Ghost(parent), parent_node, Ghost(Set::empty()));
    }
}

#[via_fn]
proof fn children_decreases_proof(this: &LinSystem, node: LinNode)
{
    if node.child.inner != 0 {
        assert(this.node_conditions(node));
        assert(this.node_conditions(this.follow(node.child)));
        assert(this.generation@ - this.follow(node.child).generation@ < this.generation@ - node.generation@);
    }
}

spec(checked) fn children(this: &LinSystem, node: LinNode) -> Seq<LinNode>
decreases this.generation@ - node.generation@
    when this.wf() && this.contains_node(node)
    via children_decreases_proof
{
    if node.child.inner != 0 {
        let direct = this.follow(node.child);
        let indirect = children(this, direct);
        Seq::insert(indirect, 0, direct)
    }
    else {
        Seq::empty()
    }
}

}
