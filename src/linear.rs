use alloc::string::String;
use vstd::prelude::*;

use crate::{ptr_map::MutPointerMap, traits::Link};

verus! {

struct LinNode {
    data: u64,
    next: LinLink,
    prev: LinLink,
}

type LinKey = String;

#[derive(Clone, Copy)]
struct LinLink {
    inner: usize,
    key: Ghost<Option<LinKey>>,
    count: Ghost<nat>,
}

impl LinLink {
    fn null() -> Self {
        LinLink {
            inner: 0,
            count: Ghost(0),
            key: Ghost(None)
        }
    }

    #[verifier::type_invariant]
    spec fn wf(&self) -> bool {
        self.inner == 0 <==> self.key@ == Option::<LinKey>::None
    }
}

struct LinSystem {
    map: MutPointerMap<LinKey, LinNode>
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

    spec fn decreasing_next(&self) -> bool {
        forall |node: LinNode| #[trigger] self.contains_node(node) ==>
            self.valid(node.next) && (node.next.inner != 0 ==>
                self.follow(node.next).next.count@ < node.next.count@)
    }

    spec fn prev_link_wf(&self, node: LinNode) -> bool {
        self.valid(node.prev) &&
        (node.prev.inner != 0 ==> self.follow(node.prev).prev.count@ < node.prev.count@)
    }

    spec fn decreasing_prev(&self) -> bool {
        forall |key: LinKey| self.map@.contains_key(key@) ==> #[trigger] self.prev_link_wf(self.map@[key@].value())
    }

    spec fn wf(&self) -> bool {
        self.decreasing_next() && self.decreasing_prev() && self.map.wf()
    }

    spec fn view(&self) -> Map<LinKey, Seq<LinNode>> {
        Map::new(|k: LinKey| self.map@.dom().contains(k@), |k: LinKey| {
            let v = self.map@[k@].value();
            Seq::insert(children(self, v), 0, v)
        })
    }

    proof fn make_space(&mut self, key: LinKey)
    requires
        old(self).wf(),
        old(self).map@.contains_key(key@)
    ensures
        self.wf(),
        old(self)@ == self@,
        self.map@[key@].value().next.count@ == old(self).map@[key@].value().next.count@ + 1
    decreases
        old(self).map@[key@].value().prev.count@
    {
        assert(self.map@.contains_key(key@));
        let node = self.map@[key@].value();
        if node.prev.inner == 0 {
            admit();
        }
        else {
            let next = node.prev.key@.unwrap();

            assert(self.prev_link_wf(node));
            assert(self.map@.contains_key(next@));
            assert(decreases_to!(node.prev.count@ => self.map@[next@].value().prev.count@));

            self.make_space(next);
            admit()
        }
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
        old(self).map@.dom().contains(parent@)
    ensures
        self.wf()
    {
        let ghost parent_count = self.map@[parent@].value().prev.count@;
        let parent_ptr = self.map.get_ptr(&parent).unwrap();
        proof! { self.addr_nonnull(parent); };

        let prev = LinLink {
            inner: parent_ptr.addr(),
            key: Ghost(Some(parent)),
            count: Ghost(parent_count + 1)
        };

        assert(self.valid(prev));
        let node = LinNode {
            data, prev, next: LinLink::null()
        };

        assert(self.map@[parent@].addr() == parent_ptr.addr());

        let (_, new_ptr) = self.map.insert(new, node);
        proof! { self.addr_nonnull(new); };

        let new_link = LinLink {
            inner: new_ptr.addr(),
            key: Ghost(Some(new)),
            count: Ghost(1),
        };

        assert(self.valid(new_link));

        proof! {
            assert(new@ != parent@);
            assert(old(self).map@[parent@] == self.map@[parent@]);
            assert(self.map@[parent@].addr() == parent_ptr.addr());
        };

        assert(old(self).contains_node(self.map@[parent@].value()));

        let mut parent_node = self.map.take(parent_ptr, Ghost(parent@), Ghost(Set::empty()));
        parent_node.next = new_link;
        self.map.untake(parent_ptr, Ghost(parent@), parent_node, Ghost(Set::empty()));

        let ghost parent_node = self.map@[parent@].value();
        assert(self.map@.contains_key(parent@));
        assert(self.contains_node(parent_node));
        assert(parent_node.prev == old(self).map@[parent@].value().prev);
        assert(old(self).follow(parent_node.prev) == self.follow(parent_node.prev)) by {
            admit()
        };
        assert(old(self).prev_link_wf(old(self).map@[parent@].value()));
        assert(old(self).valid(parent_node.prev));
        assert(self.valid(parent_node.prev)) by {
            if parent_node.prev.inner == 0 {}
            else {
                assert(parent_node.prev.inner == old(self).map@[parent_node.prev.key@.unwrap()@].addr());
                assume(parent_node.prev.key@.unwrap()@ != new@);
                assume(parent_node.prev.key@.unwrap()@ != parent@);
                assert(parent_node.prev.inner == self.map@[parent_node.prev.key@.unwrap()@].addr());
                admit()
            }
        };

        assert(self.prev_link_wf(parent_node));

        assert(self.decreasing_next()) by { admit() };

        assert(self.decreasing_prev()) by { admit() };
    }
}

#[via_fn]
proof fn children_decreases_proof(this: &LinSystem, node: LinNode)
{
    if node.next.inner != 0 {
        assert(this.valid(node.next));
        assert(decreases_to!(node.next.count => this.follow(node.next).next.count)) by { };
    }
}

spec(checked) fn children(this: &LinSystem, node: LinNode) -> Seq<LinNode>
decreases node.next.count
    when this.decreasing_next() && this.contains_node(node)
    via children_decreases_proof
{
    if node.next.inner != 0 {
        let direct = this.follow(node.next);
        let indirect = children(this, direct);
        Seq::insert(indirect, 0, direct)
    }
    else {
        Seq::empty()
    }
}

}
