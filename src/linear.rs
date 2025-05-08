use alloc::string::String;
use vstd::{
    cell::MemContents,
    map::{axiom_map_insert_different, axiom_map_insert_same},
    prelude::*,
    simple_pptr::PPtr,
};

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
        self.is_null() <==> self.key@ == Option::<LinKey>::None
    }

    spec fn spec_is_null(&self) -> bool {
        self.inner == 0
    }

    #[verifier::when_used_as_spec(spec_is_null)]
    fn is_null(&self) -> bool
    returns self.spec_is_null()
    {
        self.inner == 0
    }
}

struct LinSystem {
    map: MutPointerMap<LinKey, LinNode>,
    generation: Ghost<nat>,
}

impl LinSystem {
    spec fn valid(&self, link: LinLink) -> bool {
        link.is_null() ||
        self.map@.contains_key(link.key@.unwrap()@) && self.map@[link.key@.unwrap()@].0 == link.inner
    }

    spec fn follow(&self, link: LinLink) -> LinNode
    recommends self.valid(link) && !link.is_null()
    {
        self.map@[link.key@.unwrap()@].1.value()
    }

    spec fn contains_node(&self, node: LinNode) -> bool {
        exists |k: LinKey| #[trigger] self.map@.dom().contains(k@) && self.map@[k@].1.value() == node
    }

    spec fn node_conditions(&self, node: LinNode) -> bool {
        &&& node.generation@ < self.generation@
        &&& self.valid(node.parent)
        &&& (!node.parent.is_null() ==> self.follow(node.parent).generation@ < node.generation@)
        &&& self.valid(node.child)
        &&& (!node.child.is_null() ==> self.follow(node.child).generation@ > node.generation@)
        &&& self.valid(node.next)
        &&& (!node.next.is_null() ==> self.follow(node.next).generation@ < node.generation@)
        &&& self.valid(node.prev)
        &&& (!node.prev.is_null() ==> self.follow(node.prev).generation@ > node.generation@)
    }

    spec fn correctly_linked_horizontal(&self, key: LinKey, node: LinNode) -> bool
    recommends self.node_conditions(node)
    {
        &&& !node.next.is_null() ==>
            !self.follow(node.next).prev.is_null() && self.follow(node.next).prev.key@.unwrap()@ == key@
        &&& !node.prev.is_null() ==>
            !self.follow(node.prev).next.is_null() && self.follow(node.prev).next.key@.unwrap()@ == key@
    }

    spec fn correctly_linked_vertical(&self, key: LinKey, node: LinNode) -> bool
    recommends self.node_conditions(node)
    {
        &&& !node.child.is_null() ==> {
            &&& self.follow(node.child).prev.is_null()
            &&& !self.follow(node.child).parent.is_null()
            &&& self.follow(node.child).parent.key@.unwrap()@ == key@
        }
    }

    spec fn wf(&self) -> bool {

        &&& self.map.wf()
        &&& forall |key: LinKey| self.map@.contains_key(key@) ==> {
            let node = #[trigger] self.map@[key@].1.value(); {
                &&& self.node_conditions(node)
                &&& self.correctly_linked_horizontal(key, node)
                &&& self.correctly_linked_vertical(key, node)
            }
        }
    }

    spec fn view(&self) -> Map<LinKey, Seq<LinNode>> {
        Map::new(|k: LinKey| self.map@.dom().contains(k@), |k: LinKey| {
            let v = self.map@[k@].1.value();
            Seq::insert(children(self, v), 0, v)
        })
    }

    proof fn addr_nonnull(tracked &self, key: LinKey)
    requires self.map@.dom().contains(key@)
    ensures self.map@[key@].0 != 0
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

        assert(self.node_conditions(self.map@[parent@].1.value()));
        assert(self.follow(node.parent).generation@ < node.generation@);

        self.generation = Ghost(self.generation@ + 1);
        let (_, child_ptr) = self.map.insert(new, node);

        {
            let mut parent_node = self.map.take(parent_ptr, Ghost(parent), Ghost(Set::empty()));

            proof!{ self.addr_nonnull(new) };
            let child_link = LinLink { inner: child_ptr.addr(), key: Ghost(Some(new)) };

            if !next_link.is_null() {
                assert(next_link == parent_node.child);
                proof! { use_type_invariant(next_link); };
                assert(next_link.key@.is_some());

                let ghost vacated = Set::empty().insert(parent@);
                let mut next_child = self.map.take(PPtr::from_addr(next_link.inner), Ghost(next_link.key@.unwrap()), Ghost(vacated));

                assert(next_child.prev.is_null());
                next_child.prev = child_link;

                proof! { axiom_map_insert_same(self.map@, next_link.key@.unwrap()@, (next_link.inner, MemContents::Init(next_child))); };
                self.map.untake(PPtr::from_addr(parent_node.child.inner), Ghost(next_link.key@.unwrap()), next_child, Ghost(vacated));
                assert(self.follow(next_link) == next_child);
            }

            parent_node.child = child_link;

            proof!{ axiom_map_insert_same(self.map@, parent@, (parent_ptr.addr(), MemContents::Init(parent_node))); };
            self.map.untake(parent_ptr, Ghost(parent), parent_node, Ghost(Set::empty()));
            assert(parent_node == self.follow(parent_link));
        }

        proof! {
            assert forall |key: LinKey|
            self.map@.contains_key(key@)
            && key@ != parent@
            && key@ != new@
            && key@ != next_link.key@.unwrap()@
            implies self.map@[key@] == old(self).map@[key@]
            by {
                if next_link.is_null() {
                    assert(self.map@ == old(self).map@
                        .insert(new@, (child_ptr.addr(), MemContents::Init(node)))
                        .insert(parent@, (parent_ptr.addr(), MemContents::Uninit))
                        .insert(parent@, (parent_ptr.addr(), MemContents::Init(self.follow(parent_link))))
                    );
                } else {
                    assert(self.map@ == old(self).map@
                        .insert(new@, (child_ptr.addr(), MemContents::Init(node)))
                        .insert(parent@, (parent_ptr.addr(), MemContents::Uninit))
                        .insert(next_link.key@.unwrap()@, (next_link.inner, MemContents::Uninit))
                        .insert(next_link.key@.unwrap()@, (next_link.inner, MemContents::Init(self.follow(next_link))))
                        .insert(parent@, (parent_ptr.addr(), MemContents::Init(self.follow(parent_link))))
                    );
                }
            };

            assert forall |key: LinKey|
            self.map@.contains_key(key@)
            implies {
                self.node_conditions(self.map@[key@].1.value()) &&
                self.correctly_linked_horizontal(key, #[trigger] self.map@[key@].1.value()) &&
                self.correctly_linked_vertical(key, #[trigger] self.map@[key@].1.value())
            }
            by {
                if key@ == new@ { }
                else if key@ == parent@ { }
                else if !node.next.is_null() && node.next.key@.unwrap()@ == key@ { }
                else { }
            };

        };
    }
}

#[via_fn]
proof fn children_decreases_proof(this: &LinSystem, node: LinNode)
{
    if !node.child.is_null() {
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
    if !node.child.is_null() {
        let direct = this.follow(node.child);
        let indirect = children(this, direct);
        Seq::insert(indirect, 0, direct)
    }
    else {
        Seq::empty()
    }
}

}
