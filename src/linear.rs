use alloc::{collections::btree_map::Keys, string::String};
use vstd::{
    cell::MemContents,
    map::{axiom_map_insert_different, axiom_map_insert_same},
    prelude::*,
    simple_pptr::{self, PPtr},
};

use crate::ptr_map::MutPointerMap;

verus! {

type KobjData = u64;

struct LinNode {
    data: KobjData,
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

    proof fn is_null_ensures_eq_null(tracked self)
    requires self.is_null()
    ensures self == Self::null()
    {
        use_type_invariant(self);
    }
}

struct LinSystem {
    map: MutPointerMap<LinKey, LinNode>,
    generation: Ghost<nat>,
}

type SpecMap = Map<<LinKey as View>::V, (KobjData, Seq<LinKey>)>;

spec fn insert_child(map: SpecMap, parent_key: LinKey, child_key: LinKey, child_data: KobjData) -> SpecMap
recommends
    map.contains_key(parent_key@),
    !map.contains_key(child_key@),
{
    let (parent_data, parent_children) = map[parent_key@];
    map
        .insert(child_key@, (child_data, Seq::empty()))
        .insert(parent_key@, (parent_data, parent_children.insert(0, child_key)))
}

impl LinSystem {
    spec fn valid(&self, link: LinLink) -> bool {
        link.wf() && (
            link.is_null() ||
            self.map@.contains_key(link.key@.unwrap()@) && self.map@[link.key@.unwrap()@].0 == link.inner
        )
    }

    spec fn follow(&self, link: LinLink) -> LinNode
    recommends self.valid(link) && !link.is_null()
    {
        self.node_at(link.key@.unwrap()@)
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

    spec fn correctly_linked_horizontal(&self, key: <LinKey as View>::V) -> bool
    recommends self.node_conditions(self.node_at(key))
    {
        let node = self.node_at(key); {
            &&& !node.next.is_null() ==>
                !self.follow(node.next).prev.is_null() && self.follow(node.next).prev.key@.unwrap()@ == key
            &&& !node.prev.is_null() ==>
                !self.follow(node.prev).next.is_null() && self.follow(node.prev).next.key@.unwrap()@ == key
        }
    }

    spec fn correctly_linked_vertical(&self, key: <LinKey as View>::V) -> bool
    recommends self.node_conditions(self.node_at(key))
    {
        let node = self.node_at(key); {
            &&& !node.child.is_null() ==> {
                &&& self.follow(node.child).prev.is_null()
                &&& !self.follow(node.child).parent.is_null()
                &&& self.follow(node.child).parent.key@.unwrap()@ == key
            }
            &&& (node.prev.is_null() && !node.parent.is_null()) ==> {
                &&& !self.follow(node.parent).child.is_null()
                &&& self.follow(node.parent).child.key@.unwrap()@ == key
            }
        }
    }

    spec fn wf(&self) -> bool {
        &&& self.map.wf()
        &&& self.locally_finite()
        &&& self.correctly_linked()
    }

    spec fn locally_finite(&self) -> bool {
        &&& self.map.wf()
        &&& forall |key: <LinKey as View>::V| self.map@.contains_key(key) ==>
            #[trigger] self.node_conditions(self.node_at(key))
    }

    spec fn correctly_linked(&self) -> bool {
        &&& forall |key: <LinKey as View>::V| self.map@.contains_key(key) ==>
                #[trigger] self.correctly_linked_horizontal(key)
        &&& forall |key: <LinKey as View>::V| self.map@.contains_key(key) ==>
                #[trigger] self.correctly_linked_vertical(key)
    }

    spec fn node_at(&self, key: <LinKey as View>::V) -> LinNode {
        self.map@[key].1.value()
    }

    spec fn almost_correctly_linked(&self, exception: <LinKey as View>::V) -> bool {
        &&& forall |key: <LinKey as View>::V| self.map@.contains_key(key) && key != exception ==>
                #[trigger] self.correctly_linked_horizontal(key)
        &&& forall |key: <LinKey as View>::V| self.map@.contains_key(key) && key != exception ==>
                #[trigger] self.correctly_linked_vertical(key)
    }

    spec fn future_first_child_of(&self, child_link: LinLink, parent: <LinKey as View>::V) -> bool {
        let new_node = self.follow(child_link); {
            &&& !child_link.is_null() && self.valid(child_link)
            &&& !new_node.parent.is_null() && new_node.parent.key@.unwrap()@ == parent
            &&& new_node.next == self.follow(new_node.parent).child
            &&& new_node.prev.is_null()
            &&& new_node.child.is_null()
        }
    }

    spec fn view(&self) -> SpecMap {
        self.map@.map_values(|arg: (usize, MemContents<LinNode>)| {
            let v = arg.1.value();
            (v.data, horizontal_keys(self, v.child))
        })
    }

    proof fn addr_nonnull(tracked &self, key: LinKey)
    requires self.map@.dom().contains(key@)
    ensures self.map@[key@].0 != 0
    {
        self.map.tracked_borrow().tracked_borrow(key@).is_nonnull()
    }

    fn insert(&mut self, data: KobjData, parent: LinKey, new: LinKey) -> (r: LinLink)
    requires
        new@ != parent@,
        old(self).wf(),
        old(self).map@.contains_key(parent@),
        !old(self).map@.contains_key(new@),
    ensures
        self.map.wf(),
        self.locally_finite(),
        self@ == old(self)@.insert(new@, (data, Seq::empty())),
        self.almost_correctly_linked(new@),
        self.future_first_child_of(r, parent@),
        r.key@.unwrap() == new
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

        assert(self.node_conditions(self.node_at(parent@)));
        assert(self.follow(node.parent).generation@ < node.generation@);

        self.generation = Ghost(self.generation@ + 1);
        let (_, child_ptr) = self.map.insert(new, node);

        assert(self.map@ =~= old(self).map@
            .insert(new@, (child_ptr.addr(), MemContents::Init(node))));

        proof! {
            assert forall |key: <LinKey as View>::V|
            self.map@.contains_key(key)
            implies #[trigger] self.node_conditions(self.node_at(key))
            by {
                if key == new@ {
                    assert(old(self).node_conditions(old(self).node_at(parent@)));
                    if !node.next.is_null() {
                        assert(old(self).node_conditions(old(self).follow(node.next)));
                    }
                    assert(self.node_conditions(node));
                }
                else {
                    assert(old(self).node_conditions(old(self).node_at(key)));
                }
            };

            assert(self.map@.dom() == old(self).map@.dom().insert(new@));

            assert forall |key: <LinKey as View>::V|
            self.map@.contains_key(key) && key != new@
            implies #[trigger] self.correctly_linked_horizontal(key)
            by {
                assert(old(self).node_conditions(self.node_at(key)));
                assert(old(self).correctly_linked_horizontal(key));
                assert(self.node_at(key) == old(self).node_at(key));

                if !self.node_at(key).prev.is_null() {
                    assert(self.follow(self.node_at(key).prev) == old(self).follow(self.node_at(key).prev));
                }

                if !self.node_at(key).next.is_null() {
                    assert(self.follow(self.node_at(key).next) == old(self).follow(self.node_at(key).next));
                }
            };

            assert forall |key: <LinKey as View>::V|
            self.map@.contains_key(key) && key != new@
            implies #[trigger] self.correctly_linked_vertical(key)
            by {
                assert(old(self).node_conditions(self.node_at(key)));
                assert(old(self).correctly_linked_vertical(key));
                assert(self.node_at(key) == old(self).node_at(key));

                if !self.node_at(key).child.is_null() {
                    assert(self.follow(self.node_at(key).child) == old(self).follow(self.node_at(key).child));
                }

                if !self.node_at(key).parent.is_null() {
                    assert(self.follow(self.node_at(key).parent) == old(self).follow(self.node_at(key).parent));
                }
            };

            assert forall |key: <LinKey as View>::V| self@.contains_key(key)
            implies self@[key] == #[trigger] old(self)@.insert(new@, (data, Seq::empty()))[key]
            by {
                if key == new@ {
                    assert(horizontal_keys(self, LinLink::null()) == Seq::<LinKey>::empty()) by (compute);
                    assert(self@[key] == (data, Seq::<LinKey>::empty()));
                }
                else {
                    assert(old(self).node_conditions(old(self).node_at(key)));
                    lemma_unchanged_children_rec(old(self), self, self.node_at(key).child);
                }
            };
        };

        assert(self@ =~= old(self)@.insert(new@, (data, Seq::empty())));

        proof!{ self.addr_nonnull(new); };
        LinLink { inner: child_ptr.addr(), key: Ghost(Some(new)) }
    }

    fn read_link(&self, link: LinLink) -> &LinNode
    requires self.valid(link) && !link.is_null() && self.map.wf()
    returns self.follow(link)
    {
        proof!{ use_type_invariant(link); };
        self.map.read(PPtr::from_addr(link.inner), Ghost(link.key@.unwrap()))
    }

    spec fn update_parent_link(&self, child_link: LinLink) -> SpecMap
    recommends self.valid(child_link) && !child_link.is_null()
    {
        let parent_link = self.follow(child_link).parent;
        let parent_key = parent_link.key@.unwrap();
        self@.insert(parent_key@, (self@[parent_key@].0, self@[parent_key@].1.insert(0, child_link.key@.unwrap())))
    }

    fn update_links(&mut self, child_link: LinLink)
    requires
        old(self).map.wf(),
        old(self).locally_finite(),
        exists |parent: <LinKey as View>::V| old(self).future_first_child_of(child_link, parent),
        old(self).almost_correctly_linked(child_link.key@.unwrap()@),
    ensures
        self.wf(),
        self@ == old(self).update_parent_link(child_link)
    {
        proof!{ use_type_invariant(child_link); };
        let parent_link = self.read_link(child_link).parent;
        let parent_ptr = PPtr::from_addr(parent_link.inner);

        proof!{ use_type_invariant(parent_link); };
        let ghost parent_key = parent_link.key@.unwrap();

        assert(self.valid(child_link));
        assert(self.node_conditions(self.follow(child_link)));
        assert(self.valid(parent_link));

        assert(self.node_conditions(self.node_at(parent_key@)));

        proof!{
            if !self.follow(parent_link).child.is_null() {
            }
        };

        let mut parent_node = self.map.take(parent_ptr, Ghost(parent_key), Ghost(Set::empty()));

        if !parent_node.child.is_null() {
            let next_ptr = PPtr::from_addr(parent_node.child.inner);
            proof!{ use_type_invariant(parent_node.child); };
            let ghost next_key = parent_node.child.key@.unwrap();
            let ghost vacated = Set::empty().insert(parent_key@);

            let mut next_node = self.map.take(next_ptr, Ghost(next_key), Ghost(vacated));

            assert(old(self).correctly_linked_vertical(parent_key@));
            assert(next_node.prev.is_null());
            next_node.prev = child_link;

            proof!{ axiom_map_insert_same(self.map@, next_key@, (parent_node.child.inner, MemContents::Init(next_node))); };
            self.map.untake(next_ptr, Ghost(next_key), next_node, Ghost(vacated));
            assert(next_node == self.follow(parent_node.child));
        }

        parent_node.child = child_link;

        proof!{ axiom_map_insert_same(self.map@, parent_key@, (parent_ptr.addr(), MemContents::Init(parent_node))); };
        self.map.untake(parent_ptr, Ghost(parent_key), parent_node, Ghost(Set::empty()));
        assert(parent_node == self.follow(parent_link));

        proof! {
            let next_link = self.follow(child_link).next;
            if next_link.is_null() {
                assert(self.map@ == old(self).map@
                    .insert(parent_key@, (parent_link.inner, MemContents::Uninit))
                    .insert(parent_key@, (parent_link.inner, MemContents::Init(self.follow(parent_link))))
                );
            }
            else {
                let next_key = next_link.key@.unwrap();

                assert(self.map@ == old(self).map@
                    .insert(parent_key@, (parent_link.inner, MemContents::Uninit))
                    .insert(next_key@, (next_link.inner, MemContents::Uninit))
                    .insert(next_key@, (next_link.inner, MemContents::Init(self.follow(next_link))))
                    .insert(parent_key@, (parent_link.inner, MemContents::Init(self.follow(parent_link))))
                );
            }

            assert forall |key: <LinKey as View>::V|
            self.map@.contains_key(key)
            implies #[trigger] self.node_conditions(self.node_at(key))
            by {
                if key == child_link.key@.unwrap()@ {
                    assert(self.node_conditions(self.node_at(key)));
                }
                else if key == parent_key@ {
                    assert(self.node_conditions(self.node_at(key)));
                }
                else if !self.follow(child_link).next.is_null() && self.follow(child_link).next.key@.unwrap()@ == key {
                    assert(old(self).node_conditions(old(self).node_at(key)));
                    assert(self.node_conditions(self.node_at(key)));
                }
                else {
                    assert(old(self).node_conditions(old(self).node_at(key)));
                }
            };

            assert forall |key: <LinKey as View>::V|
            self.map@.contains_key(key)
            implies #[trigger] self.correctly_linked_horizontal(key)
            by {
                if key == child_link.key@.unwrap()@ {
                    assert(self.correctly_linked_horizontal(key));
                }
                else if key == parent_key@ {
                    assert(old(self).correctly_linked_horizontal(parent_key@));
                }
                else if !self.follow(child_link).next.is_null() && self.follow(child_link).next.key@.unwrap()@ == key {
                    assert(old(self).correctly_linked_horizontal(key));
                    assert(self.correctly_linked_horizontal(key));
                }
                else {
                    assert(old(self).correctly_linked_horizontal(key));
                }
            };

            assert forall |key: <LinKey as View>::V|
            self.map@.contains_key(key)
            implies #[trigger] self.correctly_linked_vertical(key)
            by {
                if key == child_link.key@.unwrap()@ {
                    assert(self.correctly_linked_vertical(key));
                }
                else if key == parent_key@ {
                    assert(old(self).correctly_linked_vertical(key));
                    assert(self.correctly_linked_vertical(key));
                }
                else if !self.follow(child_link).next.is_null() && self.follow(child_link).next.key@.unwrap()@ == key {
                    assert(old(self).correctly_linked_vertical(key));
                    assert(self.correctly_linked_vertical(key));
                }
                else {
                    assert(old(self).correctly_linked_vertical(key));
                }
            };

            let old_parent_node = old(self).follow(parent_link);
            let old_parent_children = old(self)@[parent_key@].1;
            let expected = old(self)@
                .insert(parent_key@, (old_parent_node.data, old_parent_children.insert(0, child_link.key@.unwrap())));

            assert forall |key: <LinKey as View>::V| self@.contains_key(key)
            implies self@[key] == #[trigger] expected[key]
            by {
                if key == child_link.key@.unwrap()@ { }
                else if key == parent_key@ {
                    lemma_unchanged_children_rec(old(self), self, self.node_at(key).child);
                }
                else if !self.follow(child_link).next.is_null() && self.follow(child_link).next.key@.unwrap()@ == key {
                    assert(old(self).node_conditions(old(self).node_at(key)));
                    assert(old(self).node_at(key).child == self.node_at(key).child);
                    lemma_unchanged_children_rec(old(self), self, self.node_at(key).child);
                }
                else {
                    assert(old(self).node_conditions(old(self).node_at(key)));
                    lemma_unchanged_children_rec(old(self), self, self.node_at(key).child);
                }
            };

            assert(self@ =~= expected);
        };
    }

    fn insert_and_update(&mut self, data: KobjData, parent: LinKey, new: LinKey)
    requires
        new@ != parent@,
        old(self).wf(),
        old(self).map@.contains_key(parent@),
        !old(self).map@.contains_key(new@),
    ensures
        self.wf(),
        self@ == insert_child(old(self)@, parent, new, data)
    {
        let child_link = self.insert(data, parent, new);

        let ghost parent_key = self.follow(child_link).parent.key@.unwrap();
        assert(parent_key@ == parent@);

        assert(self@ == old(self)@.insert(new@, (data, Seq::empty())));
        assert(self@[parent@] == old(self)@[parent@]);

        assert(child_link.key@.unwrap() == new);

        assert(self.update_parent_link(child_link) ==
            self@.insert(parent_key@, (self@[parent@].0, self@[parent@].1.insert(0, new))));

        assert(self.update_parent_link(child_link) ==
            old(self)@
                .insert(new@, (data, Seq::empty()))
                .insert(parent_key@, (self@[parent@].0, self@[parent@].1.insert(0, new))));

        assert(self.update_parent_link(child_link) =~= insert_child(old(self)@, parent, new, data));

        self.update_links(child_link);
    }
}

proof fn lemma_unchanged_children_rec(old: &LinSystem, new: &LinSystem, link: LinLink)
requires
    new.locally_finite(),
    old.locally_finite(),
    old.valid(link),
    forall |key: <LinKey as View>::V| old.map@.contains_key(key) ==>
        #[trigger] new.map@.contains_key(key),
    forall |key: <LinKey as View>::V| old.map@.contains_key(key) ==>
        #[trigger] new.map@[key].0 == old.map@[key].0,
    forall |key: <LinKey as View>::V| old.map@.contains_key(key) ==>
        new.node_at(key).next == #[trigger] old.node_at(key).next
ensures horizontal_keys(new, link) == horizontal_keys(old, link)
decreases horizontal_keys(old, link).len()
{
    if link.is_null() {
        lemma_is_null_empty_keys(new, link);
        lemma_is_null_empty_keys(old, link);
    }
    else {
        assert(old.valid(link));
        let key = link.key@.unwrap();
        assert(new.map@.contains_key(key@));

        assert(new.valid(link));

        assert(old.follow(link).next == new.follow(link).next);
        let next = old.follow(link).next;

        assert(old.node_conditions(old.follow(link)));
        assert(old.valid(next));

        let old_rest = horizontal_keys(old, next);
        let new_rest = horizontal_keys(new, next);

        assert(horizontal_keys(old, link) == old_rest.insert(0, key));
        assert(horizontal_keys(new, link) == new_rest.insert(0, key));

        lemma_unchanged_children_rec(old, new, next);
    }
}

#[via_fn]
proof fn children_decreases_proof(this: &LinSystem, link: LinLink)
{
    if !link.is_null() && !this.follow(link).next.is_null() {
        let node = this.follow(link);
        assert(this.node_conditions(node));
        assert(this.node_conditions(this.follow(node.next)));
        assert(this.follow(node.next).generation@ < node.generation@);
    }
}

spec fn horizontal_keys(this: &LinSystem, link: LinLink) -> Seq<LinKey>
decreases this.follow(link).generation@
    when this.locally_finite() && this.valid(link)
    via children_decreases_proof
{
    if link.is_null() {
        Seq::empty()
    }
    else {
        if this.follow(link).next.is_null() {
            Seq::empty().insert(0, link.key@.unwrap())
        }
        else {
            let indirect = horizontal_keys(this, this.follow(link).next);
            Seq::insert(indirect, 0, link.key@.unwrap())
        }
    }
}

proof fn lemma_is_null_empty_keys(this: &LinSystem, link: LinLink)
requires link.is_null() && this.locally_finite() && this.valid(link)
ensures horizontal_keys(this, link) == Seq::<LinKey>::empty()
{
    if link.is_null() {
        assert(horizontal_keys(this, link) =~= Seq::<LinKey>::empty());
    }
}

}
