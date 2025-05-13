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
        link.is_null() ||
        self.map@.contains_key(link.key@.unwrap()@) && self.map@[link.key@.unwrap()@].0 == link.inner
    }

    spec fn follow(&self, link: LinLink) -> LinNode
    recommends self.valid(link) && !link.is_null()
    {
        self.map@[link.key@.unwrap()@].1.value()
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

    spec fn correctly_linked_horizontal(&self, key: <LinKey as View>::V, node: LinNode) -> bool
    recommends self.node_conditions(node)
    {
        &&& !node.next.is_null() ==>
            !self.follow(node.next).prev.is_null() && self.follow(node.next).prev.key@.unwrap()@ == key
        &&& !node.prev.is_null() ==>
            !self.follow(node.prev).next.is_null() && self.follow(node.prev).next.key@.unwrap()@ == key
    }

    spec fn correctly_linked_vertical(&self, key: <LinKey as View>::V, node: LinNode) -> bool
    recommends self.node_conditions(node)
    {
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

    spec fn wf(&self) -> bool {

        &&& self.map.wf()
        &&& self.locally_finite()
        &&& self.correctly_linked()
    }

    spec fn locally_finite(&self) -> bool {

        &&& self.map.wf()
        &&& forall |key: <LinKey as View>::V| self.map@.contains_key(key) ==> {
            let node = #[trigger] self.map@[key].1.value(); {
                &&& self.node_conditions(node)
            }
        }
    }

    spec fn correctly_linked(&self) -> bool {
        forall |key: <LinKey as View>::V| self.map@.contains_key(key) ==> {
            let node = #[trigger] self.map@[key].1.value(); {
                &&& self.correctly_linked_horizontal(key, node)
                &&& self.correctly_linked_vertical(key, node)
            }
        }
    }

    spec fn almost_correctly_linked(&self, exception: <LinKey as View>::V) -> bool {
        forall |key: <LinKey as View>::V| self.map@.contains_key(key) && key != exception ==> {
            let node = #[trigger] self.map@[key].1.value(); {
                &&& self.correctly_linked_horizontal(key, node)
                &&& self.correctly_linked_vertical(key, node)
            }
        }
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
        r.key@.unwrap()@ == new@
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

        assert(self.map@ =~= old(self).map@
            .insert(new@, (child_ptr.addr(), MemContents::Init(node))));

        proof! {
            lemma_unchanged_children(old(self), self);

            assert forall |key: <LinKey as View>::V| self@.contains_key(key)
            implies self@[key] == #[trigger] old(self)@.insert(new@, (data, Seq::empty()))[key]
            by {
                if key == new@ {
                    assert(horizontal_keys(self, LinLink::null()) == Seq::<LinKey>::empty()) by (compute);
                    assert(self@[key] == (data, Seq::<LinKey>::empty()));
                }
                else {
                    let node = self.map@[key].1.value();
                    assert(old(self).map@.contains_key(key) && node == old(self).map@[key].1.value());
                    assert(old(self).valid(node.child));
                    assert(horizontal_keys(self, node.child) == horizontal_keys(old(self), node.child));
                    assert(self@[key] == old(self)@[key]);
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

    fn update_links(&mut self, child_link: LinLink)
    requires
        old(self).map.wf(),
        old(self).locally_finite(),
        exists |parent: <LinKey as View>::V| old(self).future_first_child_of(child_link, parent),
        old(self).almost_correctly_linked(child_link.key@.unwrap()@),
    ensures
        self.wf()
    {
        proof!{ use_type_invariant(child_link); };
        let parent_link = self.read_link(child_link).parent;
        let parent_ptr = PPtr::from_addr(parent_link.inner);
        let ghost parent_key = parent_link.key@.unwrap();

        let mut parent_node = self.map.take(parent_ptr, Ghost(parent_key), Ghost(Set::empty()));

        if !parent_node.child.is_null() {
            let next_ptr = PPtr::from_addr(parent_node.child.inner);
            proof!{ use_type_invariant(parent_node.child); };
            let ghost next_key = parent_node.child.key@.unwrap();
            let ghost vacated = Set::empty().insert(parent_key@);

            let mut next_node = self.map.take(next_ptr, Ghost(next_key), Ghost(vacated));

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
                assert(self.map@ =~= old(self).map@
                    .insert(parent_key@, (parent_link.inner, MemContents::Init(self.follow(parent_link))))
                );
            }
            else {
                let next_key = next_link.key@.unwrap();
                let next_uninit = (next_link.inner, MemContents::<LinNode>::Uninit);
                let next_value = (next_link.inner, MemContents::Init(self.follow(next_link)));
                let parent_uninit = (parent_link.inner, MemContents::<LinNode>::Uninit);
                let parent_value = (parent_link.inner, MemContents::Init(self.follow(parent_link)));
                let expected_map = old(self).map@.insert(next_key@, next_value).insert(parent_key@, parent_value);

                assert(self.map@.dom() == expected_map.dom());
                self.map.lemma_is_init(next_key@);

                assert(self.map@ == old(self).map@
                    .insert(parent_key@, parent_uninit)
                    .insert(next_key@, next_uninit)
                    .insert(next_key@, next_value)
                    .insert(parent_key@, parent_value)
                );

                assert forall |key: <LinKey as View>::V| self.map@.contains_key(key)
                implies self.map@[key] == expected_map[key]
                by { };
            }

            assert forall |key: <LinKey as View>::V|
            self.map@.contains_key(key)
            implies {
                self.node_conditions(self.map@[key].1.value()) &&
                self.correctly_linked_horizontal(key, #[trigger] self.map@[key].1.value()) &&
                self.correctly_linked_vertical(key, self.map@[key].1.value())
            }
            by {
                if key == child_link.key@.unwrap()@ { }
                else if key == parent_key@ { }
                else if !self.follow(child_link).next.is_null() && self.follow(child_link).next.key@.unwrap()@ == key { }
                else { }
            };
        };
    }
}

proof fn lemma_unchanged_children(old: &LinSystem, new: &LinSystem)
requires forall |key: <LinKey as View>::V| old.map@.contains_key(key) ==> new.map@[key] == #[trigger] old.map@[key]
ensures forall |link: LinLink| old.valid(link) ==> #[trigger] horizontal_keys(new, link) == horizontal_keys(old, link)
{
    admit();
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

proof fn lemma_next_link_insert(tracked this: &LinSystem, link: LinLink)
requires
    this.locally_finite(),
    this.valid(link) && this.valid(this.follow(link).next),
    !link.is_null(),
ensures
    horizontal_keys(this, link) == horizontal_keys(this, this.follow(link).next).insert(0, link.key@.unwrap())
{
    if this.follow(link).next.is_null() {
        assert(horizontal_keys(this, link) =~= Seq::empty().insert(0, link.key@.unwrap()));
        assert(horizontal_keys(this, this.follow(link).next) =~= Seq::empty());
    }
    else {
        assert(horizontal_keys(this, link) =~= horizontal_keys(this, this.follow(link).next).insert(0, link.key@.unwrap()));
    }
}

}
