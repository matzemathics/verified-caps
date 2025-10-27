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

use std::{borrow::Borrow, ptr::null_mut};

use vstd::{
    prelude::*,
    raw_ptr::{self, allocate, deallocate, ptr_mut_read, ptr_mut_write, ptr_ref, PointsTo},
};

verus! {

#[cfg(verus_keep_ghost)]
use vstd::{
    set_lib::lemma_len_subset,
    layout::{layout_for_type_is_valid, valid_layout},
};

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
    specs::cap_map::{ActId, CapId, CapKey},
    state::{LinkSystem, Token},
    tables::{ActivityCapTable, HashMetaCapTable, MetaCapTable},
};

pub type ActTable = ActivityCapTable<*mut Node>;

pub struct Node {
    next: *mut Node,
    child: *mut Node,
    back: *mut Node,
    table: *mut ActTable,
    id: CapId,
    activity: ActId,
    first_child: bool,
}

impl Node {
    spec fn key_spec(&self) -> CapKey {
        (self.activity, self.id)
    }

    #[verifier::when_used_as_spec(key_spec)]
    fn key(&self) -> CapKey
    returns self.key()
    {
        (self.activity, self.id)
    }
}

global layout Node is size == 48, align == 8;

tracked struct NodePerm {
    pt: raw_ptr::PointsTo<Node>,
    dealloc: raw_ptr::Dealloc,
}

impl NodePerm {
    #[verifier::type_invariant]
    spec fn wf(&self) -> bool {
        &&& self.pt.is_init()
        &&& self.pt.ptr()@.addr != 0
        &&& self.pt.ptr()@.addr == self.dealloc.addr()
        &&& self.pt.ptr()@.provenance == self.dealloc.provenance()
        &&& self.dealloc.size() == size_of::<Node>()
        &&& self.dealloc.align() == align_of::<Node>()
    }

    spec fn back(&self) -> *mut Node {
        self.pt.value().back
    }

    spec fn next(&self) -> *mut Node {
        self.pt.value().next
    }

    spec fn child(&self) -> *mut Node {
        self.pt.value().child
    }

    spec fn first_child(&self) -> bool {
        self.pt.value().first_child
    }

    proof fn is_init(tracked &self)
    ensures self.pt.is_init()
    {
        use_type_invariant(self)
    }

    proof fn is_wf(tracked &self)
    ensures self.wf()
    {
        use_type_invariant(self)
    }
}

impl Token for NodePerm {
    type Inner = Node;

    closed spec fn ptr(&self) -> *mut Node {
        self.pt.ptr()
    }

    proof fn is_nonnull(tracked &self)
        ensures
            self.ptr()@.addr != 0,
    {
        self.pt.is_nonnull()
    }

    closed spec fn cond(&self, next: *mut Node, child: *mut Node, back: *mut Node, first_child: bool) -> bool {
        &&& self.wf()
        &&& self.back() == back
        &&& self.child() == child
        &&& self.next() == next
        &&& self.first_child() == first_child
    }
}

pub struct Meta {
    table: HashMetaCapTable<*mut Node>,
    instance: Tracked<LinkSystem::Instance<NodePerm>>,
    spec: Tracked<LinkSystem::map<NodePerm>>,
    tokens: Tracked<LinkSystem::all_tokens<NodePerm>>,
    state: Tracked<LinkSystem::state<NodePerm>>,
    generation: Tracked<LinkSystem::depth<NodePerm>>,
}

impl Meta {
    pub fn new() -> (r: Self)
    ensures
        r.wf(),
        r@.dom().is_empty()
    {
        let table = HashMetaCapTable::new();
        let tracked (
            Tracked(instance),
            Tracked(map),
            Tracked(tokens),
            Tracked(state),
            Tracked(generation)
        ) = LinkSystem::Instance::<NodePerm>::empty(Map::tracked_empty());

        Meta {
            table,
            instance: Tracked(instance),
            spec: Tracked(map),
            tokens: Tracked(tokens),
            state: Tracked(state),
            generation: Tracked(generation)
        }
    }

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
            &&& #[trigger] self.tokens@.value()[key].ptr() == self.table@[key]
            &&& self.get(key).key() == key
        }
        &&& forall|key: CapKey| #![auto] self.table@.contains_key(key) ==> {
            self.activity_tables().contains_pair(self.get(key).activity, self.get(key).table)
        }
    }

    pub closed spec fn view(&self) -> CapMap {
        view(self.spec())
    }

    pub closed spec fn activity_tables(&self) -> Map<ActId, *mut ActTable> {
        self.table.activities()
    }

    pub open spec fn correct_table_pointer(&self, activity: ActId, table: *mut ActTable) -> bool {
        self.activity_tables().contains_key(activity) && self.activity_tables()[activity] == table
    }

    proof fn register_activity(tracked &mut self, activity: ActId, tracked permission: PointsTo<ActTable>)
    requires !old(self).activity_tables().contains_key(activity)
    ensures
        self.activity_tables() == old(self).activity_tables().insert(activity, permission.ptr())
    {
        self.table.insert_table(activity, permission);
    }

    pub fn insert_root(&mut self, table: *mut ActTable, key: CapKey)
        requires
            !old(self)@.contains_key(key),
            old(self).wf(),
            old(self).correct_table_pointer(key.0, table)
        ensures
            self.wf(),
    {
        let node = Node {
            next: null_mut(),
            child: null_mut(),
            back: null_mut(),
            table,
            first_child: false,
            activity: key.0,
            id: key.1
        };

        #[cfg(verus_keep_ghost)]
        layout_for_type_is_valid::<Node>();
        let (ptr, Tracked(mut pt), Tracked(dealloc)) = allocate(size_of::<Node>(), align_of::<Node>());
        let tracked pt = pt.into_typed::<Node>(ptr@.addr);
        let tracked _ = pt.is_nonnull();
        let ptr: *mut Node = ptr as _;

        ptr_mut_write(ptr, Tracked(&mut pt), node);
        let tracked token = NodePerm { pt, dealloc };

        let tracked _ = token.is_nonnull();
        let tracked _ = self.instance.borrow_mut().insert_root(
            key,
            token,
            self.spec.borrow_mut(),
            self.tokens.borrow_mut(),
            token,
        );

        self.table.insert(table, key, ptr);
    }

    #[inline(never)]
    pub fn insert_child(&mut self, table: *mut ActTable, parent_table: *mut ActTable, parent: CapKey, child: CapKey)
        requires
            old(self)@.contains_key(parent),
            !old(self)@.contains_key(child),
            old(self).wf(),
            old(self).correct_table_pointer(parent.0, parent_table),
            old(self).correct_table_pointer(child.0, table)
        ensures
            self.wf(),
            self@ == insert_child(old(self)@, parent, child),
            old(self).activity_tables() == self.activity_tables(),
    {
        proof!{
            // needed later to show parent.next != child && parent.back != child
            self.instance.borrow().contains_back(parent, self.spec.borrow());
            self.instance.borrow().contains_next(parent, self.spec.borrow());

            self.instance.borrow().weak_connections(self.spec.borrow());
        };

        let parent_ptr = *self.table.get(parent_table, parent).unwrap();
        let parent_node = self.borrow_node(parent, parent_ptr);

        let node = Node {
            activity: child.0,
            id: child.1,
            next: parent_node.child,
            table,
            child: null_mut(),
            back: parent_ptr,
            first_child: true
        };

        #[cfg(verus_keep_ghost)]
        layout_for_type_is_valid::<Node>();
        let (ptr, Tracked(mut pt), Tracked(dealloc)) = allocate(size_of::<Node>(), align_of::<Node>());
        let tracked pt = pt.into_typed::<Node>(ptr@.addr);
        let tracked _ = pt.is_nonnull();
        let ptr: *mut Node = ptr as _;

        ptr_mut_write(ptr, Tracked(&mut pt), node);
        let tracked token = NodePerm { pt, dealloc };

        self.table.insert(table, child, ptr);

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

        assert(parent_ptr == parent_token.ptr());
        let tracked _ = parent_token.is_wf();
        let tracked NodePerm { pt: parent_pt, dealloc: parent_dealloc } = parent_token;
        let mut parent_node = ptr_mut_read(parent_ptr, Tracked(&mut parent_pt));
        ptr_mut_write(parent_ptr, Tracked(&mut parent_pt), Node { child: ptr, ..parent_node });

        if parent_node.child as usize == 0 {
            proof!{
                self.lemma_child_null_imp_none(&parent_node);
            };
        } else {
            let tracked NodePerm { pt, dealloc } = self.instance.borrow_mut().insert_child_fix_next(
                child,
                parent,
                self.spec.borrow(),
                self.tokens.borrow_mut(),
                self.state.borrow_mut(),
            );

            let next_ptr = parent_node.child;
            assert(next_ptr == pt.ptr());

            let mut next_node = ptr_mut_read(next_ptr, Tracked(&mut pt));
            next_node.back = ptr;
            next_node.first_child = false;
            ptr_mut_write(next_ptr, Tracked(&mut pt), next_node);

            let ghost next = self.spec()[parent].child.unwrap();
            let tracked _ = self.instance.borrow_mut().insert_child_finish_next(
                NodePerm { pt, dealloc },
                child,
                parent,
                next,
                self.spec.borrow_mut(),
                self.tokens.borrow_mut(),
                self.state.borrow_mut(),
                NodePerm { pt, dealloc },
            );
        }

        proof! {
            let tracked parent_token = NodePerm { pt: parent_pt, dealloc: parent_dealloc };

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
                &&& self.tokens@.value()[key].ptr() == self.table@[key]
                &&& self.get(key).key() == key
            }
            by {
                assert(self.tokens@.value()[key].ptr() == self.table@[key]);
            };
            assert(self.wf());

            assert(self.spec() == (OpInsertChild { parent, child }).update(old(self).spec()));

            assert(self@.dom() == old(self)@.dom().insert(child));

            (OpInsertChild{parent, child}).lemma_view_update(old(self).spec());
            assert(self@ == insert_child(old(self)@, parent, child));
        };
    }

    pub fn revoke_single(&mut self, table: *mut ActTable, key: CapKey)
        requires
            old(self).wf(),
            old(self)@.contains_key(key),
            old(self)@[key].children.len() == 0,
            old(self).correct_table_pointer(key.0, table)
        ensures
            self.wf(),
            self@.dom() == old(self)@.dom().remove(key),
            self@ == revoke_single_parent_update(old(self)@, key).remove(key),
            old(self).activity_tables() == self.activity_tables(),
    {
        let tracked _ = self.instance.borrow().clean_links(self.spec.borrow(), self.state.borrow());
        let tracked token = self.instance.borrow_mut().revoke_single(
            key,
            self.spec.borrow(),
            self.tokens.borrow(),
            self.state.borrow_mut(),
        );

        let ptr = *self.table.get(table, key).unwrap();
        assert(ptr == token.ptr());
        let tracked _ = token.is_wf();
        let tracked NodePerm { pt: rev_pt, dealloc: rev_dealloc } = token;
        let node = ptr_mut_read(ptr, Tracked(&mut rev_pt));

        if node.back as usize == 0 {
            proof!{ self.lemma_back_null_imp_none(&node); }
        } else {
            let tracked tok = self.instance.borrow_mut().revoke_take_back(
                self.spec.borrow(),
                self.tokens.borrow(),
                self.state.borrow_mut(),
            );

            assert(node.back == tok.ptr());
            let tracked NodePerm { pt, dealloc } = tok;
            let mut back_node: Node = ptr_mut_read(node.back, Tracked(&mut pt));

            match node.first_child {
                true => back_node.child = node.next,
                false => back_node.next = node.next,
            }

            ptr_mut_write(node.back, Tracked(&mut pt), back_node);
            let tracked _ = self.instance.borrow_mut().revoke_put_back(
                NodePerm { pt, dealloc },
                self.spec.borrow_mut(),
                self.tokens.borrow_mut(),
                self.state.borrow_mut(),
                NodePerm { pt, dealloc },
            );
        }

        if node.next as usize == 0 {
            proof!{ self.lemma_next_null_imp_none(&node); }
        } else {
            let tracked tok = self.instance.borrow_mut().revoke_take_next(
                self.spec.borrow(),
                self.tokens.borrow(),
                self.state.borrow_mut(),
            );

            assert(node.next == tok.ptr());
            let tracked NodePerm { pt, dealloc } = tok;
            let mut next_node = ptr_mut_read(node.next, Tracked(&mut pt));

            next_node.back = node.back;
            next_node.first_child = node.first_child;

            ptr_mut_write(node.next, Tracked(&mut pt), next_node);
            let tracked _ = self.instance.borrow_mut().revoke_put_next(
                NodePerm { pt, dealloc },
                self.spec.borrow_mut(),
                self.tokens.borrow_mut(),
                self.state.borrow_mut(),
                NodePerm { pt, dealloc },
            );
        }

        self.table.remove(table, key);
        let tracked rev_pt = rev_pt.into_raw();
        deallocate(ptr as _, size_of::<Node>(), align_of::<Node>(), Tracked(rev_pt), Tracked(rev_dealloc));

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
                &&& self.tokens@.value()[key].ptr() == self.table@[key]
                &&& self.get(key).key() == key
            }
            by {
                assert(self.tokens@.value()[key].ptr() == self.table@[key]);
            };

            assert(self.dom() == old(self).dom().remove(key));
            assert(self@.dom() == old(self)@.dom().remove(key));
        };
    }

    pub fn revoke_children(&mut self, table: *mut ActTable, key: CapKey)
        requires
            old(self).wf(),
            old(self)@.contains_key(key),
            old(self).correct_table_pointer(key.0, table),
        ensures
            self.wf(),
            self@.contains_key(key),
            self@[key].children.len() == 0,
            self@.dom() == old(self)@.dom().difference(transitive_children(old(self)@, key)).insert(key),
            self@.remove(key) == old(self)@.remove_keys(transitive_children(old(self)@, key)),
            old(self).activity_tables() == self.activity_tables(),
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
                self.correct_table_pointer(key.0, table),
                self@.contains_key(key),
                self.dom().disjoint(revoked_keys),
                old(self).dom() == self.dom().union(revoked_keys),
                subtree == transitive_children(view(self.spec()), key).union(revoked_keys),
                view(old(self).spec()).remove_keys(subtree) == view(self.spec()).remove_keys(
                    subtree,
                ),
                old(self).activity_tables() == self.activity_tables(),
            ensures
                self.spec()[key].child.is_none(),
                old(self).activity_tables() == self.activity_tables(),
            decreases
                self.dom().len()
        {
            let child = self.first_child(table, key);
            let tracked _ = self.lemma_child_null_imp_none(child);

            if child.activity == key.0 && child.id == key.1 {
                break
            }

            let tracked _ = {
                self.instance.borrow().weak_connections(self.spec.borrow());
                lemma_view_acyclic(self.spec());
                self.instance.borrow().clean_links(self.spec.borrow(), self.state.borrow());
            };

            let ghost pre = self.spec();
            assert(self@ == view(pre));
            assert(self.activity_tables().contains_pair(self.get(child.key()).activity, self.get(child.key()).table));
            self.revoke_single(child.table, child.key());
            assert(view(pre).dom() == pre.dom());
            assert(self.dom() == pre.dom().remove(child.key()));

            let tracked _ = {
                self.instance.borrow().weak_connections(self.spec.borrow());
                lemma_view_acyclic(self.spec());
                lemma_revoke_transitive_changes(pre, child.key(), key);
                lemma_revoke_transitive_non_changes(pre, child.key(), key, subtree);

                revoked_keys = revoked_keys.insert(child.key());
                assert(old(self).dom() == self.dom().union(revoked_keys));

                assert(subtree == transitive_children(view(self.spec()), key).union(revoked_keys));
                assert(subtree.contains(child.key()));

                if let Some(parent) = get_parent(view(self.spec()), child.key()) {
                    assert(transitive_child_of(view(pre), child.key(), key));
                    lemma_view_tree_ish(pre);
                    lemma_transitive_child_parent(view(pre), key, parent, child.key());
                    lemma_depth_increase(view(pre), parent, child.key());
                    assert(transitive_child_of(view(pre), parent, parent));
                    lemma_still_transitive_child(view(pre), key, parent, child.key());
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

    #[inline]
    fn borrow_node(&self, key: CapKey, ptr: *mut Node) -> (res: &Node)
        requires
            self.wf(),
            self@.contains_key(key),
            self.table@[key] == ptr,
        ensures
            self.get(key) == res,
            self.contains(res),
            res.key() == key,
    {
        let tracked borrow = self.instance.borrow().borrow_token(
            key,
            self.spec.borrow(),
            self.tokens.borrow(),
            self.state.borrow(),
        );
        assert(ptr == borrow.ptr());
        let tracked _ = borrow.is_init();
        assert(borrow.pt.value().key() == key);
        ptr_ref(ptr as *const _, Tracked(&borrow.pt))
    }

    spec fn contains(&self, node: &Node) -> bool {
        &&& self@.contains_key(node.key())
        &&& self.get(node.key()) == node
    }

    spec fn get(&self, key: CapKey) -> Node {
        self.tokens@.value()[key].pt.value()
    }

    spec fn dom(&self) -> Set<CapKey> {
        self.spec().dom()
    }

    spec fn spec(&self) -> LinkMap {
        self.spec@.value()
    }

    fn first_child(&self, table: *mut ActTable, parent: CapKey) -> (res: &Node)
        requires
            self.wf(),
            self@.contains_key(parent),
            self.correct_table_pointer(parent.0, table),
        ensures
            res.child@.addr == 0,
            self.contains(res),
            transitive_child_of(view(self.spec()), res.key(), parent),
    {
        let parent_ptr = *self.table.get(table, parent).unwrap();
        let mut res = self.borrow_node(parent, parent_ptr);
        let tracked _ = self.instance.borrow().weak_connections(self.spec.borrow());
        let tracked _ = lemma_view_acyclic(self.spec());
        assert(transitive_child_of(view(self.spec()), res.key(), parent));

        while res.child as usize != 0
            invariant
                self.wf(),
                self@.contains_key(parent),
                self.contains(res),
                transitive_child_of(view(self.spec()), res.key(), parent),
            decreases
                self.generation@.value() - self.spec()[res.key()].depth
        {
            let tracked token = {
                self.instance.borrow().contains_child(res.key(), self.spec.borrow());
                self.instance.borrow().token_invariant(res.key(), self.spec.borrow(), self.tokens.borrow());
                let ghost next = self.spec()[res.key()].child.unwrap();

                self.instance.borrow().weak_connections(self.spec.borrow());
                lemma_siblings_unfold(self.spec(), next);
                assert(self.spec()[res.key()].depth < self.spec()[next].depth) by {
                    assert(decreasing_condition::<Child>(self.spec(), res.key()));
                };
                assert(siblings(self.spec(), Some(next)).last() == next);
                assert(view(self.spec())[res.key()].children.contains(next));
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

            res = ptr_ref(res.child, Tracked(&token.pt));
        }

        res
    }

    fn cap_in(&self, table: *mut ActTable, activity: ActId) -> (res: Option<CapKey>)
    requires self.wf(), self.correct_table_pointer(activity, table)
    ensures
        res matches Some(key) ==> key.0 == activity && self.dom().contains(key),
        res matches None ==> self.dom().filter(|key: CapKey| key.0 == activity).is_empty()
    {
        let act_table = self.table.get_act_table(table, Ghost(activity));
        act_table.get_element()
    }

    pub fn revoke_all(&mut self, table: *mut ActTable, activity: ActId)
        requires
            old(self).wf(),
            old(self).correct_table_pointer(activity, table)
        ensures
            self.wf(),
            self@.dom().filter(|key: CapKey| key.0 == activity).is_empty()
    {
        broadcast use vstd::set::group_set_axioms;

        loop
            invariant self.wf() && self.correct_table_pointer(activity, table)
            ensures self@.dom().filter(|key: CapKey| key.0 == activity).is_empty()
            decreases self.dom().len()
        {
            let Some(cap) = self.cap_in(table, activity) else { break; };
            let ghost before = self.dom();
            assert(before.finite());

            self.revoke_children(table, cap);
            let ghost here = self.dom();
            assert(self@.dom().subset_of(before));
            let tracked _ = lemma_len_subset(self.dom(), before);
            assert(self.dom().len() <= before.len());

            self.revoke_single(table, cap);
            assert(self@.dom() =~= here.remove(cap));
            assert(self.dom() == here.remove(cap));
            assert(self.dom().len() == here.len() - 1);
        }
    }

    proof fn lemma_next_null_imp_none(tracked &self, node: &Node)
        requires
            node.next@.addr == 0,
            self.contains(node),
            self.ties(),
        ensures
            self.spec()[node.key()].next.is_none(),
    {
        let next_key = self.spec()[node.key()].next;
        if next_key.is_some() {
            self.instance.borrow().token_invariant(
                node.key(),
                self.spec.borrow(),
                self.tokens.borrow(),
            );
            self.instance.borrow().contains_next(node.key(), self.spec.borrow());
            self.instance.borrow().token_invariant(
                next_key.unwrap(),
                self.spec.borrow(),
                self.tokens.borrow()
            );
            assert(node.child@.addr != 0);
        }
    }

    proof fn lemma_child_null_imp_none(tracked &self, node: &Node)
        requires
            node.child@.addr == 0,
            self.contains(node),
            self.ties(),
        ensures
            self.spec()[node.key()].child.is_none(),
    {
        // prove that key.child == None in this case
        let child_key = self.spec()[node.key()].child;
        if child_key.is_some() {
            self.instance.borrow().token_invariant(
                node.key(),
                self.spec.borrow(),
                self.tokens.borrow(),
            );
            self.instance.borrow().contains_child(node.key(), self.spec.borrow());
            self.instance.borrow().token_invariant(
                child_key.unwrap(),
                self.spec.borrow(),
                self.tokens.borrow(),
            );
            assert(node.child@.addr != 0);
        }
    }

    proof fn lemma_back_null_imp_none(tracked &self, node: &Node)
        requires
            node.back@.addr == 0,
            self.contains(node),
            self.ties(),
        ensures
            self.spec()[node.key()].back.is_none(),
    {
        // prove that key.back == None in this case
        let back_key = self.spec()[node.key()].back;
        if back_key.is_some() {
            self.instance.borrow().token_invariant(
                node.key(),
                self.spec.borrow(),
                self.tokens.borrow(),
            );
            self.instance.borrow().contains_back(node.key(), self.spec.borrow());
            self.instance.borrow().token_invariant(
                back_key.unwrap(),
                self.spec.borrow(),
                self.tokens.borrow(),
            );
            assert(node.back@.addr != 0);
        }
    }
}

} // verus!
