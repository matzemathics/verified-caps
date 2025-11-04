//! This module defines the traits and structures used for
//! the hash-table implementation of a `Meta`-capability-system

use vstd::{
    prelude::*,
    raw_ptr::{ptr_mut_read, ptr_mut_write, ptr_ref, PointsTo},
};

#[cfg(verus_keep_ghost)]
use vstd::std_specs::hash::*;

use crate::{
    meta::ActTable,
    specs::cap_map::{ActId, CapId, CapKey},
};

use std::{borrow::Borrow, collections::HashMap};

verus! {

broadcast use vstd::std_specs::hash::group_hash_axioms;

/// The interface definition of a capability table.
/// Currently only implemented by [`HashCapTable`]
pub trait CapTable: View<V = Map<CapId, Self::Cap>> {
    /// The type of capability node (pointers) stored in this table
    type Cap;

    /// Get an arbitrary key currently present in the capability table
    fn get_element(&self) -> (res: Option<CapId>)
    ensures
        res matches Some(value) ==> self@.contains_key(value),
        res matches None ==> self@.is_empty();

    /// Insert a capability node into the table
    fn insert(&mut self, key: CapId, value: Self::Cap)
    ensures
        self@ == old(self)@.insert(key, value),
        ;

    /// Remove a capability node from the table
    fn remove(&mut self, key: CapId)
    ensures
        self@ == old(self)@.remove(key),
        ;

    /// Get a reference to a capability node in the table
    fn get(&self, key: CapId) -> (result: Option<&Self::Cap>)
    ensures
        result matches Some(v) ==> self@.contains_key(key@) && *v == self@[key@],
        result matches None ==> !self@.contains_key(key@);
}

/// The interface of a table of capability tables.
/// Implemented by [`MetaCapTableImpl`].
pub trait MetaCapTable<Value>: View<V = Map<CapKey, Value>> {
    /// The type of [`CapTable`] managed by this meta table
    type ActTable : CapTable<Cap = Value>;

    /// The map of all capability tables
    spec fn activities(&self) -> Map<ActId, *mut Self::ActTable>;

    /// Take logical ownership of a capability table
    proof fn insert_table(
        tracked &mut self,
        act: ActId,
        tracked perm: PointsTo<Self::ActTable>
    )
        ensures
            self.activities() == old(self).activities().insert(act, perm.ptr()),
    ;

    /// Insert a node into a capability table
    fn insert(&mut self, table: *mut Self::ActTable, k: CapKey, v: Value)
        requires
            old(self).wf(),
            old(self).activities().contains_pair(k.0, table),
        ensures
            self.wf(),
            self.activities() == old(self).activities(),
            self@ == old(self)@.insert(k@, v);

    /// Remove a node from a capability table
    fn remove(&mut self, table: *mut Self::ActTable, k: CapKey)
        requires
            old(self).wf(),
            old(self).activities().contains_pair(k.0, table),
        ensures
            self.wf(),
            self@ == old(self)@.remove(k@),
            self.activities() == old(self).activities();

    /// Get a reference to a node from a capability table
    fn get(&self, table: *mut Self::ActTable, k: CapKey) -> (result: Option<&Value>)
        requires
            self.wf(),
            self.activities().contains_pair(k.0, table),
        ensures
            result matches Some(v) ==> self@.contains_key(k@) && *v == self@[k@],
            result matches None ==> !self@.contains_key(k@);

    /// Well-formedness invariant of this meta table
    spec fn wf(&self) -> bool;

    /// Get an immutable reference to an activity table
    fn get_act_table(&self, table: *mut Self::ActTable, act: ActId) -> (result: &Self::ActTable)
        requires
            self.wf(),
            self.activities().contains_pair(act, table),
        ensures
            self@.dom()
                .filter(|k: CapKey| k.0 == act)
                .map(|k: CapKey| k.1) == result@.dom(),
            result@.is_empty() ==> self@.dom().filter(|k: CapKey| k.0 == act).is_empty()
            ;
}

/// Default implementation of a capability table, based on [`std::collections::hash_map`]
pub struct HashCapTable<Value> {
    caps: HashMap<CapId, Value>
}

impl<Value> HashCapTable<Value> {
    /// Create a new empty capability table.
    pub fn new() -> Self {
        Self { caps: HashMap::new() }
    }
}

impl<Value> View for HashCapTable<Value> {
    type V = Map<CapId, Value>;

    closed spec fn view(&self) -> Self::V {
        self.caps@
    }
}

impl<Value> CapTable for HashCapTable<Value> {
    type Cap = Value;

    fn get_element(&self) -> (res: Option<CapId>)
    {
        let mut iter = self.caps.keys();
        let cap =  iter.next()?;
        Some(*cap)
    }

    fn insert(&mut self, key: CapId, value: Self::Cap) {
        self.caps.insert(key, value);
    }

    fn remove(&mut self, key: CapId) {
        self.caps.remove(&key);
    }

    fn get(&self, key: CapId) -> (result: Option<&Self::Cap>)
    {
        self.caps.get(&key)
    }
}

/// Default implementation for a [`MetaCapTable`].
/// This struct is purely ghost (i.e. compiles to a ZST).
pub struct MetaCapTableImpl<T: CapTable> {
    tokens: Tracked<Map<ActId, PointsTo<T>>>
}

impl<T: CapTable> MetaCapTableImpl<T> {
    /// Create a new [`MetaCapTableImpl`]
    pub fn new() -> (r: Self)
    ensures
        r@.dom().is_empty(),
        r.wf()
    {
        Self { tokens: Tracked(Map::tracked_empty()) }
    }
}

impl<T: CapTable> View for MetaCapTableImpl<T> {
    type V = Map<CapKey, T::Cap>;

    closed spec fn view(&self) -> Self::V {
        Map::new(
            |key: CapKey| {
                &&& self.tokens@.contains_key(key.0)
                &&& self.tokens@[key.0].value()@.contains_key(key.1)
            },
            |key: CapKey| self.tokens@[key.0].value()@[key.1])
    }
}

impl<T: CapTable> MetaCapTableImpl<T> {
    broadcast proof fn contains_pt(&self, act: ActId, table: *mut T)
        requires #[trigger] self.activities().contains_pair(act, table),
        ensures
            self.tokens@.contains_key(act),
            self.tokens@[act].ptr() == table
    {}
}

impl<T: CapTable> MetaCapTable<T::Cap> for MetaCapTableImpl<T> {
    type ActTable = T;

    fn insert(&mut self, table_ptr: *mut T, k: CapKey, v: T::Cap)
    {
        proof! { self.contains_pt(k.0, table_ptr) };
        let tracked token = self.tokens.borrow_mut().tracked_remove(k.0);
        let mut table = ptr_mut_read(table_ptr, Tracked(&mut token));
        table.insert(k.1, v);
        ptr_mut_write(table_ptr, Tracked(&mut token), table);
        let tracked _ = self.tokens.borrow_mut().tracked_insert(k.0, token);
        assert(self@ =~= old(self)@.insert(k@, v));
    }

    fn remove(&mut self, table_ptr: *mut T, k: CapKey)
    {
        let tracked token = self.tokens.borrow_mut().tracked_remove(k.0);
        let mut table = ptr_mut_read(table_ptr, Tracked(&mut token));
        table.remove(k.1);
        ptr_mut_write(table_ptr, Tracked(&mut token), table);
        let tracked _ = self.tokens.borrow_mut().tracked_insert(k.0, token);
        assert(self@ =~= old(self)@.remove(k@));
    }

    fn get(&self, table: *mut T, k: CapKey) -> (result: Option<&T::Cap>)
    {
        let tracked token = self.tokens.borrow().tracked_borrow(k.0);
        let table = ptr_ref(table, Tracked(token));
        table.get(k.1)
    }

    closed spec fn wf(&self) -> bool {
        forall |act: ActId| #![auto] self.tokens@.contains_key(act) ==> {
            &&& self.tokens@[act].is_init()
        }
    }

    fn get_act_table(&self, table: *mut T, act: ActId) -> &Self::ActTable
    {
        let res = ptr_ref(table, Tracked(self.tokens.borrow().tracked_borrow(act@)));

        proof!{
            let a = self@.dom().filter(|k: CapKey| k.0 == act@);
            assert forall |k: CapId| #![auto] res@.contains_key(k)
            implies a.map(|ck: CapKey| ck.1).contains(k)
            by { assert(a.contains((act@, k))); };
        };

        res
    }

    closed spec fn activities(&self) -> Map<ActId, *mut Self::ActTable> {
        self.tokens@.map_values(|pt: PointsTo<_>| pt.ptr())
    }

    proof fn insert_table(
        tracked &mut self,
        act: ActId,
        tracked perm: PointsTo<Self::ActTable>
    )
    {
        self.tokens.borrow_mut().tracked_insert(act, perm);
    }
}

}
