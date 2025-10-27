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

mod cell_map;
use cell_map::MutMap;

use std::{borrow::Borrow, collections::HashMap};

verus! {

broadcast use vstd::std_specs::hash::group_hash_axioms;

pub trait MetaCapTable<Value>: View<V = Map<CapKey, Value>> {
    type ActTable : View<V = Map<CapKey, Value>>;

    spec fn activities(&self) -> Map<ActId, *mut Self::ActTable>;

    proof fn insert_table(
        tracked &mut self,
        act: ActId,
        tracked perm: PointsTo<Self::ActTable>
    )
        ensures
            self.activities() == old(self).activities().insert(act, perm.ptr()),
    ;

    fn insert(&mut self, table: *mut Self::ActTable, k: CapKey, v: Value)
        requires
            old(self).wf(),
            old(self).activities().contains_pair(k.0, table),
        ensures
            self.wf(),
            self.activities() == old(self).activities(),
            self@ == old(self)@.insert(k@, v);

    fn remove(&mut self, table: *mut Self::ActTable, k: CapKey)
        requires
            old(self).wf(),
            old(self).activities().contains_pair(k.0, table),
        ensures
            self.wf(),
            self@ == old(self)@.remove(k@),
            self.activities() == old(self).activities();

    fn get(&self, table: *mut Self::ActTable, k: CapKey) -> (result: Option<&Value>)
        requires
            self.wf(),
            self.activities().contains_pair(k.0, table),
        ensures
            result matches Some(v) ==> self@.contains_key(k@) && *v == self@[k@],
            result matches None ==> !self@.contains_key(k@);

    spec fn wf(&self) -> bool;

    fn get_act_table(&self, table: *mut Self::ActTable, act: Ghost<ActId>) -> (result: &Self::ActTable)
        requires
            self.wf(),
            self.activities().contains_pair(act@, table),
        ensures
            self@.restrict(Set::new(|k: CapKey| k.0 == act@)) == result@,
            ;
}

pub struct ActivityCapTable<Value> {
    activity_id: ActId,
    caps: HashMap<CapId, Value>
}

impl<Value> View for ActivityCapTable<Value> {
    type V = Map<CapKey, Value>;

    closed spec fn view(&self) -> Self::V {
        Map::new(
            |key: CapKey| key.0 == self.activity_id && self.caps@.contains_key(key.1),
            |key: CapKey| self.caps@[key.1])
    }
}

impl<Value> ActivityCapTable<Value> {
    pub fn get_element(&self) -> (res: Option<CapKey>)
    ensures
        res matches Some(value) ==> self@.contains_key(value),
        res matches None ==> self@.is_empty()
    {
        let mut iter = self.caps.keys();
        let cap =  iter.next()?;
        Some((self.activity_id, *cap))
    }
}

#[verifier::reject_recursive_types(Value)]
pub struct HashMetaCapTable<Value> {
    tokens: Tracked<Map<ActId, PointsTo<ActivityCapTable<Value>>>>
}

impl<V> HashMetaCapTable<V> {
    pub fn new() -> (r: Self)
    ensures
        r@.dom().is_empty(),
        r.wf()
    {
        Self { tokens: Tracked(Map::tracked_empty()) }
    }
}

impl<Value> View for HashMetaCapTable<Value> {
    type V = Map<CapKey, Value>;

    closed spec fn view(&self) -> Self::V {
        Map::new(
            |key: CapKey| {
                &&& self.tokens@.contains_key(key.0)
                &&& self.tokens@[key.0].value().caps@.contains_key(key.1)
            },
            |key: CapKey| self.tokens@[key.0].value().caps@[key.1])
    }
}

impl<Value> HashMetaCapTable<Value> {
    spec fn wf_activity(&self, act: ActId) -> bool {
        &&& self.tokens@[act].value().activity_id == act
        &&& self.tokens@[act].is_init()
        &&& self@.restrict(Set::new(|key: CapKey| key.0 == act)) == self.tokens@[act].value()@
    }

    proof fn wf_activity_from_wf(&self, act: ActId)
        requires self.wf() && self.tokens@.contains_key(act)
        ensures self.wf_activity(act)
    {
        assert(self.tokens@[act].value().activity_id == act);
        assert(self.tokens@[act].is_init());
        assert(self@.restrict(Set::new(|key: CapKey| key.0 == act)) == self.tokens@[act].value()@);
    }

    broadcast proof fn contains_pt(&self, act: ActId, table: *mut ActivityCapTable<Value>)
        requires #[trigger] self.activities().contains_pair(act, table),
        ensures
            self.tokens@.contains_key(act),
            self.tokens@[act].ptr() == table
    {}
}

impl<Value> MetaCapTable<Value> for HashMetaCapTable<Value> {
    type ActTable = ActivityCapTable<Value>;

    fn insert(&mut self, table_ptr: *mut ActivityCapTable<Value>, k: CapKey, v: Value)
    {
        proof! { self.contains_pt(k.0, table_ptr) };
        let tracked token = self.tokens.borrow_mut().tracked_remove(k.0);
        let mut table = ptr_mut_read(table_ptr, Tracked(&mut token));
        table.caps.insert(k.1, v);
        ptr_mut_write(table_ptr, Tracked(&mut token), table);
        let tracked _ = self.tokens.borrow_mut().tracked_insert(k.0, token);

        assert(forall |act: ActId| #![auto]
            self.tokens@.contains_key(act) ==> self@.restrict(Set::new(|key: CapKey| key.0 == act)) == self.tokens@[act].value()@);
        assert(self@ =~= old(self)@.insert(k@, v));
    }

    fn remove(&mut self, table_ptr: *mut ActivityCapTable<Value>, k: CapKey)
    {
        let tracked token = self.tokens.borrow_mut().tracked_remove(k.0);
        let mut table = ptr_mut_read(table_ptr, Tracked(&mut token));
        table.caps.remove(&k.1);
        ptr_mut_write(table_ptr, Tracked(&mut token), table);
        let tracked _ = self.tokens.borrow_mut().tracked_insert(k.0, token);

        assert(forall |act: ActId|  #![auto]
            self.tokens@.contains_key(act) ==> self@.restrict(Set::new(|key: CapKey| key.0 == act)) == self.tokens@[act].value()@);
        assert(self@ =~= old(self)@.remove(k@));
    }

    fn get(&self, table: *mut ActivityCapTable<Value>, k: CapKey) -> (result: Option<&Value>)
    {
        let tracked token = self.tokens.borrow().tracked_borrow(k.0);
        let table = ptr_ref(table, Tracked(token));
        table.caps.get(&k.1)
    }

    closed spec fn wf(&self) -> bool {
        forall |act: ActId| #![auto] self.tokens@.contains_key(act) ==> {
            &&& self.tokens@[act].value().activity_id == act
            &&& self.tokens@[act].is_init()
            &&& self@.restrict(Set::new(|key: CapKey| key.0 == act)) == self.tokens@[act].value()@
        }
    }

    fn get_act_table(&self, table: *mut ActivityCapTable<Value>, act: Ghost<ActId>) -> (result: &Self::ActTable)
    {
        ptr_ref(table, Tracked(self.tokens.borrow().tracked_borrow(act@)))
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
