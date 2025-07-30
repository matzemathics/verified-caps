use vstd::{prelude::*, std_specs::hash::*};

use crate::{
    cell_map::MutMap,
    tcb::{ActId, CapId, CapKey},
};

use std::collections::HashMap;

verus! {

broadcast use vstd::std_specs::hash::group_hash_axioms;

pub trait MetaCapTable<Value>: View<V = Map<CapKey, Value>> {
    type ActTable : View<V = Map<CapKey, Value>>;

    fn insert(&mut self, k: CapKey, v: Value)
        requires old(self).wf()
        ensures
            self.wf(),
            self@ == old(self)@.insert(k@, v);

    fn remove(&mut self, k: CapKey)
        requires old(self).wf()
        ensures
            self.wf(),
            self@ == old(self)@.remove(k@);

    fn get(&self, k: CapKey) -> (result: Option<&Value>)
        requires self.wf()
        ensures
            result matches Some(v) ==> self@.contains_key(k@) && *v == self@[k@],
            result matches None ==> !self@.contains_key(k@);

    spec fn wf(&self) -> bool;

    fn get_act_table(&self, act: ActId) -> (result: Option<&Self::ActTable>)
        requires self.wf()
        ensures
            match result {
                Some(table) => self@.restrict(Set::new(|k: CapKey| k.0 == act)) == table@,
                None => self@.restrict(Set::new(|k: CapKey| k.0 == act)).is_empty()
            };
}

#[verifier::reject_recursive_types(Value)]
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
pub struct HashMetaCapTable<Value>(MutMap<ActId, ActivityCapTable<Value>>);

impl<Value> View for HashMetaCapTable<Value> {
    type V = Map<CapKey, Value>;

    closed spec fn view(&self) -> Self::V {
        Map::new(
            |key: CapKey| self.0@.contains_key(key.0) && self.0@[key.0].1.value().caps@.contains_key(key.1),
            |key: CapKey| self.0@[key.0].1.value().caps@[key.1])
    }
}

impl<Value> MetaCapTable<Value> for HashMetaCapTable<Value> {
    type ActTable = ActivityCapTable<Value>;

    fn insert(&mut self, k: CapKey, v: Value)
    {
        if self.0.contains_key(&k.0) {
            let mut table = self.0.take(&k.0, Ghost(Set::empty()));
            table.caps.insert(k.1, v);
            self.0.untake(&k.0, table, Ghost(Set::empty()));

            assert(self@ == old(self)@.insert(k@, v));
        }
        else {
            assume(obeys_key_model::<u64>());
            let caps = HashMap::<u64, Value>::new();

            let mut table = ActivityCapTable { activity_id: k.0, caps };
            table.caps.insert(k.1, v);
            self.0.insert(k.0, table);

            assert(self@ == old(self)@.insert(k@, v));
        }
    }

    fn remove(&mut self, k: CapKey)
    {
        if self.0.contains_key(&k.0) {
            let mut table = self.0.take(&k.0, Ghost(Set::empty()));
            table.caps.remove(&k.1);
            self.0.untake(&k.0, table, Ghost(Set::empty()));

            assert(self@ == old(self)@.remove(k@));
        }
        else {
            assert(self@ == old(self)@.remove(k@));
        }
    }

    fn get(&self, k: CapKey) -> (result: Option<&Value>)
    {
        let table = self.0.get(&k.0)?;
        table.caps.get(&k.1)
    }

    closed spec fn wf(&self) -> bool {
        &&& self.0.wf()
        &&& forall |act: ActId| self.0@.contains_key(act) ==> #[trigger] self.0@[act].1.value().activity_id == act
    }

    fn get_act_table(&self, act: ActId) -> (result: Option<&Self::ActTable>)
    {
        proof!{
            if self.0@.contains_key(act) {
                assert(self@.restrict(Set::new(|k: CapKey| k.0 == act)) =~= self.0@[act].1.value()@);
            }
        };

        self.0.get(&act)
    }
}

}
