use vstd::{hash_map::HashMapWithView, prelude::*, std_specs::hash::obeys_key_model};

use crate::{
    cell_map::MutMap,
    tcb::{ActId, CapId, CapKey},
};

verus! {

trait CapabilityMetaMap<Value>: View<V = Map<CapKey, Value>> {
    type SubMap : View<V = Map<CapKey, Value>>;

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
            self.wf(),
            match result {
                Some(v) => self@.contains_key(k@) && *v == self@[k@],
                None => !self@.contains_key(k@),
            };

    spec fn wf(&self) -> bool;
}

#[verifier::reject_recursive_types(Value)]
struct HashActionMap<Value> {
    action_id: ActId,
    caps: HashMapWithView<CapId, Value>
}

impl<Value> View for HashActionMap<Value> {
    type V = Map<CapKey, Value>;

    closed spec fn view(&self) -> Self::V {
        Map::new(
            |key: CapKey| key.0 == self.action_id && self.caps@.contains_key(key.1),
            |key: CapKey| self.caps@[key.1])
    }
}

#[verifier::reject_recursive_types(Value)]
struct HashMetaMap<Value>(MutMap<ActId, HashActionMap<Value>>);

impl<Value> View for HashMetaMap<Value> {
    type V = Map<CapKey, Value>;

    closed spec fn view(&self) -> Self::V {
        Map::new(
            |key: CapKey| self.0@.contains_key(key.0) && self.0@[key.0].1.value().caps@.contains_key(key.1),
            |key: CapKey| self.0@[key.0].1.value().caps@[key.1])
    }
}

impl<Value> CapabilityMetaMap<Value> for HashMetaMap<Value> {
    type SubMap = HashActionMap<Value>;

    fn insert(&mut self, k: CapKey, v: Value)
    {
        if self.0.contains_key(&k.0) {
            let mut action_map = self.0.take(&k.0, Ghost(Set::empty()));
            action_map.caps.insert(k.1, v);
            self.0.untake(&k.0, action_map, Ghost(Set::empty()));

            assert(self@ == old(self)@.insert(k@, v));
        }
        else {
            assume(obeys_key_model::<u64>());
            let caps = HashMapWithView::<u64, Value>::new();

            let mut action_map = HashActionMap { action_id: k.0, caps };
            action_map.caps.insert(k.1, v);
            self.0.insert(k.0, action_map);

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

    spec fn wf(&self) -> bool {
        self.0.wf()
    }
}

}
