use vstd::{hash_map::HashMapWithView, prelude::*};

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
            self@ == old(self)@.insert(k@, v);

    fn remove(&mut self, k: CapKey)
        requires old(self).wf()
        ensures
            self@ == old(self)@.remove(k@);

    fn get(&self, k: CapKey) -> (result: Option<&Value>)
        requires self.wf()
        ensures
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
        ensures
            self@ == old(self)@.insert(k@, v)
    {
    }

    fn remove(&mut self, k: CapKey)
        ensures
            self@ == old(self)@.remove(k@)
    {
    }

    fn get(&self, k: CapKey) -> (result: Option<&Value>)
        ensures
            match result {
                Some(v) => self@.contains_key(k@) && *v == self@[k@],
                None => !self@.contains_key(k@),
            }
    {
        None
    }

    spec fn wf(&self) -> bool {
        self.0.wf()
    }
}

}
