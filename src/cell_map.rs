use core::hash::Hash;
use vstd::{
    cell::{CellId, MemContents, PCell, PointsTo},
    hash_map::HashMapWithView,
    prelude::*,
};

verus! {

// there are multiple options for implementing mutation / retaking ownership of hashmap elements
// 1 - extend vstd or re-wrap rust std library (assuming the rust implementation is sound)
// 2 - use PCell to have "interior mutability"
// 3 - use PPtr to introduce an additional redirection -> allows referencing elements from the outside
#[verifier::reject_recursive_types(K)]
#[verifier::reject_recursive_types(V)]
pub struct MutMap<K: View + Eq + Hash, V> {
    m: HashMapWithView<K, PCell<V>>,
    credits: Tracked<Map<K::V, PointsTo<V>>>,
}

impl<K: View + Eq + Hash, V> View for MutMap<K, V> {
    type V = Map<K::V, (CellId, MemContents<V>)>;

    closed spec fn view(&self) -> Self::V {
        self.credits@.map_values(|pt: PointsTo<V>| (pt.id(), pt.mem_contents()))
    }
}

impl<Key: View + Eq + Hash, Value> MutMap<Key, Value> {
    pub proof fn tracked_borrow(tracked &self) -> (tracked r: &Map<
        Key::V,
        PointsTo<Value>,
    >)
        ensures
            r.map_values(|pt: PointsTo<Value>| (pt.id(), pt.mem_contents()))
                == self@,
    {
        self.credits.borrow()
    }

    pub open spec fn wf(self) -> bool {
        self.vacated(Set::empty())
    }

    pub open spec fn vacated(self, vacated: Set<Key::V>) -> bool {
        self.addrs_match() && self.init_besides(vacated) && self.uninit_vacated(vacated)
    }

    pub closed spec fn addrs_match(self) -> bool {
        self.credit_addrs() == self.map_addrs()
    }

    pub closed spec fn init_besides(self, vacated: Set<Key::V>) -> bool {
        forall|k: Key::V|
            self.credits@.dom().contains(k) && !vacated.contains(k)
                ==> #[trigger] self.credits@[k].is_init()
    }

    pub closed spec fn uninit_vacated(self, vacated: Set<Key::V>) -> bool {
        forall|k: Key::V|
            self.credits@.dom().contains(k) && vacated.contains(k)
                ==> #[trigger] self.credits@[k].is_uninit()
    }

    pub proof fn lemma_is_init(&self, key: Key::V)
        requires
            self.wf() && self@.contains_key(key),
        ensures
            self@[key].1.is_init(),
    {
        assert(self.credits@[key].is_init());
    }

    pub fn new() -> (m: Self)
        requires
            vstd::std_specs::hash::obeys_key_model::<Key>(),
            forall|k1: Key, k2: Key| k1@ == k2@ ==> k1 == k2,
        ensures
            m@.is_empty() && m.wf(),
    {
        let m = HashMapWithView::new();
        let credits = Tracked(Map::tracked_empty());

        assert(credits@.map_values(|v: PointsTo<Value>| v.id()) =~= m@.map_values(
            |v: PCell<Value>| v.id(),
        ));

        Self { m, credits }
    }

    spec fn credit_addrs(&self) -> Map<Key::V, CellId> {
        self.credits@.map_values(|v: PointsTo<Value>| v.id())
    }

    spec fn map_addrs(&self) -> Map<Key::V, CellId> {
        self.m@.map_values(|v: PCell<Value>| v.id())
    }

    proof fn lemma_dom_credits_eq_dom_m(&self)
        requires
            self.addrs_match(),
        ensures
            self.m@.dom() == self.credits@.dom(),
    {
        assert(self.m@.dom() =~= self.m@.map_values(|v: PCell<Value>| v.id()).dom());
        assert(self.credits@.dom() =~= self.credits@.map_values(
            |v: PointsTo<Value>| v.id(),
        ).dom());
    }

    pub open spec fn index_opt(&self, k: Key::V) -> Option<Value> {
        if self@.contains_key(k) {
            Some(self@[k].1.value())
        } else {
            None
        }
    }

    pub fn insert(&mut self, k: Key, v: Value) -> (res: Option<Value>)
        requires
            old(self).wf(),
        ensures
            self.wf(),
            self@.contains_key(k@),
            self@ == old(self)@.insert(k@, (self@[k@].0, MemContents::Init(v))),
            old(self).index_opt(k@) == res,
    {
        let (cell, perm) = PCell::new(v);

        let previous = match self.m.get(&k) {
            Some(cell) => {
                proof!{ self.lemma_dom_credits_eq_dom_m(); };
                assert(self.credits@.dom().contains(k@));
                let tracked perm = self.credits.borrow_mut().tracked_remove(k@);

                assert(cell.id() == old(self).map_addrs()[k@]);
                assert(cell.id() == perm.id());
                assert(perm.is_init());
                assert(old(self).index_opt(k@) == Some(perm.value()));

                Some(cell.take(Tracked(&mut perm)))
            },
            None => {
                proof!{ self.lemma_dom_credits_eq_dom_m(); };
                assert(self.index_opt(k@) == Option::<Value>::None);
                None
            },
        };

        self.m.insert(k, cell);

        assert(self.map_addrs() =~= Map::insert(old(self).map_addrs(), k@, cell.id()));

        proof!{
            let tracked Tracked(perm) = perm;
            self.credits.borrow_mut().tracked_insert(k@, perm);
            assert(self@.dom() == old(self)@.dom().insert(k@));
            assert(self.credit_addrs() =~= Map::insert(old(self).map_addrs(), k@, cell.id()));
            assert(self@ == old(self)@.insert(k@, (cell.id(), MemContents::Init(v))));
        };

        previous
    }

    proof fn borrow_perm(tracked &self, k: Key::V) -> (tracked perm: &PointsTo<Value>)
        requires
            self.wf() && self.m@.dom().contains(k),
        ensures
            perm.id() == self.map_addrs()[k],
            perm.is_init(),
            perm.id() == self@[k].0,
            perm.mem_contents() == self@[k].1,
    {
        self.lemma_dom_credits_eq_dom_m();
        assert(self.credits@.dom().contains(k));
        let tracked perm = self.credits.borrow().tracked_borrow(k);

        perm
    }

    pub fn get(&self, k: &Key) -> (res: Option<&Value>)
        requires
            self.wf(),
        ensures
            match res {
                Some(v) => self@.contains_key(k@) && *v == self@[k@].1.value(),
                None => !self@.contains_key(k@),
            },
    {
        let Some(cell) = self.m.get(k) else {
            proof!{ self.lemma_dom_credits_eq_dom_m(); };
            assert(!self@.contains_key(k@));
            return None;
        };

        let tracked perm = self.borrow_perm(k@);
        let res = cell.borrow(Tracked(perm));

        proof!{ self.lemma_dom_credits_eq_dom_m(); };
        assert(*res == self@[k@].1.value());

        Some(res)
    }

    fn update(&mut self, k: &Key, f: impl FnOnce(Value) -> Value)
        requires
            old(self).wf(),
            old(self)@.dom().contains(k@),
            f.requires((old(self)@[k@].1.value(),)),
        ensures
            self.wf(),
            f.ensures((old(self)@[k@].1.value(),), self@[k@].1.value()),
    {
        proof!{ self.lemma_dom_credits_eq_dom_m(); };
        let cell = self.m.get(k).unwrap();
        let tracked perm = self.credits.borrow_mut().tracked_remove(k@);

        assert(cell.id() == old(self).map_addrs()[k@]);
        assert(cell.id() == perm.id());
        assert(perm.is_init());
        assert(old(self).index_opt(k@) == Some(perm.value()));

        let value = cell.take(Tracked(&mut perm));
        cell.put(Tracked(&mut perm), f(value));

        proof!{
            self.credits.borrow_mut().tracked_insert(k@, perm);
            assert(self.map_addrs() =~= self.credit_addrs());
        }
    }

    pub fn take(
        &mut self,
        key: &Key,
        vacated: Ghost<Set<Key::V>>,
    ) -> (res: Value)
        requires
            old(self).vacated(vacated@),
            !vacated@.contains(key@),
            old(self)@.contains_key(key@),
        ensures
            self.vacated(vacated@.insert(key@)),
            self@.dom() == old(self)@.dom(),
            self@ == old(self)@.insert(key@, (old(self)@[key@].0, MemContents::Uninit)),
            res == old(self)@[key@].1.value(),
            self@[key@].0 == old(self)@[key@].0,
    {
        proof!{ self.lemma_dom_credits_eq_dom_m() };
        let cell = self.m.get(key).unwrap();
        assert(cell.id() == self.map_addrs()[key@]);
        assert(self@.contains_key(key@) && cell.id() == self@[key@].0);

        let tracked perm = self.credits.borrow_mut().tracked_remove(key.view());
        assert(perm.id() == cell.id());
        let result = cell.take(Tracked(&mut perm));

        proof!{
            self.credits.borrow_mut().tracked_insert(key.view(), perm);
            assert(self.credit_addrs() == self.map_addrs());

            assert(forall |k1: Key| k1@ != key@ && self@.contains_key(k1@) ==> self@[k1@] == #[trigger] old(self)@[k1@]);
            assert(self@.contains_key(key@) && self@[key@] == (cell.id(), MemContents::<Value>::Uninit));
            assert(self@ == old(self)@.insert(key@, (cell.id(), MemContents::Uninit)));
        };

        result
    }

    pub fn untake(
        &mut self,
        key: &Key,
        value: Value,
        vacated: Ghost<Set<Key::V>>,
    )
        requires
            !vacated@.contains(key@),
            old(self).vacated(vacated@.insert(key@)),
            old(self)@.contains_key(key@),
        ensures
            self.vacated(vacated@),
            self@.dom() == old(self)@.dom(),
            self@ == old(self)@.insert(key@, (old(self)@[key@].0, MemContents::Init(value))),
    {
        proof!{ self.lemma_dom_credits_eq_dom_m() };
        let cell = self.m.get(key).unwrap();
        assert(cell.id() == self.map_addrs()[key@]);
        assert(self@.contains_key(key@) && cell.id() == self@[key@].0);

        let tracked perm = self.credits.borrow_mut().tracked_remove(key.view());
        assert(perm.id() == cell.id());
        assert(perm.is_uninit());
        // proof! { perm.leak_contents(); };
        cell.put(Tracked(&mut perm), value);

        proof!{
            self.credits.borrow_mut().tracked_insert(key.view(), perm);
            assert(self.credit_addrs() == self.map_addrs());
            assert(self@ == old(self)@.insert(key@, (cell.id(), MemContents::Init(value))));

            assert forall|k: Key::V|
                self.credits@.dom().contains(k) && vacated@.contains(k)
            implies #[trigger] self.credits@[k].is_uninit()
            by {
                assert(vacated@.insert(key@).contains(k));
                assert(old(self).credits@.dom().contains(k));
                assert(old(self).credits@[k].is_uninit());
                assert(k != key@);
                assert(old(self).credits@[k] == self.credits@[k]);
            };
        };
    }
}

fn test() {
    assert(vstd::std_specs::hash::obeys_key_model::<i32>()) by { admit() };

    let mut map = MutMap::new();
    map.insert(0, 42);
    map.insert(1, 52);

    let inner = map.take(&0, Ghost(Set::empty()));
    assert(inner == 42);
    assert(map@[1].1.value() == 52);
    map.untake(&0, inner + 1, Ghost(Set::empty()));

    assert(map@[0].1.value() == 43);
}

} // verus!
