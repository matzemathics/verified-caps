use core::hash::Hash;
use vstd::{
    cell::MemContents,
    hash_map::HashMapWithView,
    prelude::*,
    simple_pptr::{self, PPtr},
};

verus! {

// there are multiple options for implementing mutation / retaking ownership of hashmap elements
// 1 - extend vstd or re-wrap rust std library (assuming the rust implementation is sound)
// 2 - use PCell to have "interior mutability"
// 3 - use PPtr to introduce an additional redirection -> allows referencing elements from the outside

#[verifier::reject_recursive_types(K)]
#[verifier::reject_recursive_types(V)]
pub struct MutPointerMap<K: View+Eq+Hash, V> {
    m: HashMapWithView<K, PPtr<V>>,
    credits: Tracked<Map<K::V, simple_pptr::PointsTo<V>>>,
}

impl<K: View+Eq+Hash, V> View for MutPointerMap<K, V> {
    type V = Map<K::V, (usize, MemContents<V>)>;

    closed spec fn view(&self) -> Self::V {
        self.credits@.map_values(|pt: simple_pptr::PointsTo<V>| (pt.addr(), pt.mem_contents()))
    }
}

impl<Key: View+Eq+Hash, Value> MutPointerMap<Key, Value> {
    pub proof fn tracked_borrow(tracked &self) -> (tracked r: &Map<Key::V, simple_pptr::PointsTo<Value>>)
    ensures r.map_values(|pt: simple_pptr::PointsTo<Value>| (pt.addr(), pt.mem_contents())) == self@
    {
        self.credits.borrow()
    }

    pub open spec fn wf(self) -> bool {
        self.vacated(Set::empty())
    }

    pub open spec fn vacated(self, vacated: Set<Key::V>) -> bool {
        self.addrs_match() && self.init_besides(vacated)
    }

    pub closed spec fn addrs_match(self) -> bool {
        self.credit_addrs() == self.map_addrs()
    }

    pub closed spec fn init_besides(self, vacated: Set<Key::V>) -> bool {
        forall |k: Key::V| self.credits@.dom().contains(k) && !vacated.contains(k) ==> #[trigger] self.credits@[k].is_init()
    }

    pub fn new() -> (m: Self)
    requires
        vstd::std_specs::hash::obeys_key_model::<Key>(),
        forall |k1: Key, k2: Key| k1@ == k2@ ==> k1 == k2
    ensures
        m@.is_empty() && m.wf()
    {
        let m = HashMapWithView::new();
        let credits = Tracked(Map::tracked_empty());

        assert(credits@.map_values(|v: simple_pptr::PointsTo<Value>| v.addr()) =~= m@.map_values(|v: PPtr<Value>| v.addr()));

        Self { m, credits }
    }

    spec fn credit_addrs(&self) -> Map<Key::V, usize> {
        self.credits@.map_values(|v: simple_pptr::PointsTo<Value>| v.addr())
    }

    spec fn map_addrs(&self) -> Map<Key::V, usize> {
        self.m@.map_values(|v: PPtr<Value>| v.addr())
    }

    proof fn lemma_dom_credits_eq_dom_m(&self)
    requires self.addrs_match()
    ensures self.m@.dom() == self.credits@.dom()
    {
        assert(self.m@.dom() =~= self.m@.map_values(|v: PPtr<Value>| v.addr()).dom());
        assert(self.credits@.dom() =~= self.credits@.map_values(|v: simple_pptr::PointsTo<Value>| v.addr()).dom());
    }

    pub open spec fn index_opt(&self, k: Key::V) -> Option<Value> {
        if self@.contains_key(k) {
            Some(self@[k].1.value())
        } else {
            None
        }
    }

    pub fn insert(&mut self, k: Key, v: Value) -> (res: (Option<Value>, PPtr<Value>))
    requires
        old(self).wf()
    ensures
        self.wf(),
        self@ == old(self)@.insert(k@, (res.1.addr(), MemContents::Init(v))),
        old(self).index_opt(k@) == res.0,
    {
        let (ptr, perm) = PPtr::new(v);

        let previous = match self.m.get(&k) {
            Some(ptr) => {
                proof!{ self.lemma_dom_credits_eq_dom_m(); };
                assert(self.credits@.dom().contains(k@));
                let tracked perm = self.credits.borrow_mut().tracked_remove(k@);

                assert(ptr.addr() == old(self).map_addrs()[k@]);
                assert(ptr.addr() == perm.addr());
                assert(perm.is_init());
                assert(old(self).index_opt(k@) == Some(perm.value()));

                Some(ptr.take(Tracked(&mut perm)))
            }
            None => {
                proof!{ self.lemma_dom_credits_eq_dom_m(); };
                assert(self.index_opt(k@) == Option::<Value>::None);
                None
            }
        };

        self.m.insert(k, ptr);

        assert(self.map_addrs() =~= Map::insert(old(self).map_addrs(), k@, ptr.addr()));

        proof!{
            let tracked Tracked(perm) = perm;
            self.credits.borrow_mut().tracked_insert(k@, perm);
            assert(self@.dom() == old(self)@.dom().insert(k@));
            assert(self.credit_addrs() =~= Map::insert(old(self).map_addrs(), k@, ptr.addr()));
            assert(self@ == old(self)@.insert(k@, (ptr.addr(), MemContents::Init(v))));
        };

        (previous, ptr)
    }

    proof fn borrow_perm(tracked &self, k: Key::V) -> (tracked perm: &simple_pptr::PointsTo<Value>)
    requires self.wf() && self.m@.dom().contains(k)
    ensures
        perm.addr() == self.map_addrs()[k],
        perm.is_init(),
        perm.addr() == self@[k].0,
        perm.mem_contents() == self@[k].1
    {
        self.lemma_dom_credits_eq_dom_m();
        assert(self.credits@.dom().contains(k));
        let tracked perm = self.credits.borrow().tracked_borrow(k);

        perm
    }

    pub fn get(&self, k: &Key) -> (res: Option<&Value>)
    requires self.wf()
    ensures
        match res {
            Some(v) => self@.contains_key(k@) && *v == self@[k@].1.value(),
            None => !self@.contains_key(k@),
        },
    {
        let Some(ptr) = self.m.get(k) else {
            proof!{ self.lemma_dom_credits_eq_dom_m(); };
            assert(!self@.contains_key(k@));
            return None;
        };

        let tracked perm = self.borrow_perm(k@);
        let res = ptr.borrow(Tracked(perm));

        proof!{ self.lemma_dom_credits_eq_dom_m(); };
        assert(*res == self@[k@].1.value());

        Some(res)
    }

    fn update(&mut self, k: &Key, f: impl FnOnce(Value) -> Value)
    requires
        old(self).wf(),
        old(self)@.dom().contains(k@),
        f.requires((old(self)@[k@].1.value(),))
    ensures
        self.wf(),
        f.ensures((old(self)@[k@].1.value(),), self@[k@].1.value())
    {
        proof!{ self.lemma_dom_credits_eq_dom_m(); };
        let ptr = self.m.get(k).unwrap();
        let tracked perm = self.credits.borrow_mut().tracked_remove(k@);

        assert(ptr.addr() == old(self).map_addrs()[k@]);
        assert(ptr.addr() == perm.addr());
        assert(perm.is_init());
        assert(old(self).index_opt(k@) == Some(perm.value()));

        let value = ptr.take(Tracked(&mut perm));
        ptr.put(Tracked(&mut perm), f(value));

        proof!{
            self.credits.borrow_mut().tracked_insert(k@, perm);
            assert(self.map_addrs() =~= self.credit_addrs());
        }
    }

    pub fn take(&mut self, element: PPtr<Value>, key: Ghost<Key>, vacated: Ghost<Set<Key::V>>) -> (res: Value)
    requires
        old(self).vacated(vacated@),
        !vacated@.contains(key@@),
        old(self)@.contains_key(key@@) && old(self)@[key@@].0 == element.addr()
    ensures
        self.vacated(vacated@.insert(key@@)),
        self@.dom() == old(self)@.dom(),
        self@ == old(self)@.insert(key@@, (element.addr(), MemContents::Uninit)),
        res == old(self)@[key@@].1.value(),
        self@[key@@].0 == element.addr(),
    {
        let tracked perm = self.credits.borrow_mut().tracked_remove(key.borrow().view());
        assert(perm.addr() == element.addr());
        let result = element.take(Tracked(&mut perm));

        proof!{
            self.credits.borrow_mut().tracked_insert(key.borrow().view(), perm);
            assert(self.credit_addrs() == self.map_addrs());

            assert(forall |k1: Key| k1@ != key@@ && self@.contains_key(k1@) ==> self@[k1@] == #[trigger] old(self)@[k1@]);
            assert(self@.contains_key(key@@) && self@[key@@] == (element.addr(), MemContents::<Value>::Uninit));
            assert(self@ == old(self)@.insert(key@@, (element.addr(), MemContents::Uninit)));
        };

        result
    }

    pub fn untake(&mut self, element: PPtr<Value>, key: Ghost<Key>, value: Value, vacated: Ghost<Set<Key::V>>)
    requires
        old(self).vacated(vacated@.insert(key@@)),
        old(self)@.contains_key(key@@) && old(self)@[key@@].0 == element.addr()
    ensures
        self.vacated(vacated@),
        self@.dom() == old(self)@.dom(),
        self@ == old(self)@.insert(key@@, (element.addr(), MemContents::Init(value)))
    {
        let tracked perm = self.credits.borrow_mut().tracked_remove(key.borrow().view());
        assert(perm.addr() == element.addr());
        proof! { perm.leak_contents(); };
        element.put(Tracked(&mut perm), value);

        proof!{
            self.credits.borrow_mut().tracked_insert(key.borrow().view(), perm);
            assert(self.credit_addrs() == self.map_addrs());
            assert(self@ == old(self)@.insert(key@@, (element.addr(), MemContents::Init(value))));
        };
    }

    pub fn get_ptr(&self, key: &Key) -> (result: Option<PPtr<Value>>)
    requires
        self.addrs_match()
    ensures
        match result {
            Some(v) => self@.contains_key(key@) && v.addr() == self@[key@].0,
            None => !self@.contains_key(key@),
        },
    {
        proof!{ self.lemma_dom_credits_eq_dom_m() };

        match self.m.get(key) {
            Some(ptr) => {
                let ptr = *ptr;
                assert(ptr.addr() == self.map_addrs()[key@]);
                assert(self@.contains_key(key@) && ptr.addr() == self@[key@].0);
                Some(ptr)
            }
            None => None
        }
    }

    pub fn read(&self, element: PPtr<Value>, key: Ghost<Key>) -> &Value
    requires self.wf() && self@.contains_key(key@@) && self@[key@@].0 == element.addr()
    returns self@[key@@].1.value()
    {
        proof!{ self.lemma_dom_credits_eq_dom_m(); };
        element.borrow(Tracked(self.borrow_perm(key@@)))
    }
}

fn test() {
    assert(vstd::std_specs::hash::obeys_key_model::<i32>()) by {
        admit()
    };

    let mut map = MutPointerMap::new();
    map.insert(0, 42);
    map.insert(1, 52);

    let elem = map.get_ptr(&0).unwrap();
    let inner = map.take(elem, ghost_exec(0), Ghost(Set::empty()));
    assert(inner == 42);
    assert(map@[1].1.value() == 52);
    map.untake(elem, ghost_exec(0), inner + 1, Ghost(Set::empty()));

    assert(map@[0].1.value() == 43);
}

}
