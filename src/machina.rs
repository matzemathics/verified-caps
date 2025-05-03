use core::hash::Hash;

use vstd::{
    cell::{self, CellId, PCell},
    hash_map::HashMapWithView,
    invariant::{InvariantPredicate, LocalInvariant},
    open_local_invariant,
    prelude::*,
};

verus! {

type CapSel = u64;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct SelRange {
    pub start: CapSel,
    // end = start + count
    pub end: CapSel,
}

impl View for SelRange {
    type V = (CapSel, CapSel);

    open spec fn view(&self) -> Self::V {
        (self.start, self.end)
    }
}

impl SelRange {
    pub open spec fn disjunct(&self, other: &Self) -> bool {
        other.end <= self.start || self.end <= other.start
    }

    pub open spec fn empty(&self) -> bool {
        self.start == self.end
    }
}

struct KObject;

type CapTableSel = u64;

struct CapSystem {
    cap_tables: HashMapWithView<CapTableSel, CapTable>
}

impl CapSystem {
    fn insert(&mut self, table: CapTableSel, cap: Capability, parent: Option<Link>)
    requires
        old(self).cap_tables@.contains_key(table),
        parent.is_none() // || self.cap_tables@.index(parent.unwrap().table)
    //ensures
        //self.cap_tables@.index(table)@.contains_key(cap.sel@)
    {
        let table = self.cap_tables.get(&table).unwrap();
    }
}

struct Link {
    table: CapTableSel,
    cap: CapSel,
}

struct CapLinks {
    parent: Option<Link>,
    child: Option<Link>,
    right: Option<Link>,
    left: Option<Link>,
}

struct Capability {
    kobj: KObject,
    sel: SelRange,
}

struct CapNode {
    cap: Capability,
    links: CapLinks,
}

struct CapTable {
    caps: HashMapWithView<SelRange, CapNode>,
    // ...plus quota
}

impl View for CapTable {
    type V = Map<(u64, u64), CapNode>;

    closed spec fn view(&self) -> Self::V {
        self.caps@
    }
}

impl CapTable {
}

struct SomeInvPred;

impl InvariantPredicate<CellId, vstd::cell::PointsTo<i32>> for SomeInvPred {
    open spec fn inv(k: CellId, v: vstd::cell::PointsTo<i32>) -> bool {
        v.id() == k && v.is_init()
    }
}

fn test_fn() {
    let (ptr, perm) = PCell::new(15);
    assert(perm@.value() == 15);
    let tracked inv = LocalInvariant::<_, _, SomeInvPred>::new(ptr.id(), perm.get(), 13);
    let tracked shared_perm = vstd::shared::Shared::new(inv);

    let mut result = 0;
    let tracked inv = shared_perm.borrow();
    open_local_invariant!(inv => v => {
        result = ptr.take(Tracked(&mut v));
        ptr.put(Tracked(&mut v), 13)
    });
}

#[verifier::reject_recursive_types(K)]
#[verifier::reject_recursive_types(V)]
pub struct MutHashMapInner<K: View+Eq+Hash, V> {
    m: HashMapWithView<K, PCell<V>>,
    credits: Tracked<Map<K::V, vstd::cell::PointsTo<V>>>,
}

impl<K: View+Eq+Hash, V> View for MutHashMapInner<K, V> {
    type V = Map<K::V, vstd::cell::PointsTo<V>>;

    closed spec fn view(&self) -> Self::V {
        self.credits@
    }
}

impl<Key: View+Eq+Hash, Value> MutHashMapInner<Key, Value> {
    pub closed spec fn wf(self) -> bool {
        self.credit_ids() == self.map_ids() &&
        forall |k: Key::V| self.credits@.dom().contains(k) ==> #[trigger] self.credits@[k].is_init()
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

        assert(credits@.map_values(|v: cell::PointsTo<Value>| v.id()) =~= m@.map_values(|v: PCell<Value>| v.id()));

        Self { m, credits }
    }

    spec fn credit_ids(&self) -> Map<Key::V, CellId> {
        self.credits@.map_values(|v: cell::PointsTo<Value>| v.id())
    }

    spec fn map_ids(&self) -> Map<Key::V, CellId> {
        self.m@.map_values(|v: cell::PCell<Value>| v.id())
    }

    proof fn lemma_dom_credits_eq_dom_m(&self)
    requires self.wf()
    ensures self.m@.dom() == self.credits@.dom()
    {
        assert(self.m@.dom() =~= self.m@.map_values(|v: cell::PCell<Value>| v.id()).dom());
        assert(self.credits@.dom() =~= self.credits@.map_values(|v: cell::PointsTo<Value>| v.id()).dom());
    }

    pub open spec fn index_opt(&self, k: Key::V) -> Option<Value> {
        if self@.contains_key(k) {
            Some(self@[k].value())
        } else {
            None
        }
    }

    pub fn insert(&mut self, k: Key, v: Value) -> (res: Option<Value>)
    requires
        old(self).wf()
    ensures
        self@[k@].value() == v,
        self.wf(),
        old(self).index_opt(k@) == res
    {
        let (cell, perm) = PCell::new(v);

        let previous = match self.m.get(&k) {
            Some(cell) => {
                proof!{ self.lemma_dom_credits_eq_dom_m(); };
                assert(self.credits@.dom().contains(k@));
                let tracked perm = self.credits.borrow_mut().tracked_remove(k@);

                assert(cell.id() == old(self).map_ids()[k@]);
                assert(cell.id() == perm.id());
                assert(perm.is_init());
                assert(old(self).index_opt(k@) == Some(perm.value()));

                Some(cell.take(Tracked(&mut perm)))
            }
            None => {
                proof!{ self.lemma_dom_credits_eq_dom_m(); };
                assert(self.index_opt(k@) == Option::<Value>::None);
                None
            }
        };

        self.m.insert(k, cell);

        assert(self.map_ids() =~= Map::insert(old(self).map_ids(), k@, cell.id()));

        proof!{
            let tracked Tracked(perm) = perm;
            self.credits.borrow_mut().tracked_insert(k@, perm);
            assert(self.credit_ids() =~= Map::insert(old(self).map_ids(), k@, cell.id()));
        };

        previous
    }

    proof fn borrow_perm(tracked &self, k: Key::V) -> (tracked perm: &cell::PointsTo<Value>)
    requires self.wf() && self.m@.dom().contains(k)
    ensures
        perm.id() == self.map_ids()[k],
        perm.is_init(),
        perm == self@[k]
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
            Some(v) => self@.contains_key(k@) && *v == self@[k@].value(),
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
        assert(*res == self@[k@].value());

        Some(res)
    }

    fn update(&mut self, k: &Key, f: impl FnOnce(Value) -> Value)
    requires
        old(self).wf(),
        old(self)@.dom().contains(k@),
        f.requires((old(self)@[k@].value(),))
    ensures
        self.wf(),
        f.ensures((old(self)@[k@].value(),), self@[k@].value())
    {
        proof!{ self.lemma_dom_credits_eq_dom_m(); };
        let cell = self.m.get(k).unwrap();
        let tracked perm = self.credits.borrow_mut().tracked_remove(k@);

        assert(cell.id() == old(self).map_ids()[k@]);
        assert(cell.id() == perm.id());
        assert(perm.is_init());
        assert(old(self).index_opt(k@) == Some(perm.value()));

        let value = cell.take(Tracked(&mut perm));
        cell.put(Tracked(&mut perm), f(value));

        proof!{
            self.credits.borrow_mut().tracked_insert(k@, perm);
            assert(self.map_ids() =~= self.credit_ids());
        }
    }
}

}
