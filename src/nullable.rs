use vstd::{
    pervasive::proof_from_false,
    prelude::*,
    simple_pptr::{PPtr, PointsTo},
};

verus! {

pub struct Nullable<V> {
    inner: PPtr<V>,
    inv: Tracked<NullableInv<V>>,
}

pub tracked enum NullableInv<V> {
    Null,
    Valid(PointsTo<V>),
}

impl<V> Nullable<V> {
    pub closed spec fn spec_is_null(&self) -> bool {
        self.inner.addr() == 0
    }

    #[verifier::when_used_as_spec(spec_is_null)]
    pub fn is_null(&self) -> (r: bool)
        ensures
            r == self.is_null(),
    {
        self.inner.addr() == 0
    }

    pub fn null() -> (p: Self)
        ensures
            p.is_null(),
    {
        Nullable { inner: PPtr::from_addr(0), inv: Tracked(NullableInv::Null) }
    }

    pub fn new(value: V) -> (p: Self) {
        let (ptr, Tracked(pt)) = PPtr::new(value);

        proof!{ pt.is_nonnull() };

        Nullable { inner: ptr, inv: Tracked(NullableInv::Valid(pt)) }
    }

    #[verifier::type_invariant]
    spec fn wf(self) -> bool {
        if self.is_null() {
            self.inv@ == NullableInv::<V>::Null
        } else {
            match self.inv@ {
                NullableInv::Null => false,
                NullableInv::Valid(pt) => {
                    &&& self.inner.addr() == pt.addr()
                    &&& pt.is_init()
                },
            }
        }
    }

    proof fn invariant(tracked &self)
        ensures
            self.wf(),
    {
        use_type_invariant(&self);
    }

    pub fn read(&self) -> &V
        requires
            !self.is_null(),
    {
        proof {
            use_type_invariant(&self);
        }

        let tracked pt = match &self.inv.borrow() {
            NullableInv::Null => { proof_from_false() },
            NullableInv::Valid(pt) => { pt },
        };

        self.inner.borrow(Tracked(pt))
    }

    pub fn read_opt(&self) -> Option<&V> {
        match self.is_null() {
            true => None,
            false => Some(self.read()),
        }
    }

    fn into_inner_non_null(self) -> V
        requires
            !self.is_null(),
    {
        proof {
            use_type_invariant(&self);
        }

        let tracked pt = match self.inv.get() {
            NullableInv::Null => proof_from_false(),
            NullableInv::Valid(pt) => pt,
        };

        self.inner.into_inner(Tracked(pt))
    }

    pub fn into_inner(self) -> Option<V> {
        match self.is_null() {
            true => None,
            false => Some(self.into_inner_non_null()),
        }
    }

    pub fn take_inner(&mut self) -> Option<V> {
        self.take().into_inner()
    }

    pub fn take(&mut self) -> Nullable<V> {
        let mut replacement = Nullable::null();
        core::mem::swap(self, &mut replacement);
        replacement
    }

    pub fn into_hole(self) -> (Hole<V>, V)
        requires
            !self.is_null(),
    {
        proof {
            use_type_invariant(&self);
        }
        let tracked pt = match self.inv.get() {
            NullableInv::Null => proof_from_false(),
            NullableInv::Valid(pt) => pt,
        };

        let value = self.inner.take(Tracked(&mut pt));
        (Hole { inner: self.inner, inv: Tracked(HoleInv::Active(pt)) }, value)
    }
}

impl<V> Drop for Nullable<V> {
    #[verifier::external_body]
    fn drop(&mut self)
        opens_invariants none
        no_unwind
    {
        let _ = self.take_inner();
    }
}

pub struct Hole<T> {
    inner: PPtr<T>,
    inv: Tracked<HoleInv<T>>,
}

enum HoleInv<T> {
    Null,
    Active(PointsTo<T>),
}

impl<T> Hole<T> {
    pub closed spec fn spec_is_null(&self) -> bool {
        self.inner.addr() == 0
    }

    #[verifier::when_used_as_spec(spec_is_null)]
    pub fn is_null(&self) -> (r: bool)
        ensures
            r == self.is_null(),
    {
        self.inner.addr() == 0
    }

    #[verifier::type_invariant]
    spec fn wf(self) -> bool {
        if self.is_null() {
            self.inv@ == HoleInv::<T>::Null
        } else {
            match self.inv@ {
                HoleInv::Null => false,
                HoleInv::Active(pt) => {
                    &&& self.inner.addr() == pt.addr()
                    &&& pt.is_uninit()
                },
            }
        }
    }

    fn null() -> (r: Self)
        ensures
            r.is_null(),
    {
        Hole { inner: PPtr::from_usize(0), inv: Tracked(HoleInv::Null) }
    }

    pub fn fill(self, value: T) -> Nullable<T> {
        if self.is_null() {
            return Nullable::null()
        }
        proof {
            use_type_invariant(&self);
        }

        let tracked pt = match self.inv.get() {
            HoleInv::Null => proof_from_false(),
            HoleInv::Active(pt) => pt,
        };

        self.inner.put(Tracked(&mut pt), value);
        Nullable { inner: self.inner, inv: Tracked(NullableInv::Valid(pt)) }
    }

    fn make_null(&mut self)
        ensures
            self.is_null(),
    {
        if self.is_null() {
            return
        }
        let mut replacement = Hole::null();
        core::mem::swap(self, &mut replacement);

        proof!{ use_type_invariant(&replacement); };

        let tracked pt = match replacement.inv.get() {
            HoleInv::Null => proof_from_false(),
            HoleInv::Active(pt) => pt,
        };

        replacement.inner.free(Tracked(pt));
    }
}

impl<T> Drop for Hole<T> {
    #[verifier::external_body]
    fn drop(&mut self)
        opens_invariants none
        no_unwind
    {
        self.make_null()
    }
}

} // verus!
