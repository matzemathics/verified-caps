#![allow(internal_features)]
#![feature(allocator_internals)]
#![feature(core_intrinsics)]
#![feature(maybe_uninit_write_slice)]
#![feature(linked_list_cursors)]
#![feature(btree_cursors)]
#![default_lib_allocator]
#![cfg_attr(not(feature = "linux"), no_std)]

pub extern crate alloc;

pub mod boxed {
    pub use alloc::boxed::Box;
}

use vstd::{
    pervasive::proof_from_false,
    prelude::*,
    simple_pptr::{PPtr, PointsTo},
};

mod bin_tree;
mod linear;
mod machina;
mod ptr_map;
mod traits;
mod treap;

verus! {

spec fn min(x: int, y: int) -> int {
    if x <= y {
        x
    } else {
        y
    }
}

pub struct Nullable<V> {
    inner: PPtr<V>,
    inv: Tracked<NullableInv<V>>
}

pub tracked enum NullableInv<V> {
    Null,
    Valid(PointsTo<V>)
}

impl<V> Nullable<V> {
    pub closed spec fn spec_is_null(&self) -> bool {
        self.inner.addr() == 0
    }

    #[verifier::when_used_as_spec(spec_is_null)]
    pub fn is_null(&self) -> (r: bool)
    ensures r == self.is_null()
    {
        self.inner.addr() == 0
    }

    pub fn null() -> (p: Self)
    ensures p.is_null()
    {
        Nullable {
            inner: PPtr::from_addr(0),
            inv: Tracked(NullableInv::Null)
        }
    }

    #[verifier::type_invariant]
    spec fn wf(self) -> bool {
        if self.is_null() {
            self.inv@ == NullableInv::<V>::Null
        }
        else {
            match self.inv@ {
                NullableInv::Null => false,
                NullableInv::Valid(pt) => {
                    &&& self.inner.addr() == pt.addr()
                    &&& pt.is_init()
                }
            }
        }
    }

    proof fn invariant(tracked &self)
    ensures self.wf()
    {
        use_type_invariant(&self);
    }

    pub fn read(&self) -> &V
    requires !self.is_null()
    {
        proof {
            use_type_invariant(&self);
        }

        let tracked pt = match &self.inv.borrow() {
            NullableInv::Null => {
                proof_from_false()
            }
            NullableInv::Valid(pt) => {
                pt
            }
        };

        self.inner.borrow(Tracked(pt))
    }

    pub fn read_opt(&self) -> Option<&V> {
        match self.is_null() {
            true => None,
            false => Some(self.read())
        }
    }

    fn into_inner_non_null(self) -> V
    requires !self.is_null()
    {
        proof {
            use_type_invariant(&self);
        }

        let tracked pt = match self.inv.get() {
            NullableInv::Null => proof_from_false(),
            NullableInv::Valid(pt) => pt
        };

        self.inner.into_inner(Tracked(pt))
    }

    pub fn into_inner(self) -> Option<V> {
        match self.is_null() {
            true => None,
            false => Some(self.into_inner_non_null())
        }
    }
}

fn main() {
    assert(min(10, 20) == 10);
    assert(min(-10, -20) == -20);
    assert(forall|i: int, j: int| min(i, j) <= i && min(i, j) <= j);
    assert(forall|i: int, j: int| min(i, j) == i || min(i, j) == j);
    assert(forall|i: int, j: int| min(i, j) == min(j, i));


    // ALLOCATE p
    let (p, Tracked(mut perm_p)) = PPtr::<u64>::empty();

    // ALLOCATE q
    let (q, Tracked(mut perm_q)) = PPtr::<u64>::empty();

    // DEALLOCATE p
    p.free(Tracked(perm_p));
}

} // verus!
