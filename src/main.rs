#![allow(internal_features)]
#![feature(allocator_internals)]
#![feature(core_intrinsics)]
#![feature(maybe_uninit_write_slice)]
#![feature(linked_list_cursors)]
#![feature(btree_cursors)]
#![default_lib_allocator]
// #![cfg_attr(not(feature = "linux"), no_std)]

pub extern crate alloc;

pub mod boxed {
    pub use alloc::boxed::Box;
}

use vstd::prelude::*;

mod cell_map;
// mod insert_view;
mod lemmas;
// mod meta;
mod nullable;
mod ptr_map;
// mod revoke_view;
mod state;
mod tables;
mod tcb;

verus! {

fn main() {
}

} // verus!
