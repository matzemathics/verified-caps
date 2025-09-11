#![allow(non_snake_case)]

use vstd::prelude::*;

pub extern crate alloc;

pub mod boxed {
    pub use alloc::boxed::Box;
}

mod lemmas;
mod meta;
mod specs;
mod state;
mod tables;

verus! {}

fn main() {}
