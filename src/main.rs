#![allow(non_snake_case)]

use std::{io::Error, process::exit};

use meta::Node;
use tables::ActivityCapTable;
use vstd::prelude::*;

pub extern crate alloc;

pub mod boxed {
    pub use alloc::boxed::Box;
}

#[cfg(verus_keep_ghost)]
mod lemmas;
mod meta;
mod specs;
mod state;
mod tables;

verus! {}

fn run() -> std::io::Result<()> {
    let mut args = std::env::args();
    args.next().ok_or(Error::other("missing argument"))?;
    let arg = args.next().ok_or(Error::other("missing argument"))?;
    let n = arg.parse::<u64>().map_err(Error::other)?;

    let mut cap_system = meta::Meta::new();
    let (table, _, _) = vstd::raw_ptr::allocate(
        std::mem::size_of::<ActivityCapTable<*mut Node>>(),
        std::mem::align_of::<ActivityCapTable<*mut Node>>(),
    );
    let table = table as *mut ActivityCapTable<*mut Node>;

    cap_system.insert_root(table, (0, 0));

    for i in 0..n {
        cap_system.insert_child(table, table, (0, i), (0, i + 1));
    }

    cap_system.revoke_children(table, (0, 0));

    Ok(())
}

fn main() {
    if let Err(e) = run() {
        eprintln!("linear_example: {e}");
        exit(e.raw_os_error().unwrap_or_default())
    }
}
