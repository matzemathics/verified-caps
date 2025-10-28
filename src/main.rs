#![allow(non_snake_case)]

use std::marker::PhantomData;
use std::{io::Error, process::exit};

use meta::{Meta, Node};
use tables::HashCapTable;
use vstd::layout::layout_for_type_is_valid;
use vstd::{prelude::*, raw_ptr::ptr_mut_write};

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

use vstd::prelude::*;

verus! {}

fn allocate_table() -> *mut HashCapTable<*mut Node> {
    let (table, _, _) = vstd::raw_ptr::allocate(
        std::mem::size_of::<HashCapTable<*mut Node>>(),
        std::mem::align_of::<HashCapTable<*mut Node>>(),
    );
    let table = table as *mut HashCapTable<*mut Node>;
    ptr_mut_write(table, Tracked::assume_new(), HashCapTable::new());

    table
}

fn run() -> std::io::Result<()> {
    let mut args = std::env::args();
    args.next().ok_or(Error::other("missing argument"))?;
    let arg = args.next().ok_or(Error::other("missing argument"))?;
    let n = arg.parse::<u64>().map_err(Error::other)?;

    let table = allocate_table();

    let mut cap_system = meta::Meta::new();
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
