//! This module is a collection of "pure-ghost" code, i.e. code that uses
//! neither executable nor linear ghost types and is only relevant to the
//! smt-solver.

mod common;
pub mod insert_view;
pub mod revoke_view;

#[cfg(verus_keep_ghost)]
pub use common::{
    lemma_depth_increase, lemma_siblings_none_empty, lemma_siblings_unfold,
    lemma_transitive_child_parent, lemma_transitive_children_empty, lemma_view_acyclic,
    lemma_view_tree_ish,
};
