/*
 * Copyright (C) 2018 Nils Asmussen <nils@os.inf.tu-dresden.de>
 * Economic rights: Technische Universitaet Dresden (Germany)
 *
 * Copyright (C) 2019-2021 Nils Asmussen, Barkhausen Institut
 *
 * This file is part of M3 (Microkernel-based SysteM for Heterogeneous Manycores).
 *
 * M3 is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License version 2 as
 * published by the Free Software Foundation.
 *
 * M3 is distributed in the hope that it will be useful, but
 * WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU
 * General Public License version 2 for more details.
 */
use core::cmp::Ordering;
use core::fmt;
use core::mem::size_of;
use core::num::Wrapping;
use core::ptr::{read_volatile, NonNull};

use vstd::prelude::*;
use vstd::simple_pptr::PPtr;

use crate::boxed::Box;
use crate::nullable::Nullable;

verus! {

struct Node<K, V> {
    left: Nullable<Node<K, V>>,
    right: Nullable<Node<K, V>>,
    prio: Wrapping<u32>,
    key: K,
    value: V,
}

impl<K: Copy + Ord, V> Node<K, V> {
    fn new(key: K, value: V, prio: Wrapping<u32>) -> Self {
        Node { left: Nullable::null(), right: Nullable::null(), prio, key, value }
    }

    fn into_value(self) -> V {
        self.value
    }
}

/// A balanced binary tree.
///
/// A treap is a combination of a binary tree and a heap. So the child-node on the left has a
/// smaller key than the parent and the child on the right has a bigger key.
///
/// Additionally the root-node has the smallest priority and it increases when walking towards the
/// leafs. The priority is "randomized" by fibonacci-hashing. This way, the tree is well balanced
/// in most cases.
///
/// The idea and parts of the implementation are taken from the [MMIX](http://mmix.cs.hm.edu/)
/// simulator, written by Donald Knuth
pub struct Treap<K: Copy + Ord, V> {
    root: Nullable<Node<K, V>>,
    prio: Wrapping<u32>,
}

impl<K: Copy + Ord, V> Treap<K, V> {
    /// Creates an empty treap
    pub const fn new() -> Self {
        Treap { root: Nullable::null(), prio: Wrapping(314_159_265) }
    }

    /// Returns true if the treap has no elements
    pub fn is_empty(&self) -> bool {
        self.root.is_null()
    }

    /// Removes all elements from the treap
    pub fn clear(&mut self) {
        if let Some(r) = self.root.take_inner() {
            Self::remove_rec(r);
        }
        self.prio = Wrapping(314_159_265);
    }

    fn do_search<'a, F>(node: &'a Nullable<Node<K, V>>, f: &F) -> Option<&'a V> where
        F: Fn(&V) -> bool,
     {
        if node.is_null() {
            return None
        }
        let valid_node = node.read();

        if let Some(matched_value) = Self::do_search(&valid_node.left, f) {
            return Some(matched_value);
        }
        if f(&valid_node.value) {
            return Some(&valid_node.value);
        }
        if let Some(matched_value) = Self::do_search(&valid_node.right, f) {
            return Some(matched_value);
        }
        None
    }

    pub fn find<F>(&self, f: F) -> Option<&V> where F: Fn(&V) -> bool {
        Self::do_search(&self.root, &f)
    }

    fn remove_rec(mut node: Node<K, V>) {
        unsafe {
            if let Some(l) = node.left.take_inner() {
                Self::remove_rec(l);
            }
            if let Some(r) = node.right.take_inner() {
                Self::remove_rec(r);
            }
        }
    }

    /// Returns a reference to the value for the given key
    pub fn get(&self, key: &K) -> Option<&V> {
        self.get_node(key).map(|n| &n.value)
    }

    fn get_node<'a>(&'a self, key: &K) -> Option<&'a Node<K, V>> {
        let mut node = &self.root;

        loop {
            if node.is_null() {
                return None;
            }
            match key.cmp(&node.read().key) {
                Ordering::Less => node = &node.read().left,
                Ordering::Greater => node = &node.read().right,
                Ordering::Equal => return node.read_opt(),
            }
        }
    }

    /// Inserts the given value for given key, assuming that the key does not exist in the tree and
    /// returns a mutable reference to the stored value
    #[inline(always)]
    pub fn insert(&mut self, key: K, value: V) {
        let node = Node::new(key, value, self.prio);
        self.do_insert(node)
    }

    #[verifier::external_body]
    fn do_insert(&mut self, mut node: Node<K, V>) {
        let mut q = &mut self.root;
        loop {
            if q.is_null() {
                break ;
            }
            if q.read().prio >= self.prio {
                break
            }
            match node.key.cmp(&q.read().key) {
                Ordering::Less => q = &mut q.read().left,
                Ordering::Greater => q = &mut q.read().right,
                Ordering::Equal => panic!("Key does already exist"),
            }
        }

        let mut prev = *q;

        {
            // At this point we want to split the binary search tree p into two parts based on the
            // given key, forming the left and right subtrees of the new node q. The effect will be
            // as if key had been inserted before all of p’s nodes.
            let mut l = &mut node.left;
            let mut r = &mut node.right;

            loop {
                if prev.is_null() {
                    break
                }
                match node.key.cmp(&prev.read().key) {
                    Ordering::Less => {
                        *r = prev;
                        r = &mut prev.read().left;
                        prev = *r;
                    },
                    Ordering::Greater => {
                        *l = prev;
                        l = &mut prev.read().right;
                        prev = *l;
                    },
                    Ordering::Equal => panic!("Key does already exist"),
                }
            }
        }

        *q = Nullable::new(node);

        // fibonacci hashing to spread the priorities very even in the 32-bit room
        self.prio += Wrapping(0x9e37_79b9);  // floor(2^32 / phi), with phi = golden ratio
    }

    /// Sets the given key to given value, either by inserting a new node or by updating the value
    /// of the existing node. It returns a mutable reference to the stored value
    #[cfg(later)]
    pub fn set(&mut self, key: K, value: V) -> &mut V {
        if let Some(n) = self.get_node(&key) {
            unsafe {
                (*n.as_ptr()).value = value;
                &mut (*n.as_ptr()).value
            }
        } else {
            self.insert(key, value)
        }
    }

    /// Removes the root element of the treap and returns the value
    #[cfg(later)]
    pub fn remove_root(&mut self) -> Option<V> {
        self.root.map(
            |r|
                {
                    Self::remove_from(&mut self.root, r);
                    unsafe { Box::from_raw(r.as_ptr()).into_value() }
                },
        )
    }

    /// Removes the element from the treap for the given key and returns the value
    #[verifier::external_body]
    pub fn remove(&mut self, key: &K) -> Option<V> {
        let mut p = &mut self.root;

        loop {
            if p.is_null() {
                return None;
            }
            match key.cmp(&p.read().key) {
                Ordering::Less => p = &mut p.read().left,
                Ordering::Greater => p = &mut p.read().right,
                Ordering::Equal => break ,
            }
        }

        Self::remove_from(p);
        Some(p.into_inner().unwrap().into_value())
    }

    #[verifier::external_body]
    fn remove_from(p: &mut Nullable<Node<K, V>>) {
        if p.is_null() {
            return ;
        }
        let (hole, mut node) = p.take().into_hole();

        let (left, right) = (node.left.take(), node.right.take());

        if left.is_null() {
            *p = right;
        } else if right.is_null() {
            *p = left;
        } else {
            // rotate with left
            if left.read().prio < right.read().prio {
                let (left_hole, mut left) = left.into_hole();

                node.left = left.right;
                node.right = right;

                left.right = hole.fill(node);
                Self::remove_from(&mut left.right);

                *p = left_hole.fill(left);
            }
            // rotate with right
             else {
                let (right_hole, mut right) = right.into_hole();

                node.right = right.left;
                node.left = left;

                right.left = hole.fill(node);
                Self::remove_from(&mut right.left);

                *p = right_hole.fill(right);
            }
        }
    }

    /// The size of an allocation that a treap of this type performs
    pub const fn alloc_size() -> usize {
        size_of::<Node<K, V>>()
    }
}

impl<K: Copy + Ord, V> Default for Treap<K, V> {
    fn default() -> Self {
        Self::new()
    }
}

impl<K: Copy + Ord, V> Drop for Treap<K, V> {
    #[verifier::external_body]
    fn drop(&mut self)
        opens_invariants none
        no_unwind
    {
        self.clear();
    }
}

fn print_rec<K, V>(node: &Node<K, V>, f: &mut fmt::Formatter<'_>) -> fmt::Result where
    K: Copy + Ord + fmt::Debug,
    V: fmt::Debug,
 {
    writeln!(f, "  {:?} -> {:?}", node.key, node.value)?;
    if let Some(l) = node.left.read_opt() {
        print_rec(l, f)?;
    }
    if let Some(r) = node.right.read_opt() {
        print_rec(r, f)?;
    }
    Ok(())
}

impl<K: Copy + Ord + fmt::Debug, V: fmt::Debug> fmt::Debug for Treap<K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.root.read_opt() {
            Some(r) => print_rec(r, f),
            None => Ok(()),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::col::Vec;

    const TEST_NODE_COUNT: u32 = 10;

    #[test]
    fn test_in_order() {
        let vals = (0..TEST_NODE_COUNT).collect::<Vec<u32>>();
        test_add_modify_and_rem(&vals);
    }

    #[test]
    fn test_rev_order() {
        let vals = (0..TEST_NODE_COUNT).rev().collect::<Vec<u32>>();
        test_add_modify_and_rem(&vals);
    }

    #[test]
    fn test_rand_order() {
        let vals = [1, 6, 2, 3, 8, 9, 7, 5, 4];
        test_add_modify_and_rem(&vals);
    }

    fn test_add_modify_and_rem(vals: &[u32]) {
        let mut plus_one = Vec::new();
        for v in vals {
            plus_one.push(v + 1);
        }

        let mut treap = Treap::new();

        // create
        for v in vals {
            treap.insert(*v, v);
        }

        // modify
        for (i, v) in vals.iter().enumerate() {
            treap.set(*v, &plus_one[i]);
        }

        // find all
        for (i, v) in vals.iter().enumerate() {
            let val = treap.get(v);
            assert_eq!(val, Some(&&plus_one[i]));
        }

        // remove
        for (i, v) in vals.iter().enumerate() {
            let val = treap.remove(v);
            assert_eq!(val, Some(&plus_one[i]));
            assert_eq!(treap.get(v), None);
        }
    }

    #[test]
    fn test_clear() {
        let mut treap = Treap::new();
        treap.insert(0, 4);
        treap.insert(1, 5);
        treap.insert(4, 42);
        assert!(!treap.is_empty());
        treap.clear();
        assert!(treap.is_empty());
    }

    #[test]
    fn test_print() {
        use crate::format;

        let mut treap = Treap::new();
        treap.insert(78, 4);
        treap.insert(91, 5);
        treap.insert(44, 42);
        treap.insert(45, 11);
        treap.insert(1, 56);
        treap.insert(109, 10);
        assert_eq!(
            format!("{:x?}", treap),
            "  \
            78 -> 4\n  \
            44 -> 42\n  \
            1 -> 56\n  \
            45 -> 11\n  \
            109 -> 10\n  \
            91 -> 5\n\
            "
        );
    }

    #[test]
    fn test_remove() {
        let mut treap = Treap::new();
        treap.insert(78, 4);
        treap.insert(91, 5);
        treap.insert(44, 42);
        treap.insert(45, 11);
        treap.insert(1, 56);
        treap.insert(109, 10);
        treap.insert(250, 8);
        treap.insert(2, 41);

        let root = treap.get_root_mut().unwrap();
        assert_eq!(*root, 4);

        treap.remove(&78);
        treap.remove(&250);
        treap.remove(&1);
        treap.remove(&45);
        treap.remove(&109);
        treap.remove(&2);
        treap.remove(&91);
        treap.remove(&44);
        assert!(treap.is_empty());
    }

    #[test]
    fn test_remove_root() {
        let mut treap = Treap::new();
        treap.insert(0x123, 4);
        treap.insert(0x444, 5);
        treap.insert(0x222, 42);
        let val = treap.get_mut(&0x222).unwrap();
        *val += 1;
        assert_eq!(treap.get(&0x222), Some(&43));
        assert!(treap.remove_root().is_some());
        assert!(treap.remove_root().is_some());
        assert!(treap.remove_root().is_some());
        assert!(treap.is_empty());
    }

    #[test]
    fn test_alloc_size() {
        assert!(Treap::<(), ()>::alloc_size() > 0);
    }

}

} // verus!
