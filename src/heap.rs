use core::usize;

use alloc::vec::Vec;
use vstd::{
    cell::{CellId, PCell, PointsTo},
    prelude::*,
};

verus! {

#[derive(PartialEq, Eq, PartialOrd, Ord)]
struct HeapElt(u64);

struct Heap {
    elts: Vec<PCell<HeapElt>>,
    perms: Tracked<Seq<PointsTo<HeapElt>>>,
}

impl Heap {
    spec fn view(&self) -> Seq<PointsTo<HeapElt>> {
        self.perms@
    }

    spec fn perm_indices(&self) -> Seq<CellId> {
        self.perms@.map_values(|pt: PointsTo<HeapElt>| pt.id())
    }

    spec fn elt_indices(&self) -> Seq<CellId> {
        self.elts@.map_values(|cell: PCell<HeapElt>| cell.id())
    }

    spec fn indices_match(&self) -> bool {
        self.perm_indices() == self.elt_indices()
    }

    spec fn hole_at(&self, hole: usize) -> bool {
        self.indices_match() && forall|index: usize|
            index != hole && index < self@.len() ==> #[trigger] self@[index as int].is_init()
    }

    spec fn wf(&self) -> bool {
        self.indices_match() && forall|index: usize|
            index < self@.len() ==> #[trigger] self@[index as int].is_init()
    }

    fn move_hole(&mut self, hole: usize, index: usize)
        requires
            old(self).hole_at(hole),
            index != hole,
            index < old(self)@.len(),
            hole < old(self)@.len(),
        ensures
            self.hole_at(index),
    {
        let tracked mut perm = self.perms.borrow_mut().tracked_remove(index as int);
        let elt = self.elts[index].take(Tracked(&mut perm));
        self.perms.borrow_mut().tracked_insert(index, perm);
    }
}

spec fn spec_parent(index: usize) -> usize {
    index.checked_sub(1).unwrap_or(0) / 2
}

#[verifier::when_used_as_spec(spec_parent)]
fn parent(index: usize) -> usize
    returns
        parent(index),
{
    index.checked_sub(1).unwrap_or(0) / 2
}

proof fn lemma_parent_decreases(index: usize)
    requires
        index != 0,
    ensures
        index > parent(index),
{
}

} // verus!
