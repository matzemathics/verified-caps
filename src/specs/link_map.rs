use vstd::prelude::*;

use super::cap_map::{CapKey, CapMap, CapNode};

verus! {

pub ghost struct LinkedNode {
    pub back: Option<CapKey>,
    pub next: Option<CapKey>,
    pub child: Option<CapKey>,
    pub first_child: bool,
    pub depth: nat,
    pub index: nat,
}

pub type LinkMap = Map<CapKey, LinkedNode>;

pub open spec fn view(map: LinkMap) -> CapMap {
    map.map_values(|node: LinkedNode| node.to_spec(map))
}

impl LinkedNode {
    pub open spec fn to_spec(self, map: LinkMap) -> CapNode {
        CapNode { children: siblings(map, self.child) }
    }
}

pub trait MonotonicFunction<T> {
    type Result;

    spec fn apply(it: T) -> Self::Result;
    spec fn condition(a: T, b: T) -> bool;
}

pub struct Next;
impl MonotonicFunction<LinkedNode> for Next {
    type Result = Option<CapKey>;

    open spec fn apply(it: LinkedNode) -> Self::Result {
        it.next
    }

    open spec fn condition(a: LinkedNode, b: LinkedNode) -> bool {
        a.index > b.index && a.depth == b.depth
    }
}

pub struct Child;
impl MonotonicFunction<LinkedNode> for Child {
    type Result = Option<CapKey>;

    open spec fn apply(it: LinkedNode) -> Self::Result {
        it.child
    }

    open spec fn condition(a: LinkedNode, b: LinkedNode) -> bool {
        a.depth + 1 == b.depth
    }
}

pub open spec fn decreasing_condition<F: MonotonicFunction<LinkedNode, Result = Option<CapKey>>>(map: LinkMap, key: CapKey) -> bool {
    match F::apply(map[key]) {
        Some(next) => {
            &&& map.contains_key(next)
            &&& F::condition(map[key], map[next])
        }
        None => true
    }
}

#[via_fn]
proof fn siblings_decreases(map: LinkMap, link: Option<CapKey>) {
    if let Some(key) = link {
        assert(decreasing_condition::<Next>(map, key))
    }
}

pub open spec fn siblings(map: LinkMap, link: Option<CapKey>) -> Seq<CapKey>
    decreases next_index(map, link),
    when {
    &&& decreasing::<Next>(map)
    &&& link.is_some() ==> map.contains_key(link.unwrap())
}
    via siblings_decreases
{
    if let Some(key) = link {
        siblings(map, map[key].next).push(key)
    } else {
        Seq::empty()
    }
}

pub open spec fn next_index(map: LinkMap, key: Option<CapKey>) -> nat {
    if key.is_some() {
        map[key.unwrap()].index + 1
    } else {
        0
    }
}

pub open spec fn decreasing<F: MonotonicFunction<LinkedNode, Result = Option<CapKey>>>(map: LinkMap) -> bool {
    forall|key: CapKey| map.contains_key(key) ==> #[trigger] decreasing_condition::<F>(map, key)
}

}
