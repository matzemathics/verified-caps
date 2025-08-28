use vstd::prelude::*;

verus! {

pub type ActId = u16;
pub type CapId = u64;
pub type CapKey = (ActId, CapId);

pub ghost struct LinkedNode {
    pub back: Option<CapKey>,
    pub next: Option<CapKey>,
    pub child: Option<CapKey>,
    pub first_child: bool,
    pub depth: nat,
    pub index: nat,
}

pub type LinkMap = Map<CapKey, LinkedNode>;

pub type CapData = u64;

pub type CapMap = Map<CapKey, CapNode>;

pub ghost struct CapNode {
    pub children: Seq<CapKey>,
}

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

pub open spec fn get_parent(map: CapMap, child: CapKey) -> Option<CapKey> {
    if exists|parent: CapKey| map.contains_key(parent) && child_of(map, child, parent) {
        Some(choose|parent: CapKey| map.contains_key(parent) && child_of(map, child, parent))
    } else {
        None
    }
}

pub open spec fn child_of(map: CapMap, child: CapKey, parent: CapKey) -> bool {
    map[parent].children.contains(child)
}

pub open spec fn sibling_of(map: CapMap, a: CapKey, b: CapKey) -> bool {
    get_parent(map, a) == get_parent(map, b)
}

pub open spec fn depth_fn_condition(f: spec_fn(CapKey) -> nat, map: CapMap, key: CapKey) -> bool {
    if let Some(parent) = get_parent(map, key) {
        f(key) == f(parent) + 1
    }
    else {
        true
    }
}

pub open spec fn depth_fn(f: spec_fn(CapKey) -> nat, map: CapMap) -> bool {
    forall |key: CapKey| map.contains_key(key) ==> #[trigger] depth_fn_condition(f, map, key)
}

pub open spec fn depth(map: CapMap, key: CapKey) -> nat {
    let depth = choose |f: spec_fn(CapKey) -> nat| depth_fn(f, map);
    depth(key)
}

pub open spec fn acyclic(map: CapMap) -> bool {
    exists |f: spec_fn(CapKey) -> nat| depth_fn(f, map)
}

pub open spec fn tree_ish(map: CapMap) -> bool {
    forall |k: CapKey| map.contains_key(k) ==> parents(map, k).finite() && #[trigger] parents(map, k).len() <= 1
}

pub open spec fn parents(map: CapMap, key: CapKey) -> Set<CapKey> {
    Set::new(|parent: CapKey| map.contains_key(parent) && child_of(map, key, parent))
}

#[via_fn]
proof fn transitive_child_of_decreases(map: CapMap, child: CapKey, parent: CapKey) {
    assert forall|node: CapKey| #[trigger] map.contains_key(node) && map[node].children.contains(child)
    implies false by // depth(map, node) < depth(map, child)
    {}
}

pub open spec fn transitive_child_of(map: CapMap, child: CapKey, parent: CapKey) -> bool
    decreases depth(map, child),
    when acyclic(map)
    via transitive_child_of_decreases
{
    if child == parent {
        true
    } else {
        exists|node: CapKey|
            {
                &&& map.contains_key(node)
                &&& #[trigger] map[node].children.contains(child)
                &&& transitive_child_of(map, node, parent)
            }
    }
}

pub open spec fn transitive_children(map: CapMap, parent: CapKey) -> Set<CapKey> {
    map.dom().filter(|node| transitive_child_of(map, node, parent))
}

pub open spec fn insert_child(map: CapMap, parent: CapKey, child: CapKey) -> CapMap {
    let CapNode { children } = map[parent];
    let parent_node = CapNode { children: children.push(child) };
    let child_node = CapNode { children: Seq::empty() };
    map.insert(parent, parent_node).insert(child, child_node)
}

pub open spec fn revoke_single_parent_update(before: CapMap, removed: CapKey) -> CapMap {
    if let Some(parent) = get_parent(before, removed) {
        let parent_node = before[parent];
        let parent_node = CapNode {
            children: parent_node.children.remove_value(removed),
            ..parent_node
        };
        before.insert(parent, parent_node)
    } else {
        before
    }
}

} // verus!
