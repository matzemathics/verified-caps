use vstd::prelude::*;

use crate::lemmas::lemma_depth_increase;

verus! {

pub type ActId = u16;
pub type CapId = u64;
pub type CapKey = (ActId, CapId);

pub type CapData = u64;

pub type CapMap = Map<CapKey, CapNode>;

pub ghost struct CapNode {
    pub children: Seq<CapKey>,
}

pub open spec fn get_parent(map: CapMap, child: CapKey) -> Option<CapKey> {
    if exists |parent: CapKey| edge(map, parent, child) {
        Some(choose |parent: CapKey| edge(map, parent, child))
    } else {
        None
    }
}

pub open spec fn edge(map: CapMap, parent: CapKey, child: CapKey) -> bool {
    map.contains_key(parent) && map[parent].children.contains(child)
}

pub open spec fn sibling_of(map: CapMap, a: CapKey, b: CapKey) -> bool {
    get_parent(map, a) == get_parent(map, b)
}

pub open spec fn depth_fn(f: spec_fn(CapKey) -> nat, map: CapMap) -> bool {
    forall |p: CapKey, key: CapKey|
        map.contains_key(key) &&
        map.contains_key(p) &&
        map[p].children.contains(key)
        ==> f(key) == f(p) + 1
}

pub open spec fn depth(map: CapMap, key: CapKey) -> nat {
    let depth = choose |f: spec_fn(CapKey) -> nat| depth_fn(f, map);
    depth(key)
}

pub open spec fn acyclic(map: CapMap) -> bool {
    exists |f: spec_fn(CapKey) -> nat| depth_fn(f, map)
}

pub open spec fn tree_ish(map: CapMap) -> bool {
    forall |k: CapKey| map.contains_key(k)
    ==> parents(map, k).finite() &&
     #[trigger] parents(map, k).len() <= 1
}

pub open spec fn parents(map: CapMap, key: CapKey) -> Set<CapKey> {
    Set::new(|parent: CapKey| edge(map, parent, key))
}

#[via_fn]
proof fn transitive_child_of_decreases(map: CapMap, child: CapKey, parent: CapKey) {
    assert forall|node: CapKey| #[trigger] map.contains_key(node) && map[node].children.contains(child)
    implies depth(map, node) < depth(map, child) by
    {
        lemma_depth_increase(map, node, child);
    }
}

pub open spec fn transitive_child_of(map: CapMap, child: CapKey, parent: CapKey) -> bool
    decreases depth(map, child),
    when acyclic(map) && map.contains_key(child)
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
