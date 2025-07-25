use vstd::prelude::*;

use crate::lemmas::lemma_child_of_depth;

verus! {

pub type CapKey = u64;

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
    pub generation: nat,
    pub children: Seq<CapKey>,
}

pub open spec fn view(map: LinkMap) -> CapMap {
    map.map_values(|node: LinkedNode| node.to_spec(map))
}

impl LinkedNode {
    pub open spec fn to_spec(self, map: LinkMap) -> CapNode {
        CapNode { generation: self.depth, children: siblings(map, self.child) }
    }
}

pub open spec fn weak_next_link_condition(map: LinkMap, key: CapKey) -> bool {
    if map[key].next.is_none() {
        true
    } else {
        let next = map[key].next.unwrap();
        {
            &&& next != key
            &&& map.contains_key(next)
            &&& map[key].depth == map[next].depth
            &&& map[key].index > map[next].index
        }
    }
}

#[via_fn]
proof fn siblings_decreases(map: LinkMap, link: Option<CapKey>) {
    if let Some(key) = link {
        assert(weak_next_link_condition(map, key))
    }
}

pub open spec fn siblings(map: LinkMap, link: Option<CapKey>) -> Seq<CapKey>
    decreases next_index(map, link),
    when {
    &&& weak_next_connected(map)
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

pub open spec fn weak_next_connected(map: LinkMap) -> bool {
    forall|key: CapKey| map.contains_key(key) ==> #[trigger] weak_next_link_condition(map, key)
}

pub open spec fn get_parent(map: LinkMap, child: CapKey) -> Option<CapKey> {
    if exists|parent: CapKey| map.contains_key(parent) && child_of(map, child, parent) {
        Some(choose|parent: CapKey| map.contains_key(parent) && child_of(map, child, parent))
    } else {
        None
    }
}

pub open spec fn child_of(map: LinkMap, child: CapKey, parent: CapKey) -> bool {
    siblings(map, map[parent].child).contains(child)
}

pub open spec fn sibling_of(map: LinkMap, a: CapKey, b: CapKey) -> bool {
    get_parent(map, a) == get_parent(map, b)
}

pub open spec fn connection_condition(map: CapMap, child: CapKey, parent: CapKey) -> bool {
    map.contains_key(parent) && map[parent].children.contains(child) ==> {
        &&& map.contains_key(child)
        &&& map[child].generation == map[parent].generation + 1
    }
}

pub open spec fn map_connected(map: CapMap) -> bool {
    forall|parent: CapKey, child: CapKey| #[trigger] connection_condition(map, child, parent)
}

#[via_fn]
proof fn transitive_child_of_decreases(map: CapMap, child: CapKey, parent: CapKey) {
    assert forall|node: CapKey| map.contains_key(node) && map[node].children.contains(child)
    implies map[node].generation < map[child].generation by {
        assert(connection_condition(map, child, node));
    }
}

pub open spec fn transitive_child_of(map: CapMap, child: CapKey, parent: CapKey) -> bool
    decreases map[child].generation,
    when map_connected(map)
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

pub open spec fn weak_child_link_condition(map: LinkMap, key: CapKey) -> bool {
    if map[key].child.is_none() {
        true
    } else {
        let child = map[key].child.unwrap();
        {
            &&& child != key
            &&& map.contains_key(child)
            &&& map[key].depth + 1 == map[child].depth
        }
    }
}

pub open spec fn weak_child_connected(map: LinkMap) -> bool {
    forall|key: CapKey| map.contains_key(key) ==> #[trigger] weak_child_link_condition(map, key)
}

pub open spec fn insert_child(map: CapMap, parent: CapKey, child: CapKey) -> CapMap {
    let CapNode { generation, children } = map[parent];
    let parent_node = CapNode { children: children.push(child), generation };
    let child_node = CapNode { generation: generation + 1, children: Seq::empty() };
    map.insert(parent, parent_node).insert(child, child_node)
}

pub open spec fn revoke_single_parent_update(before: LinkMap, removed: CapKey) -> CapMap {
    if let Some(parent) = get_parent(before, removed) {
        let parent_node = view(before)[parent];
        let parent_node = CapNode {
            children: parent_node.children.remove_value(removed),
            ..parent_node
        };
        view(before).insert(parent, parent_node)
    } else {
        view(before)
    }
}

} // verus!
