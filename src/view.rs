use vstd::{
    prelude::*,
    seq::{axiom_seq_add_index1, axiom_seq_add_index2, axiom_seq_new_index},
};

use crate::state::{
    back_link_condition, child_link_condition, next_index, next_link_condition,
    weak_child_connected, weak_child_link_condition, weak_next_connected, weak_next_link_condition,
    CapKey, LinkMap, LinkedNode, SysState,
};

verus! {

pub type CapData = u64;

pub type CapMap = Map<CapKey, CapNode>;

pub ghost struct CapNode {
    pub generation: nat,
    pub children: Seq<CapKey>,
}

pub open spec fn connected(map: CapMap) -> bool {
    forall|key: CapKey|
        map.contains_key(key) ==> forall|index: int|
            0 <= index < map[key].children.len() ==> {
                &&& map.contains_key(#[trigger] map[key].children[index])
                &&& map[key].generation < map[map[key].children[index]].generation
            }
}

pub open spec fn generation_bounded(map: CapMap, bound: nat) -> bool {
    forall|key: CapKey| map.contains_key(key) ==> #[trigger] map[key].generation < bound
}

pub open spec fn direct_children(map: CapMap, keys: Seq<CapKey>) -> Seq<CapKey> {
    keys.map_values(|key| map[key].children).flatten()
}

proof fn lemma_direct_children_inc_gen(map: CapMap, keys: Seq<CapKey>)
    requires
        keys.to_set().subset_of(map.dom()),
        connected(map),
        direct_children(map, keys).len() != 0,
    ensures
        keys.map_values(|key| map[key].generation as int).min() < direct_children(
            map,
            keys,
        ).map_values(|key| map[key].generation as int).min(),
{
    let generation = |key| map[key].generation as int;

    let parents = keys.map_values(generation);
    let children = direct_children(map, keys).map_values(generation);

    children.min_ensures();
    assert(exists|index| 0 <= index < children.len() && children[index] == children.min());
    let min_child_index = choose|index: int|
        0 <= index < children.len() && children[index] == children.min();

    axiom_seq_new_index(
        direct_children(map, keys).len(),
        |i| generation(direct_children(map, keys)[i]),
        min_child_index,
    );

    parents.min_ensures();
    assert(exists|index| 0 <= index < parents.len() && parents[index] == parents.min());
    let min_parent_index = choose|index: int|
        0 <= index < parents.len() && parents[index] == parents.min();

    axiom_seq_new_index(keys.len(), |i| generation(keys[i]), min_parent_index);

    let get_children = |key: CapKey| map[key].children;
    let unflat = keys.map_values(get_children);
    lemma_flatten_index(unflat, min_child_index);

    let (origin, offset) = choose|origin: int, offset: int|
        0 <= origin < unflat.len() && 0 <= offset < unflat[origin].len() && unflat[origin][offset]
            == unflat.flatten()[min_child_index];

    assert(generation(keys[min_parent_index]) <= parents[origin] == generation(keys[origin]));

    assert(map.contains_key(keys[origin]));
    assert(map[keys[origin]].children[offset] == direct_children(map, keys)[min_child_index]);

    assert(generation(keys[origin]) < children[min_child_index]);
}

proof fn lemma_direct_children_closed(map: CapMap, keys: Seq<CapKey>)
    requires
        keys.to_set().subset_of(map.dom()),
        connected(map),
    ensures
        direct_children(map, keys).to_set().subset_of(map.dom()),
{
    assert forall|key: CapKey|
        direct_children(map, keys).contains(key) implies #[trigger] map.dom().contains(key) by {
        let that_index = choose|index: int|
            0 <= index < direct_children(map, keys).len() && direct_children(map, keys)[index]
                == key;

        let children = |key: CapKey| map[key].children;
        let unflat = keys.map_values(children);
        lemma_flatten_index(unflat, that_index);

        let (origin, offset) = choose|origin: int, offset: int|
            0 <= origin < unflat.len() && 0 <= offset < unflat[origin].len()
                && unflat[origin][offset] == unflat.flatten()[that_index];

        assert(map.contains_key(keys[origin]));
        assert(map.contains_key(map[keys[origin]].children[offset]));
    }
}

proof fn lemma_flatten_index<A>(arg: Seq<Seq<A>>, index: int)
    requires
        0 <= index < arg.flatten().len(),
    ensures
        exists|origin: int, offset: int|
            0 <= origin < arg.len() && 0 <= offset < arg[origin].len() && arg[origin][offset]
                == arg.flatten()[index],
    decreases arg.len(),
{
    if arg.len() == 0 {
    } else {
        if index < arg.first().len() {
            axiom_seq_add_index1(arg.first(), arg.drop_first().flatten(), index);
        } else {
            axiom_seq_add_index2(arg.first(), arg.drop_first().flatten(), index);
            lemma_flatten_index(arg.drop_first(), index - arg.first().len());
        }
    }
}

proof fn lemma_flatten_index2<A>(arg: Seq<Seq<A>>, origin: int, offset: int)
    requires
        0 <= origin < arg.len(),
        0 <= offset < arg[origin].len(),
    ensures
        exists|index|
            0 <= index < arg.flatten().len() && arg.flatten()[index] == arg[origin][offset],
    decreases arg.len(),
{
    if origin == 0 {
        axiom_seq_add_index1(arg.first(), arg.drop_first().flatten(), offset);
        assert(arg[0][offset] == arg.flatten()[offset]);
    } else {
        lemma_flatten_index2(arg.drop_first(), origin - 1, offset);
        let index = choose|index: int|
            0 <= index < arg.drop_first().flatten().len() && arg.drop_first().flatten()[index]
                == arg[origin][offset];

        axiom_seq_add_index2(arg.first(), arg.drop_first().flatten(), index + arg.first().len());
        assert(arg[origin][offset] == arg.flatten()[index + arg.first().len()]);
    }
}

proof fn lemma_transitive_children_decreases(map: CapMap, keys: Seq<CapKey>, bound: nat)
    requires
        connected(map),
        generation_bounded(map, bound),
        keys.to_set().subset_of(map.dom()),
        direct_children(map, keys).len() != 0,
    ensures
        bound - keys.map_values(|key| map[key].generation as int).min() > bound - direct_children(
            map,
            keys,
        ).map_values(|key| map[key].generation as int).min(),
{
    lemma_direct_children_inc_gen(map, keys);

    let generation = |key: CapKey| map[key].generation as int;
    let children = |key: CapKey| map[key].children;
    let new_gens = direct_children(map, keys).map_values(generation);

    new_gens.min_ensures();
    assert(exists|i: int| new_gens.len() > i && new_gens[i] == new_gens.min());
    let that_index = choose|i: int| 0 <= i < new_gens.len() && new_gens[i] == new_gens.min();

    assert(that_index < direct_children(map, keys).len() == direct_children(map, keys).map_values(
        generation,
    ).len());
    axiom_seq_new_index(
        direct_children(map, keys).len(),
        |i| generation(direct_children(map, keys)[i]),
        that_index,
    );

    assert(direct_children(map, keys).map_values(generation)[that_index] == generation(
        direct_children(map, keys)[that_index],
    ));
    let that_key = direct_children(map, keys)[that_index];

    let unflat = keys.map_values(children);
    lemma_flatten_index(unflat, that_index);

    let (origin, offset) = choose|origin: int, offset: int|
        0 <= origin < unflat.len() && 0 <= offset < unflat[origin].len() && unflat[origin][offset]
            == unflat.flatten()[that_index];

    assert(map.contains_key(keys[origin]));
    assert(map.contains_key(map[keys[origin]].children[offset]));

    axiom_seq_new_index(keys.len(), |i| children(keys[i]), origin);
    assert(map[keys[origin]].children[offset] == keys.map_values(children)[origin][offset]);

    assert(map.contains_key(that_key));

    assert(0 <= new_gens.min() < bound);
}

#[via_fn]
proof fn transitive_children_decreases_via(map: CapMap, keys: Seq<CapKey>, bound: nat) {
    if direct_children(map, keys).len() == 0 {
    } else {
        lemma_direct_children_closed(map, keys);
        lemma_transitive_children_decreases(map, keys, bound);
    }
}

pub open spec fn remove_all<A>(input: Seq<A>, needles: Seq<A>) -> Seq<A>
    decreases needles.len(),
{
    if needles.len() == 0 {
        input
    } else {
        remove_all(input.remove_value(needles.last()), needles.drop_last())
    }
}

pub open spec fn transitive_children(map: CapMap, keys: Seq<CapKey>, bound: nat) -> Seq<CapKey>
    decreases bound - keys.map_values(|key| map[key].generation as int).min(),
    when keys.to_set().subset_of(map.dom()) && connected(map) && generation_bounded(map, bound)
    via transitive_children_decreases_via
{
    let new_keys = direct_children(map, keys);

    if new_keys.len() == 0 {
        keys
    } else {
        keys + transitive_children(map, new_keys, bound)
    }
}

proof fn lemma_direct_children_complete(
    map: CapMap,
    keys: Seq<CapKey>,
    parent: CapKey,
    child: CapKey,
)
    requires
        map.contains_key(parent),
        map[parent].children.contains(child),
        keys.contains(parent),
    ensures
        direct_children(map, keys).contains(child),
{
    let parent_index = choose|index: int| 0 <= index < keys.len() && keys[index] == parent;
    let child_offset = choose|index: int|
        0 <= index < map[parent].children.len() && map[parent].children[index] == child;

    let children = |key: CapKey| map[key].children;
    lemma_flatten_index2(keys.map_values(children), parent_index, child_offset);
}

proof fn lemma_transitive_children_rec(map: CapMap, keys: Seq<CapKey>, bound: nat)
    requires
        connected(map),
        generation_bounded(map, bound),
        keys.to_set().subset_of(map.dom()),
    ensures
        transitive_children(map, keys, bound) == keys + transitive_children(
            map,
            direct_children(map, keys),
            bound,
        ),
{
    if direct_children(map, keys).len() == 0 {
        assert(transitive_children(map, keys, bound) == keys);
        assert(transitive_children(map, direct_children(map, keys), bound).len() == 0);
    } else {
        lemma_direct_children_closed(map, keys);
    }
}

proof fn lemma_transitive_children_complete(
    map: CapMap,
    keys: Seq<CapKey>,
    bound: nat,
    parent: CapKey,
    child: CapKey,
)
    requires
        connected(map),
        generation_bounded(map, bound),
        keys.to_set().subset_of(map.dom()),
        map.contains_key(parent),
        transitive_children(map, keys, bound).contains(parent),
        map[parent].children.contains(child),
    ensures
        transitive_children(map, keys, bound).contains(child),
    decreases bound - keys.map_values(|key| map[key].generation as int).min(),
{
    let new_keys = direct_children(map, keys);

    if keys.contains(parent) {
        lemma_direct_children_complete(map, keys, parent, child);
        assert(new_keys.contains(child));
        assert(new_keys.len() > 0);

        lemma_direct_children_closed(map, keys);
        assert(new_keys.is_prefix_of(transitive_children(map, new_keys, bound)));

        assert(transitive_children(map, new_keys, bound).contains(child));
        assert(transitive_children(map, new_keys, bound).is_suffix_of(
            transitive_children(map, keys, bound),
        ));
    } else {
        let parent_index = choose|index: int|
            0 <= index < transitive_children(map, keys, bound).len() && transitive_children(
                map,
                keys,
                bound,
            )[index] == parent;

        lemma_transitive_children_rec(map, keys, bound);

        if parent_index < keys.len() {
            axiom_seq_add_index1(keys, transitive_children(map, new_keys, bound), parent_index);
        } else {
            axiom_seq_add_index2(keys, transitive_children(map, new_keys, bound), parent_index);
            assert(transitive_children(map, new_keys, bound).contains(parent));

            if new_keys.len() == 0 {
                assert(transitive_children(map, keys, bound) == keys);
            } else {
                lemma_direct_children_closed(map, keys);
                lemma_transitive_children_decreases(map, keys, bound);
                lemma_transitive_children_complete(map, new_keys, bound, parent, child);
                assert(transitive_children(map, new_keys, bound).contains(child));

                let child_index = choose|index: int|
                    0 <= index < transitive_children(map, new_keys, bound).len()
                        && transitive_children(map, new_keys, bound)[index] == child;

                axiom_seq_add_index2(
                    keys,
                    transitive_children(map, new_keys, bound),
                    keys.len() + child_index,
                );
                assert(transitive_children(map, keys, bound).contains(child));
            }
        }
    }
}

pub open spec fn revoke_children(map: CapMap, parent: CapKey, bound: nat) -> CapMap {
    map.insert(parent, CapNode { children: Seq::empty(), ..map[parent] }).remove_keys(
        transitive_children(map, map[parent].children, bound).to_set(),
    )
}

pub open spec fn insert_child(
    map: CapMap,
    parent: CapKey,
    child: CapKey,
) -> CapMap {
    let CapNode { generation, children } = map[parent];
    let parent_node = CapNode { children: children.push(child), generation };
    let child_node = CapNode { generation: generation + 1, children: Seq::empty() };
    map.insert(parent, parent_node).insert(child, child_node)
}

pub open spec fn view(map: LinkMap) -> CapMap {
    map.map_values(|node: LinkedNode| node.to_spec(map))
}

impl LinkedNode {
    pub open spec fn to_spec(self, map: LinkMap) -> CapNode {
        CapNode {
            generation: self.depth,
            children: siblings(map, self.child)
        }
    }
}

#[via_fn]
proof fn siblings_decreases(map: LinkMap, link: Option<CapKey>)
{
    if let Some(key) = link {
        assert(weak_next_link_condition(map, key))
    }
}

pub open spec fn siblings(map: LinkMap, link: Option<CapKey>) -> Seq<CapKey>
decreases next_index(map, link)
    when {
        &&& weak_next_connected(map)
        &&& link.is_some() ==> map.contains_key(link.unwrap())
    }
    via siblings_decreases
{
    if let Some(key) = link {
        siblings(map, map[key].next).push(key)
    }
    else {
        Seq::empty()
    }
}

proof fn lemma_siblings_none_empty(map: LinkMap)
ensures siblings(map, None) == Seq::<CapKey>::empty()
{
    assert(siblings(map, None) == Seq::<CapKey>::empty()) by (compute_only);
}

proof fn lemma_siblings_unfold(map: LinkMap, key: CapKey)
requires
    weak_next_connected(map),
    map.contains_key(key)
ensures siblings(map, Some(key)) == siblings(map, map[key].next).push(key)
{
    assert(weak_next_link_condition(map, key));
}

proof fn lemma_insert_siblings_unchanged(map: LinkMap, new: (CapKey, LinkedNode), key: CapKey)
requires
    !map.contains_key(new.0),
    map.contains_key(key),
    weak_next_connected(map),
    weak_next_link_condition(map.insert(new.0, new.1), new.0)
ensures
    siblings(map, Some(key)) == siblings(map.insert(new.0, new.1), Some(key))
decreases
    map[key].index
{
    assert(map[key] == map.insert(new.0, new.1)[key]);

    assert forall |key: CapKey| map.insert(new.0, new.1).contains_key(key)
    implies #[trigger] weak_next_link_condition(map.insert(new.0, new.1), key)
    by {
        if key == new.0 { }
        else { assert(weak_next_link_condition(map, key)); }
    };

    assert(weak_next_connected(map.insert(new.0, new.1)));

    if let Some(next) = map[key].next {
        assert(weak_next_link_condition(map, key));
        lemma_insert_siblings_unchanged(map, new, next);
        assert(siblings(map, Some(key)) == siblings(map.insert(new.0, new.1), Some(key)));
    }
    else {
        lemma_siblings_none_empty(map);
        lemma_siblings_none_empty(map.insert(new.0, new.1));
        assert(siblings(map, Some(key)) == siblings(map, None).push(key));
        lemma_siblings_unfold(map.insert(new.0, new.1), key);
        assert(siblings(map.insert(new.0, new.1), Some(key)) == siblings(map, None).push(key));
        //siblings(map.insert(new.0, new.1), Some(key)));
    }
}

proof fn lemma_siblings_unchanged(map_a: LinkMap, map_b: LinkMap, key: CapKey)
requires
    forall |key: CapKey| #[trigger] map_a[key].next == map_b[key].next,
    weak_next_connected(map_a),
    weak_next_connected(map_b),
    map_a.contains_key(key),
    map_b.contains_key(key),
ensures
    siblings(map_a, Some(key)) == siblings(map_b, Some(key))
decreases map_a[key].index
{
    lemma_siblings_unfold(map_a, key);
    lemma_siblings_unfold(map_b, key);

    if let Some(next) = map_a[key].next {
        assert(weak_next_link_condition(map_a, key));
        assert(weak_next_link_condition(map_b, key));
        lemma_siblings_unchanged(map_a, map_b, next);
    }
    else {
        lemma_siblings_none_empty(map_a);
        lemma_siblings_none_empty(map_b);
    }
}

pub open spec fn ith_predecessor(map: LinkMap, from: CapKey, i: int, to: CapKey) -> bool {
    let siblings = siblings(map, Some(from));
    0 <= i < siblings.len() && siblings[siblings.len() - i - 1] == to
}

proof fn lemma_ith_predecessor_univalent(map: LinkMap, from_a: CapKey, from_b: CapKey, i: int, to: CapKey)
requires
    forall |key: CapKey| #[trigger] map.contains_key(key) ==>
        next_link_condition(SysState::Clean, map, key),
    ith_predecessor(map, from_a, i, to),
    ith_predecessor(map, from_b, i, to),
    map.contains_key(from_a),
    map.contains_key(from_b),
ensures
    from_a == from_b
decreases i
{
    if i == 0 { }
    else {
        let a = siblings(map, Some(from_a)).drop_last();
        assert(a[a.len() - i] == to);
        assert(siblings(map, map[from_a].next) == a);
        assert(a == siblings(map, Some(a.last())));

        let b = siblings(map, Some(from_b)).drop_last();
        assert(b[b.len() - i] == to);
        assert(siblings(map, map[from_b].next) == b);
        assert(b == siblings(map, Some(b.last())));

        lemma_ith_predecessor_univalent(map, a.last(), b.last(), i - 1, to);
    }
}

pub open spec fn predecessor(map: LinkMap, node: CapKey, i: int) -> Option<CapKey> {
    if exists |key: CapKey| ith_predecessor(map, key, i, node) {
        Some(choose |key: CapKey| ith_predecessor(map, key, i, node))
    }
    else {
        None
    }
}

proof fn lemma_no_predecessor(map: LinkMap, node: CapKey, i: int, pred: CapKey)
requires
    forall |key: CapKey| #[trigger] map.contains_key(key) ==>
        next_link_condition(SysState::Clean, map, key),
    ith_predecessor(map, pred, i, node),
    map.contains_key(pred),
    map[node].first_child,
    i > 0,
ensures false
decreases i
{
    if i == 1 {
        lemma_siblings_unfold(map, pred);
        assert(map[pred].next == Some(node));
    }
    else {
        let a = siblings(map, Some(pred)).drop_last();
        assert(a[a.len() - i] == node);
        assert(siblings(map, map[pred].next) == a);
        assert(a == siblings(map, Some(a.last())));

        lemma_no_predecessor(map, node, i - 1, a.last());
    }
}

proof fn lemma_predecessor_transitive(map: LinkMap, a: CapKey, i: int, b: CapKey, j: int, c: CapKey)
requires
    forall |key: CapKey| #[trigger] map.contains_key(key) ==>
        next_link_condition(SysState::Clean, map, key),
    i >= 0,
    ith_predecessor(map, a, i + j, c),
    ith_predecessor(map, b, j, c),
    map.contains_key(a),
    map.contains_key(b),
ensures
    ith_predecessor(map, a, i, b),
decreases i
{
    if i == 0 {
        lemma_ith_predecessor_univalent(map, a, b, j, c);
    }
    else {
        let a_prime = siblings(map, Some(a)).drop_last();
        assert(a_prime[a_prime.len() - (i + j)] == c);
        assert(siblings(map, map[a].next) == a_prime);
        assert(a_prime == siblings(map, Some(a_prime.last())));

        lemma_predecessor_transitive(map, a_prime.last(), i - 1, b, j, c);
    }
}

pub open spec fn child_of(map: LinkMap, child: CapKey, parent: CapKey) -> bool {
    siblings(map, map[parent].child).contains(child)
}

proof fn lemma_child_of_univalent(map: LinkMap, parent_a: CapKey, parent_b: CapKey, child: CapKey)
requires
    forall |key: CapKey| #[trigger] map.contains_key(key) ==> {
        &&& next_link_condition(SysState::Clean, map, key)
        &&& back_link_condition(SysState::Clean, map, key)
        &&& child_link_condition(SysState::Clean, map, key)
    },
    child_of(map, child, parent_a),
    child_of(map, child, parent_b),
    map.contains_key(parent_a),
    map.contains_key(parent_b),
ensures
    parent_a == parent_b
{
    let a = map[parent_a].child.unwrap();
    let index_a = choose |i: int|
        0 <= i < siblings(map, Some(a)).len() && siblings(map, Some(a))[i] == child;
    let step_a = siblings(map, Some(a)).len() - index_a - 1;
    assert(ith_predecessor(map, a, step_a, child));

    let b = map[parent_b].child.unwrap();
    let index_b = choose |i: int|
        0 <= i < siblings(map, Some(b)).len() && siblings(map, Some(b))[i] == child;
    let step_b = siblings(map, Some(b)).len() - index_b - 1;
    assert(ith_predecessor(map, b, step_b, child));

    if step_a == step_b {
        lemma_ith_predecessor_univalent(map, a, b, step_a, child);
    }
    else if step_a > step_b {
        lemma_predecessor_transitive(map, a, step_a - step_b, b, step_b, child);
        lemma_no_predecessor(map, b, step_a - step_b, a);
    }
    else {
        assert(step_b > step_a);
        lemma_predecessor_transitive(map, b, step_b - step_a, a, step_a, child);
        lemma_no_predecessor(map, a, step_b - step_a, b);
    }
}

pub ghost struct OpInsertChild {
    pub parent: CapKey,
    pub child: CapKey,
}

impl OpInsertChild {
    pub open spec fn insert_node(&self, map: LinkMap) -> LinkedNode {
        LinkedNode {
            first_child: true,
            back: Some(self.parent),
            next: map[self.parent].child,
            child: None,
            depth: map[self.parent].depth + 1,
            index: next_index(map, map[self.parent].child),
        }
    }

    pub open spec fn insert_view_node(&self, map: LinkMap) -> CapNode {
        CapNode { generation: map[self.parent].depth+1, children: Seq::empty()}
    }

    pub open spec fn child_update(&self, map: LinkMap) -> LinkMap {
        map.insert(self.child, self.insert_node(map))
    }

    pub open spec fn next_update(&self, map: LinkMap) -> LinkMap {
        if map[self.parent].child.is_none() {
            map
        }
        else {
            let next = map[self.parent].child.unwrap();
            let next_node = LinkedNode { back: Some(self.child), first_child: false, ..map[next] };

            map.insert(next, next_node)
        }
    }

    pub open spec fn update(&self, map: LinkMap) -> LinkMap {
        self.parent_update(self.next_update(self.child_update(map)))
    }

    pub open spec fn parent_update(&self, map: LinkMap) -> LinkMap {
        let parent_node = LinkedNode { child: Some(self.child), ..map[self.parent] };
        map.insert(self.parent,  parent_node)
    }

    proof fn lemma_view_child_update(&self, map: LinkMap)
    requires
        !map.contains_key(self.child),
        map.contains_key(self.parent),
        weak_next_connected(map),
        weak_child_connected(map),
    ensures
        view(self.child_update(map)) == view(map).insert(self.child, self.insert_view_node(map))
    {
        assert forall |key: CapKey| #[trigger] map.contains_key(key)
        implies {
            &&& self.child_update(map)[key].depth == map[key].depth
            &&& self.child_update(map)[key].child == map[key].child
        }
        by {};

        lemma_siblings_none_empty(map);
        lemma_siblings_none_empty(self.child_update(map));

        assert(weak_next_link_condition(self.child_update(map), self.child)) by {
            if map[self.parent].child.is_none() {
                assert(self.child_update(map)[self.child].next.is_none());
            }
            else {
                let next = map[self.parent].child.unwrap();
                assert(weak_child_link_condition(map, self.parent));
            }
        };

        assert forall |key: CapKey| map.contains_key(key)
        implies #[trigger] siblings(self.child_update(map), Some(key)) == siblings(map, Some(key))
        by {
            lemma_insert_siblings_unchanged(map, (self.child, self.insert_node(map)), key);
        };

        assert(self.insert_view_node(map) == self.insert_node(map).to_spec(self.child_update(map)));
        assert(view(map).insert(self.child, self.insert_view_node(map))[self.child] == view(self.child_update(map))[self.child]);


        assert forall |key: CapKey| map.contains_key(key)
        implies #[trigger] view(self.child_update(map))[key] == view(map).insert(self.child, self.insert_view_node(map))[key]
        by {
            assert(view(map).insert(self.child, self.insert_view_node(map))[key] == view(map)[key]);
            assert(view(map)[key] == self.child_update(map)[key].to_spec(map));
            if map[key].child.is_none() { }
            else {
                let child = map[key].child.unwrap();
                assert(weak_child_link_condition(map, key));
                assert(map.contains_key(child));
                assert(siblings(map, Some(child)) == siblings(self.child_update(map), Some(child)));
            }
        };

        assert(view(self.child_update(map)) =~= view(map).insert(self.child, self.insert_view_node(map)));
    }

    proof fn lemma_view_next_update(&self, map: LinkMap)
    requires
        map.contains_key(self.parent),
        weak_next_connected(map),
        weak_child_connected(map),
    ensures
        view(self.next_update(map)) == view(map)
    {
        if map[self.parent].child.is_none() { }
        else {
            let next = map[self.parent].child.unwrap();

            assert forall |key: CapKey| map.contains_key(key)
            implies #[trigger] view(map)[key] == view(self.next_update(map))[key]
            by {
                if map[key].child.is_none() {
                    lemma_siblings_none_empty(map);
                    lemma_siblings_none_empty(self.next_update(map));
                }
                else {
                    assert(weak_child_link_condition(map, key));
                    self.lemma_invariants_update_next(map);
                    lemma_siblings_unchanged(map, self.next_update(map), map[key].child.unwrap());
                }
            };

            assert(weak_child_link_condition(map, self.parent));
            assert(view(map).dom() =~= view(self.next_update(map)).dom());
            assert(view(self.next_update(map)) =~= view(map));
        }
    }

    pub open spec fn invariants(&self, map: LinkMap) -> bool {
        &&& map.contains_key(self.parent)
        &&& weak_child_connected(map)
        &&& weak_next_connected(map)
    }

    proof fn lemma_weak_next_update_child(&self, map: LinkMap)
    requires self.invariants(map), !map.contains_key(self.child)
    ensures weak_next_connected(self.child_update(map))
    {
        assert forall |key: CapKey| self.child_update(map).contains_key(key)
        implies #[trigger] weak_next_link_condition(self.child_update(map), key)
        by {
            if key == self.child {
                assert(weak_child_link_condition(map, self.parent));
                assert(weak_next_link_condition(self.child_update(map), self.child));
            }
            else {
                assert(weak_next_link_condition(map, key));
            }
        };
    }

    proof fn lemma_weak_child_update_child(&self, map: LinkMap)
    requires self.invariants(map), !map.contains_key(self.child)
    ensures weak_child_connected(self.child_update(map))
    {
        assert forall |key: CapKey| self.child_update(map).contains_key(key)
        implies #[trigger] weak_child_link_condition(self.child_update(map), key)
        by {
            if key == self.child { }
            else {
                assert(weak_child_link_condition(map, key));
            }
        };
    }

    proof fn lemma_invariants_update_next(&self, map: LinkMap)
    requires self.invariants(map)
    ensures self.invariants(self.next_update(map))
    {
        assert forall |key: CapKey| #[trigger] self.next_update(map).contains_key(key)
        implies {
            &&& weak_next_link_condition(self.next_update(map), key)
            &&& weak_child_link_condition(self.next_update(map), key)
        }
        by {
            assert(weak_child_link_condition(map, self.parent));
            assert(weak_next_link_condition(map, key));
            assert(weak_child_link_condition(map, key));
        };
    }

    proof fn lemma_invariants_update_parent(&self, map: LinkMap)
    requires
        self.invariants(map),
        map.contains_key(self.child),
        map[self.child].depth == map[self.parent].depth + 1
    ensures self.invariants(self.parent_update(map))
    {
        assert forall |key: CapKey| #[trigger] self.parent_update(map).contains_key(key)
        implies {
            &&& weak_next_link_condition(self.parent_update(map), key)
            &&& weak_child_link_condition(self.parent_update(map), key)
        }
        by {
            assert(weak_next_link_condition(map, key));

            if key == self.parent {
                assert(weak_child_link_condition(self.parent_update(map), self.parent));
            }
            else {
                assert(weak_child_link_condition(map, key));
            };
        };
    }

    pub proof fn lemma_view_update(&self, map: LinkMap)
    requires
        !map.contains_key(self.child),
        self.invariants(map)
    ensures
        view(self.update(map)) == insert_child(view(map), self.parent, self.child)
    {
        self.lemma_view_child_update(map);
        self.lemma_weak_next_update_child(map);
        self.lemma_weak_child_update_child(map);
        self.lemma_view_next_update(self.child_update(map));
        self.lemma_invariants_update_next(self.child_update(map));

        let checkpoint = self.next_update(self.child_update(map));
        assert(view(checkpoint) == view(map).insert(self.child, self.insert_view_node(map)));

        self.lemma_invariants_update_parent(checkpoint);
        assert(weak_next_connected(self.update(map)));

        assert forall |key: CapKey| self.update(map).contains_key(key)
        implies #[trigger] siblings(checkpoint, Some(key)) == siblings(self.update(map), Some(key))
        by {
            lemma_siblings_unchanged(checkpoint, self.update(map), key);
        }

        lemma_siblings_unfold(self.update(map), self.child);
        assert(siblings(self.update(map), Some(self.child)) == view(checkpoint)[self.parent].children.push(self.child));

        assert forall |key: CapKey| self.update(map).contains_key(key) && key != self.parent
        implies #[trigger] view(self.update(map))[key] == view(checkpoint)[key]
        by {
            assert(self.update(map)[key] == checkpoint[key]);
            assert(weak_child_link_condition(checkpoint, key));
        };

        assert(weak_child_link_condition(self.update(map), self.parent));
        let CapNode { generation, children } = view(map)[self.parent];
        let parent_node = CapNode { generation, children: children.push(self.child) };
        let child_node = CapNode { generation: generation + 1, children: Seq::empty() };
        assert(view(self.update(map))[self.parent] == parent_node);

        assert(view(checkpoint) == view(map).insert(self.child, child_node));
        assert(view(self.update(map)) =~= view(checkpoint).insert(self.parent, parent_node));
        assert(insert_child(view(map), self.parent, self.child) == view(map).insert(self.child, child_node).insert(self.parent, parent_node));
    }

}

}
