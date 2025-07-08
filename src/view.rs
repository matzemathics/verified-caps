use vstd::{
    prelude::*,
    seq::{axiom_seq_add_index1, axiom_seq_add_index2, axiom_seq_new_index},
};

use crate::state::{
    back_link_condition, child_link_condition, next_index, next_link_condition,
    weak_next_link_condition, CapKey, LinkMap, LinkedNode, SysState,
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
    generation: nat,
) -> CapMap {
    let parent_node = map[parent];
    map.insert(
        parent,
        CapNode { children: parent_node.children.push(child), ..parent_node },
    ).insert(child, CapNode { generation, children: Seq::empty() })
}

pub open spec fn view<T>(map: LinkMap<T>) -> CapMap {
    map.map_values(|node: (T, LinkedNode)| CapNode {
        generation: node.1.depth,
        children: siblings(map, node.1.child)
    })
}

pub open spec fn siblings<T>(map: LinkMap<T>, link: Option<CapKey>) -> Seq<CapKey>
decreases next_index(map, link)
    when {
        &&& forall |key: CapKey| #[trigger] map.contains_key(key) ==> weak_next_link_condition(map, key)
        &&& link.is_some() ==> map.contains_key(link.unwrap())
    }
{
    if let Some(key) = link {
        siblings(map, map[key].1.next).push(key)
    }
    else {
        Seq::empty()
    }
}

pub open spec fn ith_predecessor<T>(map: LinkMap<T>, from: CapKey, i: int, to: CapKey) -> bool {
    let siblings = siblings(map, Some(from));
    0 <= i < siblings.len() && siblings[siblings.len() - i - 1] == to
}

proof fn lemma_ith_predecessor_univalent<T>(map: LinkMap<T>, from_a: CapKey, from_b: CapKey, i: int, to: CapKey)
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
        assert(siblings(map, map[from_a].1.next) == a);
        assert(a == siblings(map, Some(a.last())));

        let b = siblings(map, Some(from_b)).drop_last();
        assert(b[b.len() - i] == to);
        assert(siblings(map, map[from_b].1.next) == b);
        assert(b == siblings(map, Some(b.last())));

        lemma_ith_predecessor_univalent(map, a.last(), b.last(), i - 1, to);
    }
}

pub open spec fn predecessor<T>(map: LinkMap<T>, node: CapKey, i: int) -> Option<CapKey> {
    if exists |key: CapKey| ith_predecessor(map, key, i, node) {
        Some(choose |key: CapKey| ith_predecessor(map, key, i, node))
    }
    else {
        None
    }
}

proof fn lemma_no_predecessor<T>(map: LinkMap<T>, node: CapKey, i: int, pred: CapKey)
requires
    forall |key: CapKey| #[trigger] map.contains_key(key) ==>
        next_link_condition(SysState::Clean, map, key),
    ith_predecessor(map, pred, i, node),
    map.contains_key(pred),
    map[node].1.first_child,
    i > 0,
ensures false
decreases i
{
    if i == 1 { }
    else {
        let a = siblings(map, Some(pred)).drop_last();
        assert(a[a.len() - i] == node);
        assert(siblings(map, map[pred].1.next) == a);
        assert(a == siblings(map, Some(a.last())));

        lemma_no_predecessor(map, node, i - 1, a.last());
    }
}

proof fn lemma_predecessor_transitive<T>(map: LinkMap<T>, a: CapKey, i: int, b: CapKey, j: int, c: CapKey)
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
        assert(siblings(map, map[a].1.next) == a_prime);
        assert(a_prime == siblings(map, Some(a_prime.last())));

        lemma_predecessor_transitive(map, a_prime.last(), i - 1, b, j, c);
    }
}

pub open spec fn child_of<T>(map: LinkMap<T>, child: CapKey, parent: CapKey) -> bool {
    siblings(map, map[parent].1.child).contains(child)
}

proof fn lemma_child_of_univalent<T>(map: LinkMap<T>, parent_a: CapKey, parent_b: CapKey, child: CapKey)
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
    let a = map[parent_a].1.child.unwrap();
    let index_a = choose |i: int|
        0 <= i < siblings(map, Some(a)).len() && siblings(map, Some(a))[i] == child;
    let step_a = siblings(map, Some(a)).len() - index_a - 1;
    assert(ith_predecessor(map, a, step_a, child));

    let b = map[parent_b].1.child.unwrap();
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

}
