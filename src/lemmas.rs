use vstd::prelude::*;

use crate::{
    state::{
        back_link_condition, child_link_condition, clean_links, next_link_condition, SysState,
    },
    tcb::{
        child_of, connection_condition, decreasing_condition, get_parent, map_connected,
        sibling_of, siblings, transitive_child_of, view, weak_child_connected,
        weak_child_link_condition, weak_next_connected, CapKey, CapMap, LinkMap, Next
    },
};

verus! {

pub proof fn lemma_siblings_contained(map: LinkMap, link: Option<CapKey>, key: CapKey)
    requires
        weak_next_connected(map),
        link.is_some() ==> map.contains_key(link.unwrap()),
        siblings(map, link).contains(key),
    ensures
        map.contains_key(key),
    decreases map[link.unwrap()].index,
{
    if let Some(current) = link {
        lemma_siblings_unfold(map, current);

        if current != key {
            assert(siblings(map, map[current].next).contains(key));
            assert(decreasing_condition::<Next>(map, current));
            lemma_siblings_contained(map, map[current].next, key);
        }
    }
}

pub proof fn lemma_siblings_none_empty(map: LinkMap)
    ensures
        siblings(map, None) == Seq::<CapKey>::empty(),
{
    assert(siblings(map, None) == Seq::<CapKey>::empty()) by (compute_only);
}

pub proof fn lemma_siblings_unfold(map: LinkMap, key: CapKey)
    requires
        weak_next_connected(map),
        map.contains_key(key),
    ensures
        siblings(map, Some(key)) == siblings(map, map[key].next).push(key),
{
    assert(decreasing_condition::<Next>(map, key));
}

pub proof fn lemma_siblings_take_n(map: LinkMap, key: CapKey, n: int)
    requires
        map.contains_key(key),
        weak_next_connected(map),
        0 <= n < siblings(map, Some(key)).len(),
    ensures
        map.contains_key(siblings(map, Some(key))[n]),
        siblings(map, Some(key)).take(n + 1) == siblings(map, Some(siblings(map, Some(key))[n])),
    decreases siblings(map, Some(key)).len() - n,
{
    if n == siblings(map, Some(key)).len() - 1 {
        lemma_siblings_unfold(map, key);
        assert(siblings(map, Some(key))[n] == key);
        assert(siblings(map, Some(key)).take(n + 1) == siblings(map, Some(key)));
    } else {
        lemma_siblings_take_n(map, key, n + 1);
        let pred = siblings(map, Some(key))[n + 1];
        assert(siblings(map, Some(key)).take(n + 1) == siblings(map, Some(pred)).drop_last());
        lemma_siblings_unfold(map, pred);
        assert(decreasing_condition::<Next>(map, pred));
        lemma_siblings_unfold(map, map[pred].next.unwrap());
        assert(siblings(map, Some(pred)).drop_last().last() == map[pred].next.unwrap());
        assert(siblings(map, Some(key)).take(n + 1) == siblings(map, map[pred].next))
    }
}

pub proof fn lemma_siblings_unchanged(map_a: LinkMap, map_b: LinkMap, key: CapKey)
    requires
        forall|key: CapKey| #[trigger] map_a[key].next == map_b[key].next,
        weak_next_connected(map_a),
        weak_next_connected(map_b),
        map_a.contains_key(key),
        map_b.contains_key(key),
    ensures
        siblings(map_a, Some(key)) == siblings(map_b, Some(key)),
    decreases map_a[key].index,
{
    lemma_siblings_unfold(map_a, key);
    lemma_siblings_unfold(map_b, key);

    if let Some(next) = map_a[key].next {
        assert(decreasing_condition::<Next>(map_a, key));
        assert(decreasing_condition::<Next>(map_b, key));
        lemma_siblings_unchanged(map_a, map_b, next);
    } else {
        lemma_siblings_none_empty(map_a);
        lemma_siblings_none_empty(map_b);
    }
}

pub proof fn lemma_siblings_unchanged_after(pre: LinkMap, post: LinkMap, key: CapKey)
    requires
        forall|sib: CapKey| #[trigger]
            siblings(pre, Some(key)).contains(sib) ==> pre[sib].next == post[sib].next,
        weak_next_connected(pre),
        weak_next_connected(post),
        pre.contains_key(key),
        post.contains_key(key),
    ensures
        siblings(pre, Some(key)) == siblings(post, Some(key)),
    decreases pre[key].index,
{
    assert(siblings(pre, Some(key)).last() == key);
    assert(siblings(pre, Some(key)).contains(key));
    assert(post[key].next == pre[key].next);
    assert(decreasing_condition::<Next>(post, key));

    if let Some(next) = pre[key].next {
        assert(decreasing_condition::<Next>(pre, key));
        lemma_siblings_unfold(pre, next);
        lemma_siblings_unfold(post, next);
        assert(decreasing_condition::<Next>(pre, next));

        assert forall|sib: CapKey| #[trigger]
            siblings(pre, Some(next)).contains(sib) implies pre[sib].next == post[sib].next by {
            lemma_siblings_contained(pre, Some(next), sib);
            assert(siblings(pre, Some(next)) == siblings(pre, pre[next].next).push(next));
            if siblings(pre, pre[key].next).contains(sib) {
                let index = choose|i: int|
                    0 <= i < siblings(pre, pre[key].next).len() && siblings(pre, pre[key].next)[i]
                        == sib;
                assert(siblings(pre, Some(key)) == siblings(pre, pre[key].next).push(key));
                assert(siblings(pre, Some(key))[index] == sib);
                assert(siblings(pre, Some(key)).contains(sib));
            } else {
                assert(sib != next);
                assert(!siblings(pre, pre[next].next).push(next).contains(sib));
                assert(false);
            }
        };

        lemma_siblings_unchanged_after(pre, post, next);
    } else {
        lemma_siblings_unfold(pre, key);
        lemma_siblings_unfold(post, key);
        lemma_siblings_none_empty(pre);
        lemma_siblings_none_empty(post);
    }
}

pub proof fn lemma_siblings_decreasing(map: LinkMap, key: CapKey, sib: CapKey)
    requires
        weak_next_connected(map),
        map.contains_key(key),
        siblings(map, map[key].next).contains(sib),
    ensures
        map[sib].index < map[key].index,
    decreases map[key].index,
{
    if let Some(next) = map[key].next {
        assert(decreasing_condition::<Next>(map, key));
        lemma_siblings_unfold(map, key);
        lemma_siblings_unfold(map, next);

        if next != sib {
            lemma_siblings_decreasing(map, next, sib);
        }
    } else {
        lemma_siblings_none_empty(map);
    }
}

pub proof fn lemma_siblings_no_loop(map: LinkMap, key: CapKey)
    requires
        weak_next_connected(map),
        map.contains_key(key),
    ensures
        !siblings(map, map[key].next).contains(key),
{
    if siblings(map, map[key].next).contains(key) {
        lemma_siblings_decreasing(map, key, key)
    }
}

pub open spec fn ith_predecessor(map: LinkMap, from: CapKey, i: int, to: CapKey) -> bool {
    let siblings = siblings(map, Some(from));
    0 <= i < siblings.len() && siblings[siblings.len() - i - 1] == to
}

pub proof fn lemma_ith_predecessor_univalent(
    map: LinkMap,
    from_a: CapKey,
    from_b: CapKey,
    i: int,
    to: CapKey,
)
    requires
        forall|key: CapKey| #[trigger]
            map.contains_key(key) ==> next_link_condition(SysState::Clean, map, key),
        ith_predecessor(map, from_a, i, to),
        ith_predecessor(map, from_b, i, to),
        map.contains_key(from_a),
        map.contains_key(from_b),
    ensures
        from_a == from_b,
    decreases i,
{
    if i == 0 {
    } else {
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
    if exists|key: CapKey| ith_predecessor(map, key, i, node) {
        Some(choose|key: CapKey| ith_predecessor(map, key, i, node))
    } else {
        None
    }
}

pub proof fn lemma_no_predecessor(map: LinkMap, node: CapKey, i: int, pred: CapKey)
    requires
        forall|key: CapKey| #[trigger]
            map.contains_key(key) ==> next_link_condition(SysState::Clean, map, key),
        ith_predecessor(map, pred, i, node),
        map.contains_key(pred),
        map[node].first_child,
        i > 0,
    ensures
        false,
    decreases i,
{
    if i == 1 {
        lemma_siblings_unfold(map, pred);
        assert(map[pred].next == Some(node));
    } else {
        let a = siblings(map, Some(pred)).drop_last();
        assert(a[a.len() - i] == node);
        assert(siblings(map, map[pred].next) == a);
        assert(a == siblings(map, Some(a.last())));

        lemma_no_predecessor(map, node, i - 1, a.last());
    }
}

pub proof fn lemma_predecessor_transitive(
    map: LinkMap,
    a: CapKey,
    i: int,
    b: CapKey,
    j: int,
    c: CapKey,
)
    requires
        forall|key: CapKey| #[trigger]
            map.contains_key(key) ==> next_link_condition(SysState::Clean, map, key),
        i >= 0,
        ith_predecessor(map, a, i + j, c),
        ith_predecessor(map, b, j, c),
        map.contains_key(a),
        map.contains_key(b),
    ensures
        ith_predecessor(map, a, i, b),
    decreases i,
{
    if i == 0 {
        lemma_ith_predecessor_univalent(map, a, b, j, c);
    } else {
        let a_prime = siblings(map, Some(a)).drop_last();
        assert(a_prime[a_prime.len() - (i + j)] == c);
        assert(siblings(map, map[a].next) == a_prime);
        assert(a_prime == siblings(map, Some(a_prime.last())));

        lemma_predecessor_transitive(map, a_prime.last(), i - 1, b, j, c);
    }
}

pub proof fn lemma_child_of_first_child(map: LinkMap, parent: CapKey)
    requires
        weak_next_connected(map),
        weak_child_connected(map),
        map.contains_key(parent),
        map[parent].child.is_some(),
    ensures
        child_of(map, map[parent].child.unwrap(), parent),
{
    assert(weak_child_link_condition(map, parent));
    lemma_siblings_unfold(map, map[parent].child.unwrap());
    assert(siblings(map, map[parent].child).last() == map[parent].child.unwrap());
}

pub proof fn lemma_siblings_depth(map: LinkMap, a: CapKey, b: CapKey)
    requires
        siblings(map, Some(a)).contains(b),
        weak_next_connected(map),
        map.contains_key(a),
    ensures
        map[a].depth == map[b].depth,
    decreases map[a].index,
{
    lemma_siblings_unfold(map, a);

    if a == b {
    } else {
        if let Some(next) = map[a].next {
            assert(decreasing_condition::<Next>(map, a));
            lemma_siblings_depth(map, next, b);
        } else {
            lemma_siblings_none_empty(map);
        }
    }
}

pub proof fn lemma_child_of_depth(map: LinkMap, child: CapKey, parent: CapKey)
    requires
        child_of(map, child, parent),
        weak_child_connected(map),
        weak_next_connected(map),
        map.contains_key(parent),
    ensures
        map[child].depth == map[parent].depth + 1,
{
    if let Some(first_child) = map[parent].child {
        assert(weak_child_link_condition(map, parent));
        lemma_siblings_depth(map, first_child, child);
    } else {
        lemma_siblings_none_empty(map)
    }
}

pub proof fn lemma_child_of_univalent(
    map: LinkMap,
    parent_a: CapKey,
    parent_b: CapKey,
    child: CapKey,
)
    requires
        clean_links(map),
        child_of(map, child, parent_a),
        child_of(map, child, parent_b),
        map.contains_key(parent_a),
        map.contains_key(parent_b),
    ensures
        parent_a == parent_b,
{
    assert(next_link_condition(SysState::Clean, map, parent_a));
    let a = map[parent_a].child.unwrap();
    let index_a = choose|i: int|
        0 <= i < siblings(map, Some(a)).len() && siblings(map, Some(a))[i] == child;
    let step_a = siblings(map, Some(a)).len() - index_a - 1;
    assert(ith_predecessor(map, a, step_a, child));

    let b = map[parent_b].child.unwrap();
    let index_b = choose|i: int|
        0 <= i < siblings(map, Some(b)).len() && siblings(map, Some(b))[i] == child;
    let step_b = siblings(map, Some(b)).len() - index_b - 1;
    assert(ith_predecessor(map, b, step_b, child));

    if step_a == step_b {
        lemma_ith_predecessor_univalent(map, a, b, step_a, child);
    } else if step_a > step_b {
        lemma_predecessor_transitive(map, a, step_a - step_b, b, step_b, child);
        lemma_no_predecessor(map, b, step_a - step_b, a);
    } else {
        assert(step_b > step_a);
        lemma_predecessor_transitive(map, b, step_b - step_a, a, step_a, child);
        lemma_no_predecessor(map, a, step_b - step_a, b);
    }
}

pub proof fn lemma_parent_child(map: LinkMap, parent: CapKey, child: CapKey)
    requires
        map.contains_key(parent),
        forall|key: CapKey| #[trigger]
            map.contains_key(key) ==> {
                &&& next_link_condition(SysState::Clean, map, key)
                &&& back_link_condition(SysState::Clean, map, key)
                &&& child_link_condition(SysState::Clean, map, key)
            },
    ensures
        child_of(map, child, parent) <==> get_parent(map, child) == Some(parent),
{
    if let Some(alt_parent) = get_parent(map, child) {
        if child_of(map, child, parent) {
            lemma_child_of_univalent(map, alt_parent, parent, child);
        }
    }
}

pub proof fn lemma_sibling_of_next(map: LinkMap, key: CapKey)
    requires
        clean_links(map),
        map.contains_key(key),
        map[key].next.is_some(),
    ensures
        sibling_of(map, key, map[key].next.unwrap()),
{
    let next = map[key].next.unwrap();
    lemma_siblings_unfold(map, key);
    assert(ith_predecessor(map, key, 1, next));

    if let Some(parent) = get_parent(map, key) {
        assert(child_of(map, key, parent));
        let child = map[parent].child.unwrap();
        let index = siblings(map, Some(child)).index_of(key);

        lemma_siblings_take_n(map, child, index);
        assert(child_of(map, next, parent));

        lemma_child_of_univalent(map, parent, get_parent(map, next).unwrap(), next);
    } else if let Some(alt_parent) = get_parent(map, next) {
        let child = map[alt_parent].child.unwrap();
        let index = siblings(map, Some(child)).index_of(next);

        let step = siblings(map, Some(child)).len() - index - 1;
        assert(ith_predecessor(map, child, step, next));

        lemma_predecessor_transitive(map, child, step - 1, key, 1, next);
    }
}

pub proof fn lemma_siblings_unchanged_local(
    pre: LinkMap,
    post: LinkMap,
    changed: CapKey,
    key: CapKey,
)
    requires
        forall|key: CapKey|
            #![trigger sibling_of(pre, changed, key)]
            pre.contains_key(key) && !sibling_of(pre, changed, key) ==> pre[key].next
                == post[key].next,
        !sibling_of(pre, changed, key),
        pre.contains_key(key),
        post.contains_key(key),
        weak_next_connected(post),
        clean_links(pre),
    ensures
        siblings(pre, Some(key)) == siblings(post, Some(key)),
    decreases pre[key].index,
{
    assert(next_link_condition(SysState::Clean, pre, key));
    lemma_siblings_unfold(pre, key);
    lemma_siblings_unfold(post, key);

    if let Some(next) = pre[key].next {
        lemma_sibling_of_next(pre, key);
        assert(decreasing_condition::<Next>(post, key));

        lemma_siblings_unchanged_local(pre, post, changed, next);
        assert(siblings(pre, Some(key)) == siblings(post, Some(key)));
    } else {
        lemma_siblings_none_empty(pre);
        lemma_siblings_none_empty(post);
    }
}

pub proof fn lemma_sib_back_some(map: LinkMap, start: CapKey, child: CapKey)
    requires
        clean_links(map),
        map.contains_key(start),
        map.contains_key(child),
        siblings(map, Some(start)).contains(child),
        start != child,
    ensures
        map[child].back.is_some(),
    decreases map[start].index,
{
    lemma_siblings_unfold(map, start);
    assert(next_link_condition(SysState::Clean, map, start));

    if let Some(next) = map[start].next {
        if next != child {
            lemma_sib_back_some(map, next, child);
        }
    } else {
        lemma_siblings_none_empty(map);
    }
}

pub proof fn lemma_view_well_formed(map: LinkMap)
    requires
        weak_next_connected(map),
        weak_child_connected(map),
    ensures
        map_connected(view(map)),
{
    assert forall|parent: CapKey, child: CapKey| connection_condition(view(map), child, parent) by {
        if view(map).contains_key(parent) && view(map)[parent].children.contains(child) {
            assert(child_of(map, child, parent));
            assert(weak_child_link_condition(map, parent));
            lemma_child_of_depth(map, child, parent);
            lemma_siblings_contained(map, map[parent].child, child);
        }
    }
}

pub proof fn lemma_transitive_children_empty(map: CapMap, parent: CapKey, child: CapKey)
    requires
        map.contains_key(parent),
        map_connected(map),
        transitive_child_of(map, child, parent),
        map[parent].children.len() == 0,
    ensures
        child == parent,
    decreases map[child].generation,
{
    if child != parent {
        let intermediate = choose|key: CapKey|
            {
                &&& map.contains_key(key)
                &&& #[trigger] map[key].children.contains(child)
                &&& transitive_child_of(map, key, parent)
            };

        assert(connection_condition(map, child, intermediate));
        lemma_transitive_children_empty(map, parent, intermediate);
    }
}

} // verus!
