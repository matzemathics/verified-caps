use vstd::prelude::*;

use crate::state::{
    back_link_condition, child_link_condition, clean_links, next_index, next_link_condition,
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

proof fn lemma_siblings_contained(map: LinkMap, link: Option<CapKey>, key: CapKey)
requires
    weak_next_connected(map),
    link.is_some() ==> map.contains_key(link.unwrap()),
    siblings(map, link).contains(key)
ensures
    map.contains_key(key)
decreases
    map[link.unwrap()].index
{
    if let Some(current) = link {
        lemma_siblings_unfold(map, current);

        if current != key {
            assert(siblings(map, map[current].next).contains(key));
            assert(weak_next_link_condition(map, current));
            lemma_siblings_contained(map, map[current].next, key);
        }
    }
}

proof fn lemma_siblings_none_empty(map: LinkMap)
ensures siblings(map, None) == Seq::<CapKey>::empty()
{
    assert(siblings(map, None) == Seq::<CapKey>::empty()) by (compute_only);
}

pub proof fn lemma_siblings_unfold(map: LinkMap, key: CapKey)
requires
    weak_next_connected(map),
    map.contains_key(key)
ensures siblings(map, Some(key)) == siblings(map, map[key].next).push(key)
{
    assert(weak_next_link_condition(map, key));
}

pub proof fn lemma_siblings_take_n(map: LinkMap, key: CapKey, n: int)
requires
    map.contains_key(key),
    weak_next_connected(map),
    0 <= n < siblings(map, Some(key)).len(),
ensures
    map.contains_key(siblings(map, Some(key))[n]),
    siblings(map, Some(key)).take(n + 1) == siblings(map, Some(siblings(map, Some(key))[n]))
decreases
    siblings(map, Some(key)).len() - n
{
    if n == siblings(map, Some(key)).len() - 1 {
        lemma_siblings_unfold(map, key);
        assert(siblings(map, Some(key))[n] == key);
        assert(siblings(map, Some(key)).take(n + 1) == siblings(map, Some(key)));
    }
    else {
        lemma_siblings_take_n(map, key, n + 1);
        let pred = siblings(map, Some(key))[n + 1];
        assert(siblings(map, Some(key)).take(n + 1) == siblings(map, Some(pred)).drop_last());
        lemma_siblings_unfold(map, pred);
        assert(weak_next_link_condition(map, pred));
        lemma_siblings_unfold(map, map[pred].next.unwrap());
        assert(siblings(map, Some(pred)).drop_last().last() == map[pred].next.unwrap());
        assert(siblings(map, Some(key)).take(n + 1) == siblings(map, map[pred].next))
    }
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

proof fn lemma_siblings_unchanged_after(pre: LinkMap, post: LinkMap, key: CapKey)
requires
    forall |sib: CapKey| #[trigger] siblings(pre, Some(key)).contains(sib) ==> pre[sib].next == post[sib].next,
    weak_next_connected(pre),
    weak_next_connected(post),
    pre.contains_key(key),
    post.contains_key(key)
ensures
    siblings(pre, Some(key)) == siblings(post, Some(key))
decreases
    pre[key].index
{
    assert(siblings(pre, Some(key)).last() == key);
    assert(siblings(pre, Some(key)).contains(key));
    assert(post[key].next == pre[key].next);
    assert(weak_next_link_condition(post, key));

    if let Some(next) = pre[key].next {
        assert(weak_next_link_condition(pre, key));
        lemma_siblings_unfold(pre, next);
        lemma_siblings_unfold(post, next);
        assert(weak_next_link_condition(pre, next));

        assert forall |sib: CapKey| #[trigger] siblings(pre, Some(next)).contains(sib)
        implies pre[sib].next == post[sib].next
        by {
            lemma_siblings_contained(pre, Some(next), sib);
            assert(siblings(pre, Some(next)) == siblings(pre, pre[next].next).push(next));
            if siblings(pre, pre[key].next).contains(sib) {
                let index = choose |i: int| 0 <= i < siblings(pre, pre[key].next).len() &&
                    siblings(pre, pre[key].next)[i] == sib;
                assert(siblings(pre, Some(key)) == siblings(pre, pre[key].next).push(key));
                assert(siblings(pre, Some(key))[index] == sib);
                assert(siblings(pre, Some(key)).contains(sib));
            }
            else {
                assert(sib != next);
                assert(!siblings(pre, pre[next].next).push(next).contains(sib));
                assert(false);
            }
        };

        lemma_siblings_unchanged_after(pre, post, next);
    }
    else {
        lemma_siblings_unfold(pre, key);
        lemma_siblings_unfold(post, key);
        lemma_siblings_none_empty(pre);
        lemma_siblings_none_empty(post);
    }
}

proof fn lemma_siblings_decreasing(map: LinkMap, key: CapKey, sib: CapKey)
requires
    weak_next_connected(map),
    map.contains_key(key),
    siblings(map, map[key].next).contains(sib),
ensures
    map[sib].index < map[key].index
decreases
    map[key].index
{
    if let Some(next) = map[key].next {
        assert(weak_next_link_condition(map, key));
        lemma_siblings_unfold(map, key);
        lemma_siblings_unfold(map, next);

        if next != sib { lemma_siblings_decreasing(map, next, sib); }
    }
    else {
        lemma_siblings_none_empty(map);
    }
}

proof fn lemma_siblings_no_loop(map: LinkMap, key: CapKey)
requires
    weak_next_connected(map),
    map.contains_key(key)
ensures
    !siblings(map, map[key].next).contains(key)
{
    if siblings(map, map[key].next).contains(key) {
        lemma_siblings_decreasing(map, key, key)
    }
}

proof fn lemma_siblings_jump(pre: LinkMap, post: LinkMap, start: CapKey, jump: CapKey)
requires
    weak_next_connected(pre),
    weak_next_connected(post),
    forall |key: CapKey| post.contains_key(key) && key != jump ==> #[trigger] post[key].next == pre[key].next,
    pre.contains_key(jump),
    pre.contains_key(start),
    pre[jump].next.is_some(),
    post.dom() == pre.dom().remove(pre[jump].next.unwrap()),

    post[jump].next == pre[pre[jump].next.unwrap()].next,
    siblings(pre, Some(start)).contains(jump),
ensures
    siblings(post, Some(start)) == siblings(pre, Some(start)).remove_value(pre[jump].next.unwrap())
decreases
    pre[start].index
{
    let removed = pre[jump].next.unwrap();

    if start == jump {
        if let Some(next) = post[jump].next {
            assert(weak_next_link_condition(post, jump));
            assert(weak_next_link_condition(pre, jump));
            assert(weak_next_link_condition(pre, pre[jump].next.unwrap()));

            assert forall |after: CapKey| #[trigger] siblings(pre, Some(next)).contains(after)
            implies post[after].next == pre[after].next
            by {
                lemma_siblings_contained(pre, Some(next), after);
                lemma_siblings_decreasing(pre, removed, after);
            };

            lemma_siblings_unchanged_after(pre, post, next);
        }

        let critical = siblings(pre,post[jump].next);
        assert(critical == siblings(post, post[jump].next));

        if let Some(i) = critical.index_of_first(removed) {
            siblings(pre, pre[removed].next).index_of_first_ensures(removed);
            assert(siblings(pre, pre[removed].next)[i] == removed);
            assert(siblings(pre, pre[removed].next).contains(removed));
            lemma_siblings_decreasing(pre, removed, removed);
            assert(false);
        }

        lemma_siblings_unfold(pre, jump);
        lemma_siblings_unfold(pre, removed);
        assert(siblings(pre, Some(jump)) == siblings(pre,post[jump].next).push(removed).push(jump));

        assert(critical.index_of_first(removed).is_none());

        assert(critical.push(removed).push(jump).index_of_first(removed) == Some(critical.len() as int)) by {
            critical.push(removed).push(jump).index_of_first_ensures(removed);
            assert(critical.push(removed).push(jump)[critical.len() as int] == removed);
            let i = critical.push(removed).push(jump).index_of_first(removed).unwrap();
            if i < critical.len() as int {
                assert(critical[i] == removed);
                assert(critical.contains(removed));
                critical.index_of_first_ensures(removed);
                assert(critical.index_of_first(removed).is_some());
                assert(false);
            }
        };

        assert(critical.push(removed).push(jump).remove_value(removed) == critical.push(jump));
    }
    else {
        assert(weak_next_link_condition(pre, jump));
        lemma_siblings_unfold(pre, start);
        lemma_siblings_decreasing(pre, start, jump);
        assert(removed != start);
        lemma_siblings_unfold(post, start);

        assert(weak_next_link_condition(pre, start));
        assert(weak_next_link_condition(post, start));
        let next = pre[start].next.unwrap();
        lemma_siblings_jump(pre, post, next, jump);

        assert(siblings(post, Some(next)) ==
            siblings(pre, Some(next)).remove_value(pre[jump].next.unwrap()));

        assert(siblings(post, Some(start)) == siblings(post, Some(next)).push(start));
        assert(siblings(pre, Some(start)) == siblings(pre, Some(next)).push(start));

        siblings(pre, Some(next)).push(start).index_of_first_ensures(removed);

        let critical = siblings(pre, Some(next));

        if critical.index_of_first(removed) != critical.push(start).index_of_first(removed) {
            critical.index_of_first_ensures(removed);
            critical.push(start).index_of_first_ensures(removed);
            let a = critical.index_of_first(removed).unwrap();
            assert(critical.push(start)[a] == removed);
            assert(false);
        }

        assert(siblings(post, Some(start)) == siblings(pre, Some(start)).remove_value(removed));
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

proof fn lemma_child_of_first_child(map: LinkMap, parent: CapKey)
requires
    weak_next_connected(map),
    weak_child_connected(map),
    map.contains_key(parent),
    map[parent].child.is_some()
ensures
    child_of(map, map[parent].child.unwrap(), parent)
{
    assert(weak_child_link_condition(map, parent));
    lemma_siblings_unfold(map, map[parent].child.unwrap());
    assert(siblings(map, map[parent].child).last() == map[parent].child.unwrap());
}

proof fn lemma_siblings_depth(map: LinkMap, a: CapKey, b: CapKey)
requires
    siblings(map, Some(a)).contains(b),
    weak_next_connected(map),
    map.contains_key(a)
ensures map[a].depth == map[b].depth
decreases map[a].index
{
    lemma_siblings_unfold(map, a);

    if a == b { }
    else {
        if let Some(next) = map[a].next {
            assert(weak_next_link_condition(map, a));
            lemma_siblings_depth(map, next, b);
        }
        else {
            lemma_siblings_none_empty(map);
        }
    }
}

proof fn lemma_child_of_depth(map: LinkMap, child: CapKey, parent: CapKey)
requires
    child_of(map, child, parent),
    weak_child_connected(map),
    weak_next_connected(map),
    map.contains_key(parent),
ensures
    map[child].depth == map[parent].depth + 1
{
    if let Some(first_child) = map[parent].child {
        assert(weak_child_link_condition(map, parent));
        lemma_siblings_depth(map, first_child, child);
    }
    else {
        lemma_siblings_none_empty(map)
    }
}

#[via_fn]
proof fn transitive_child_of_decreases(map: LinkMap, child: CapKey, parent: CapKey)
{
    assert forall |node: CapKey| #[trigger] child_of(map, child, node)
    implies map[child].depth > map[node].depth
    by {
        lemma_child_of_depth(map, child, node);
    }
}

pub open spec fn transitive_child_of(map: LinkMap, child: CapKey, parent: CapKey) -> bool
decreases map[child].depth
when weak_child_connected(map) && weak_next_connected(map) && map.contains_key(parent)
via transitive_child_of_decreases
{
    if child == parent { true }
    else {
        exists |node: CapKey| child_of(map, child, node) && transitive_child_of(map, node, parent)
    }
}

proof fn lemma_child_of_univalent(map: LinkMap, parent_a: CapKey, parent_b: CapKey, child: CapKey)
requires
    clean_links(map),
    child_of(map, child, parent_a),
    child_of(map, child, parent_b),
    map.contains_key(parent_a),
    map.contains_key(parent_b),
ensures
    parent_a == parent_b
{
    assert(next_link_condition(SysState::Clean, map, parent_a));
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

pub open spec fn get_parent(map: LinkMap, child: CapKey) -> Option<CapKey> {
    if exists |parent: CapKey| map.contains_key(parent) && child_of(map, child, parent) {
        Some(choose |parent: CapKey| map.contains_key(parent) && child_of(map, child, parent))
    }
    else {
        None
    }
}

pub proof fn lemma_parent_child(map: LinkMap, parent: CapKey, child: CapKey)
requires
    map.contains_key(parent),
    forall |key: CapKey| #[trigger] map.contains_key(key) ==> {
        &&& next_link_condition(SysState::Clean, map, key)
        &&& back_link_condition(SysState::Clean, map, key)
        &&& child_link_condition(SysState::Clean, map, key)
    },
ensures
    child_of(map, child, parent) <==> get_parent(map, child) == Some(parent)
{
    if let Some(alt_parent) = get_parent(map, child) {
        if child_of(map, child, parent) {
            lemma_child_of_univalent(map, alt_parent, parent, child);
        }
    }
}

pub open spec fn revoke_single_view(before: LinkMap, removed: CapKey) -> CapMap {
    if let Some(parent) = get_parent(before, removed) {
        let parent_node = view(before)[parent];
        let parent_node = CapNode { children: parent_node.children.remove_value(removed), ..parent_node };
        view(before).insert(parent, parent_node)
    }
    else {
        view(before)
    }
}

pub open spec fn close_to(map: LinkMap, target: CapKey, key: CapKey) -> bool {
    key == target || map[target].next == Some(key) || map[target].back == Some(key) || map[target].child == Some(key)
}

pub open spec fn revoke_back_update(pre: LinkMap, post: LinkMap, removed: CapKey) -> bool {
    pre[removed].back == Option::<CapKey>::None || {
        &&& {
            ||| {
                &&& pre[removed].first_child
                &&& post[pre[removed].back.unwrap()].child == pre[removed].next
                &&& post[pre[removed].back.unwrap()].next == pre[pre[removed].back.unwrap()].next
            }
            ||| {
                &&& !pre[removed].first_child
                &&& post[pre[removed].back.unwrap()].next == pre[removed].next
                &&& post[pre[removed].back.unwrap()].child == pre[pre[removed].back.unwrap()].child
            }
        }

        &&& post[pre[removed].back.unwrap()].back == pre[pre[removed].back.unwrap()].back
        &&& post[pre[removed].back.unwrap()].first_child == pre[pre[removed].back.unwrap()].first_child
        &&& post[pre[removed].back.unwrap()].depth == pre[pre[removed].back.unwrap()].depth
    }
}

pub open spec fn revoke_next_update(pre: LinkMap, post: LinkMap, removed: CapKey) -> bool {
    pre[removed].next == Option::<CapKey>::None || {
        &&& post[pre[removed].next.unwrap()].back == pre[removed].back
        &&& post[pre[removed].next.unwrap()].first_child == pre[removed].first_child

        &&& post[pre[removed].next.unwrap()].next == pre[pre[removed].next.unwrap()].next
        &&& post[pre[removed].next.unwrap()].child == pre[pre[removed].next.unwrap()].child
        &&& post[pre[removed].next.unwrap()].depth == pre[pre[removed].next.unwrap()].depth
    }
}

pub open spec fn sibling_of(map: LinkMap, a: CapKey, b: CapKey) -> bool {
    get_parent(map, a) == get_parent(map, b)
}

proof fn lemma_sibling_of_next(map: LinkMap, key: CapKey)
requires
    clean_links(map),
    map.contains_key(key),
    map[key].next.is_some()
ensures
    sibling_of(map, key, map[key].next.unwrap())
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
    }
    else if let Some(alt_parent) = get_parent(map, next) {
        let child = map[alt_parent].child.unwrap();
        let index = siblings(map, Some(child)).index_of(next);

        let step = siblings(map, Some(child)).len() - index - 1;
        assert(ith_predecessor(map, child, step, next));

        lemma_predecessor_transitive(map, child, step - 1, key, 1, next);
    }
}

proof fn lemma_siblings_unchanged_local(pre: LinkMap, post: LinkMap, changed: CapKey, key: CapKey)
requires
    forall |key: CapKey| #![trigger sibling_of(pre, changed, key)]
    pre.contains_key(key) && !sibling_of(pre, changed, key) ==> pre[key].next == post[key].next,
    !sibling_of(pre, changed, key),
    pre.contains_key(key),
    post.contains_key(key),
    weak_next_connected(post),
    clean_links(pre)
ensures
    siblings(pre, Some(key)) == siblings(post, Some(key))
decreases pre[key].index
{
    assert(next_link_condition(SysState::Clean, pre, key));
    lemma_siblings_unfold(pre, key);
    lemma_siblings_unfold(post, key);

    if let Some(next) = pre[key].next {
        lemma_sibling_of_next(pre, key);
        assert(weak_next_link_condition(post, key));

        lemma_siblings_unchanged_local(pre, post, changed, next);
        assert(siblings(pre, Some(key)) == siblings(post, Some(key)));
    }
    else {
        lemma_siblings_none_empty(pre);
        lemma_siblings_none_empty(post);
    }
}

proof fn lemma_sib_back_some(map: LinkMap, start: CapKey, child: CapKey)
requires
    clean_links(map),
    map.contains_key(start),
    map.contains_key(child),
    siblings(map, Some(start)).contains(child),
    start != child,
ensures
    map[child].back.is_some()
decreases
    map[start].index
{
    lemma_siblings_unfold(map, start);
    assert(next_link_condition(SysState::Clean, map, start));

    if let Some(next) = map[start].next {
        if next != child {
            lemma_sib_back_some(map, next, child);
        }
    }
    else {
        lemma_siblings_none_empty(map);
    }
}

pub proof fn lemma_revoke_link_view(pre: LinkMap, post: LinkMap, removed: CapKey)
requires
    post.dom() == pre.dom().remove(removed),
    clean_links(pre),
    weak_next_connected(post),
    pre[removed].child.is_none(),
    forall |key: CapKey| pre.contains_key(key) && !close_to(pre, removed, key) ==> #[trigger] pre[key] == post[key],
    revoke_back_update(pre, post, removed),
    revoke_next_update(pre, post, removed),
    pre.contains_key(removed),
ensures
    view(post) == revoke_single_view(pre, removed).remove(removed)
{
    assert forall |key: CapKey| post.contains_key(key) && pre[removed].back != Some(key)
    implies #[trigger] pre[key].next == post[key].next
    by {
        if Some(key) == pre[removed].next { }
        else if Some(key) == pre[removed].child { }
        else { }
    };

    assert forall |key: CapKey| pre.contains_key(key) && !sibling_of(pre, removed, key)
    implies #[trigger] pre[key].next == post[key].next
    by {
        if Some(key) == pre[removed].back {
            if pre[removed].first_child {}
            else {
                assert(back_link_condition(SysState::Clean, pre, removed));
                lemma_sibling_of_next(pre, key);
            }
        }
        else { }
    };

    assert forall |parent: CapKey| post.contains_key(parent) && !child_of(pre, removed, parent)
    implies #[trigger] view(post)[parent] == view(pre)[parent]
    by {
        assert(pre[parent].depth == post[parent].depth);
        assert(get_parent(pre, removed) != Some(parent));

        if let Some(child) = pre[parent].child {
            assert(child_of(pre, child, parent)) by {
                lemma_siblings_unfold(pre, child);
                assert(siblings(pre, pre[parent].child).last() == child);
            };

            lemma_parent_child(pre, parent, child);
            lemma_siblings_unchanged_local(pre, post, removed, child);
        }
        else {
            lemma_siblings_none_empty(pre);
            lemma_siblings_none_empty(post);
        }
    };

    if let Some(parent) = get_parent(pre, removed) {
        if pre[removed].back == Some(parent) {
            assert(back_link_condition(SysState::Clean, pre, removed));
            lemma_child_of_depth(pre, removed, parent);
            assert(pre[removed].first_child);

            assert(post[parent].child == pre[removed].next);
            lemma_siblings_unfold(pre, removed);
            lemma_siblings_no_loop(pre, removed);
            let critical = siblings(pre, pre[removed].next);
            critical.index_of_first_ensures(removed);
            assert(critical.index_of_first(removed).is_none());

            assert(siblings(pre, pre[removed].next).remove_value(removed) == siblings(pre, pre[removed].next));

            critical.push(removed).index_of_first_ensures(removed);
            assert(critical.push(removed).remove_value(removed) == siblings(pre, pre[removed].next));

            assert(view(pre)[parent].children.remove_value(removed) == critical);
            assert(view(post)[parent].children == siblings(post, post[parent].child));

            assert forall |sib: CapKey| #[trigger] siblings(pre, pre[removed].next).contains(sib)
            implies post[sib].next == pre[sib].next
            by {
                lemma_siblings_contained(pre, pre[removed].next, sib);

                if sib == parent { }
                else if pre[removed].next == Some(sib) { }
                else if sib == removed { }
                else { }
            };

            assert(siblings(pre, pre[removed].next) == siblings(post, pre[removed].next)) by {
                if let Some(next) = pre[removed].next {
                    lemma_siblings_unchanged_after(pre, post, next);
                }
                else {
                    lemma_siblings_none_empty(pre);
                    lemma_siblings_none_empty(post);
                }
            };

            assert(view(post)[parent] == revoke_single_view(pre, removed)[parent]);
        }
        else {
            assert(back_link_condition(SysState::Clean, pre, removed));

            if let Some(back) = pre[removed].back {
                lemma_parent_child(pre, back, removed);
                if pre[removed].first_child {
                    lemma_child_of_first_child(pre, back);
                    assert(child_of(pre, removed, back));
                }
                assert(!pre[removed].first_child);

                lemma_siblings_jump(pre, post, pre[parent].child.unwrap(), back);
            }
            else {
                lemma_sib_back_some(pre, pre[parent].child.unwrap(), removed);
            }
        }
    }

    assert forall |key: CapKey| #[trigger] post.contains_key(key)
    implies view(post)[key] == revoke_single_view(pre, removed).remove(removed)[key]
    by {
        if Some(key) == get_parent(pre, removed) {}
        else {
            assert(!child_of(pre, removed, key)) by {
                if child_of(pre, removed, key) {
                    if let Some(parent) = get_parent(pre, removed) {
                        lemma_child_of_univalent(pre, key, parent, removed);
                    }
                }
            };

            assert(view(post)[key] == view(pre)[key]);
        }
    };

    assert(view(post) =~= revoke_single_view(pre, removed).remove(removed));
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
