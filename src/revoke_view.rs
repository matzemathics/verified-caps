use vstd::prelude::*;

use crate::{
    lemmas::{
        lemma_child_of_depth, lemma_child_of_first_child, lemma_child_of_univalent,
        lemma_parent_child, lemma_sib_back_some, lemma_sibling_of_next, lemma_siblings_contained,
        lemma_siblings_decreasing, lemma_siblings_no_loop, lemma_siblings_none_empty,
        lemma_siblings_unchanged_after, lemma_siblings_unchanged_local, lemma_siblings_unfold,
    },
    state::{back_link_condition, clean_links, SysState},
    tcb::{
        child_of, get_parent, revoke_single_parent_update, sibling_of, siblings,
        transitive_child_of, transitive_children, view, weak_next_connected,
        weak_next_link_condition, CapKey, LinkMap,
    },
};

verus! {

pub open spec fn close_to(map: LinkMap, target: CapKey, key: CapKey) -> bool {
    key == target || map[target].next == Some(key) || map[target].back == Some(key)
        || map[target].child == Some(key)
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
        &&& post[pre[removed].back.unwrap()].first_child
            == pre[pre[removed].back.unwrap()].first_child
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

pub proof fn lemma_siblings_jump(pre: LinkMap, post: LinkMap, start: CapKey, jump: CapKey)
    requires
        weak_next_connected(pre),
        weak_next_connected(post),
        forall|key: CapKey|
            post.contains_key(key) && key != jump ==> #[trigger] post[key].next == pre[key].next,
        pre.contains_key(jump),
        pre.contains_key(start),
        pre[jump].next.is_some(),
        post.dom() == pre.dom().remove(pre[jump].next.unwrap()),
        post[jump].next == pre[pre[jump].next.unwrap()].next,
        siblings(pre, Some(start)).contains(jump),
    ensures
        siblings(post, Some(start)) == siblings(pre, Some(start)).remove_value(
            pre[jump].next.unwrap(),
        ),
    decreases pre[start].index,
{
    assert(weak_next_link_condition(pre, jump));
    let removed = pre[jump].next.unwrap();

    if start == jump {
        if let Some(next) = post[jump].next {
            assert(weak_next_link_condition(post, jump));
            assert(weak_next_link_condition(pre, jump));
            assert(weak_next_link_condition(pre, pre[jump].next.unwrap()));

            assert forall|after: CapKey| #[trigger]
                siblings(pre, Some(next)).contains(after) implies post[after].next
                == pre[after].next by {
                lemma_siblings_contained(pre, Some(next), after);
                lemma_siblings_decreasing(pre, removed, after);
            };

            lemma_siblings_unchanged_after(pre, post, next);
        }
        let critical = siblings(pre, post[jump].next);
        assert(critical == siblings(post, post[jump].next));

        assert(critical.index_of_first(removed).is_none()) by {
            if let Some(i) = critical.index_of_first(removed) {
                siblings(pre, pre[removed].next).index_of_first_ensures(removed);
                assert(siblings(pre, pre[removed].next)[i] == removed);
                assert(siblings(pre, pre[removed].next).contains(removed));
                lemma_siblings_decreasing(pre, removed, removed);
                assert(false);
            }
        }

        lemma_siblings_unfold(pre, jump);
        lemma_siblings_unfold(pre, removed);
        assert(siblings(pre, Some(jump)) == siblings(pre, post[jump].next).push(removed).push(
            jump,
        ));

        assert(critical.push(removed).push(jump).index_of_first(removed) == Some(
            critical.len() as int,
        )) by {
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
    } else {
        assert(weak_next_link_condition(pre, jump));
        lemma_siblings_unfold(pre, start);
        lemma_siblings_decreasing(pre, start, jump);
        assert(removed != start);
        lemma_siblings_unfold(post, start);

        assert(weak_next_link_condition(pre, start));
        assert(weak_next_link_condition(post, start));
        let next = pre[start].next.unwrap();
        lemma_siblings_jump(pre, post, next, jump);

        assert(siblings(post, Some(next)) == siblings(pre, Some(next)).remove_value(
            pre[jump].next.unwrap(),
        ));

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

pub proof fn lemma_revoke_link_view(pre: LinkMap, post: LinkMap, removed: CapKey)
    requires
        post.dom() == pre.dom().remove(removed),
        clean_links(pre),
        weak_next_connected(post),
        pre[removed].child.is_none(),
        forall|key: CapKey|
            pre.contains_key(key) && !close_to(pre, removed, key) ==> #[trigger] pre[key]
                == post[key],
        revoke_back_update(pre, post, removed),
        revoke_next_update(pre, post, removed),
        pre.contains_key(removed),
    ensures
        view(post) == revoke_single_parent_update(pre, removed).remove(removed),
{
    assert forall|key: CapKey|
        post.contains_key(key) && pre[removed].back != Some(key) implies #[trigger] pre[key].next
        == post[key].next by {
        if Some(key) == pre[removed].next {
        } else if Some(key) == pre[removed].child {
        } else {
        }
    };

    assert forall|key: CapKey|
        pre.contains_key(key) && !sibling_of(pre, removed, key) implies #[trigger] pre[key].next
        == post[key].next by {
        if Some(key) == pre[removed].back {
            if pre[removed].first_child {
            } else {
                assert(back_link_condition(SysState::Clean, pre, removed));
                lemma_sibling_of_next(pre, key);
            }
        } else {
        }
    };

    assert forall|parent: CapKey|
        post.contains_key(parent) && !child_of(pre, removed, parent) implies #[trigger] view(
        post,
    )[parent] == view(pre)[parent] by {
        assert(pre[parent].depth == post[parent].depth);
        assert(get_parent(pre, removed) != Some(parent));

        if let Some(child) = pre[parent].child {
            assert(child_of(pre, child, parent)) by {
                lemma_siblings_unfold(pre, child);
                assert(siblings(pre, pre[parent].child).last() == child);
            };

            lemma_parent_child(pre, parent, child);
            lemma_siblings_unchanged_local(pre, post, removed, child);
        } else {
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

            assert(siblings(pre, pre[removed].next).remove_value(removed) == siblings(
                pre,
                pre[removed].next,
            ));

            critical.push(removed).index_of_first_ensures(removed);
            assert(critical.push(removed).remove_value(removed) == siblings(
                pre,
                pre[removed].next,
            ));

            assert(view(pre)[parent].children.remove_value(removed) == critical);
            assert(view(post)[parent].children == siblings(post, post[parent].child));

            assert forall|sib: CapKey| #[trigger]
                siblings(pre, pre[removed].next).contains(sib) implies post[sib].next
                == pre[sib].next by {
                lemma_siblings_contained(pre, pre[removed].next, sib);

                if sib == parent {
                } else if pre[removed].next == Some(sib) {
                } else if sib == removed {
                } else {
                }
            };

            assert(siblings(pre, pre[removed].next) == siblings(post, pre[removed].next)) by {
                if let Some(next) = pre[removed].next {
                    lemma_siblings_unchanged_after(pre, post, next);
                } else {
                    lemma_siblings_none_empty(pre);
                    lemma_siblings_none_empty(post);
                }
            };

            assert(view(post)[parent] == revoke_single_parent_update(pre, removed)[parent]);
        } else {
            assert(back_link_condition(SysState::Clean, pre, removed));

            if let Some(back) = pre[removed].back {
                lemma_parent_child(pre, back, removed);
                if pre[removed].first_child {
                    lemma_child_of_first_child(pre, back);
                    assert(child_of(pre, removed, back));
                }
                assert(!pre[removed].first_child);

                lemma_siblings_jump(pre, post, pre[parent].child.unwrap(), back);
            } else {
                lemma_sib_back_some(pre, pre[parent].child.unwrap(), removed);
            }
        }
    }
    assert forall|key: CapKey| #[trigger] post.contains_key(key) implies view(post)[key]
        == revoke_single_parent_update(pre, removed).remove(removed)[key] by {
        if Some(key) == get_parent(pre, removed) {
        } else {
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

    assert(view(post) =~= revoke_single_parent_update(pre, removed).remove(removed));
}

pub proof fn lemma_revoke_transitive_changes(pre: LinkMap, removed: CapKey, parent: CapKey)
requires
    transitive_child_of(view(pre), removed, parent)
ensures
    transitive_children(view(pre), parent) ==
    transitive_children(revoke_single_parent_update(pre, removed).remove(removed), parent).insert(removed)
{
    admit()
}

pub proof fn lemma_revoke_transitive_non_changes(pre: LinkMap, removed: CapKey, parent: CapKey, subtree: Set<CapKey>)
requires
    transitive_child_of(view(pre), removed, parent),
    transitive_children(view(pre), parent).subset_of(subtree)
ensures
    view(pre).remove_keys(subtree) ==
    revoke_single_parent_update(pre, removed).remove(removed).remove_keys(subtree)
{
    admit()
}

} // verus!
