use alloc::string::String;
use state_machines_macros::state_machine;
use vstd::{
    assert_by_contradiction,
    map_lib::lemma_submap_of_trans,
    prelude::*,
    seq_lib::{lemma_flatten_concat, lemma_seq_concat_contains_all_elements},
    set_lib::{
        lemma_len_union, lemma_len_union_ind, lemma_set_difference_len, lemma_set_disjoint_lens,
    },
};

verus! {

type CapKey = <String as View>::V;
type CapData = u64;
type CapMap = Map<CapKey, CapNode>;

pub ghost struct CapNode {
    pub generation: nat,
    pub parent: Option<CapKey>,
    pub children: Seq<CapKey>,
}

pub open spec fn connected(map: CapMap) -> bool {
    forall |key: CapKey| map.contains_key(key)
    ==> forall |index: int| 0 <= index < map[key].children.len()
    ==> {
        &&& map.contains_key(#[trigger] map[key].children[index])
        &&& map[key].generation < map[map[key].children[index]].generation
    }
}

pub open spec fn generation_bounded(map: CapMap, bound: nat) -> bool {
    forall |key: CapKey| map.contains_key(key) ==> #[trigger] map[key].generation < bound
}

#[cfg(disable)]
mod useless {
ghost struct GenerationMap {
    map: Map<CapKey, nat>,
    bound: nat,
}

impl GenerationMap {
    spec fn bounded(self) -> bool {
        forall |key: CapKey| self.map.contains_key(key) ==> #[trigger] self.map[key] < self.bound
    }

    spec fn increasing(self, relations: ChildrenMap) -> bool {
        forall |key: CapKey| relations.contains_key(key)
        ==> forall |index: int| 0 <= index < relations[key].1.len()
        ==> self.map[key] < #[trigger] self.map[relations[key].1[index]]
    }
}

type ChildrenMap = Map<CapKey, (Option<CapKey>, Seq<CapKey>)>;

spec fn remove_nodes_rec(map: ChildrenMap, keys: Seq<CapKey>, parent: CapKey, gens: GenerationMap) -> (ChildrenMap, Set<CapKey>)
decreases gens.bound - gens.map[parent], keys.len()
    when
        gens.bounded()
        && gens.increasing(map)
        && map.contains_key(parent)
        && (keys.len() == 0 || map.contains_key(keys.last()))
        && gens.map.contains_key(parent)
        && (keys.len() == 0 || gens.map.contains_key(keys.last()))
        && keys.is_prefix_of(map[parent].1)
{
    if keys.len() == 0 {
        (map, Set::empty())
    }
    else {
        // remove all children of keys.last()
        let (updated, children) = remove_nodes_rec(map, map[keys.last()].1, keys.last(), gens);

        // remove all neighbours of keys.last()
        let (updated, neighbours) = remove_nodes_rec(updated, keys.drop_last(), parent, gens);

        // remove keys.last()
        (updated.remove(keys.last()), children.union(neighbours).insert(keys.last()))
    }
}

spec fn remove_children(maps: (ChildrenMap, GenerationMap), key: CapKey) -> (ChildrenMap, Set<CapKey>)
{
    remove_nodes_rec(maps.0, maps.0[key].1, key, maps.1)
}

spec fn connected(map: ChildrenMap) -> bool {
    forall |key: CapKey, index: int| map.contains_key(key) && 0 <= index < map[key].1.len()
    ==> #[trigger] map.contains_key(map[key].1[index]) && map[map[key].1[index]].0 == Some(key)
}

spec fn almost_connected(map: ChildrenMap, exception: CapKey) -> bool {
    forall |key: CapKey, index: int| map.contains_key(key) && 0 <= index < map[key].1.len() && key != exception
    ==> #[trigger] map.contains_key(map[key].1[index]) && map[map[key].1[index]].0 == Some(key)
}

proof fn lemma_remove_nodes_disjoint(map: ChildrenMap, keys: Seq<CapKey>, parent: CapKey, gens: GenerationMap)
requires
    almost_connected(map, parent),
    map.dom().subset_of(gens.map.dom()),
    gens.bounded(),
    gens.increasing(map),
    keys.is_prefix_of(map[parent].1),
    map.contains_key(parent),
ensures
    ({
        let (updated, deleted) = remove_nodes_rec(map, keys, parent, gens); {
            &&& almost_connected(map, parent)
            &&& updated.dom().disjoint(deleted)
            &&& map.dom() == updated.dom().union(deleted)
            &&& updated.submap_of(map)
            &&& forall |key: CapKey| deleted.contains(key) ==> #[trigger] gens.map[key] > gens.map[parent]
            &&& keys.to_set().subset_of(deleted)
            &&& gens.increasing(updated)
        }
    })
decreases gens.bound - gens.map[parent], keys.len()
{
    if keys.len() == 0 {
        let (updated, deleted) = remove_nodes_rec(map, keys, parent, gens);
        assert(keys == Seq::<CapKey>::empty());
        assert(updated == map);
        assert(deleted == Set::<CapKey>::empty());
        assert(updated.dom().union(deleted) == map.dom());
        assert(updated.submap_of(map));
    }
    else {
        lemma_remove_nodes_disjoint(map, map[keys.last()].1, keys.last(), gens);
        let (fst_updated, fst_deleted) = remove_nodes_rec(map, map[keys.last()].1, keys.last(), gens);

        assert(fst_updated.submap_of(map));

        lemma_remove_nodes_disjoint(fst_updated, keys.drop_last(), parent, gens);
        let (snd_updated, snd_deleted) = remove_nodes_rec(fst_updated, keys.drop_last(), parent, gens);

        assert(connected(snd_updated));
        assert(snd_updated.submap_of(fst_updated));
        lemma_submap_of_trans(snd_updated, fst_updated, map);

        let result = snd_updated.remove(keys.last());
        let deleted = fst_deleted.union(snd_deleted).insert(keys.last());

        assert(result.dom().disjoint(deleted.insert(keys.last())));
        assert(map.dom() == result.dom().union(deleted));
        assert(result.submap_of(snd_updated));
        lemma_submap_of_trans(result, snd_updated, map);

        assert forall |key: CapKey| deleted.contains(key) ==> #[trigger] gens.map[key] > gens.map[parent]
        by {};

        assert forall |key: CapKey, index: int| result.contains_key(key) && 0 <= index < result[key].1.len() && key != parent
        implies #[trigger] result.contains_key(result[key].1[index]) && result[result[key].1[index]].0 == Some(key)
        by {
            assert(map.contains_key(result[key].1[index]));

            if snd_updated.contains_key(result[key].1[index]) {
                if result[key].1[index] == keys.last() {
                    assert(map.contains_key(key));
                    assert(result[key] == map[key]);
                    assert(keys.is_prefix_of(map[parent].1));
                    assert(keys[keys.len() - 1] == map[parent].1[keys.len() - 1]);
                    assert(map.contains_key(map[parent].1[keys.len() - 1]));
                    assert(map[key].0 == Some(parent));
                }
                else {}
            }
            else {
                assert(!result.contains_key(key));
            }
        };
    }
}
}

pub open spec fn direct_children(map: CapMap, keys: Set<CapKey>) -> Set<CapKey>
{
    keys.to_seq().map(|i, key| map[key].children).flatten().to_set()
}

spec fn closed(map: CapMap) -> bool {
    forall |key: CapKey| map.contains_key(key) ==> #[trigger] map[key].children.to_set().subset_of(map.dom())
}

// proof fn lemma_flatten_contains<A>(arg: Seq<Seq<A>>, elem: A)
// requires arg.flatten().contains(elem)
// ensures exists |index: int| arg.len() > index && #[trigger] arg[index].contains(elem)
// decreases arg.len()
// {
//     if arg.len() == 0 {}
//     else {
//         if arg.last().contains(elem) {}
//         else {
//             seq![arg.last()].lemma_flatten_one_element();
//             assert(seq![arg.last()].flatten() == arg.last());
//             lemma_flatten_concat(arg.drop_last(), seq![arg.last()]);
//
//
//             lemma_flatten_contains(arg.drop_last(), elem)
//         }
//     }
// }
//
// proof fn lemma_direct_children_closed(map: CapMap, keys: Set<CapKey>)
// requires keys.subset_of(map.dom()) && closed(map)
// ensures direct_children(map, keys).subset_of(map.dom())
// {
//     assert forall |key: CapKey| direct_children(map, keys).contains(key)
//     implies map.dom().contains(key)
//     by {
//         let unflattened = keys.to_seq().map(|i, key| map[key].children);
//         assert(unflattened.flatten().contains(key));
//         lemma_flatten_contains(unflattened, key);
//         let index = choose |index: int| unflattened.len() > index && #[trigger] unflattened[index].contains(key);
//
//         assert(exists |parent: CapKey| keys.to_seq().contains(parent) && map[parent].children.contains(key));
//     };
// }

#[via_fn]
proof fn transitive_children_decreases(map: CapMap, keys: Set<CapKey>)
{
    if direct_children(map, keys).subset_of(keys) { }
    else {
        let witness = choose |key: CapKey| !keys.contains(key) && #[trigger] direct_children(map, keys).contains(key);
        let diff = direct_children(map, keys).difference(keys);
        assert(diff.disjoint(keys));
        assert(diff.union(keys) == direct_children(map, keys).union(keys));
        assert(diff.contains(witness));
        assert(diff.len() > 0);
        lemma_set_disjoint_lens(diff, keys);
        assert(diff.union(keys).len() == diff.len() + keys.len());
        assert(keys.subset_of(map.dom()));
        //assert(diff.subset_of(map.dom()));

        lemma_set_difference_len(map.dom(), keys);
        lemma_set_difference_len(map.dom(), diff.union(keys));

        assume(map.dom().difference(keys).len() > map.dom().difference(diff.union(keys)).len());
    }
}

pub open spec fn transitive_children(map: CapMap, keys: Set<CapKey>) -> Set<CapKey>
decreases map.dom().difference(keys).len()
    when keys.subset_of(map.dom()) && keys.finite() && map.dom().finite()
    via transitive_children_decreases
{
    if direct_children(map, keys).subset_of(keys) { keys }
    else { transitive_children(map, direct_children(map, keys).union(keys)) }
}

state_machine!{
    CapState {
        fields {
            pub generation: nat,
            pub nodes: CapMap,
        }

        #[invariant]
        pub fn generation_bounded(&self) -> bool {
            generation_bounded(self.nodes, self.generation)
        }

        #[invariant]
        pub fn connected(&self) -> bool {
            connected(self.nodes)
        }

        #[invariant]
        pub fn generation_bound(&self) -> bool {
            self.generation > 0
        }

        #[invariant]
        pub fn parent_child(&self) -> bool {
            forall |key: CapKey| self.nodes.contains_key(key) && self.nodes[key].parent.is_some()
            ==> {
                &&& #[trigger] self.nodes.contains_key(self.nodes[key].parent.unwrap())
                &&& self.nodes[self.nodes[key].parent.unwrap()].children.contains(key)
            }
        }

        #[invariant]
        pub fn child_parent(&self) -> bool {
            forall |key: CapKey, index: int| self.nodes.contains_key(key) && 0 <= index < self.nodes[key].children.len()
            ==> {
                &&& self.nodes.contains_key(self.nodes[key].children[index])
                &&& #[trigger] self.nodes[self.nodes[key].children[index]].parent == Some(key)
            }
        }

        init!{
            empty() {
                init generation = 1;
                init nodes = Map::empty();
            }
        }

        #[inductive(empty)]
        fn empty_inductive(post: Self) { }

        transition!{
            insert_root(key: CapKey) {
                require !pre.nodes.contains_key(key);
                update nodes = pre.nodes.insert(key, CapNode { generation: 0, parent: None, children: Seq::empty() });
            }
        }

        #[inductive(insert_root)]
        fn insert_root_inductive(pre: Self, post: Self, key: CapKey) { }

        transition!{
            insert_child(child: CapKey, parent: CapKey) {
                require pre.nodes.contains_key(parent);
                require !pre.nodes.contains_key(child);
                let parent_node = pre.nodes[parent];
                update nodes[parent] = CapNode { children: parent_node.children.push(child), ..parent_node };
                update nodes[child] = CapNode { generation: pre.generation, parent: Some(parent), children: Seq::empty() };
                update generation = pre.generation + 1;
            }
        }

        #[inductive(insert_child)]
        fn insert_child_inductive(pre: Self, post: Self, child: CapKey, parent: CapKey) {
            assert forall |key: CapKey| #[trigger] pre.nodes.contains_key(key)
            implies post.nodes.contains_key(key) && pre.nodes[key].children.is_prefix_of(post.nodes[key].children)
            by {
                if key == parent {}
                else {}
            };

            assert forall |key: CapKey| post.nodes.contains_key(key) && #[trigger] post.nodes[key].parent.is_some()
            implies {
                &&& post.nodes.contains_key(post.nodes[key].parent.unwrap())
                &&& post.nodes[post.nodes[key].parent.unwrap()].children.contains(key)
            }
            by {
                if key == child {
                    assert(post.nodes[parent].children.last() == child);
                }
                else if key == parent { }
                else { }
            };
        }

        transition!{
            revoke_children(parent: CapKey) {
                require pre.nodes.contains_key(parent);
                let all_children = transitive_children(pre.nodes, pre.nodes[parent].children.to_set());
                update nodes[parent] = CapNode { children: Seq::empty(), ..parent_node };
                update nodes = pre.nodes.remove_keys(all_children);
            }
        }

        #[inductive(revoke_children)]
        fn revoke_children_inductive(pre: Self, post: Self, parent: CapKey) {
            admit()
        }
    }
}


}
