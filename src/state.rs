use state_machines_macros::state_machine;
use vstd::{
    prelude::*,
    seq::{axiom_seq_add_index1, axiom_seq_add_index2, axiom_seq_new_index},
};

verus! {

type CapKey = u64;
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

pub open spec fn direct_children(map: CapMap, keys: Seq<CapKey>) -> Seq<CapKey>
{
    keys.map_values(|key| map[key].children).flatten()
}

proof fn lemma_direct_children_inc_gen(map: CapMap, keys: Seq<CapKey>)
requires
    keys.to_set().subset_of(map.dom()),
    connected(map),
    direct_children(map, keys).len() != 0
ensures keys.map_values(|key| map[key].generation as int).min() < direct_children(map, keys).map_values(|key| map[key].generation as int).min()
{
    let generation = |key| map[key].generation as int;

    let parents = keys.map_values(generation);
    let children = direct_children(map, keys).map_values(generation);

    children.min_ensures();
    assert(exists |index| 0 <= index < children.len() && children[index] == children.min());
    let min_child_index = choose |index: int|
        0 <= index < children.len() && children[index] == children.min();

    axiom_seq_new_index(
        direct_children(map, keys).len(),
        |i| generation(direct_children(map, keys)[i]),
        min_child_index
    );

    parents.min_ensures();
    assert(exists |index| 0 <= index < parents.len() && parents[index] == parents.min());
    let min_parent_index = choose |index: int|
        0 <= index < parents.len() && parents[index] == parents.min();

    axiom_seq_new_index(keys.len(), |i| generation(keys[i]), min_parent_index);

    let get_children = |key: CapKey| map[key].children;
    let unflat = keys.map_values(get_children);
    lemma_flatten_index(unflat, min_child_index);

    let (origin, offset) = choose |origin: int, offset: int|
        0 <= origin < unflat.len() && 0 <= offset < unflat[origin].len() &&
        unflat[origin][offset] == unflat.flatten()[min_child_index];

    assert(generation(keys[min_parent_index]) <= parents[origin] == generation(keys[origin]));

    assert(map.contains_key(keys[origin]));
    assert(map[keys[origin]].children[offset] == direct_children(map, keys)[min_child_index]);

    assert(generation(keys[origin]) < children[min_child_index]);
}

proof fn lemma_direct_children_closed(map: CapMap, keys: Seq<CapKey>)
requires
    keys.to_set().subset_of(map.dom()),
    connected(map)
ensures
    direct_children(map, keys).to_set().subset_of(map.dom())
{
    assert forall |key: CapKey| direct_children(map, keys).contains(key)
    implies map.dom().contains(key)
    by {
        let that_index = choose |index: int|
            0 <= index < direct_children(map, keys).len() &&
            direct_children(map, keys)[index] == key;

        let children = |key: CapKey| map[key].children;
        let unflat = keys.map_values(children);
        lemma_flatten_index(unflat, that_index);

        let (origin, offset) = choose |origin: int, offset: int|
            0 <= origin < unflat.len() && 0 <= offset < unflat[origin].len() &&
            unflat[origin][offset] == unflat.flatten()[that_index];

        assert(map.contains_key(keys[origin]));
        assert(map.contains_key(map[keys[origin]].children[offset]));
    }
}

proof fn lemma_flatten_index<A>(arg: Seq<Seq<A>>, index: int)
requires 0 <= index < arg.flatten().len()
ensures exists |origin: int, offset: int|
    0 <= origin < arg.len() && 0 <= offset < arg[origin].len() &&
    arg[origin][offset] == arg.flatten()[index]
decreases arg.len()
{
    if arg.len() == 0 { }
    else {
        if index < arg.first().len() {
            axiom_seq_add_index1(arg.first(), arg.drop_first().flatten(), index);
        }
        else {
            axiom_seq_add_index2(arg.first(), arg.drop_first().flatten(), index);
            lemma_flatten_index(arg.drop_first(), index - arg.first().len());
        }
    }
}

proof fn lemma_flatten_index2<A>(arg: Seq<Seq<A>>, origin: int, offset: int)
requires
    0 <= origin < arg.len(),
    0 <= offset < arg[origin].len(),
ensures exists |index|
    0 <= index < arg.flatten().len() && arg.flatten()[index] == arg[origin][offset]
decreases arg.len()
{
    if origin == 0 {
        axiom_seq_add_index1(arg.first(), arg.drop_first().flatten(), offset);
        assert(arg[0][offset] == arg.flatten()[offset]);
    }
    else {
        lemma_flatten_index2(arg.drop_first(), origin - 1, offset);
        let index = choose |index: int|
            0 <= index < arg.drop_first().flatten().len() &&
            arg.drop_first().flatten()[index] == arg[origin][offset];

        axiom_seq_add_index2(arg.first(), arg.drop_first().flatten(), index + arg.first().len());
        assert(arg[origin][offset] == arg.flatten()[index + arg.first().len()]);
    }
}

proof fn lemma_transitive_children_decreases(map: CapMap, keys: Seq<CapKey>, bound: nat)
requires
    connected(map),
    generation_bounded(map, bound),
    keys.to_set().subset_of(map.dom()),
    direct_children(map, keys).len() != 0
ensures
    bound - keys.map_values(|key| map[key].generation as int).min() >
    bound - direct_children(map, keys).map_values(|key| map[key].generation as int).min()
{
    lemma_direct_children_inc_gen(map, keys);

    let generation = |key: CapKey| map[key].generation as int;
    let children = |key: CapKey| map[key].children;
    let new_gens = direct_children(map, keys).map_values(generation);

    new_gens.min_ensures();
    assert(exists |i: int| new_gens.len() > i && new_gens[i] == new_gens.min());
    let that_index = choose |i: int| 0 <= i < new_gens.len() && new_gens[i] == new_gens.min();

    assert(that_index < direct_children(map, keys).len() == direct_children(map, keys).map_values(generation).len());
    axiom_seq_new_index(direct_children(map, keys).len(), |i| generation(direct_children(map, keys)[i]), that_index);

    assert(direct_children(map, keys).map_values(generation)[that_index] == generation(direct_children(map, keys)[that_index]));
    let that_key = direct_children(map, keys)[that_index];

    let unflat = keys.map_values(children);
    lemma_flatten_index(unflat, that_index);

    let (origin, offset) = choose |origin: int, offset: int|
        0 <= origin < unflat.len() && 0 <= offset < unflat[origin].len() &&
        unflat[origin][offset] == unflat.flatten()[that_index];

    assert(map.contains_key(keys[origin]));
    assert(map.contains_key(map[keys[origin]].children[offset]));

    axiom_seq_new_index(keys.len(), |i| children(keys[i]), origin);
    assert(map[keys[origin]].children[offset] == keys.map_values(children)[origin][offset]);

    assert(map.contains_key(that_key));

    assert(0 <= new_gens.min() < bound);
}

#[via_fn]
proof fn transitive_children_decreases_via(map: CapMap, keys: Seq<CapKey>, bound: nat)
{
    if direct_children(map, keys).len() == 0 {}
    else {
        lemma_direct_children_closed(map, keys);
        lemma_transitive_children_decreases(map, keys, bound);
    }
}

pub open spec fn remove_all<A>(input: Seq<A>, needles: Seq<A>) -> Seq<A>
decreases needles.len()
{
    if needles.len() == 0 { input }
    else {
        remove_all(input.remove_value(needles.last()), needles.drop_last())
    }
}

pub open spec fn transitive_children(map: CapMap, keys: Seq<CapKey>, bound: nat) -> Seq<CapKey>
decreases bound - keys.map_values(|key| map[key].generation as int).min()
    when keys.to_set().subset_of(map.dom())
        && connected(map)
        && generation_bounded(map, bound)
    via transitive_children_decreases_via
{
    let new_keys = direct_children(map, keys);

    if new_keys.len() == 0 { keys }
    else { keys + transitive_children(map, new_keys, bound) }
}

proof fn lemma_direct_children_complete(map: CapMap, keys: Seq<CapKey>, parent: CapKey, child: CapKey)
requires
    map.contains_key(parent),
    map[parent].children.contains(child),
    keys.contains(parent),
ensures
    direct_children(map, keys).contains(child)
{
    let parent_index = choose |index: int| 0 <= index < keys.len() && keys[index] == parent;
    let child_offset = choose |index: int| 0 <= index < map[parent].children.len() && map[parent].children[index] == child;

    let children = |key: CapKey| map[key].children;
    lemma_flatten_index2(keys.map_values(children), parent_index, child_offset);
}

proof fn lemma_direct_children_co_complete(map: CapMap, keys: Seq<CapKey>, child: CapKey)
requires
    map.contains_key(child),
    child_parent(map),
    keys.to_set().subset_of(map.dom()),
    map[child].parent.is_some(),
    direct_children(map, keys).contains(child),
ensures
    keys.contains(map[child].parent.unwrap()),
{
    let that_index = choose |index: int|
        0 <= index < direct_children(map, keys).len() &&
        direct_children(map, keys)[index] == child;

    let get_children = |key: CapKey| map[key].children;
    let unflat = keys.map_values(get_children);
    lemma_flatten_index(unflat, that_index);

    let (origin, offset) = choose |origin: int, offset: int|
        0 <= origin < unflat.len() && 0 <= offset < unflat[origin].len() &&
        unflat[origin][offset] == unflat.flatten()[that_index];

    assert(map[keys[origin]].children[offset] == child);
    assert(map[child].parent == Some(keys[origin]));
}

proof fn lemma_transitive_children_rec(map: CapMap, keys: Seq<CapKey>, bound: nat)
requires
    connected(map),
    generation_bounded(map, bound),
    keys.to_set().subset_of(map.dom()),
ensures
    transitive_children(map, keys, bound) == keys + transitive_children(map, direct_children(map, keys), bound)
{
    if direct_children(map, keys).len() == 0 {
        assert(transitive_children(map, keys, bound) == keys);
        assert(transitive_children(map, direct_children(map, keys), bound).len() == 0);
    }
    else {
        lemma_direct_children_closed(map, keys);
    }
}

proof fn lemma_transitive_children_complete(map: CapMap, keys: Seq<CapKey>, bound: nat, parent: CapKey, child: CapKey)
requires
    connected(map),
    generation_bounded(map, bound),
    keys.to_set().subset_of(map.dom()),
    map.contains_key(parent),
    transitive_children(map, keys, bound).contains(parent),
    map[parent].children.contains(child)
ensures
    transitive_children(map, keys, bound).contains(child)
decreases bound - keys.map_values(|key| map[key].generation as int).min()
{
    let new_keys = direct_children(map, keys);

    if keys.contains(parent) {
        lemma_direct_children_complete(map, keys, parent, child);
        assert(new_keys.contains(child));
        assert(new_keys.len() > 0);

        lemma_direct_children_closed(map, keys);
        assert(new_keys.is_prefix_of(transitive_children(map, new_keys, bound)));

        assert(transitive_children(map, new_keys, bound).contains(child));
        assert(transitive_children(map, new_keys, bound).is_suffix_of(transitive_children(map, keys, bound)));
    }
    else {
        let parent_index = choose |index: int|
            0 <= index < transitive_children(map, keys, bound).len() &&
            transitive_children(map, keys, bound)[index] == parent;

        lemma_transitive_children_rec(map, keys, bound);

        if parent_index < keys.len() {
            axiom_seq_add_index1(keys, transitive_children(map, new_keys, bound), parent_index);
        }
        else {
            axiom_seq_add_index2(keys, transitive_children(map, new_keys, bound), parent_index);
            assert(transitive_children(map, new_keys, bound).contains(parent));

            if new_keys.len() == 0 {
                assert(transitive_children(map, keys, bound) == keys);
            }
            else {
                lemma_direct_children_closed(map, keys);
                lemma_transitive_children_decreases(map, keys, bound);
                lemma_transitive_children_complete(map, new_keys, bound, parent, child);
                assert(transitive_children(map, new_keys, bound).contains(child));

                let child_index = choose |index: int|
                    0 <= index < transitive_children(map, new_keys, bound).len() &&
                    transitive_children(map, new_keys, bound)[index] == child;

                axiom_seq_add_index2(keys, transitive_children(map, new_keys, bound), keys.len() + child_index);
                assert(transitive_children(map, keys, bound).contains(child));
            }
        }
    }
}

proof fn lemma_transitive_children_co_complete(map: CapMap, keys: Seq<CapKey>, bound: nat, child: CapKey)
requires
    connected(map),
    generation_bounded(map, bound),
    child_parent(map),

    transitive_children(map, keys, bound).contains(child),
    keys.to_set().subset_of(map.dom()),
    map.contains_key(child),
    !keys.contains(child),
    map[child].parent.is_some(),

ensures
    transitive_children(map, keys, bound).contains(map[child].parent.unwrap()),

decreases bound - keys.map_values(|key| map[key].generation as int).min()
{
    let parent = map[child].parent.unwrap();
    let rec_call = transitive_children(map, direct_children(map, keys), bound);
    lemma_transitive_children_rec(map, keys, bound);

    lemma_direct_children_closed(map, keys);
    assert(transitive_children(map, direct_children(map, keys), bound).contains(child));

    if direct_children(map, keys).contains(child) {
        lemma_direct_children_co_complete(map, keys, child);
        let index = choose |index: int| 0 <= index < keys.len() && keys[index] == parent;
        axiom_seq_add_index1(keys, rec_call, index);
    }
    else {
        lemma_transitive_children_decreases(map, keys, bound);
        lemma_transitive_children_co_complete(map, direct_children(map, keys), bound, child);
        let index = choose |index: int| 0 <= index < rec_call.len() && rec_call[index] == parent;
        axiom_seq_add_index2(keys, rec_call, index + keys.len());
    }
}

pub open spec fn parent_child(map: CapMap) -> bool {
    forall |key: CapKey| map.contains_key(key) && map[key].parent.is_some()
    ==> {
        &&& #[trigger] map.contains_key(map[key].parent.unwrap())
        &&& map[map[key].parent.unwrap()].children.contains(key)
    }
}

pub open spec fn child_parent(map: CapMap) -> bool {
    forall |key: CapKey, index: int| map.contains_key(key) && 0 <= index < map[key].children.len()
    ==> {
        &&& map.contains_key(map[key].children[index])
        &&& #[trigger] map[map[key].children[index]].parent == Some(key)
    }
}

pub open spec fn revoke_children(map: CapMap, parent: CapKey, bound: nat) -> CapMap {
    map
        .insert(parent, CapNode { children: Seq::empty(), ..map[parent] })
        .remove_keys(transitive_children(map, map[parent].children, bound).to_set())
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
            parent_child(self.nodes)
        }

        #[invariant]
        pub fn child_parent(&self) -> bool {
            child_parent(self.nodes)
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
                update nodes = revoke_children(pre.nodes, parent, pre.generation);
            }
        }

        #[inductive(revoke_children)]
        fn revoke_children_inductive(pre: Self, post: Self, parent: CapKey) {
            revoke_inv_connected(pre.nodes, post.nodes, parent, post.generation);
            revoke_inv_parent_child(pre.nodes, post.nodes, parent, post.generation);
        }
    }
}

proof fn revoke_inv_connected(pre: CapMap, post: CapMap, parent: CapKey, bound: nat)
requires
    connected(pre),
    child_parent(pre),
    pre.contains_key(parent),
    generation_bounded(pre, bound),
    generation_bounded(post, bound),
    post == revoke_children(pre, parent, bound),
ensures connected(post)
{
    assert forall |key: CapKey, index: int|
        post.contains_key(key) && 0 <= index < post[key].children.len()

    implies {
        &&& post.contains_key(#[trigger] post[key].children[index])
        &&& post[key].generation < post[post[key].children[index]].generation
    }

    by {
        if key == parent {
            // this has no children
        }
        else if transitive_children(pre, pre[parent].children, bound).contains(key) {
            // keys were removed
        }
        else {
            // prove that children were not removed
            let child = post[key].children[index];

            if transitive_children(pre, pre[parent].children, bound).contains(child) {
                assert(pre[child].parent.unwrap() == key);

                if pre[parent].children.contains(child) {}
                else {
                    lemma_transitive_children_co_complete(pre, pre[parent].children, bound, child);
                    assert(transitive_children(pre, pre[parent].children, bound).contains(key));
                }
            }
            else { }
        }
    };
}

proof fn revoke_inv_parent_child(pre: CapMap, post: CapMap, parent: CapKey, bound: nat)
requires
    connected(pre),
    parent_child(pre),
    generation_bounded(pre, bound),
    pre.contains_key(parent),
    post == revoke_children(pre, parent, bound),
ensures parent_child(post)
{
    assert forall |key: CapKey| post.contains_key(key) && post[key].parent.is_some()
    implies {
        &&& #[trigger] post.contains_key(post[key].parent.unwrap())
        &&& post[post[key].parent.unwrap()].children.contains(key)
    }
    by {
        let current_parent = pre[key].parent.unwrap();
        assert(current_parent == post[key].parent.unwrap());

        assert(pre.contains_key(current_parent));
        assert(pre[current_parent].children.contains(key));

        if current_parent == parent {
            assert(pre[parent].children.contains(key));
            assert(pre[parent].children.len() > 0);
            assert(pre[parent].children.is_prefix_of(transitive_children(pre, pre[parent].children, bound)));
            assert(transitive_children(pre, pre[parent].children, bound).contains(key));
        }
        else if transitive_children(pre, pre[parent].children, bound).contains(current_parent) {
            lemma_transitive_children_complete(pre, pre[parent].children, bound, current_parent, key);
            assert(transitive_children(pre, pre[parent].children, bound).contains(key));
        }
        else {
            assert(post.contains_key(current_parent));
            assert(post[current_parent] == pre[current_parent]);
        }
    };
}

fn test() {
    let ghost test: CapState::State = CapState::take_step::empty();

    proof!{
        test = CapState::take_step::insert_root(test, 1);
        test = CapState::take_step::insert_child(test, 2, 1);
        test = CapState::take_step::insert_child(test, 3, 1);
        test = CapState::take_step::insert_child(test, 4, 3);

        assert(test.nodes[1].children == seq![2u64, 3]);
        assert(test.nodes[2].children == Seq::<u64>::empty());
        assert(test.nodes[3].children == seq![4u64]);
        assert(test.nodes[4].children == Seq::<u64>::empty());

        assert(direct_children(test.nodes, seq![2, 3]) == seq![4u64]) by (compute);
        assert(direct_children(test.nodes, seq![4]) == Seq::<u64>::empty()) by (compute);
        assert(direct_children(test.nodes, seq![2]) == Seq::<u64>::empty()) by (compute);

        reveal_with_fuel(remove_all, 20);

        assert forall |v: u64| #[trigger] Seq::empty().remove_value(v) == Seq::<u64>::empty()
        by { Seq::empty().index_of_first_ensures(v) };

        reveal_with_fuel(transitive_children, 5);
        assert(transitive_children(test.nodes, seq![4], test.generation) == seq![4u64]);
        assert(transitive_children(test.nodes, seq![2], test.generation) == seq![2u64]);
        assert(transitive_children(test.nodes, seq![2, 3], test.generation) == seq![2u64, 3, 4]);

        test = CapState::take_step::revoke_children(test, 1);

        assert(test.nodes.dom() =~= set![1u64]);
    }
}

}
