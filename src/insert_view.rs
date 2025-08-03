use vstd::prelude::*;

use crate::{
    lemmas::{lemma_siblings_none_empty, lemma_siblings_unchanged, lemma_siblings_unfold},
    tcb::{
        decreasing, decreasing_condition, insert_child, next_index, siblings, view, CapKey,
        CapNode, Child, LinkMap, LinkedNode, Next,
    },
};

verus! {

pub proof fn lemma_insert_siblings_unchanged(map: LinkMap, new: (CapKey, LinkedNode), key: CapKey)
    requires
        !map.contains_key(new.0),
        map.contains_key(key),
        decreasing::<Next>(map),
        decreasing_condition::<Next>(map.insert(new.0, new.1), new.0),
    ensures
        siblings(map, Some(key)) == siblings(map.insert(new.0, new.1), Some(key)),
    decreases map[key].index,
{
    assert(map[key] == map.insert(new.0, new.1)[key]);

    assert forall|key: CapKey|
        map.insert(new.0, new.1).contains_key(key) implies #[trigger] decreasing_condition::<Next>(
        map.insert(new.0, new.1),
        key,
    ) by {
        if key == new.0 {
        } else {
            assert(decreasing_condition::<Next>(map, key));
        }
    };

    assert(decreasing::<Next>(map.insert(new.0, new.1)));

    if let Some(next) = map[key].next {
        assert(decreasing_condition::<Next>(map, key));
        lemma_insert_siblings_unchanged(map, new, next);
        assert(siblings(map, Some(key)) == siblings(map.insert(new.0, new.1), Some(key)));
    } else {
        lemma_siblings_none_empty(map);
        lemma_siblings_none_empty(map.insert(new.0, new.1));
        assert(siblings(map, Some(key)) == siblings(map, None).push(key));
        lemma_siblings_unfold(map.insert(new.0, new.1), key);
        assert(siblings(map.insert(new.0, new.1), Some(key)) == siblings(map, None).push(key));
        //siblings(map.insert(new.0, new.1), Some(key)));
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
        CapNode { generation: map[self.parent].depth + 1, children: Seq::empty() }
    }

    pub open spec fn child_update(&self, map: LinkMap) -> LinkMap {
        map.insert(self.child, self.insert_node(map))
    }

    pub open spec fn next_update(&self, map: LinkMap) -> LinkMap {
        if map[self.parent].child.is_none() {
            map
        } else {
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
        map.insert(self.parent, parent_node)
    }

    proof fn lemma_view_child_update(&self, map: LinkMap)
        requires
            !map.contains_key(self.child),
            map.contains_key(self.parent),
            decreasing::<Next>(map),
            decreasing::<Child>(map),
        ensures
            view(self.child_update(map)) == view(map).insert(
                self.child,
                self.insert_view_node(map),
            ),
    {
        assert forall|key: CapKey| #[trigger] map.contains_key(key) implies {
            &&& self.child_update(map)[key].depth == map[key].depth
            &&& self.child_update(map)[key].child == map[key].child
        } by {};

        lemma_siblings_none_empty(map);
        lemma_siblings_none_empty(self.child_update(map));

        assert(decreasing_condition::<Next>(self.child_update(map), self.child)) by {
            if map[self.parent].child.is_none() {
                assert(self.child_update(map)[self.child].next.is_none());
            } else {
                let next = map[self.parent].child.unwrap();
                assert(decreasing_condition::<Child>(map, self.parent));
            }
        };

        assert forall|key: CapKey| map.contains_key(key) implies #[trigger] siblings(
            self.child_update(map),
            Some(key),
        ) == siblings(map, Some(key)) by {
            lemma_insert_siblings_unchanged(map, (self.child, self.insert_node(map)), key);
        };

        assert(self.insert_view_node(map) == self.insert_node(map).to_spec(self.child_update(map)));
        assert(view(map).insert(self.child, self.insert_view_node(map))[self.child] == view(
            self.child_update(map),
        )[self.child]);

        assert forall|key: CapKey| map.contains_key(key) implies #[trigger] view(
            self.child_update(map),
        )[key] == view(map).insert(self.child, self.insert_view_node(map))[key] by {
            assert(view(map).insert(self.child, self.insert_view_node(map))[key] == view(map)[key]);
            assert(view(map)[key] == self.child_update(map)[key].to_spec(map));
            if map[key].child.is_none() {
            } else {
                let child = map[key].child.unwrap();
                assert(decreasing_condition::<Child>(map, key));
                assert(map.contains_key(child));
                assert(siblings(map, Some(child)) == siblings(self.child_update(map), Some(child)));
            }
        };

        assert(view(self.child_update(map)) =~= view(map).insert(
            self.child,
            self.insert_view_node(map),
        ));
    }

    proof fn lemma_view_next_update(&self, map: LinkMap)
        requires
            map.contains_key(self.parent),
            decreasing::<Next>(map),
            decreasing::<Child>(map),
        ensures
            view(self.next_update(map)) == view(map),
    {
        if map[self.parent].child.is_none() {
        } else {
            let next = map[self.parent].child.unwrap();

            assert forall|key: CapKey| map.contains_key(key) implies #[trigger] view(map)[key]
                == view(self.next_update(map))[key] by {
                if map[key].child.is_none() {
                    lemma_siblings_none_empty(map);
                    lemma_siblings_none_empty(self.next_update(map));
                } else {
                    assert(decreasing_condition::<Child>(map, key));
                    self.lemma_invariants_update_next(map);
                    lemma_siblings_unchanged(map, self.next_update(map), map[key].child.unwrap());
                }
            };

            assert(decreasing_condition::<Child>(map, self.parent));
            assert(view(map).dom() =~= view(self.next_update(map)).dom());
            assert(view(self.next_update(map)) =~= view(map));
        }
    }

    pub open spec fn invariants(&self, map: LinkMap) -> bool {
        &&& map.contains_key(self.parent)
        &&& decreasing::<Child>(map)
        &&& decreasing::<Next>(map)
    }

    proof fn lemma_weak_next_update_child(&self, map: LinkMap)
        requires
            self.invariants(map),
            !map.contains_key(self.child),
        ensures
            decreasing::<Next>(self.child_update(map)),
    {
        assert forall|key: CapKey|
            self.child_update(map).contains_key(key) implies #[trigger] decreasing_condition::<Next>(
            self.child_update(map),
            key,
        ) by {
            if key == self.child {
                assert(decreasing_condition::<Child>(map, self.parent));
                assert(decreasing_condition::<Next>(self.child_update(map), self.child));
            } else {
                assert(decreasing_condition::<Next>(map, key));
            }
        };
    }

    proof fn lemma_weak_child_update_child(&self, map: LinkMap)
        requires
            self.invariants(map),
            !map.contains_key(self.child),
        ensures
            decreasing::<Child>(self.child_update(map)),
    {
        assert forall|key: CapKey|
            self.child_update(map).contains_key(key) implies #[trigger] decreasing_condition::<Child>(
            self.child_update(map),
            key,
        ) by {
            if key == self.child {
            } else {
                assert(decreasing_condition::<Child>(map, key));
            }
        };
    }

    proof fn lemma_invariants_update_next(&self, map: LinkMap)
        requires
            self.invariants(map),
        ensures
            self.invariants(self.next_update(map)),
    {
        assert forall|key: CapKey| #[trigger] self.next_update(map).contains_key(key) implies {
            &&& decreasing_condition::<Next>(self.next_update(map), key)
            &&& decreasing_condition::<Child>(self.next_update(map), key)
        } by {
            assert(decreasing_condition::<Child>(map, self.parent));
            assert(decreasing_condition::<Next>(map, key));
            assert(decreasing_condition::<Child>(map, key));
        };
    }

    proof fn lemma_invariants_update_parent(&self, map: LinkMap)
        requires
            self.invariants(map),
            map.contains_key(self.child),
            map[self.child].depth == map[self.parent].depth + 1,
        ensures
            self.invariants(self.parent_update(map)),
    {
        assert forall|key: CapKey| #[trigger] self.parent_update(map).contains_key(key) implies {
            &&& decreasing_condition::<Next>(self.parent_update(map), key)
            &&& decreasing_condition::<Child>(self.parent_update(map), key)
        } by {
            assert(decreasing_condition::<Next>(map, key));

            if key == self.parent {
                assert(decreasing_condition::<Child>(self.parent_update(map), self.parent));
            } else {
                assert(decreasing_condition::<Child>(map, key));
            };
        };
    }

    pub proof fn lemma_view_update(&self, map: LinkMap)
        requires
            !map.contains_key(self.child),
            self.invariants(map),
        ensures
            view(self.update(map)) == insert_child(view(map), self.parent, self.child),
    {
        self.lemma_view_child_update(map);
        self.lemma_weak_next_update_child(map);
        self.lemma_weak_child_update_child(map);
        self.lemma_view_next_update(self.child_update(map));
        self.lemma_invariants_update_next(self.child_update(map));

        let checkpoint = self.next_update(self.child_update(map));
        assert(view(checkpoint) == view(map).insert(self.child, self.insert_view_node(map)));

        self.lemma_invariants_update_parent(checkpoint);
        assert(decreasing::<Next>(self.update(map)));

        assert forall|key: CapKey| self.update(map).contains_key(key) implies #[trigger] siblings(
            checkpoint,
            Some(key),
        ) == siblings(self.update(map), Some(key)) by {
            lemma_siblings_unchanged(checkpoint, self.update(map), key);
        }

        lemma_siblings_unfold(self.update(map), self.child);
        assert(siblings(self.update(map), Some(self.child)) == view(
            checkpoint,
        )[self.parent].children.push(self.child));

        assert forall|key: CapKey|
            self.update(map).contains_key(key) && key != self.parent implies #[trigger] view(
            self.update(map),
        )[key] == view(checkpoint)[key] by {
            assert(self.update(map)[key] == checkpoint[key]);
            assert(decreasing_condition::<Child>(checkpoint, key));
        };

        assert(decreasing_condition::<Child>(self.update(map), self.parent));
        let CapNode { generation, children } = view(map)[self.parent];
        let parent_node = CapNode { generation, children: children.push(self.child) };
        let child_node = CapNode { generation: generation + 1, children: Seq::empty() };
        assert(view(self.update(map))[self.parent] == parent_node);

        assert(view(checkpoint) == view(map).insert(self.child, child_node));
        assert(view(self.update(map)) =~= view(checkpoint).insert(self.parent, parent_node));
        assert(insert_child(view(map), self.parent, self.child) == view(map).insert(
            self.child,
            child_node,
        ).insert(self.parent, parent_node));
    }
}

} // verus!
