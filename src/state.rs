use verus_state_machines_macros::tokenized_state_machine;
use vstd::prelude::*;

verus! {

#[cfg(verus_keep_ghost)]
use crate::specs::link_map::{decreasing, next_index, Child, LinkedNode, Next};
use crate::specs::link_map::LinkMap;
use crate::specs::cap_map::CapKey;

pub ghost enum LinkState {
    Null,
    Unchanged(CapKey),
    Taken(CapKey),
    Fixed(CapKey),
}

impl LinkState {
    pub open spec fn dom(&self) -> Set<CapKey> {
        match self {
            LinkState::Taken(key) => set![*key],
            _ => set![],
        }
    }

    pub open spec fn fixed(&self) -> bool {
        match self {
            LinkState::Null => true,
            LinkState::Unchanged(_) => false,
            LinkState::Taken(_) => false,
            LinkState::Fixed(_) => true,
        }
    }

    pub open spec fn key(&self) -> Option<CapKey> {
        match self {
            LinkState::Null => None,
            LinkState::Unchanged(k) => Some(*k),
            LinkState::Taken(k) => Some(*k),
            LinkState::Fixed(k) => Some(*k),
        }
    }
}

#[allow(inconsistent_fields)]
pub enum SysState {
    Clean,
    InsertChild { inserted: CapKey, parent: CapKey, next: LinkState },
    RevokeSingle { key: CapKey, back: LinkState, next: LinkState, first_child: bool },
}

impl SysState {
    pub open spec fn dom(self) -> Set<CapKey> {
        match self {
            SysState::Clean => Set::empty(),
            SysState::InsertChild { inserted, parent, next } => next.dom().insert(parent),
            SysState::RevokeSingle { key, back, next, first_child } => {
                back.dom().union(next.dom()).insert(key)
            },
        }
    }

    pub open spec fn allow_broken_back_link(self, key: CapKey, target: CapKey) -> bool {
        match self {
            SysState::Clean => false,
            SysState::InsertChild { inserted, parent, next } => key == inserted,
            SysState::RevokeSingle { key: removed, back, next, first_child } => {
                next == LinkState::Fixed(key) || key == removed
            },
        }
    }

    pub open spec fn allow_broken_next_link(self, key: CapKey, target: CapKey) -> bool {
        match self {
            SysState::Clean => false,
            SysState::InsertChild { inserted, parent, next } => key == inserted && !next.fixed(),
            SysState::RevokeSingle { key: removed, back, next, first_child } => {
                (back == LinkState::Fixed(key) && !first_child) || key == removed
            },
        }
    }

    pub open spec fn allow_broken_child_link(self, key: CapKey, target: CapKey) -> bool {
        match self {
            SysState::Clean => false,
            SysState::InsertChild { inserted, parent, next } => key == parent && next.fixed(),
            SysState::RevokeSingle { key: removed, back, next, first_child } => {
                (back == LinkState::Fixed(key) && first_child) || key == removed
            },
        }
    }
}

pub open spec fn back_link_condition(state: SysState, map: LinkMap, key: CapKey) -> bool {
    if map[key].back.is_none() {
        true
    } else {
        let back = map[key].back.unwrap();
        {
            &&& back != key
            &&& map.contains_key(back)
            &&& map[key].first_child ==> map[key].depth == map[back].depth + 1
            &&& map[key].first_child || (map[key].depth == map[back].depth && map[key].index
                < map[back].index)
            &&& (state.allow_broken_back_link(key, back) || {
                match map[key].first_child {
                    true => map[back].child == Some(key),
                    false => map[back].next == Some(key),
                }
            })
        }
    }
}

pub open spec fn next_link_condition(state: SysState, map: LinkMap, key: CapKey) -> bool {
    if map[key].next.is_none() {
        true
    } else {
        let next = map[key].next.unwrap();
        {
            &&& next != key
            &&& map.contains_key(next)
            &&& map[key].depth == map[next].depth && map[key].index > map[next].index
            &&& (state.allow_broken_next_link(key, next) || {
                map[next].back == Some(key) && map[next].first_child == false
            })
        }
    }
}

pub open spec fn child_link_condition(state: SysState, map: LinkMap, key: CapKey) -> bool {
    if map[key].child.is_none() {
        true
    } else {
        let child = map[key].child.unwrap();
        {
            &&& child != key
            &&& map.contains_key(child)
            &&& map[key].depth + 1 == map[child].depth
            &&& (state.allow_broken_child_link(key, child) || {
                map[child].back == Some(key) && map[child].first_child == true
            })
        }
    }
}

pub trait Token: Sized {
    spec fn addr(&self) -> usize;

    proof fn is_nonnull(tracked &self)
        ensures
            self.addr() != 0,
    ;

    spec fn cond(&self, next: usize, child: usize, back: usize, first_child: bool) -> bool;
}

pub open spec fn token_invariant<T: Token>(
    map: LinkMap,
    tokens: Map<CapKey, T>,
    key: CapKey,
) -> bool {
    let next = if map[key].next.is_none() {
        0
    } else {
        tokens[map[key].next.unwrap()].addr()
    };

    let child = if map[key].child.is_none() {
        0
    } else {
        tokens[map[key].child.unwrap()].addr()
    };

    let back = if map[key].back.is_none() {
        0
    } else {
        tokens[map[key].back.unwrap()].addr()
    };

    tokens[key].cond(next, child, back, map[key].first_child)
}

pub open spec fn revoke_back_fixed(map: LinkMap, key: CapKey) -> bool {
    map[key].back == Option::<CapKey>::None || {
        ||| (map[key].first_child && map[map[key].back.unwrap()].child == map[key].next)
        ||| (!map[key].first_child && map[map[key].back.unwrap()].next == map[key].next)
    }
}

pub open spec fn revoke_next_fixed(map: LinkMap, key: CapKey) -> bool {
    map[key].next == Option::<CapKey>::None || {
        &&& map[key].first_child == map[map[key].next.unwrap()].first_child
        &&& map[key].back == map[map[key].next.unwrap()].back
    }
}

pub open spec fn clean_links(map: LinkMap) -> bool {
    forall|key: CapKey|
        #![trigger map[key].child]
        #![trigger map[key].next]
        #![trigger map[key].back]
        map.contains_key(key) ==> {
            &&& next_link_condition(SysState::Clean, map, key)
            &&& back_link_condition(SysState::Clean, map, key)
            &&& child_link_condition(SysState::Clean, map, key)
        }
}

tokenized_state_machine!(LinkSystem<T: Token>{
    fields {
        #[sharding(variable)]
        pub map: LinkMap,

        #[sharding(variable)]
        pub all_tokens: Map<CapKey, T>,

        #[sharding(variable)]
        pub state: SysState,

        #[sharding(variable)]
        pub depth: nat,

        #[sharding(storage_map)]
        pub tokens: Map<CapKey, T>,
    }

    #[invariant]
    pub fn state_tokens_disjoint(&self) -> bool {
        self.tokens.dom().disjoint(self.state.dom())
    }

    #[invariant]
    pub fn token_invariant(&self) -> bool {
        forall |key: CapKey| self.map.contains_key(key) ==>
            #[trigger] token_invariant(self.map, self.all_tokens, key)
    }

    #[invariant]
    pub fn map_tokens(&self) -> bool {
        &&& self.map.dom() == self.tokens.dom().union(self.state.dom())
        &&& self.map.dom() == self.all_tokens.dom()
    }

    #[invariant]
    pub fn next_back(&self) -> bool {
        forall |key: CapKey| #[trigger] self.map.contains_key(key) ==>
            next_link_condition(self.state, self.map, key)
    }

    #[invariant]
    pub fn child_back(&self) -> bool {
        forall |key: CapKey| #[trigger] self.map.contains_key(key) ==>
            child_link_condition(self.state, self.map, key)
    }

    #[invariant]
    pub fn back_link(&self) -> bool {
        forall |key: CapKey| #[trigger] self.map.contains_key(key) ==>
            back_link_condition(self.state, self.map, key)
    }

    #[invariant]
    pub fn token_value(&self) -> bool {
        forall |key: CapKey| self.tokens.contains_key(key) ==>
            self.all_tokens[key] == #[trigger] self.tokens[key]
    }

    init!{
        empty() {
            init map = Map::empty();
            init all_tokens = Map::empty();
            init tokens = Map::empty();
            init state = SysState::Clean;
            init depth = 1;
        }
    }

    #[inductive(empty)]
    fn empty_inductive(post: Self) {
        assert(post.map.dom() =~= post.tokens.dom().union(post.state.dom()));
    }

    property!{
        clean_links() {
            require pre.state == SysState::Clean;
            assert(clean_links(pre.map));
        }
    }

    property!{
        token_invariant(key: CapKey) {
            assert(pre.map.contains_key(key) ==> token_invariant(pre.map, pre.all_tokens, key));
        }
    }

    property!{
        contains_next(parent: CapKey) {
            assert(pre.map.contains_key(parent) && pre.map[parent].next.is_some()
                ==> (pre.map[parent].next.unwrap() != parent && pre.map.contains_key(pre.map[parent].next.unwrap())));
        }
    }

    property!{
        contains_back(parent: CapKey) {
            assert(pre.map.contains_key(parent) && pre.map[parent].back.is_some()
                ==> (pre.map[parent].back.unwrap() != parent && pre.map.contains_key(pre.map[parent].back.unwrap())));
        }
    }

    property!{
        contains_child(parent: CapKey) {
            require pre.map.contains_key(parent);
            assert(pre.map[parent].child.is_some()
                ==> (pre.map[parent].child.unwrap() != parent && pre.map.contains_key(pre.map[parent].child.unwrap())));
        }
    }

    property!{
        weak_connections() {
            assert(decreasing::<Child>(pre.map));
            assert(decreasing::<Next>(pre.map));
        }
    }

    property!{
        depth_bound(key: CapKey) {
            require pre.map.contains_key(key);
            assert(pre.map[key].depth < pre.depth);
        }
    }

    #[invariant]
    pub fn addr_nonnull(&self) -> bool {
        forall |key: CapKey| self.map.contains_key(key) ==>
            #[trigger] self.all_tokens[key].addr() != 0
    }

    #[invariant]
    pub fn pos_depth(&self) -> bool {
        self.depth > 0
    }

    #[invariant]
    pub fn depth_bound(&self) -> bool {
        forall |key: CapKey| self.map.contains_key(key) ==>
            #[trigger] self.map[key].depth < self.depth
    }

    #[invariant]
    pub fn next_back_unequal(&self) -> bool {
        forall |key: CapKey| self.map.contains_key(key) ==>
            self.map[key].back.is_none() || #[trigger] self.map[key].next != self.map[key].back
    }

    property!{
        addr_nonnull(key: CapKey) {
            require pre.map.contains_key(key);
            assert(pre.all_tokens[key].addr() != 0);
        }
    }

    property!{
        borrow_token(key: CapKey) {
            require !pre.state.dom().contains(key);
            require pre.map.contains_key(key);

            assert(token_invariant(pre.map, pre.all_tokens, key));
            guard tokens >= [key => pre.all_tokens[key]];
        }
    }

    transition!{
        insert_root(key: CapKey, token: T) {
            let node = LinkedNode {
                first_child: false,
                back: None,
                next: None,
                child: None,
                depth: 0,
                index: 0,
            };

            require !pre.map.contains_key(key);
            require token_invariant(pre.map.insert(key, node), pre.all_tokens.insert(key, token), key);
            require token.addr() != 0;

            update map = pre.map.insert(key, node);
            update all_tokens = pre.all_tokens.insert(key, token);
            deposit tokens += [key => token];
        }
    }

    #[inductive(insert_root)]
    fn insert_root_inductive(pre: Self, post: Self, key: CapKey, token: T) {
        assert forall |key: CapKey| pre.map.contains_key(key)
        implies #[trigger] token_invariant(post.map, post.all_tokens, key)
        by {
            assert(token_invariant(pre.map, pre.all_tokens, key));
        };

        assert(post.map.dom() =~= post.tokens.dom().union(post.state.dom()));
    }

    transition!{
        insert_child(t: T, key: CapKey, parent: CapKey) {
            let inserted = LinkedNode {
                first_child: true,
                back: Some(parent),
                next: pre.map[parent].child,
                child: None,
                depth: pre.map[parent].depth + 1,
                index: next_index(pre.map, pre.map[parent].child),
            };

            let new_map = pre.map.insert(key, inserted);

            require token_invariant(new_map, pre.all_tokens.insert(key, t), key);
            require !pre.map.contains_key(key);
            require pre.map.contains_key(parent);
            require pre.state == SysState::Clean;
            require t.addr() != 0;

            deposit tokens += [key => t];
            withdraw tokens -= [parent => pre.all_tokens[parent]];

            if pre.map[parent].child.is_some() {
                let next = pre.map[parent].child.unwrap();
                update state = SysState::InsertChild { inserted: key, parent, next: LinkState::Unchanged(next) };
            } else {
                update state = SysState::InsertChild { inserted: key, parent, next: LinkState::Null };
            }

            update map = new_map;
            update all_tokens = pre.all_tokens.insert(key, t);
            update depth = vstd::math::max(pre.depth as int, inserted.depth + 1 as int) as nat;

            assert(decreasing::<Child>(new_map));
            assert(decreasing::<Next>(new_map));
        }
    }

    #[invariant]
    pub fn state_inv(&self) -> bool {
        match self.state {
            SysState::InsertChild { inserted, parent, next } => {
                let insert_node = LinkedNode {
                    first_child: true,
                    back: Some(parent),
                    next: self.map[parent].child,
                    child: None,
                    depth: self.map[parent].depth + 1,
                    index: next_index(self.map, self.map[parent].child),
                };

                {
                    &&& self.map.contains_key(parent) && self.map[parent].child == next.key()
                    &&& self.map.contains_key(inserted)
                    &&& Some(inserted) != next.key()
                    &&& self.map[inserted] == insert_node
                    &&& inserted != parent
                    &&& match next {
                        LinkState::Fixed(next) => self.map[next].back == Some(inserted) && !self.map[next].first_child,
                        _ => true
                    }
                }
            }
            SysState::RevokeSingle { key, back, next, first_child } => {
                &&& self.map.contains_key(key)
                &&& self.map[key].child.is_none()
                &&& first_child <==> self.map[key].first_child
                &&& back.key() == self.map[key].back
                &&& back.key().is_none() || back.fixed()
                    || (first_child && self.map[back.key().unwrap()].child == Some(key))
                    || (!first_child && self.map[back.key().unwrap()].next == Some(key))
                &&& next.key() == self.map[key].next
                &&& next.key().is_none() || next.fixed()
                    || (!self.map[next.key().unwrap()].first_child && self.map[next.key().unwrap()].back == Some(key))
                &&& next.key().is_none() || next.key() != back.key()
                &&& back.fixed() <==> revoke_back_fixed(self.map, key)
                &&& next.fixed() <==> revoke_next_fixed(self.map, key)
            }
            _ => true
        }
    }

    #[inductive(insert_child)]
    fn insert_child_inductive(pre: Self, post: Self, t: T, key: CapKey, parent: CapKey) {
        assert(post.map.dom() =~= post.tokens.dom().union(post.state.dom()));
        assert(next_link_condition(post.state, post.map, key));

        assert forall |other: CapKey| #[trigger] post.map.contains_key(other) && other != key
        implies
            token_invariant(post.map, pre.all_tokens, other) && post.all_tokens[other].addr() != 0
        by {
            assert(post.map[other] == pre.map[other]);
            assert(token_invariant(pre.map, pre.all_tokens, other));
            assert(pre.all_tokens[other].addr() != 0);
        };
    }

    transition! {
        insert_child_fix_next(inserted: CapKey, parent: CapKey) {
            let next_link = match pre.state {
                SysState::InsertChild { inserted: i, parent: p, next: LinkState::Unchanged(next) }
                if i == inserted && p == parent => Some(next),
                _ => None
            };

            require next_link.is_some();
            assert(next_link == pre.map[parent].child);
            let next = next_link.unwrap();

            withdraw tokens -= [next => pre.all_tokens[next]];

            update state = SysState::InsertChild { inserted, parent, next: LinkState::Taken(next) };
            assert(token_invariant(pre.map, pre.all_tokens, next));
        }
    }

    #[inductive(insert_child_fix_next)]
    fn insert_child_fix_next_inductive(pre: Self, post: Self, inserted: CapKey, parent: CapKey) {
        assert(post.map.dom() =~= post.tokens.dom().union(post.state.dom()));
    }

    transition! {
        insert_child_finish_next(token: T, inserted: CapKey, parent: CapKey, next: CapKey) {
            let next_node = pre.map[next];
            let new_map = pre.map
                .insert(next, LinkedNode { back: Some(inserted), first_child: false, ..next_node});

            require pre.state == SysState::InsertChild { inserted, parent, next: LinkState::Taken(next) };
            require token.addr() == pre.all_tokens[next].addr();
            require token_invariant(new_map, pre.all_tokens.insert(next, token), next);

            deposit tokens += [next => token];
            update state = SysState::InsertChild { inserted, parent, next: LinkState::Fixed(next) };
            update map = new_map;
            update all_tokens = pre.all_tokens.insert(next, token);

            assert(decreasing::<Child>(new_map));
            assert(decreasing::<Next>(new_map));
        }
    }

    #[inductive(insert_child_finish_next)]
    fn insert_child_finish_next_inductive(pre: Self, post: Self, token: T, inserted: CapKey, parent: CapKey, next: CapKey) {
        assert(post.map.dom() =~= post.tokens.dom().union(post.state.dom()));

        assert forall |other: CapKey| #[trigger] post.map.contains_key(other) && other != next
        implies token_invariant(post.map, pre.all_tokens, other) && post.all_tokens[other].addr() != 0
        by {
            assert(post.map[other] == pre.map[other]);
            assert(token_invariant(pre.map, pre.all_tokens, other));
            assert(pre.all_tokens[other].addr() != 0);
        };
    }

    transition! {
        finish_insert(p: T, inserted: CapKey, parent: CapKey) {
            let parent_node = pre.map[parent];
            let new_map = pre.map.insert(parent, LinkedNode { child: Some(inserted), ..parent_node });

            require p.addr() == pre.all_tokens[parent].addr();
            require token_invariant(new_map, pre.all_tokens.insert(parent, p), parent);
            require match pre.state {
                SysState::InsertChild { inserted: i, parent: p, next } => {
                    p == parent && i == inserted && next.fixed()
                }
                _ => false
            };

            deposit tokens += [parent => p];
            update state = SysState::Clean;
            update map = new_map;
            update all_tokens = pre.all_tokens.insert(parent, p);

            assert(clean_links(new_map));
        }
    }

    #[inductive(finish_insert)]
    fn finish_insert_inductive(pre: Self, post: Self, p: T, inserted: CapKey, parent: CapKey) {
        assert(post.map.dom() =~= post.tokens.dom().union(post.state.dom()));

        assert forall |other: CapKey| #[trigger] post.map.contains_key(other) && other != parent
        implies token_invariant(post.map, pre.all_tokens, other) && post.all_tokens[other].addr() != 0
        by {
            assert(post.map[other] == pre.map[other]);
            assert(token_invariant(pre.map, pre.all_tokens, other));
            assert(pre.all_tokens[other].addr() != 0);
        };
    }

    transition! {
        revoke_single(key: CapKey) {
            require pre.state == SysState::Clean;
            require pre.map.contains_key(key);
            require pre.map[key].child == Option::<CapKey>::None;

            withdraw tokens -= [key => pre.all_tokens[key]];
            let back = match pre.map[key].back {
                None => LinkState::Null,
                Some(back) => LinkState::Unchanged(back),
            };
            let next = match pre.map[key].next {
                None => LinkState::Null,
                Some(next) => LinkState::Unchanged(next),
            };

            update state = SysState::RevokeSingle { key, back, next, first_child: pre.map[key].first_child };
            assert(token_invariant(pre.map, pre.all_tokens, key));
        }
    }

    #[inductive(revoke_single)]
    fn revoke_single_inductive(pre: Self, post: Self, key: CapKey) {
        assert(post.state.dom() =~= set![key]);
        assert(post.map.dom() =~= post.tokens.dom().union(post.state.dom()));
    }

    transition! {
        revoke_take_back() {
            let state = match pre.state {
                SysState::RevokeSingle { key, next, back: LinkState::Unchanged(back), first_child } => {
                    Some((key, next, back, first_child))
                }
                _ => None
            };

            require state.is_some();
            let (key, next, back, first_child) = state.unwrap();

            update state = SysState::RevokeSingle { key, next, back: LinkState::Taken(back), first_child };

            assert(pre.map.contains_key(back));
            assert(!pre.state.dom().contains(back));

            withdraw tokens -= [back => pre.all_tokens[back]];
            assert(token_invariant(pre.map, pre.all_tokens, back));
        }
    }

    #[inductive(revoke_take_back)]
    fn revoke_take_back_inductive(pre: Self, post: Self) {
        assert(post.map.dom() =~= post.tokens.dom().union(post.state.dom()));
    }

    transition! {
        revoke_take_next() {
            let state = match pre.state {
                SysState::RevokeSingle { key, next: LinkState::Unchanged(next), back, first_child } => {
                    Some((key, next, back, first_child))
                }
                _ => None
            };

            require state.is_some();
            let (key, next, back, first_child) = state.unwrap();

            update state = SysState::RevokeSingle { key, next: LinkState::Taken(next), back, first_child };

            assert(pre.map.contains_key(next));
            assert(!pre.state.dom().contains(next));

            withdraw tokens -= [next => pre.all_tokens[next]];
            assert(token_invariant(pre.map, pre.all_tokens, next));
        }
    }

    #[inductive(revoke_take_next)]
    fn revoke_take_next_inductive(pre: Self, post: Self) {
        assert(post.map.dom() =~= post.tokens.dom().union(post.state.dom()));
    }

    transition! {
        revoke_put_back(t: T) {
            let state = match pre.state {
                SysState::RevokeSingle { key, next, back: LinkState::Taken(back), first_child } => {
                    Some((key, next, back, first_child))
                }
                _ => None
            };

            require state.is_some();
            let (key, next, back, first_child) = state.unwrap();

            let new_back = match first_child {
                true => LinkedNode { child: pre.map[key].next, ..pre.map[back] },
                false => LinkedNode { next: pre.map[key].next, ..pre.map[back] }
            };

            let new_map = pre.map.insert(back, new_back);
            require t.addr() == pre.all_tokens[back].addr();
            require token_invariant(new_map, pre.all_tokens.insert(back, t), back);
            assert(revoke_back_fixed(new_map, key));

            deposit tokens += [back => t];
            update state = SysState::RevokeSingle { key, next, back: LinkState::Fixed(back), first_child };
            update map = new_map;
            update all_tokens = pre.all_tokens.insert(back, t);
        }
    }

    #[inductive(revoke_put_back)]
    fn revoke_put_back_inductive(pre: Self, post: Self, t: T) {
        assert(post.map.dom() =~= post.tokens.dom().union(post.state.dom()));

        let (key, next, back, first_child) = match pre.state {
            SysState::RevokeSingle { key, next, back: LinkState::Taken(back), first_child } => {
                (key, next, back, first_child)
            }
            _ => arbitrary()
        };

        if first_child {
            assert(pre.map[back].back == post.map[back].back);

            if pre.map[back].back.is_some() {
                let bback = pre.map[back].back.unwrap();
                assert(back_link_condition(pre.state, pre.map, back));
                assert(pre.map[bback].depth <= pre.map[back].depth);

                assert(pre.map[back].depth < pre.map[key].depth);

                if pre.map[key].next.is_some() {
                    let next = pre.map[key].next.unwrap();
                    assert(pre.map[next].depth == pre.map[key].depth);

                    assert(next != bback);
                }
            }
        }

        assert forall |other: CapKey| #[trigger] post.map.contains_key(other) && other != back
        implies {
            &&& token_invariant(post.map, pre.all_tokens, other)
            &&& post.all_tokens[other].addr() != 0
        }
        by {
            assert(post.map[other] == pre.map[other]);
            assert(token_invariant(pre.map, pre.all_tokens, other));
            assert(pre.all_tokens[other].addr() != 0);
        };
    }

    transition! {
        revoke_put_next(t: T) {
            let state = match pre.state {
                SysState::RevokeSingle { key, next: LinkState::Taken(next), back, first_child } => {
                    Some((key, next, back, first_child))
                }
                _ => None
            };

            require state.is_some();
            let (key, next, back, first_child) = state.unwrap();

            let new_next = LinkedNode {
                back: pre.map[key].back,
                first_child: pre.map[key].first_child,
                ..pre.map[next]
            };

            let new_map = pre.map.insert(next, new_next);
            require t.addr() == pre.all_tokens[next].addr();
            require token_invariant(new_map, pre.all_tokens.insert(next, t), next);
            assert(revoke_next_fixed(new_map, key));

            deposit tokens += [next => t];
            update state = SysState::RevokeSingle { key, next: LinkState::Fixed(next), back, first_child };
            update map = new_map;
            update all_tokens = pre.all_tokens.insert(next, t);
        }
    }

    #[inductive(revoke_put_next)]
    fn revoke_put_next_inductive(pre: Self, post: Self, t: T) {
        assert(post.map.dom() =~= post.tokens.dom().union(post.state.dom()));

        let (key, next, back, first_child) = match pre.state {
            SysState::RevokeSingle { key, next: LinkState::Taken(next), back, first_child } => {
                (key, next, back, first_child)
            }
            _ => arbitrary()
        };

        if pre.map[next].next.is_some() {
            let nnext = pre.map[next].next.unwrap();
            assert(next_link_condition(pre.state, pre.map, next));
            assert(pre.map[next].back == Some(key));
            assert(pre.map[key].index > pre.map[next].index);
            assert(pre.map[next].index > pre.map[nnext].index);
            assert(key != nnext);
        }

        assert forall |other: CapKey| #[trigger] post.map.contains_key(other) && other != next
        implies token_invariant(post.map, pre.all_tokens, other) && post.all_tokens[other].addr() != 0
        by {
            assert(post.map[other] == pre.map[other]);
            assert(token_invariant(pre.map, pre.all_tokens, other));
            assert(pre.all_tokens[other].addr() != 0);
        };
    }

    transition! {
        finish_revoke_single(removed: CapKey) {
            require match pre.state {
                SysState::RevokeSingle { key, back, next, first_child } => key == removed && back.fixed() && next.fixed(),
                _ => false
            };

            update state = SysState::Clean;
            update map = pre.map.remove(removed);
            update all_tokens = pre.all_tokens.remove(removed);
        }
    }

    #[inductive(finish_revoke_single)]
    fn finish_revoke_single_inductive(pre: Self, post: Self, removed: CapKey) {
        assert(post.map.dom() =~= post.tokens.dom().union(post.state.dom()));

        assert(revoke_back_fixed(pre.map, removed));
        assert(revoke_next_fixed(pre.map, removed));

        let (back_link, next_link) = match pre.state {
            SysState::RevokeSingle { back, next, .. } => (back, next),
            _ => arbitrary()
        };

        if let LinkState::Fixed(back) = back_link {
            assert(back == pre.map[removed].back.unwrap());
            assert(next_link_condition(SysState::Clean, post.map, back));
            assert(child_link_condition(SysState::Clean, post.map, back));
        }

        if let LinkState::Fixed(next) = next_link {
            assert(next == pre.map[removed].next.unwrap());
            assert(back_link_condition(SysState::Clean, post.map, next));
        }

        assert(post.next_back());
        assert(post.child_back());
        assert(post.back_link());

        assert forall |other: CapKey| #[trigger] post.map.contains_key(other) && other != removed
        implies token_invariant(post.map, pre.all_tokens, other) && post.all_tokens[other].addr() != 0
        by {
            assert(post.map[other] == pre.map[other]);
            assert(token_invariant(pre.map, pre.all_tokens, other));
            assert(pre.all_tokens[other].addr() != 0);
        };
    }
});

} // verus!
