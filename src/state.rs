use state_machines_macros::tokenized_state_machine;
use vstd::prelude::*;

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

pub type LinkMap<T> = Map<CapKey, (T, LinkedNode)>;

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
    InsertFirst { inserted: CapKey, parent: CapKey },
    InsertNext { inserted: CapKey, parent: CapKey, next: CapKey },
    InsertFinish { inserted: CapKey, parent: CapKey },
    RevokeSingle { key: CapKey, back: LinkState, next: LinkState, first_child: bool },
}

impl SysState {
    pub open spec fn dom(self) -> Set<CapKey> {
        match self {
            SysState::Clean => Set::empty(),
            SysState::InsertFirst { inserted, parent } => set![parent],
            SysState::InsertFinish { inserted, parent } => set![parent],
            SysState::InsertNext { inserted, parent, next } => set![parent, next],
            SysState::RevokeSingle { key, back, next, first_child } => {
                back.dom().union(next.dom()).insert(key)
            },
        }
    }

    pub open spec fn allow_broken_back_link(self, key: CapKey, target: CapKey) -> bool {
        match self {
            SysState::Clean => false,
            SysState::InsertFirst { inserted, parent } => key == inserted,
            SysState::InsertFinish { inserted, parent } => key == inserted,
            SysState::InsertNext { inserted, parent, next: child } => key == inserted,
            SysState::RevokeSingle { key: removed, back, next, first_child } => {
                next == LinkState::Fixed(key) || key == removed
            },
        }
    }

    pub open spec fn allow_broken_next_link(self, key: CapKey, target: CapKey) -> bool {
        match self {
            SysState::Clean => false,
            SysState::InsertFirst { inserted, parent } => key == inserted,
            SysState::InsertNext { inserted, parent, next: child } => key == inserted,
            SysState::InsertFinish { inserted, parent } => false,
            SysState::RevokeSingle { key: removed, back, next, first_child } => {
                (back == LinkState::Fixed(key) && !first_child) || key == removed
            },
        }
    }

    pub open spec fn allow_broken_child_link(self, key: CapKey, target: CapKey) -> bool {
        match self {
            SysState::Clean => false,
            SysState::InsertFirst { inserted, parent } => false,
            SysState::InsertNext { inserted, parent, next } => false,
            SysState::InsertFinish { inserted, parent } => key == parent,
            SysState::RevokeSingle { key: removed, back, next, first_child } => {
                (back == LinkState::Fixed(key) && first_child) || key == removed
            },
        }
    }
}

pub open spec fn back_link_condition<T>(
    state: SysState,
    map: LinkMap<T>,
    key: CapKey,
) -> bool {
    if map[key].1.back.is_none() {
        true
    } else {
        let back = map[key].1.back.unwrap(); {
            &&& back != key
            &&& map.contains_key(back)
            &&& map[key].1.first_child ==> map[key].1.depth == map[back].1.depth + 1
            &&& map[key].1.first_child || (map[key].1.depth == map[back].1.depth && map[key].1.index < map[back].1.index)
            &&& (state.allow_broken_back_link(key, back) || {
                match map[key].1.first_child {
                    true => map[back].1.child == Some(key),
                    false => map[back].1.next == Some(key),
                }
            })
        }
    }
}

pub open spec fn next_link_condition<T>(
    state: SysState,
    map: LinkMap<T>,
    key: CapKey,
) -> bool {
    if map[key].1.next.is_none() {
        true
    } else {
        let next = map[key].1.next.unwrap(); {
            &&& next != key
            &&& map.contains_key(next)
            &&& map[key].1.depth == map[next].1.depth && map[key].1.index > map[next].1.index
            &&& (state.allow_broken_next_link(key, next) || {
                map[next].1.back == Some(key) && map[next].1.first_child == false
            })
        }
    }
}

pub open spec fn weak_next_link_condition<T>(
    map: LinkMap<T>,
    key: CapKey,
) -> bool {
    if map[key].1.next.is_none() {
        true
    } else {
        let next = map[key].1.next.unwrap(); {
            &&& next != key
            &&& map.contains_key(next)
            &&& map[key].1.depth == map[next].1.depth
            &&& map[key].1.index > map[next].1.index
        }
    }
}

pub open spec fn child_link_condition<T>(
    state: SysState,
    map: LinkMap<T>,
    key: CapKey,
) -> bool {
    if map[key].1.child.is_none() {
        true
    } else {
        let child = map[key].1.child.unwrap(); {
            &&& child != key
            &&& map.contains_key(child)
            &&& map[key].1.depth < map[child].1.depth
            &&& (state.allow_broken_child_link(key, child) || {
                map[child].1.back == Some(key) && map[child].1.first_child == true
            })
        }

    }
}

pub open spec fn next_index<T>(map: LinkMap<T>, key: Option<CapKey>) -> nat {
    if key.is_some() {
        map[key.unwrap()].1.index + 1
    }
    else {
        0
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

pub open spec fn token_invariant<T: Token>(map: LinkMap<T>, key: CapKey) -> bool {
    let next = if map[key].1.next.is_none() {
        0
    } else {
        map[map[key].1.next.unwrap()].0.addr()
    };

    let child = if map[key].1.child.is_none() {
        0
    } else {
        map[map[key].1.child.unwrap()].0.addr()
    };

    let back = if map[key].1.back.is_none() {
        0
    } else {
        map[map[key].1.back.unwrap()].0.addr()
    };

    map[key].0.cond(next, child, back, map[key].1.first_child)
}

pub open spec fn revoke_back_fixed<T>(map: LinkMap<T>, key: CapKey) -> bool {
    map[key].1.back == Option::<CapKey>::None || {
        ||| (map[key].1.first_child && map[map[key].1.back.unwrap()].1.child == map[key].1.next)
        ||| (!map[key].1.first_child && map[map[key].1.back.unwrap()].1.next == map[key].1.next)
    }
}

pub open spec fn revoke_next_fixed<T>(map: LinkMap<T>, key: CapKey) -> bool {
    map[key].1.next == Option::<CapKey>::None || {
        &&& map[key].1.first_child == map[map[key].1.next.unwrap()].1.first_child
        &&& map[key].1.back == map[map[key].1.next.unwrap()].1.back
    }
}

tokenized_state_machine!(LinkSystem<T: Token>{
    fields {
        #[sharding(variable)]
        pub map: LinkMap<T>,

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
            #[trigger] token_invariant(self.map, key)
    }

    #[invariant]
    pub fn map_tokens(&self) -> bool {
        self.map.dom() == self.tokens.dom().union(self.state.dom())
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
            self.map[key].0 == #[trigger] self.tokens[key]
    }

    init!{
        empty() {
            init map = Map::empty();
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
        token_invariant(key: CapKey) {
            assert(pre.map.contains_key(key) ==> token_invariant(pre.map, key));
        }
    }

    property!{
        contains_next(parent: CapKey) {
            assert(pre.map.contains_key(parent) && pre.map[parent].1.next.is_some()
                ==> (pre.map[parent].1.next.unwrap() != parent && pre.map.contains_key(pre.map[parent].1.next.unwrap())));
        }
    }

    property!{
        contains_back(parent: CapKey) {
            assert(pre.map.contains_key(parent) && pre.map[parent].1.back.is_some()
                ==> (pre.map[parent].1.back.unwrap() != parent && pre.map.contains_key(pre.map[parent].1.back.unwrap())));
        }
    }

    property!{
        contains_child(parent: CapKey) {
            require pre.map.contains_key(parent);
            assert(pre.map[parent].1.child.is_some()
                ==> (pre.map[parent].1.child.unwrap() != parent && pre.map.contains_key(pre.map[parent].1.child.unwrap())));
        }
    }

    #[invariant]
    pub fn addr_nonnull(&self) -> bool {
        forall |key: CapKey| self.map.contains_key(key) ==>
            #[trigger] self.map[key].0.addr() != 0
    }

    #[invariant]
    pub fn pos_depth(&self) -> bool {
        self.depth > 0
    }

    #[invariant]
    pub fn depth_bound(&self) -> bool {
        forall |key: CapKey| self.map.contains_key(key) ==>
            #[trigger] self.map[key].1.depth < self.depth
    }

    #[invariant]
    pub fn next_back_unequal(&self) -> bool {
        forall |key: CapKey| self.map.contains_key(key) ==>
            self.map[key].1.back.is_none() || #[trigger] self.map[key].1.next != self.map[key].1.back
    }

    property!{
        addr_nonnull(key: CapKey) {
            require pre.map.contains_key(key);
            assert(pre.map[key].0.addr() != 0);
        }
    }

    property!{
        borrow_token(key: CapKey) {
            require !pre.state.dom().contains(key);
            require pre.map.contains_key(key);

            assert(token_invariant(pre.map, key));
            guard tokens >= [key => pre.map[key].0];
        }
    }

    transition!{
        insert_child(t: T, key: CapKey, parent: CapKey) {
            let inserted = LinkedNode {
                first_child: true,
                back: Some(parent),
                next: pre.map[parent].1.child,
                child: None,
                depth: pre.map[parent].1.depth + 1,
                index: next_index(pre.map, pre.map[parent].1.child),
            };

            let new_map = pre.map.insert(key, (t, inserted));

            require token_invariant(new_map, key);
            require !pre.map.contains_key(key);
            require pre.map.contains_key(parent);
            require pre.state == SysState::Clean;
            require t.addr() != 0;

            deposit tokens += [key => t];
            withdraw tokens -= [parent => pre.map[parent].0];

            if pre.map[parent].1.child == Option::<CapKey>::None {
                update state = SysState::InsertFinish { inserted: key, parent };
            }
            else {
                update state = SysState::InsertFirst { inserted: key, parent };
            }

            update map = new_map;
            update depth = vstd::math::max(pre.depth as int, inserted.depth + 1 as int) as nat;
        }
    }

    #[invariant]
    pub fn state_inv(&self) -> bool {
        match self.state {
            SysState::InsertFirst { inserted, parent } => {
                let insert_node = LinkedNode {
                    first_child: true,
                    back: Some(parent),
                    next: self.map[parent].1.child,
                    child: None,
                    depth: self.map[parent].1.depth + 1,
                    index: next_index(self.map, self.map[parent].1.child),
                };

                self.map.contains_key(parent)
                && self.map.contains_key(inserted)
                && self.map[inserted].1 == insert_node
                && self.map[parent].1.child.is_some()
                && inserted != parent
            }
            SysState::InsertFinish { inserted, parent } => {
                let insert_node = LinkedNode {
                    first_child: true,
                    back: Some(parent),
                    next: self.map[parent].1.child,
                    child: None,
                    depth: self.map[parent].1.depth + 1,
                    index: next_index(self.map, self.map[parent].1.child),
                };

                self.map.contains_key(parent)
                && self.map.contains_key(inserted)
                && self.map[inserted].1 == insert_node
                && inserted != parent
            }
            SysState::InsertNext { inserted, parent, next } => {
                let insert_node = LinkedNode {
                    first_child: true,
                    back: Some(parent),
                    next: Some(next),
                    child: None,
                    depth: self.map[parent].1.depth + 1,
                    index: next_index(self.map, self.map[parent].1.child),
                };

                self.map.contains_key(parent) && self.map.contains_key(inserted) && self.map.contains_key(next)
                && inserted != parent && inserted != next && parent != next
                && self.map[inserted].1 == insert_node
                && self.map[parent].1.child == Some(next)
            }
            SysState::RevokeSingle { key, back, next, first_child } => {
                &&& self.map.contains_key(key)
                &&& self.map[key].1.child.is_none()
                &&& first_child <==> self.map[key].1.first_child
                &&& back.key() == self.map[key].1.back
                &&& back.key().is_none() || back.fixed()
                    || (first_child && self.map[back.key().unwrap()].1.child == Some(key))
                    || (!first_child && self.map[back.key().unwrap()].1.next == Some(key))
                &&& next.key() == self.map[key].1.next
                &&& next.key().is_none() || next.fixed()
                    || (!self.map[next.key().unwrap()].1.first_child && self.map[next.key().unwrap()].1.back == Some(key))
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
            token_invariant(post.map, other) && post.map[other].0.addr() != 0
        by {
            assert(post.map[other] == pre.map[other]);
            assert(token_invariant(pre.map, other));
            assert(pre.map[other].0.addr() != 0);
        };
    }

    transition! {
        insert_child_fix_next(inserted: CapKey, parent: CapKey) {
            require pre.state == SysState::InsertFirst { inserted, parent };
            let next = pre.map[parent].1.child.unwrap();
            withdraw tokens -= [next => pre.map[next].0];

            update state = SysState::InsertNext { inserted, parent, next };
            assert(token_invariant(pre.map, next));
        }
    }

    #[inductive(insert_child_fix_next)]
    fn insert_child_fix_next_inductive(pre: Self, post: Self, inserted: CapKey, parent: CapKey) {
        assert(post.map.dom() =~= post.tokens.dom().union(post.state.dom()));
    }

    transition! {
        insert_child_finish_next(token: T, inserted: CapKey, parent: CapKey, next: CapKey) {
            let (old, next_node) = pre.map[next];
            let new_map = pre.map
                .insert(next, (token, LinkedNode { back: Some(inserted), first_child: false, ..next_node}));

            require pre.state == SysState::InsertNext { inserted, parent, next };
            require token.addr() == old.addr();
            require token_invariant(new_map, next);

            deposit tokens += [next => token];
            update state = SysState::InsertFinish { inserted, parent };
            update map = new_map;
        }
    }

    #[inductive(insert_child_finish_next)]
    fn insert_child_finish_next_inductive(pre: Self, post: Self, token: T, inserted: CapKey, parent: CapKey, next: CapKey) {
        assert(post.map.dom() =~= post.tokens.dom().union(post.state.dom()));

        assert forall |other: CapKey| #[trigger] post.map.contains_key(other) && other != next
        implies token_invariant(post.map, other) && post.map[other].0.addr() != 0
        by {
            assert(post.map[other] == pre.map[other]);
            assert(token_invariant(pre.map, other));
            assert(pre.map[other].0.addr() != 0);
        };
    }

    transition! {
        finish_insert(p: T, inserted: CapKey, parent: CapKey) {
            let (old, parent_node) = pre.map[parent];
            let new_map = pre.map.insert(parent, (p, LinkedNode { child: Some(inserted), ..parent_node }));

            require p.addr() == old.addr();
            require token_invariant(new_map, parent);
            require pre.state == SysState::InsertFinish { inserted, parent };

            deposit tokens += [parent => p];
            update state = SysState::Clean;
            update map = new_map;
        }
    }

    #[inductive(finish_insert)]
    fn finish_insert_inductive(pre: Self, post: Self, p: T, inserted: CapKey, parent: CapKey) {
        assert(post.map.dom() =~= post.tokens.dom().union(post.state.dom()));

        assert forall |other: CapKey| #[trigger] post.map.contains_key(other) && other != parent
        implies token_invariant(post.map, other) && post.map[other].0.addr() != 0
        by {
            assert(post.map[other] == pre.map[other]);
            assert(token_invariant(pre.map, other));
            assert(pre.map[other].0.addr() != 0);
        };
    }

    transition! {
        revoke_single(key: CapKey) {
            require pre.state == SysState::Clean;
            require pre.map.contains_key(key);
            require pre.map[key].1.child == Option::<CapKey>::None;

            withdraw tokens -= [key => pre.map[key].0];
            let back = match pre.map[key].1.back {
                None => LinkState::Null,
                Some(back) => LinkState::Unchanged(back),
            };
            let next = match pre.map[key].1.next {
                None => LinkState::Null,
                Some(next) => LinkState::Unchanged(next),
            };

            update state = SysState::RevokeSingle { key, back, next, first_child: pre.map[key].1.first_child };
            assert(token_invariant(pre.map, key));
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

            withdraw tokens -= [back => pre.map[back].0];
            assert(token_invariant(pre.map, back));
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

            withdraw tokens -= [next => pre.map[next].0];
            assert(token_invariant(pre.map, next));
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
                true => LinkedNode { child: pre.map[key].1.next, ..pre.map[back].1 },
                false => LinkedNode { next: pre.map[key].1.next, ..pre.map[back].1 }
            };

            let new_map = pre.map.insert(back, (t, new_back));
            require t.addr() == pre.map[back].0.addr();
            require token_invariant(new_map, back);
            assert(revoke_back_fixed(new_map, key));

            deposit tokens += [back => t];
            update state = SysState::RevokeSingle { key, next, back: LinkState::Fixed(back), first_child };
            update map = new_map;
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
            assert(pre.map[back].1.back == post.map[back].1.back);

            if pre.map[back].1.back.is_some() {
                let bback = pre.map[back].1.back.unwrap();
                assert(back_link_condition(pre.state, pre.map, back));
                assert(pre.map[bback].1.depth <= pre.map[back].1.depth);

                assert(pre.map[back].1.depth < pre.map[key].1.depth);

                if pre.map[key].1.next.is_some() {
                    let next = pre.map[key].1.next.unwrap();
                    assert(pre.map[next].1.depth == pre.map[key].1.depth);

                    assert(next != bback);
                }
            }
        }

        assert forall |other: CapKey| #[trigger] post.map.contains_key(other) && other != back
        implies {
            &&& token_invariant(post.map, other)
            &&& post.map[other].0.addr() != 0
        }
        by {
            assert(post.map[other] == pre.map[other]);
            assert(token_invariant(pre.map, other));
            assert(pre.map[other].0.addr() != 0);
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
                back: pre.map[key].1.back,
                first_child: pre.map[key].1.first_child,
                ..pre.map[next].1
            };

            let new_map = pre.map.insert(next, (t, new_next));
            require t.addr() == pre.map[next].0.addr();
            require token_invariant(new_map, next);
            assert(revoke_next_fixed(new_map, key));

            deposit tokens += [next => t];
            update state = SysState::RevokeSingle { key, next: LinkState::Fixed(next), back, first_child };
            update map = new_map;
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

        if pre.map[next].1.next.is_some() {
            let nnext = pre.map[next].1.next.unwrap();
            assert(next_link_condition(pre.state, pre.map, next));
            assert(pre.map[next].1.back == Some(key));
            assert(pre.map[key].1.index > pre.map[next].1.index);
            assert(pre.map[next].1.index > pre.map[nnext].1.index);
            assert(key != nnext);
        }

        assert forall |other: CapKey| #[trigger] post.map.contains_key(other) && other != next
        implies token_invariant(post.map, other) && post.map[other].0.addr() != 0
        by {
            assert(post.map[other] == pre.map[other]);
            assert(token_invariant(pre.map, other));
            assert(pre.map[other].0.addr() != 0);
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
            assert(back == pre.map[removed].1.back.unwrap());
            assert(next_link_condition(SysState::Clean, post.map, back));
            assert(child_link_condition(SysState::Clean, post.map, back));
        }

        if let LinkState::Fixed(next) = next_link {
            assert(next == pre.map[removed].1.next.unwrap());
            assert(back_link_condition(SysState::Clean, post.map, next));
        }

        assert(post.next_back());
        assert(post.child_back());
        assert(post.back_link());

        assert forall |other: CapKey| #[trigger] post.map.contains_key(other) && other != removed
        implies token_invariant(post.map, other) && post.map[other].0.addr() != 0
        by {
            assert(post.map[other] == pre.map[other]);
            assert(token_invariant(pre.map, other));
            assert(pre.map[other].0.addr() != 0);
        };
    }
});

} // verus!
