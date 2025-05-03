use vstd::prelude::*;

verus! {

pub trait Link {
    spec fn spec_is_null(&self) -> bool;
    spec fn link_count(&self) -> int;

    #[verifier::when_used_as_spec(spec_is_null)]
    fn is_null(&self) -> bool
    returns self.is_null();
}

pub struct Node<Link, Inner> {
    pub inner: Inner,
    pub left: Link,
    pub right: Link,
    pub parent: Link,
    pub child: Link,
}

pub trait LinkSystem {
    type Link: Link;
    type Inner;

    spec fn valid(&self, link: Self::Link) -> bool;

    open spec fn wf_node(&self, node: Node<Self::Link, Self::Inner>) -> bool {
        self.valid(node.child)
        && self.valid(node.parent)
        && self.valid(node.left)
        && self.valid(node.right)
    }

    open spec fn decreasing_right(&self) -> bool {
        forall |node: Node<Self::Link, Self::Inner>| !node.right.is_null() ==>
            #[trigger] node.right.link_count() > self.follow(node.right).right.link_count()
    }

    spec fn follow(&self, link: Self::Link) -> Node<Self::Link, Self::Inner>
    recommends !link.is_null();
}

#[via_fn]
proof fn right_neighbours_decreases_proof<S: LinkSystem>(this: &S, node: Node<S::Link, S::Inner>)
{
    if !node.right.is_null() {
        assert(decreases_to!(node.right.link_count() => this.follow(node.right).right.link_count())) by { };
    }
}

pub open spec(checked) fn right_neighbours<S: LinkSystem>(this: &S, node: Node<S::Link, S::Inner>) -> Seq<Node<S::Link, S::Inner>>
decreases node.right.link_count()
    when this.decreasing_right()
    via right_neighbours_decreases_proof::<S>
{
    if !node.right.is_null() {
        let direct = this.follow(node.right);
        let indirect = right_neighbours(this, direct);
        Seq::insert(indirect, 0, direct)
    }
    else {
        Seq::empty()
    }
}

}
