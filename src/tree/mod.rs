//! Provides a catch-all for tree implementations not currently implemented in stdlib.

extern crate alloc;

use alloc::boxed::Box;
use core::ptr::NonNull;

pub mod binary;
pub mod redblack;

/// Represents a type that has a Color representation in the tree.
trait Directional {
    /// Returns the direction of a node if the node is not the root of the tree.
    /// Otherwise `None` is returned.
    fn direction(&self) -> Option<Direction>;
}

/// Direction represents the directional branch that a given child is on for
/// a given node.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Direction {
    Left,
    Right,
}

/// NodeRef represents a Non-Null pointer to a Node.
#[derive(PartialEq)]
pub(crate) struct NodeRef<T, A>(NonNull<Node<T, A>>);

impl<T, A> NodeRef<T, A> {
    /// Consumes the enclosing NodeRef, returning the wrapped raw pointer.
    fn as_ptr(self) -> *mut Node<T, A> {
        self.0.as_ptr()
    }
}

impl<T, A> From<NonNull<Node<T, A>>> for NodeRef<T, A> {
    fn from(ptr: NonNull<Node<T, A>>) -> Self {
        Self(ptr)
    }
}

impl<T, A> From<Node<T, A>> for NodeRef<T, A> {
    fn from(node: Node<T, A>) -> Self {
        let boxed_node = Box::new(node);
        Self::from(boxed_node)
    }
}

impl<T, A> From<Box<Node<T, A>>> for NodeRef<T, A> {
    fn from(node: Box<Node<T, A>>) -> Self {
        NonNull::new(Box::into_raw(node))
            .map(NodeRef::from)
            .expect("Box points to an invalid memory location")
    }
}

impl<T, A> Clone for NodeRef<T, A> {
    fn clone(&self) -> Self {
        Self(self.0)
    }
}

impl<T, A> Copy for NodeRef<T, A> {}

impl<T, A> Directional for NodeRef<T, A>
where
    Node<T, A>: Directional,
{
    fn direction(&self) -> Option<Direction> {
        unsafe {
            let node = self.0.as_ref();
            node.direction()
        }
    }
}

impl<T, A> core::convert::AsRef<Node<T, A>> for NodeRef<T, A> {
    fn as_ref(&self) -> &Node<T, A> {
        unsafe { self.0.as_ref() }
    }
}

impl<T, A> core::convert::AsMut<Node<T, A>> for NodeRef<T, A> {
    fn as_mut(&mut self) -> &mut Node<T, A> {
        unsafe { self.0.as_mut() }
    }
}

impl<T, A> core::fmt::Debug for NodeRef<T, A>
where
    T: core::fmt::Debug,
    A: core::fmt::Debug,
{
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_tuple("NodeRef")
            .field(unsafe { &self.0.as_ref().inner })
            .finish()
    }
}

/// Node represents an interior node to the Binary Tree, storing
/// information about direct ancestor/descendent nodes as well as an inner
/// value denoted by type V.
#[derive(Debug, Clone)]
pub(crate) struct Node<T, A> {
    /// An inner value stored in the tree.
    inner: T,
    /// An optional parent node. A value of None signifies that this node is
    /// the root.
    parent: Option<NodeRef<T, A>>,
    /// An optional left-side direcitonaldescendant node.
    left: Option<NodeRef<T, A>>,
    /// An optional right-side direcitonaldescendant node.
    right: Option<NodeRef<T, A>>,
    attributes: A,
}
impl<T, A> Node<T, A>
where
    T: PartialEq,
{
    pub(crate) fn new(
        inner: T,
        parent: Option<NodeRef<T, A>>,
        left: Option<NodeRef<T, A>>,
        right: Option<NodeRef<T, A>>,
        attributes: A,
    ) -> Self {
        Self {
            inner,
            parent,
            left,
            right,
            attributes,
        }
    }

    #[allow(dead_code)]
    pub(crate) fn parent(&self) -> Option<NodeRef<T, A>> {
        self.parent
    }

    #[allow(dead_code)]
    fn sibling(&self) -> Option<NodeRef<T, A>> {
        let direction = self.direction()?;
        let parent = self.parent?;

        match direction {
            Direction::Left => parent.as_ref().right,
            Direction::Right => parent.as_ref().left,
        }
    }

    #[allow(dead_code)]
    fn grandparent(&self) -> Option<NodeRef<T, A>> {
        self.parent.and_then(|parent| parent.as_ref().parent)
    }

    #[allow(dead_code)]
    fn uncle(&self) -> Option<NodeRef<T, A>> {
        self.parent.and_then(|parent| parent.as_ref().sibling())
    }

    #[allow(dead_code)]
    fn borrow_attributes_mut(&mut self) -> &mut A {
        &mut self.attributes
    }
}

impl<T, A> Directional for Node<T, A>
where
    T: PartialEq,
{
    fn direction(&self) -> Option<Direction> {
        let optional_parent = self.parent?;

        match optional_parent.as_ref().left {
            Some(left_node) if left_node.as_ref().inner == self.inner => Some(Direction::Left),
            _ => Some(Direction::Right),
        }
    }
}
