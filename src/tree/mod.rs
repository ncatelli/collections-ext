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
pub(crate) struct NodeRef<T>(NonNull<Node<T>>);

impl<T> NodeRef<T> {
    /// Consumes the enclosing NodeRef, returning the wrapped raw pointer.
    fn as_ptr(self) -> *mut Node<T> {
        self.0.as_ptr()
    }
}

impl<T> From<NonNull<Node<T>>> for NodeRef<T> {
    fn from(ptr: NonNull<Node<T>>) -> Self {
        Self(ptr)
    }
}

impl<T> From<Node<T>> for NodeRef<T> {
    fn from(node: Node<T>) -> Self {
        let boxed_node = Box::new(node);
        Self::from(boxed_node)
    }
}

impl<T> From<Box<Node<T>>> for NodeRef<T> {
    fn from(node: Box<Node<T>>) -> Self {
        NonNull::new(Box::into_raw(node))
            .map(NodeRef::from)
            .expect("Box points to an invalid memory location")
    }
}

impl<T> Clone for NodeRef<T> {
    fn clone(&self) -> Self {
        Self(self.0)
    }
}

impl<T> Copy for NodeRef<T> {}

impl<T> Directional for NodeRef<T>
where
    Node<T>: Directional,
{
    fn direction(&self) -> Option<Direction> {
        unsafe {
            let node = self.0.as_ref();
            node.direction()
        }
    }
}

impl<T> core::convert::AsRef<Node<T>> for NodeRef<T> {
    fn as_ref(&self) -> &Node<T> {
        unsafe { self.0.as_ref() }
    }
}

impl<T> core::convert::AsMut<Node<T>> for NodeRef<T> {
    fn as_mut(&mut self) -> &mut Node<T> {
        unsafe { self.0.as_mut() }
    }
}

impl<T: core::fmt::Debug> core::fmt::Debug for NodeRef<T> {
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
pub(crate) struct Node<T> {
    /// An inner value stored in the tree.
    inner: T,
    /// An optional parent node. A value of None signifies that this node is
    /// the root.
    parent: Option<NodeRef<T>>,
    /// An optional left-side direcitonaldescendant node.
    left: Option<NodeRef<T>>,
    /// An optional right-side direcitonaldescendant node.
    right: Option<NodeRef<T>>,
}
impl<T> Node<T>
where
    T: PartialEq,
{
    pub(crate) fn new(
        inner: T,
        parent: Option<NodeRef<T>>,
        left: Option<NodeRef<T>>,
        right: Option<NodeRef<T>>,
    ) -> Self {
        Self {
            inner,
            parent,
            left,
            right,
        }
    }

    #[allow(dead_code)]
    pub(crate) fn parent(&self) -> Option<NodeRef<T>> {
        self.parent
    }

    #[allow(dead_code)]
    fn sibling(&self) -> Option<NodeRef<T>> {
        let direction = self.direction()?;
        let parent = self.parent?;

        match direction {
            Direction::Left => parent.as_ref().right,
            Direction::Right => parent.as_ref().left,
        }
    }

    #[allow(dead_code)]
    fn grandparent(&self) -> Option<NodeRef<T>> {
        self.parent.and_then(|parent| parent.as_ref().parent)
    }

    #[allow(dead_code)]
    fn uncle(&self) -> Option<NodeRef<T>> {
        self.parent.and_then(|parent| parent.as_ref().sibling())
    }
}

impl<T> Directional for Node<T>
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
