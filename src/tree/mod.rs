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
pub(crate) struct NodeRef<K, V, A>(NonNull<Node<K, V, A>>);

impl<K, V, A> NodeRef<K, V, A> {
    /// Consumes the enclosing NodeRef, returning the wrapped raw pointer.
    fn as_ptr(self) -> *mut Node<K, V, A> {
        self.0.as_ptr()
    }
}

impl<K, V, A> From<NonNull<Node<K, V, A>>> for NodeRef<K, V, A> {
    fn from(ptr: NonNull<Node<K, V, A>>) -> Self {
        Self(ptr)
    }
}

impl<K, V, A> From<Node<K, V, A>> for NodeRef<K, V, A> {
    fn from(node: Node<K, V, A>) -> Self {
        let boxed_node = Box::new(node);
        Self::from(boxed_node)
    }
}

impl<K, V, A> From<Box<Node<K, V, A>>> for NodeRef<K, V, A> {
    fn from(node: Box<Node<K, V, A>>) -> Self {
        NonNull::new(Box::into_raw(node))
            .map(NodeRef::from)
            .expect("Box points to an invalid memory location")
    }
}

impl<K, V, A> Clone for NodeRef<K, V, A> {
    fn clone(&self) -> Self {
        Self(self.0)
    }
}

impl<K, V, A> Copy for NodeRef<K, V, A> {}

impl<K, V, A> PartialEq for NodeRef<K, V, A> {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl<K, V, A> Directional for NodeRef<K, V, A>
where
    Node<K, V, A>: Directional,
{
    fn direction(&self) -> Option<Direction> {
        unsafe {
            let node = self.0.as_ref();
            node.direction()
        }
    }
}

impl<K, V, A> core::convert::AsRef<Node<K, V, A>> for NodeRef<K, V, A> {
    fn as_ref(&self) -> &Node<K, V, A> {
        unsafe { self.0.as_ref() }
    }
}

impl<K, V, A> core::convert::AsMut<Node<K, V, A>> for NodeRef<K, V, A> {
    fn as_mut(&mut self) -> &mut Node<K, V, A> {
        unsafe { self.0.as_mut() }
    }
}

impl<K, V, A> core::fmt::Debug for NodeRef<K, V, A>
where
    K: core::fmt::Debug,
    V: core::fmt::Debug,
    A: core::fmt::Debug,
{
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_tuple("NodeRef")
            .field(unsafe { &self.0.as_ref().key })
            .field(unsafe { &self.0.as_ref().value })
            .finish()
    }
}

/// Node represents an interior node to the Tree, storing
/// information about direct ancestor/descendent nodes as well as an inner
/// value denoted by type V.
#[derive(Debug, Clone)]
pub(crate) struct Node<K, V, A> {
    key: K,
    /// An inner value stored in the tree.
    value: V,
    /// An optional parent node. A value of None signifies that this node is
    /// the root.
    parent: Option<NodeRef<K, V, A>>,
    /// An optional left-side direcitonaldescendant node.
    left: Option<NodeRef<K, V, A>>,
    /// An optional right-side direcitonaldescendant node.
    right: Option<NodeRef<K, V, A>>,
    /// Additional attributes on the node.
    attributes: A,
}
impl<K, V, A> Node<K, V, A>
where
    K: PartialEq,
{
    pub(crate) fn new(
        key: K,
        value: V,
        parent: Option<NodeRef<K, V, A>>,
        left: Option<NodeRef<K, V, A>>,
        right: Option<NodeRef<K, V, A>>,
        attributes: A,
    ) -> Self {
        Self {
            key,
            value,
            parent,
            left,
            right,
            attributes,
        }
    }

    #[allow(dead_code)]
    pub(crate) fn parent(&self) -> Option<NodeRef<K, V, A>> {
        self.parent
    }

    #[allow(dead_code)]
    fn sibling(&self) -> Option<NodeRef<K, V, A>> {
        let direction = self.direction()?;
        let parent = self.parent?;

        match direction {
            Direction::Left => parent.as_ref().right,
            Direction::Right => parent.as_ref().left,
        }
    }

    #[allow(dead_code)]
    fn grandparent(&self) -> Option<NodeRef<K, V, A>> {
        self.parent.and_then(|parent| parent.as_ref().parent)
    }

    #[allow(dead_code)]
    fn uncle(&self) -> Option<NodeRef<K, V, A>> {
        self.parent.and_then(|parent| parent.as_ref().sibling())
    }

    #[allow(dead_code)]
    /// Provides a mutable borrow of the attribute field for applying changes
    /// in place.
    fn borrow_attributes_mut(&mut self) -> &mut A {
        &mut self.attributes
    }
}

impl<K, V, A> Directional for Node<K, V, A>
where
    K: PartialEq,
{
    fn direction(&self) -> Option<Direction> {
        let optional_parent = self.parent?;

        match optional_parent.as_ref().left {
            Some(left_node) if left_node.as_ref().key == self.key => Some(Direction::Left),
            _ => Some(Direction::Right),
        }
    }
}
