use std::fmt::Debug;

/// NodeId represents an Id for a node. This must be able to convert cleanly between a usize and
#[derive(Debug, Clone, Copy, PartialEq, Default)]
pub struct NodeId(usize);

impl NodeId {
    pub fn new(inner: usize) -> Self {
        Self(inner)
    }

    pub fn to_usize(self) -> usize {
        self.0
    }

    pub fn as_usize(&self) -> &usize {
        &self.0
    }
}

impl From<usize> for NodeId {
    fn from(id: usize) -> Self {
        Self(id)
    }
}

#[derive(Debug, Clone)]
pub struct Node<T> {
    id: NodeId,
    inner: T,
    parent: Option<NodeId>,
    left: Option<NodeId>,
    right: Option<NodeId>,
}

impl<T> Node<T> {
    pub fn new(
        id: NodeId,
        inner: T,
        parent: Option<NodeId>,
        left: Option<NodeId>,
        right: Option<NodeId>,
    ) -> Self {
        Self {
            id,
            inner,
            parent,
            left,
            right,
        }
    }

    /// Returns a boolean signifying if this node is the root (has no parents)
    /// node.
    pub fn is_root(&self) -> bool {
        self.parent.is_none()
    }

    /// Returns a boolean signifying if this node is a branch (has a parent
    /// and atleast one child) node.
    pub fn is_branch(&self) -> bool {
        !(self.is_root() || self.is_leaf())
    }

    /// Returns a boolean signifying if this node is a leaf (has no children)
    /// node.
    pub fn is_leaf(&self) -> bool {
        self.left.is_none() && self.right.is_none()
    }
}

#[derive(Debug, Clone)]
pub enum ColorNode<T> {
    Red(Node<T>),
    Black(Node<T>),
}

impl<T> ColorNode<T> {
    pub fn as_inner(&self) -> &Node<T> {
        match self {
            ColorNode::Red(inner) | ColorNode::Black(inner) => inner,
        }
    }

    pub fn flip_color(self) -> Self {
        match self {
            Self::Red(inner) => Self::Black(inner),
            Self::Black(inner) => Self::Red(inner),
        }
    }
}

#[derive(Debug, Default, Clone)]
pub struct RedBlackTree<T> {
    root: Option<NodeId>,
    nodes: Vec<ColorNode<T>>,
}

impl<T> RedBlackTree<T> {
    pub fn new(root: Option<NodeId>, nodes: Vec<ColorNode<T>>) -> Self {
        Self { root, nodes }
    }
}

/// Helper functions
impl<T> RedBlackTree<T> {
    /// Retrieves a Node by Id. If the Id exists in the tree, Some<&Node> is
    /// returned. Otherwise None is returned.
    pub fn get(&self, id: NodeId) -> Option<&ColorNode<T>> {
        self.nodes.get(*id.as_usize())
    }

    /// Retrieves a the parent of a Node, Optionally returning a reference to
    /// the parent Node if it exists.
    pub fn get_parent(&self, id: NodeId) -> Option<&ColorNode<T>> {
        self.get(id).and_then(|node| {
            node.as_inner()
                .parent
                .and_then(|parent_id| self.get(parent_id))
        })
    }

    /// Retrieves the parent of a Node's parent, Optionally returning a
    /// reference to the grandparent Node if it exists.
    pub fn get_grandparent(&self, id: NodeId) -> Option<&ColorNode<T>> {
        self.get_parent(id).and_then(|node| {
            node.as_inner()
                .parent
                .and_then(|parent_id| self.get(parent_id))
        })
    }

    /// Retrieves the sibling of a Node, Optionally returning a reference to the
    /// sibling Node if it exists.
    pub fn get_sibling(&self, id: NodeId) -> Option<&ColorNode<T>> {
        self.get_parent(id)
            .and_then(|node| match (node.as_inner().left, node.as_inner().right) {
                // return any leaf that doesn't match the original id or none.
                (_, Some(leaf_id)) if leaf_id != id => self.get(leaf_id),
                (Some(leaf_id), _) if leaf_id != id => self.get(leaf_id),
                _ => None,
            })
    }

    /// Retrieves the uncle of a Node, Optionally returning a reference to the
    /// uncle Node if it exists.
    pub fn get_uncle(&self, id: NodeId) -> Option<&ColorNode<T>> {
        self.get_parent(id)
            .and_then(|node| self.get_sibling(node.as_inner().id))
    }
}
