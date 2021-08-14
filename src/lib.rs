//! A naive implementation of a red-black tree for education purposes.

/// NodeId represents an Id for a node. This must be able to convert cleanly
/// between a usize and
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub struct NodeId(usize);

impl NodeId {
    /// Instantiates a NodeId from a usize value.
    pub fn new(inner: usize) -> Self {
        Self(inner)
    }

    /// Converts the NodeId to a usize.
    pub fn to_usize(self) -> usize {
        self.0
    }

    /// Borrows the enclosuing usize value of the NodeId.
    pub fn as_usize(&self) -> &usize {
        &self.0
    }
}

impl From<usize> for NodeId {
    fn from(id: usize) -> Self {
        Self::new(id)
    }
}

/// Node represents an interior node to the Red-Black Tree, storing
/// information about direct ancestor/descendent nodes as well as an inner
/// value denoted by type T.
#[derive(Debug, Clone)]
pub struct Node<T> {
    /// A unique identifier for the node
    id: NodeId,
    /// An inner value stored in the tree.
    inner: T,
    /// An optional parent node. A value of None signifies that this node is
    /// the root.
    parent: Option<NodeId>,
    /// An optional left-side direcitonaldescendant node.
    left: Option<NodeId>,
    /// An optional right-side direcitonaldescendant node.
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

/// An enumerable value representing the available colors of a node.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Color {
    Red,
    Black,
}

/// ColorNode Wraps a node, with an optional Color value.
#[derive(Debug, Clone)]
pub enum ColorNode<T> {
    Red(Node<T>),
    Black(Node<T>),
}

impl<T> ColorNode<T> {
    /// Borrows and returns the inner value of the node.
    pub fn as_inner(&self) -> &Node<T> {
        match self {
            ColorNode::Red(inner) | ColorNode::Black(inner) => inner,
        }
    }

    /// Mutably borrows and returns the inner value of the node.
    pub fn as_inner_mut(&mut self) -> &mut Node<T> {
        match self {
            ColorNode::Red(inner) | ColorNode::Black(inner) => inner,
        }
    }

    /// Returns the inner value, `T` of the node, consuming the enclosing
    /// `Node<T>`.
    pub fn into_inner(self) -> Node<T> {
        match self {
            ColorNode::Red(inner) | ColorNode::Black(inner) => inner,
        }
    }

    /// Inverts the color of a node, rewrapping the nodes inner value.
    pub fn flip_color(self) -> Self {
        match self {
            Self::Red(inner) => Self::Black(inner),
            Self::Black(inner) => Self::Red(inner),
        }
    }

    /// Returns the Color of a node.
    pub fn color(&self) -> Color {
        match self {
            Self::Red(_) => Color::Red,
            Self::Black(_) => Color::Black,
        }
    }
}

impl<T> From<(Color, Node<T>)> for ColorNode<T> {
    fn from((color, node): (Color, Node<T>)) -> Self {
        match color {
            Color::Red => ColorNode::Red(node),
            Color::Black => ColorNode::Black(node),
        }
    }
}

/// Direction represents the directional branch that a given child is on for
/// a given node.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Direction {
    Left,
    Right,
}

/// An implementation of a Red-Black Tree
#[derive(Debug, Default, Clone)]
pub struct RedBlackTree<T> {
    root: Option<NodeId>,
    nodes: Vec<ColorNode<T>>,
}

impl<T> RedBlackTree<T> {
    /// Instantiates a new instance of RedBlackTree, making the first item in
    /// the passed vector the root node.
    pub fn new(nodes: Vec<ColorNode<T>>) -> Self {
        match nodes.get(0) {
            Some(node_id) => Self {
                root: Some(node_id.as_inner().id),
                nodes,
            },
            None => Self { root: None, nodes },
        }
    }
}

/// Helper functions
impl<T> RedBlackTree<T> {
    /// Retrieves a Node by Id. If the Id exists in the tree, Some<&Node> is
    /// returned. Otherwise None is returned.
    pub fn get(&self, id: NodeId) -> Option<&ColorNode<T>> {
        self.nodes.get(id.to_usize())
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
                (Some(leaf_id), _) if leaf_id != id => self.get(leaf_id),
                (_, Some(leaf_id)) if leaf_id != id => self.get(leaf_id),
                _ => None,
            })
    }

    /// Retrieves the uncle of a Node, Optionally returning a reference to the
    /// uncle Node if it exists.
    pub fn get_uncle(&self, id: NodeId) -> Option<&ColorNode<T>> {
        self.get_parent(id)
            .and_then(|node| self.get_sibling(node.as_inner().id))
    }

    /// Retrieves the direction of a node from it's parent.
    pub fn get_direction_of_node(&self, id: NodeId) -> Option<Direction> {
        self.get_parent(id)
            .and_then(|node| match (node.as_inner().left, node.as_inner().right) {
                (Some(leaf_id), _) if leaf_id == id => Some(Direction::Left),
                (_, Some(leaf_id)) if leaf_id == id => Some(Direction::Right),
                _ => None,
            })
    }
}
