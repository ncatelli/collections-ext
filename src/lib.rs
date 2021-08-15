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
/// value denoted by type V.
#[derive(Default, Debug, Clone)]
pub struct Node<V> {
    /// A unique identifier for the node
    pub id: NodeId,
    /// An inner value stored in the tree.
    pub inner: V,
    /// An optional parent node. A value of None signifies that this node is
    /// the root.
    pub parent: Option<NodeId>,
    /// An optional left-side direcitonaldescendant node.
    pub left: Option<NodeId>,
    /// An optional right-side direcitonaldescendant node.
    pub right: Option<NodeId>,
}

impl<V> Node<V> {
    pub fn new(
        id: NodeId,
        inner: V,
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

    /// Returns the inner value of the Node.
    pub fn unwrap(self) -> V {
        self.inner
    }
}

/// An enumerable value representing the available colors of a node.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Color {
    Red,
    Black,
}

impl Color {
    pub fn flip(self) -> Self {
        match self {
            Self::Black => Self::Red,
            Self::Red => Self::Black,
        }
    }
}

/// ColorNode Wraps a node, with an optional Color value.
#[derive(Debug, Clone)]
pub enum ColorNode<V> {
    Red(Node<V>),
    Black(Node<V>),
}

impl<T> ColorNode<T>
where
    T: Default,
{
    /// Returns the id of the enclosed node.
    pub fn id(&self) -> NodeId {
        self.as_inner().id
    }

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
    pub fn flip_color(mut self) -> Self {
        self.flip_color_mut();
        self
    }

    pub fn flip_color_mut(&mut self) {
        match self {
            ColorNode::Red(inner) => *self = Self::Black(std::mem::take(inner)),
            ColorNode::Black(inner) => *self = Self::Red(std::mem::take(inner)),
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

/// Rebalance captures the states of rebalance operation.
enum Rebalance {
    LeftLeft(NodeId),
    LeftRight(NodeId),
    RightRight(NodeId),
    RightLeft(NodeId),
    Continue(NodeId),
}

/// SearchResult represents the results of a binary tree search.
#[derive(Debug, PartialEq, Eq)]
pub enum SearchResult {
    /// Hit signifies the exact value was found in the tree and
    /// contains a reference to the NodeId for said value.
    Hit(NodeId),
    /// Miss represents the value was not found in the tree and represents the
    /// nearest parent node.
    Miss(NodeId),
    /// Empty represents an empty tree.
    Empty,
}

impl SearchResult {
    /// Calls `f` if the self is `SearchResult::Hit` returning the result of
    /// `f` wrapped in `Some` otherwise `None` is returned.
    pub fn hit_then<F, B>(self, f: F) -> Option<B>
    where
        F: Fn(NodeId) -> B,
    {
        match self {
            SearchResult::Hit(node_id) => Some(f(node_id)),
            _ => None,
        }
    }

    /// Calls `f` if the self is `SearchResult::Miss` returning the result of
    /// `f` wrapped in `Some` otherwise `None` is returned.
    pub fn miss_then<F, B>(self, f: F) -> Option<B>
    where
        F: Fn(NodeId) -> B,
    {
        match self {
            SearchResult::Miss(node_id) => Some(f(node_id)),
            _ => None,
        }
    }
}

/// Captures the state of a tree walk.
enum WalkStep {
    /// Continue encloses the next node to check for a match in a binary walk.
    Continue(NodeId),
    /// Signifies the end node in walk and that the walk should stop.
    Stop(NodeId),
}

impl WalkStep {
    /// Unpacks a `WalkStep::Stop` into an Option. Returning `None` if the
    /// variant is not `Stop`.
    fn stop(self) -> Option<NodeId> {
        match self {
            WalkStep::Stop(inner) => Some(inner),
            _ => None,
        }
    }
}

/// An implementation of a Red-Black Tree
#[derive(Debug, Default, Clone)]
pub struct RedBlackTree<V> {
    root: Option<NodeId>,
    nodes: Vec<ColorNode<V>>,
}

impl<V> RedBlackTree<V>
where
    V: Default,
{
    /// Instantiates a new instance of RedBlackTree, making the first item in
    /// the passed vector the root node.
    pub fn new(nodes: Vec<ColorNode<V>>) -> Self {
        match nodes.get(0) {
            Some(node_id) => Self {
                root: Some(node_id.as_inner().id),
                nodes,
            },
            None => Self { root: None, nodes },
        }
    }

    /// Returns a boolean representing if the tree is empty (root node is None).
    pub fn is_empty(&self) -> bool {
        self.root.is_none()
    }
}

/// Helper functions
impl<V> RedBlackTree<V>
where
    V: PartialEq + PartialOrd + Default,
{
    /// Retrieves a Node by Id. If the Id exists in the tree, Some<&Node> is
    /// returned. Otherwise None is returned.
    pub fn get(&self, id: NodeId) -> Option<&ColorNode<V>> {
        self.nodes.get(id.to_usize())
    }

    /// Retrieves a mutable Node by Id. If the Id exists in the tree,
    /// Some<&mut Node> is returned. Otherwise None is returned.
    pub fn get_mut(&mut self, id: NodeId) -> Option<&mut ColorNode<V>> {
        self.nodes.get_mut(id.to_usize())
    }

    /// Searches for a value in the tree returning a SearchResult that
    /// captures if the search yield a hit, miss or empty tree.  
    pub fn search(&self, value: &V) -> SearchResult {
        self.root.map_or_else(
            || SearchResult::Empty,
            |root| {
                let mut next_step = WalkStep::Continue(root);
                while let WalkStep::Continue(next_id) = next_step {
                    next_step = self.next_step(next_id, value);
                }

                next_step
                    .stop()
                    .and_then(|last| {
                        self.get(last).map(|last_color_node| {
                            let last_node = last_color_node.as_inner();
                            if value == &last_node.inner {
                                SearchResult::Hit(last)
                            } else {
                                SearchResult::Miss(last)
                            }
                        })
                    })
                    // Unwraps should be safe. these will always exist.
                    .unwrap()
            },
        )
    }

    /// Returns an option representing the next step in a tree walk. If `None`
    /// is returned. There are no further steps to take. Otherwise the the
    /// direction of the next step is returned.
    fn next_step(&self, base_id: NodeId, value: &V) -> WalkStep {
        // panic if no node.
        let node = self.get(base_id).unwrap().as_inner();

        if value == &node.inner {
            WalkStep::Stop(base_id)
        } else if value < &node.inner {
            // if left leaf exists follow that direction.
            match node.left {
                Some(next) => WalkStep::Continue(next),
                None => WalkStep::Stop(base_id),
            }
        } else {
            // if right leaf exists follow that direction.
            match node.right {
                Some(next) => WalkStep::Continue(next),
                None => WalkStep::Stop(base_id),
            }
        }
    }

    /// Inserts a value into the tree, Returning the tree containing said value.
    /// This will not reinsert the value if it already exists.
    pub fn insert(mut self, value: V) -> Self {
        self.insert_mut(value);
        self
    }

    /// Inserts a value into the tree. if the value already exists,
    /// Some(NodeId) to the already defined value is returned. Otherwise None
    /// is returned.
    pub fn insert_mut(&mut self, value: V) -> Option<NodeId> {
        let next_id = NodeId::from(self.nodes.len());
        // new nodes should always be red.
        let mut child_color = Color::Red;

        match self.search(&value) {
            SearchResult::Hit(node) => Some(node),
            SearchResult::Empty => {
                self.root = Some(next_id);
                self.nodes.push(ColorNode::Black(Node::new(
                    next_id, value, None, None, None,
                )));
                None
            }
            SearchResult::Miss(parent_node_id) => {
                let is_defined = match self.get_mut(parent_node_id) {
                    Some(parent_color_node) => {
                        child_color = parent_color_node.color().flip();

                        let parent_inner = parent_color_node.as_inner_mut();

                        if value < parent_inner.inner {
                            parent_inner.left = Some(next_id);
                            None
                        } else if value > parent_inner.inner {
                            parent_inner.right = Some(next_id);
                            None
                        } else {
                            Some(parent_inner.id)
                        }
                    }
                    None => None,
                };

                if is_defined.is_some() {
                    is_defined
                } else {
                    self.nodes.push(ColorNode::from((
                        child_color,
                        Node::new(next_id, value, Some(parent_node_id), None, None),
                    )));

                    // rebalance the tree after a new insertions
                    self.rebalance_mut(next_id);
                    None
                }
            }
        }
    }

    fn rebalance_mut(&mut self, node_id: NodeId) {
        let mut next_step = Some(Rebalance::Continue(node_id));
        while let Some(step) = next_step {
            match step {
                Rebalance::LeftLeft(_) => todo!(),
                Rebalance::LeftRight(_) => todo!(),
                Rebalance::RightRight(_) => todo!(),
                Rebalance::RightLeft(_) => todo!(),
                Rebalance::Continue(next) => next_step = self.rebalance_step_mut(next),
            }
        }
    }

    /// Rebalance a tree starting at node_id and recursing up. If a recolor
    /// occurs, a `Some(NodeId)` is returned, where the `NodeId` represents
    /// the parent of the starting node to continue the recolor recursively up.
    fn rebalance_step_mut(&mut self, node_id: NodeId) -> Option<Rebalance> {
        self.get(node_id)
            .and_then(|base_color_node| {
                // if the base node is not root and it's parent is red, continue.
                self.get_parent(base_color_node.id())
                    // base node is not root.
                    .and_then(|parent_color_node| {
                        if parent_color_node.color() == Color::Red {
                            Some(parent_color_node.id())
                        } else {
                            None
                        }
                    })
                    // base node is not root and parent is red.
                    .and_then(|parent_id| {
                        self.get_uncle(node_id)
                            .and_then(|uncle_color_node| match uncle_color_node.color() {
                                Color::Red => Some((parent_id, uncle_color_node.id())),
                                Color::Black => None,
                            })
                    })
            })
            // base node is not root and both parent and uncle are red.
            .and_then(|(parent_id, uncle_id)| {
                // flip parent color
                let _ = self
                    .get_mut(parent_id)
                    .map(|parent_node| parent_node.flip_color_mut());
                // flip uncle color
                let _ = self
                    .get_mut(uncle_id)
                    .map(|uncle_node| uncle_node.flip_color_mut());

                // if grandparent is black, flip to red and recurse up.
                self.get_grandparent(node_id)
                    .map(|grandparent_color_node| grandparent_color_node.id())
                    .and_then(|grandparent_id| {
                        self.get_mut(grandparent_id)
                            .map(|grandparent_node| match grandparent_node.color() {
                                Color::Red => (),
                                Color::Black => grandparent_node.flip_color_mut(),
                            })
                            .map(|_| Rebalance::Continue(grandparent_id))
                    })
            })
    }

    /// Retrieves a the parent of a Node, Optionally returning a reference to
    /// the parent Node if it exists.
    pub fn get_parent(&self, id: NodeId) -> Option<&ColorNode<V>> {
        self.get(id).and_then(|node| {
            node.as_inner()
                .parent
                .and_then(|parent_id| self.get(parent_id))
        })
    }

    /// Retrieves the parent of a Node's parent, Optionally returning a
    /// reference to the grandparent Node if it exists.
    pub fn get_grandparent(&self, id: NodeId) -> Option<&ColorNode<V>> {
        self.get_parent(id).and_then(|node| {
            node.as_inner()
                .parent
                .and_then(|parent_id| self.get(parent_id))
        })
    }

    /// Retrieves the uncle of a Node, Optionally returning a reference to the
    /// uncle Node if it exists.
    pub fn get_uncle(&self, id: NodeId) -> Option<&ColorNode<V>> {
        self.get_parent(id)
            .and_then(|node| self.get_sibling(node.as_inner().id))
    }

    /// Retrieves the sibling of a Node, Optionally returning a reference to the
    /// sibling Node if it exists.
    pub fn get_sibling(&self, id: NodeId) -> Option<&ColorNode<V>> {
        self.get_parent(id)
            .and_then(|node| match (node.as_inner().left, node.as_inner().right) {
                // return any leaf that doesn't match the original id or none.
                (Some(leaf_id), _) if leaf_id != id => self.get(leaf_id),
                (_, Some(leaf_id)) if leaf_id != id => self.get(leaf_id),
                _ => None,
            })
    }

    /// Retrieves the close nephew of a Node, Optionally returning a reference
    /// to the close nephew Node if it exists.
    pub fn get_close_nephew(&self, id: NodeId) -> Option<&ColorNode<V>> {
        let direction = self.get_direction_of_node(id)?;

        self.get_sibling(id)
            .and_then(|node| match direction {
                Direction::Left => node.as_inner().left,
                Direction::Right => node.as_inner().right,
            })
            // Attempt to lookup the node after unpacking it from the sibling.
            .and_then(|nephew_id| self.get(nephew_id))
    }

    /// Retrieves the distant nephew of a Node, Optionally returning a reference
    /// to the distant nephew Node if it exists.
    pub fn get_distant_nephew(&self, id: NodeId) -> Option<&ColorNode<V>> {
        let direction = self.get_direction_of_node(id)?;

        self.get_sibling(id)
            .and_then(|node| match direction {
                Direction::Left => node.as_inner().right,
                Direction::Right => node.as_inner().left,
            })
            // Attempt to lookup the node after unpacking it from the sibling.
            .and_then(|nephew_id| self.get(nephew_id))
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn should_return_correct_empty_state_when_tree_has_values() {
        let tree = RedBlackTree::default();

        assert!(tree.is_empty());
        assert!(!tree.insert(10).is_empty());
    }

    #[test]
    fn should_return_node_on_search_for_inserted_value() {
        let tree = vec![10, 5]
            .into_iter()
            .fold(RedBlackTree::default(), |tree, x| tree.insert(x));

        assert_eq!(SearchResult::Hit(NodeId::from(1)), tree.search(&5));
    }

    #[test]
    fn should_get_correct_relationships_for_nodes() {
        let child = 5;
        let parent = 2;
        let close_nephew = 4;
        let distant_nephew = 3;
        let uncle = 1;
        let grandparent = 0;

        let tree = vec![10, 5, 15, 3, 7, 20]
            .into_iter()
            .fold(RedBlackTree::default(), |tree, x| tree.insert(x));

        assert_eq!(
            Some(NodeId::from(parent)),
            tree.get_parent(NodeId::from(child)).map(|node| node.id())
        );

        assert_eq!(
            Some(NodeId::from(uncle)),
            tree.get_uncle(NodeId::from(child)).map(|node| node.id())
        );

        assert_eq!(
            Some(NodeId::from(grandparent)),
            tree.get_grandparent(NodeId::from(child))
                .map(|node| node.id())
        );

        assert_eq!(
            Some(NodeId::from(uncle)),
            tree.get_sibling(NodeId::from(parent)).map(|node| node.id())
        );

        assert_eq!(
            Some(NodeId::from(close_nephew)),
            tree.get_close_nephew(NodeId::from(parent))
                .map(|node| node.id())
        );

        assert_eq!(
            Some(NodeId::from(distant_nephew)),
            tree.get_distant_nephew(NodeId::from(parent))
                .map(|node| node.id())
        );
    }

    #[test]
    fn should_paint_newly_inserted_nodes_red() {
        let tree = vec![10, 5, 15]
            .into_iter()
            .fold(RedBlackTree::default(), |tree, x| tree.insert(x));

        let root = tree
            .search(&10)
            .hit_then(|matching_node: NodeId| tree.get(matching_node).unwrap())
            .map(|color_node| color_node.color());

        let left = tree
            .search(&5)
            .hit_then(|matching_node: NodeId| tree.get(matching_node).unwrap())
            .map(|color_node| color_node.color());

        let right = tree
            .search(&15)
            .hit_then(|matching_node: NodeId| tree.get(matching_node).unwrap())
            .map(|color_node| color_node.color());

        assert_eq!(Some(Color::Black), root);
        assert_eq!(Some(Color::Red), left);
        assert_eq!(Some(Color::Red), right);
    }

    #[ignore = "Repainting looks completely wrong."]
    #[test]
    fn should_recolor_node_if_two_red_nodes_occur() {
        let tree = vec![15, 10, 20, 5]
            .into_iter()
            .fold(RedBlackTree::default(), |tree, x| tree.insert(x));

        let child = tree
            .search(&5)
            .hit_then(|matching_node: NodeId| tree.get(matching_node).unwrap())
            .map(|color_node| color_node.color());

        let parent = tree
            .search(&10)
            .hit_then(|matching_node: NodeId| tree.get(matching_node).unwrap())
            .map(|color_node| color_node.color());

        let uncle = tree
            .search(&5)
            .hit_then(|matching_node: NodeId| tree.get(matching_node).unwrap())
            .map(|color_node| color_node.color());

        let grandparent = tree
            .search(&15)
            .hit_then(|matching_node: NodeId| tree.get(matching_node).unwrap())
            .map(|color_node| color_node.color());

        assert_eq!(Some(Color::Black), child);
        assert_eq!(Some(Color::Red), parent);
        assert_eq!(Some(Color::Red), uncle);
        assert_eq!(Some(Color::Black), grandparent);
    }
}
