use core::borrow;
use std::borrow::Borrow;
use std::rc::{Rc, Weak};

/// Direction represents the directional branch that a given child is on for
/// a given node.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Direction {
    Left,
    Right,
}

/// Rebalance captures the states of rebalance operation.
enum Rebalance<V> {
    /// Represents a LeftLeft case of inbalance.
    LeftLeft,
    /// Represents a LeftRight case of inbalance.
    LeftRight,
    /// Represents a RightRight case of inbalance.
    RightRight,
    /// Represents a RightLeft case of inbalance.
    RightLeft,
    /// Contains the next base node for recoloring.
    Recolor(Rc<Node<V>>),
}

/// An enumerable value representing the available colors of a node.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
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

type WeakNodeRef<V> = Weak<Node<V>>;
type NodeRef<V> = Rc<Node<V>>;

/// Node represents an interior node to the Red-Black Tree, storing
/// information about direct ancestor/descendent nodes as well as an inner
/// value denoted by type V.
#[derive(Debug, Clone)]
pub struct Node<V> {
    color: Color,
    /// An inner value stored in the tree.
    inner: V,
    /// An optional parent node. A value of None signifies that this node is
    /// the root.
    parent: WeakNodeRef<V>,
    /// An optional left-side direcitonaldescendant node.
    left: Option<NodeRef<V>>,
    /// An optional right-side direcitonaldescendant node.
    right: Option<NodeRef<V>>,
}

impl<V> Node<V>
where
    V: PartialEq,
{
    pub fn new(
        color: Color,
        inner: V,
        parent: WeakNodeRef<V>,
        left: Option<NodeRef<V>>,
        right: Option<NodeRef<V>>,
    ) -> Self {
        Self {
            color,
            inner,
            parent,
            left,
            right,
        }
    }

    /// Returns a boolean signifying if this node is the root (has no parents)
    /// node.
    pub fn is_root(&self) -> bool {
        self.parent.borrow().upgrade().is_none()
    }

    /// Returns a boolean signifying if the node is a leaf node (has no
    /// children)
    pub fn is_leaf(&self) -> bool {
        self.left.is_none() && self.right.is_none()
    }

    /// Returns the inner value of the Node.
    pub fn unwrap(self) -> V {
        self.inner
    }

    pub fn direction(&self) -> Option<Direction> {
        let parent = self.parent.borrow().upgrade()?;

        match &parent.left {
            Some(left_node) if left_node.inner == self.inner => Some(Direction::Left),
            _ => Some(Direction::Right),
        }
    }

    pub fn sibling(&self) -> Option<NodeRef<V>> {
        let direction = self.direction()?;
        let parent = self.parent.upgrade()?;

        match direction {
            Direction::Left => parent.right.clone(),
            Direction::Right => parent.left.clone(),
        }
    }

    pub fn grandparent(&self) -> Option<NodeRef<V>> {
        let parent = self.parent.upgrade()?;
        parent.parent.upgrade()
    }

    pub fn uncle(&self) -> Option<NodeRef<V>> {
        let parent = self.parent.upgrade()?;
        parent.sibling()
    }
}

/// SearchResult represents the results of a binary tree search.
#[derive(Debug)]
enum SearchResult<V> {
    /// Hit signifies the exact value was found in the tree and
    /// contains a reference to the NodeId for said value.
    Hit(Rc<Node<V>>),
    /// Miss represents the value was not found in the tree and represents the
    /// nearest parent node.
    Miss(Rc<Node<V>>),
    /// Empty represents an empty tree.
    Empty,
}

impl<V> SearchResult<V> {
    /// Calls `f` if the self is `SearchResult::Hit` returning the result of
    /// `f` wrapped in `Some` otherwise `None` is returned.
    fn hit_then<F, B>(self, f: F) -> Option<B>
    where
        F: Fn(Rc<Node<V>>) -> B,
    {
        match self {
            SearchResult::Hit(node) => Some(f(node)),
            _ => None,
        }
    }
}

/// An implementation of a Red-Black Tree
#[derive(Debug, Clone)]
pub struct RedBlackTree<V> {
    root: Option<NodeRef<V>>,
}

impl<V> RedBlackTree<V>
where
    V: PartialEq,
{
    pub fn new(root: V) -> Self {
        Self {
            root: Some(Rc::new(Node::new(
                Color::Black,
                root,
                Weak::new(),
                None,
                None,
            ))),
        }
    }
}

// helper methods
impl<V> RedBlackTree<V>
where
    V: PartialEq + PartialOrd,
{
    /// Returns a boolean representing if the tree is empty or not.
    pub fn is_empty(&self) -> bool {
        self.root.is_none()
    }

    /// Searches for a value in the tree returning a SearchResult that
    /// captures if the search yield a hit, miss or empty tree.  
    fn find_nearest_node(&self, value: &V) -> SearchResult<V> {
        if let Some(root) = &self.root {
            let mut next_step = root.clone();
            loop {
                if value == &next_step.inner {
                    return SearchResult::Hit(next_step.clone());
                } else if value <= &next_step.inner {
                    // if left leaf exists follow that direction.
                    match &next_step.left {
                        Some(left) => {
                            let left = left.clone();
                            next_step = left
                        }
                        // return the parent
                        None => return SearchResult::Miss(next_step),
                    }
                } else {
                    // if right leaf exists follow that direction.
                    match &next_step.right {
                        Some(right) => {
                            let right = right.clone();
                            next_step = right
                        }
                        // return the parent
                        None => return SearchResult::Miss(next_step),
                    }
                }
            }
        } else {
            SearchResult::Empty
        }
    }

    pub fn insert(mut self, value: V) -> Self {
        self.insert_mut(value);
        self
    }

    pub fn insert_mut(&mut self, value: V) {
        match self.find_nearest_node(&value) {
            SearchResult::Hit(_) => (),
            SearchResult::Empty => {
                self.root = Some(Rc::new(Node::new(
                    Color::Black,
                    value,
                    Weak::new(),
                    None,
                    None,
                )));
            }
            SearchResult::Miss(mut parent_node) => {
                let is_left = value < parent_node.inner;
                let child = Rc::new(Node::new(
                    Color::Red,
                    value,
                    Rc::downgrade(&parent_node),
                    None,
                    None,
                ));

                if is_left {
                    let _ =
                        Rc::get_mut(&mut parent_node).map(|node| node.left = Some(child.clone()));
                    //self.rebalance_mut(child, Operation::Insert);
                } else {
                    let _ =
                        Rc::get_mut(&mut parent_node).map(|node| node.right = Some(child.clone()));
                    //self.rebalance_mut(child, Operation::Insert);
                }
            }
        };
    }

    /*
    fn rebalance_mut(&mut self, node_id: NodeId, action: Operation) {
        let mut next_step = match action {
            Operation::Insert => self.needs_rebalance_after_insertion(node_id),
        };

        while let Some(step) = next_step {
            next_step = None;
            match step {
                Rebalance::LeftLeft => {
                    self.handle_ll_mut(node_id);
                }
                Rebalance::LeftRight => {
                    self.handle_lr_mut(node_id);
                }
                Rebalance::RightRight => {
                    self.handle_rr_mut(node_id);
                }
                Rebalance::RightLeft => {
                    self.handle_rl_mut(node_id);
                }
                Rebalance::Recolor(base_id) => next_step = self.recolor_mut(base_id, action),
            }
        }
    }*/

    fn needs_rebalance_after_insertion(&self, base_node: NodeRef<V>) -> Option<Rebalance<V>> {
        // short-circuit to none if the base is root.
        let base_node_direction = base_node.direction()?;
        let parent = base_node.parent.borrow().upgrade()?;
        let parent_direction = base_node.direction()?;
        let uncle_color = base_node.uncle().map_or(Color::Black, |uncle| uncle.color);

        if parent.color == Color::Red {
            if uncle_color == Color::Red {
                Some(Rebalance::Recolor(base_node))
            } else {
                match (parent_direction, base_node_direction) {
                    (Direction::Left, Direction::Left) => Some(Rebalance::LeftLeft),
                    (Direction::Left, Direction::Right) => Some(Rebalance::LeftRight),
                    (Direction::Right, Direction::Left) => Some(Rebalance::RightLeft),
                    (Direction::Right, Direction::Right) => Some(Rebalance::RightRight),
                }
            }
        } else {
            None
        }
    }

    /// Rotates left from a root node, returning the new root NodeId.
    ///  x            z
    ///   \          /
    ///    z --->  x
    ///     \       \
    ///      y       y
    fn rotate_left_mut(&mut self, x: NodeRef<V>) -> Option<NodeRef<V>> {
        self.rotate_mut(x, Direction::Left)
    }

    /// Rotates right from a root node, returning the new root NodeId.
    ///      x  z
    ///     /     \
    ///    z --->   x
    ///   /        /
    ///  y        y
    fn rotate_right_mut(&mut self, x: NodeRef<V>) -> Option<NodeRef<V>> {
        self.rotate_mut(x, Direction::Right)
    }

    /// Rotates a node by a passed direction
    fn rotate_mut(&mut self, mut x: NodeRef<V>, direction: Direction) -> Option<NodeRef<V>> {
        // if z or x aren't set return None
        let mut z = match direction {
            Direction::Left => Rc::get_mut(&mut x)?.right.take(),
            Direction::Right => Rc::get_mut(&mut x)?.left.take(),
        }?;
        let y = match direction {
            Direction::Left => Rc::get_mut(&mut z)?.left.take(),
            Direction::Right => Rc::get_mut(&mut z)?.right.take(),
        };
        let optional_upstream_parent = x.parent.upgrade();

        if let Some(mut upstream_parent) = optional_upstream_parent.clone() {
            // Switch x with z on the upstream parent.
            // safe to unwrap
            let upstream_direction = x.direction().unwrap();
            match upstream_direction {
                Direction::Left => Rc::get_mut(&mut upstream_parent)?.left.replace(z.clone()),
                Direction::Right => Rc::get_mut(&mut upstream_parent)?.right.replace(z.clone()),
            };
        } else {
            self.root = Some(z.clone());
        }

        // Set the parent of z to the upstream parent and make x a child of z.
        if let Some(z_node) = Rc::get_mut(&mut z) {
            z_node.parent = optional_upstream_parent
                .map(|parent| Rc::downgrade(&parent))
                .unwrap_or_default();
        }
        match direction {
            Direction::Left => Rc::get_mut(&mut z)?.left.replace(x.clone()),
            Direction::Right => Rc::get_mut(&mut z)?.right.replace(x.clone()),
        };

        // Set the parent of x to z and the inverse direction node of x to y if
        // it exists.
        if let Some(x_node) = Rc::get_mut(&mut x) {
            x_node.parent = Rc::downgrade(&z)
        }
        match direction {
            Direction::Left => Rc::get_mut(&mut x)?.right = y.clone(),
            Direction::Right => Rc::get_mut(&mut x)?.left = y.clone(),
        };

        // if y exists, set its parent to x.
        if let Some(mut y_node) = y {
            if let Some(y_node) = Rc::get_mut(&mut y_node) {
                y_node.parent = Rc::downgrade(&x)
            }
        }

        Some(z)
    }

    /*
    #[allow(clippy::redundant_closure)]
    fn recolor_mut(&mut self, base_id: NodeId, action: Operation) -> Option<Rebalance> {
        match action {
            Operation::Insert => self.recolor_on_insertion_mut(base_id),
        }
    }

    #[allow(clippy::redundant_closure)]
    fn recolor_on_insertion_mut(&mut self, base_id: NodeId) -> Option<Rebalance> {
        // set parent to black and return the id
        let parent_id = self.get_parent_mut(base_id).map(|parent_node| {
            parent_node.set_color_mut(Color::Black);
            parent_node.id()
        })?;

        // set uncle to black and return its id.
        let uncle_id = self.get_uncle(base_id).map(|uncle_node| uncle_node.id())?;
        self.get_mut(uncle_id).map(|uncle_node| {
            uncle_node.set_color_mut(Color::Black);
            uncle_node.id()
        })?;

        // if grandparent is black, flip to red and recurse up.
        self.get_parent_mut(parent_id)
            .and_then(|grandparent_node| match grandparent_node.color() {
                Color::Red => None,
                Color::Black => {
                    grandparent_node.set_color_mut(Color::Red);
                    Some(grandparent_node.id())
                }
            })
            .map(|grandparent_id| Rebalance::Recolor(grandparent_id))
    }

    fn handle_ll_mut(&mut self, node_id: NodeId) {
        let parent_id = self.get_parent(node_id).map(|parent| parent.id()).unwrap();
        let grandparent_id = self
            .get_grandparent(node_id)
            .map(|grandfather| grandfather.id())
            .unwrap();

        // rotate grandfather right
        self.rotate_right_mut(grandparent_id);

        // flip the colors of the original grandparent and parent
        self.get_mut(grandparent_id)
            .map(|grandfather| grandfather.flip_color_mut())
            .unwrap();
        self.get_mut(parent_id)
            .map(|grandfather| grandfather.flip_color_mut())
            .unwrap();
    }

    fn handle_lr_mut(&mut self, node_id: NodeId) {
        let parent_id = self.get_parent(node_id).map(|parent| parent.id()).unwrap();

        // rotate parent left
        self.rotate_left_mut(parent_id);
        // rotated down.
        let new_base_id = parent_id;

        // then apply an LL case
        self.handle_ll_mut(new_base_id)
    }

    fn handle_rr_mut(&mut self, node_id: NodeId) {
        let parent_id = self.get_parent(node_id).map(|parent| parent.id()).unwrap();
        let grandparent_id = self
            .get_grandparent(node_id)
            .map(|grandfather| grandfather.id())
            .unwrap();

        // rotate grandfather left
        self.rotate_left_mut(grandparent_id);

        // flip the colors of the original grandparent and parent
        self.get_mut(grandparent_id)
            .map(|grandfather| grandfather.flip_color_mut())
            .unwrap();
        self.get_mut(parent_id)
            .map(|grandfather| grandfather.flip_color_mut())
            .unwrap();
    }

    fn handle_rl_mut(&mut self, node_id: NodeId) {
        let parent_id = self.get_parent(node_id).map(|parent| parent.id()).unwrap();

        // rotate parent right
        self.rotate_right_mut(parent_id);

        // rotated down.
        let new_base_id = parent_id;

        // then apply an RR case
        self.handle_rr_mut(new_base_id)
    }*/
}

impl<V> Default for RedBlackTree<V> {
    fn default() -> Self {
        Self { root: None }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn should_return_correct_empty_state_when_tree_has_values() {
        let tree = RedBlackTree::<usize>::default();

        assert!(tree.is_empty());
        assert!(!tree.insert(5).is_empty());
    }
}
