use std::borrow::{Borrow, BorrowMut};
use std::cell::RefCell;
use std::rc::{Rc, Weak};

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

type WeakNodeRef<V> = RefCell<Weak<Node<V>>>;
type NodeRef<V> = RefCell<Rc<Node<V>>>;

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

impl<V> Node<V> {
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
        self.parent.borrow().upgrade().clone().is_none()
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

impl<V> RedBlackTree<V> {
    pub fn new(root: V) -> Self {
        Self {
            root: Some(RefCell::new(Rc::new(Node::new(
                Color::Black,
                root,
                RefCell::new(Weak::new()),
                None,
                None,
            )))),
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
            let mut next_step = root.borrow().clone();
            loop {
                if value == &next_step.inner {
                    return SearchResult::Hit(next_step.clone());
                } else if value <= &next_step.inner {
                    // if left leaf exists follow that direction.
                    match next_step.left.borrow() {
                        Some(left) => {
                            let left = left.borrow().clone();
                            next_step = left
                        }
                        // return the parent
                        None => return SearchResult::Miss(next_step),
                    }
                } else {
                    // if right leaf exists follow that direction.
                    match next_step.right.borrow() {
                        Some(right) => {
                            let right = right.borrow().clone();
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
                self.root = Some(RefCell::new(Rc::new(Node::new(
                    Color::Black,
                    value,
                    RefCell::new(Weak::new()),
                    None,
                    None,
                ))));
            }
            SearchResult::Miss(mut parent_node) => {
                let is_left = value < parent_node.inner;
                let child = Rc::new(Node::new(
                    Color::Red,
                    value,
                    RefCell::new(Rc::downgrade(&parent_node)),
                    None,
                    None,
                ));

                if is_left {
                    let _ = Rc::get_mut(&mut parent_node)
                        .map(|node| node.left = Some(RefCell::new(child.clone())));
                    //self.rebalance_mut(child, Operation::Insert);
                } else {
                    let _ = Rc::get_mut(&mut parent_node)
                        .map(|node| node.right = Some(RefCell::new(child.clone())));
                    //self.rebalance_mut(child, Operation::Insert);
                }
            }
        };
    }

    /*
    /// Inserts a value into the tree. if the value already exists,
    /// Some(NodeId) to the already defined value is returned. Otherwise None
    /// is returned.
    pub fn insert_mut(&mut self, value: V) -> Option<NodeId> {
        let next_id = NodeId::from(self.nodes.len());

        match self.find_nearest_node(&value) {
            SearchResult::Hit(node) => Some(node),
            SearchResult::Empty => {
                self.root = Some(next_id);
                self.nodes.push(Some(ColorNode::Black(Node::new(
                    next_id, value, None, None, None,
                ))));
                None
            }
            SearchResult::Miss(parent_node_id) => {
                let is_defined = match self.get_mut(parent_node_id) {
                    Some(parent_color_node) => {
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
                    self.nodes.push(Some(ColorNode::Red(Node::new(
                        next_id,
                        value,
                        Some(parent_node_id),
                        None,
                        None,
                    ))));

                    // rebalance the tree after a new insertions
                    self.rebalance_mut(next_id, Operation::Insert);
                    None
                }
            }
        }
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
