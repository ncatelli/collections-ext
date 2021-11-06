//! Provides an implementation of a Red-Black Tree for use as a priority queue.

use super::{Direction, Directional, Node, NodeRef};

extern crate alloc;
use alloc::{boxed::Box, vec::Vec};

/// Represents a type that has a Color representation in the tree.
trait Colorable {
    /// Returns the color of a specific item.
    fn color(&self) -> Color;
}

/// A subtype of the `Colored` trait that allows for mutation of its color
trait ColorableMut: Colorable {
    /// Sets the color of an object to a passed color.
    fn set_color_mut(&mut self, color: Color);
    /// Inverts the color of a node.
    /// i.e. Red -> Black, or Black -> Red
    fn set_flip_mut(&mut self);
}

impl<K, V> Colorable for NodeRef<K, V, Color> {
    fn color(&self) -> Color {
        let node = unsafe { self.0.as_ref() };
        node.attributes
    }
}

impl<K, V> ColorableMut for NodeRef<K, V, Color> {
    fn set_color_mut(&mut self, color: Color) {
        let mut node = unsafe { self.0.as_mut() };
        node.attributes = color;
    }

    fn set_flip_mut(&mut self) {
        let node = unsafe { self.0.as_mut() };
        let current_color = node.attributes;
        node.set_color_mut(current_color.flip());
    }
}

impl<K, V> Colorable for Option<NodeRef<K, V, Color>> {
    fn color(&self) -> Color {
        match self {
            Some(noderef) => noderef.color(),
            None => Color::Black,
        }
    }
}

impl<K, V> ColorableMut for Option<NodeRef<K, V, Color>> {
    fn set_color_mut(&mut self, color: Color) {
        if let Some(ref mut noderef) = self {
            noderef.set_color_mut(color)
        }
    }

    fn set_flip_mut(&mut self) {
        if let Some(ref mut noderef) = self {
            noderef.set_flip_mut()
        }
    }
}

/// Represents the three possible situations that a node can encounter on a delete,
#[derive(Clone, Copy, PartialEq)]
enum DeleteSuccessor<K, V> {
    /// Node has two children. Return the in-order successor.
    Double(Option<NodeRef<K, V, Color>>),
    /// Node has a single child.
    Single(NodeRef<K, V, Color>),
    /// Node has no children (is a leaf or root).
    /// Can be deleted directly.
    None,
}

/// InsertRebalance captures the states of an insertion rebalance operation.
enum InsertRebalance<K, V> {
    /// Represents a LeftLeft case of inbalance.
    LeftLeft(NodeRef<K, V, Color>),
    /// Represents a LeftRight case of inbalance.
    LeftRight(NodeRef<K, V, Color>),
    /// Represents a RightRight case of inbalance.
    RightRight(NodeRef<K, V, Color>),
    /// Represents a RightLeft case of inbalance.
    RightLeft(NodeRef<K, V, Color>),
    /// Contains the next base node for recoloring.
    Recolor(NodeRef<K, V, Color>),
}

/// An enumerable value representing the available colors of a node.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Color {
    Red,
    Black,
}

impl Color {
    fn flip(self) -> Self {
        match self {
            Self::Black => Self::Red,
            Self::Red => Self::Black,
        }
    }
}

impl<K, V> Colorable for Node<K, V, Color> {
    fn color(&self) -> Color {
        self.attributes
    }
}

impl<K, V> ColorableMut for Node<K, V, Color> {
    fn set_color_mut(&mut self, color: Color) {
        self.attributes = color;
    }

    fn set_flip_mut(&mut self) {
        let current_color = self.attributes;
        self.set_color_mut(current_color.flip());
    }
}

/// SearchResult represents the results of a binary tree search.
#[derive(Debug)]
enum SearchResult<K, V> {
    /// Hit signifies the exact value was found in the tree and
    /// contains a reference to the NodeId for said value.
    Hit(NodeRef<K, V, Color>),
    /// Miss represents the value was not found in the tree and represents the
    /// nearest parent node.
    Miss(NodeRef<K, V, Color>),
    /// Empty represents an empty tree.
    Empty,
}

impl<K, V> SearchResult<K, V> {
    /// Calls `f` if the self is `SearchResult::Hit` returning the result of
    /// `f` wrapped in `Some` otherwise `None` is returned.
    fn hit_then<F, B>(self, f: F) -> Option<B>
    where
        F: Fn(NodeRef<K, V, Color>) -> B,
    {
        match self {
            SearchResult::Hit(node) => Some(f(node)),
            _ => None,
        }
    }
}

/// An implementation of a Binary Tree
#[derive(Debug)]
pub struct RedBlackTree<T>
where
    T: PartialEq + PartialOrd,
{
    inner: KeyedRedBlackTree<T, ()>,
}

impl<T> RedBlackTree<T>
where
    T: PartialEq + PartialOrd,
{
    pub fn new(root: T) -> Self {
        Self {
            inner: KeyedRedBlackTree::new(root, ()),
        }
    }
}

impl<T> RedBlackTree<T>
where
    T: PartialEq + PartialOrd,
{
    /// Returns a boolean representing if the tree is empty or not.
    ///
    /// # Example
    ///
    /// ```
    /// use collections_ext::tree::redblack::RedBlackTree;
    ///
    /// assert!(RedBlackTree::<usize>::default().is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }

    /// Returns the number of nodes in a tree.
    ///
    /// # Example
    ///
    /// ```
    /// use collections_ext::tree::redblack::RedBlackTree;
    ///
    /// let tree = RedBlackTree::<usize>::default();
    ///
    /// assert_eq!(0, tree.len());
    ///
    /// assert_eq!(2, tree.insert(5).insert(10).len());
    /// ```
    pub fn len(&self) -> usize {
        self.inner.len()
    }

    /// Searches for a node in the tree that satisfies the given predicate.
    ///
    /// # Example
    ///
    /// ```
    /// use collections_ext::tree::redblack::RedBlackTree;
    ///
    /// let tree = (0..1024).fold(RedBlackTree::default(), |tree, x| tree.insert(x));
    /// assert!(tree.find(|x| x == &&513).is_some());
    /// ```
    pub fn find<P>(&self, predicate: P) -> Option<&T>
    where
        P: FnMut(&&T) -> bool,
    {
        self.traverse_in_order().find(predicate)
    }

    /// Inserts a value `T` into the tree returning a the modified tree in
    /// place.
    ///
    /// # Example
    ///
    /// ```
    /// use collections_ext::tree::redblack::RedBlackTree;
    ///
    /// RedBlackTree::new(5).insert(10);
    /// ```
    pub fn insert(mut self, value: T) -> Self {
        self.insert_mut(value);
        self
    }

    /// Inserts a value `T` into the tree. If the value already exists in the
    /// tree, nothing is done.
    ///
    /// # Example
    ///
    /// ```
    /// use collections_ext::tree::redblack::RedBlackTree;
    ///
    /// let mut tree = RedBlackTree::new(5);
    /// tree.insert_mut(10);
    /// ```
    pub fn insert_mut(&mut self, value: T) {
        unsafe { self.inner.insert_mut_unchecked(value, ()) }
    }

    /// Remove a node, `T`, from the tree, returning the modifed tree.
    ///
    /// # Example
    ///
    /// ```
    /// use collections_ext::tree::redblack::RedBlackTree;
    ///
    /// let tree = RedBlackTree::new(5).insert(10);
    /// assert!(!tree.remove(&10).remove_mut(&10));
    /// ```
    pub fn remove(mut self, value: &T) -> Self {
        self.remove_mut(value);
        self
    }

    /// Remove a value, `T`, from the tree in place.
    ///
    /// # Example
    ///
    /// ```
    /// use collections_ext::tree::redblack::RedBlackTree;
    ///
    /// let mut tree = RedBlackTree::new(5).insert(10);
    /// assert!(tree.remove_mut(&10));
    ///
    /// // returns false if the value isn't in tree.
    /// assert!(!tree.remove_mut(&20));
    /// ```
    pub fn remove_mut(&mut self, value: &T) -> bool {
        unsafe { self.inner.remove_mut_unchecked(value) }.is_some()
    }

    /// Returns the node with the left-most value (smallest) or `None` if the
    /// tree is empty.
    ///
    /// # Example
    ///
    /// ```
    /// use collections_ext::tree::redblack::RedBlackTree;
    ///
    /// let tree = RedBlackTree::new(5).insert(10);
    /// assert_eq!(Some(&5), tree.min());
    /// ```
    pub fn min(&self) -> Option<&T> {
        self.inner.min().map(|(value, _)| value)
    }

    /// Returns the node with the right-most value (largest) or `None` if the
    /// tree is empty.
    ///
    /// # Example
    ///
    /// ```
    /// use collections_ext::tree::redblack::RedBlackTree;
    ///
    /// let tree = RedBlackTree::new(5).insert(10);
    /// assert_eq!(Some(&10), tree.max());
    /// ```
    pub fn max(&self) -> Option<&T> {
        self.inner.max().map(|(value, _)| value)
    }

    /// Returns an Iterator for traversing an array in order.
    ///
    /// # Example
    ///
    /// ```
    /// use collections_ext::tree::redblack::RedBlackTree;
    ///
    /// let tree = RedBlackTree::new(5);
    /// assert_eq!(Some(&5), tree.traverse_in_order().next());
    /// ```
    pub fn traverse_in_order(&self) -> IterInOrder<'_, T> {
        IterInOrder::new(&self.inner)
    }
}

impl<T> Default for RedBlackTree<T>
where
    T: PartialEq + PartialOrd,
{
    fn default() -> Self {
        Self {
            inner: KeyedRedBlackTree::default(),
        }
    }
}

/// An implementation of a Red-Black Tree
#[derive(Debug)]
pub struct KeyedRedBlackTree<K, V>
where
    K: PartialEq + PartialOrd,
{
    len: usize,
    root: Option<NodeRef<K, V, Color>>,
}

impl<K, V> KeyedRedBlackTree<K, V>
where
    K: PartialEq + PartialOrd,
{
    /// Instantiates a new Red-Black tree from an initial value.
    pub fn new(key: K, value: V) -> Self {
        let node = Node::new(key, value, None, None, None, Color::Black);
        let root_ptr = NodeRef::from(node);

        Self {
            len: 1,
            root: Some(root_ptr),
        }
    }
}

// helper methods
impl<K, V> KeyedRedBlackTree<K, V>
where
    K: PartialEq + PartialOrd,
{
    /// Returns a boolean representing if the tree is empty or not.
    ///
    /// # Example
    ///
    /// ```
    /// use collections_ext::tree::redblack::KeyedRedBlackTree;
    ///
    /// assert!(KeyedRedBlackTree::<usize, usize>::default().is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Returns the number of nodes in a tree.
    ///
    /// # Example
    ///
    /// ```
    /// use collections_ext::tree::redblack::KeyedRedBlackTree;
    ///
    /// let tree = KeyedRedBlackTree::<usize, usize>::default();
    ///
    /// assert_eq!(0, tree.len());
    ///
    /// assert_eq!(2, tree.insert(5, 10).insert(15, 20).len());
    /// ```
    pub fn len(&self) -> usize {
        self.len
    }

    /// Searches for a value in the tree returning a SearchResult that
    /// captures if the search yield a hit, miss or empty tree.  
    unsafe fn find_nearest_node(&self, key: &K) -> SearchResult<K, V> {
        if let Some(root) = self.root {
            let mut next_step = root;
            loop {
                let next_step_node = next_step.as_ref();

                if key == &next_step_node.key {
                    return SearchResult::Hit(next_step);
                } else if key <= &next_step_node.key {
                    // if left leaf exists follow that direction.
                    match &next_step_node.left {
                        Some(left) => next_step = *left,
                        // return the parent
                        None => return SearchResult::Miss(next_step),
                    }
                } else {
                    // if right leaf exists follow that direction.
                    match &next_step_node.right {
                        Some(right) => next_step = *right,
                        // return the parent
                        None => return SearchResult::Miss(next_step),
                    }
                }
            }
        } else {
            SearchResult::Empty
        }
    }

    /// Searches for a node in the tree that satisfies the given predicate.
    ///
    /// # Example
    ///
    /// ```
    /// use collections_ext::tree::redblack::KeyedRedBlackTree;
    ///
    /// let tree = (0..1024).fold(KeyedRedBlackTree::default(), |tree, x| tree.insert(x, ()));
    /// assert!(tree.find(|x| x == &&513).is_some());
    /// ```
    pub fn find<P>(&self, mut predicate: P) -> Option<&V>
    where
        P: FnMut(&&K) -> bool,
    {
        self.traverse_in_order()
            .find(|(k, _)| predicate(k))
            .map(|(_, v)| v)
    }

    /// Searches for a node in the tree that satisfies the given predicate.
    ///
    /// # Example
    ///
    /// ```
    /// use collections_ext::tree::redblack::KeyedRedBlackTree;
    ///
    /// let tree = (0..1024).fold(KeyedRedBlackTree::default(), |tree, x| tree.insert(x, x*2));
    /// assert!(tree.find_with_key_value(|k, v| k == &&513 && v == &&(513 * 2)).is_some());
    /// ```
    pub fn find_with_key_value<P>(&self, mut predicate: P) -> Option<&V>
    where
        P: core::ops::FnMut(&&K, &&V) -> bool,
    {
        self.traverse_in_order()
            .find(|(k, v)| predicate(k, v))
            .map(|(_, v)| v)
    }

    /// Inserts a key `K` and value `V` into the tree returning a the modified
    /// tree in place.
    ///
    /// # Example
    ///
    /// ```
    /// use collections_ext::tree::redblack::KeyedRedBlackTree;
    ///
    /// KeyedRedBlackTree::new(5, 10).insert(15, 20);
    /// ```
    pub fn insert(mut self, key: K, value: V) -> Self {
        self.insert_mut(key, value);
        self
    }

    /// Inserts a key `K` and value `V` into the tree. If the value already
    /// exists in the tree, nothing is done.
    ///
    /// # Example
    ///
    /// ```
    /// use collections_ext::tree::redblack::KeyedRedBlackTree;
    ///
    /// let mut tree = KeyedRedBlackTree::new(5, 10);
    /// tree.insert(15, 20);
    /// ```
    pub fn insert_mut(&mut self, key: K, value: V) {
        unsafe { self.insert_mut_unchecked(key, value) }
    }

    unsafe fn insert_mut_unchecked(&mut self, key: K, value: V) {
        let nearest = self.find_nearest_node(&key);
        match nearest {
            SearchResult::Hit(_) => (),
            SearchResult::Empty => {
                let node = Node::new(key, value, None, None, None, Color::Black);

                self.len += 1;
                self.root = Some(NodeRef::from(node));
            }
            SearchResult::Miss(mut parent_node) => {
                let is_left = key < parent_node.as_ref().key;
                let child = Node::new(key, value, Some(parent_node), None, None, Color::Red);
                let child_ptr = NodeRef::from(child);

                self.len += 1;
                if is_left {
                    parent_node.as_mut().left = Some(child_ptr);
                } else {
                    parent_node.as_mut().right = Some(child_ptr);
                }

                if let Some(rebalance_operation) = self.needs_rebalance_after_insertion(child_ptr) {
                    self.rebalance_on_insertion_mut(rebalance_operation)
                }
            }
        };
    }

    /// Remove a node, `K` from the tree, returning the modifed tree.
    ///
    /// # Example
    ///
    /// ```
    /// use collections_ext::tree::redblack::KeyedRedBlackTree;
    ///
    /// let tree = KeyedRedBlackTree::new(5, 10).insert(15, 20);
    /// assert_eq!(None, tree.remove(&5).remove_mut(&5));
    /// ```
    pub fn remove(mut self, key: &K) -> Self {
        self.remove_mut(key);
        self
    }

    /// Remove a value, `K`, from the tree in place. Optionally returning an
    /// owned `V` associated with the passed `K`.
    ///
    /// # Example
    ///
    /// ```
    /// use collections_ext::tree::redblack::KeyedRedBlackTree;
    ///
    /// let mut tree = KeyedRedBlackTree::new(5, 10).insert(15, 20);
    /// assert_eq!(Some(10), tree.remove_mut(&5));
    /// ```
    pub fn remove_mut(&mut self, key: &K) -> Option<V> {
        unsafe { self.remove_mut_unchecked(key) }
    }

    unsafe fn remove_mut_unchecked(&mut self, key: &K) -> Option<V> {
        let node_to_be_deleted = self.find_nearest_node(key).hit_then(|node| node)?;
        let optional_node_direction = node_to_be_deleted.as_ref().direction();
        let original_color = node_to_be_deleted.color();
        let optional_parent = node_to_be_deleted.as_ref().parent;
        let optional_left_child = node_to_be_deleted.as_ref().left;
        let optional_right_child = node_to_be_deleted.as_ref().right;

        let delete_successor = match (optional_left_child, optional_right_child) {
            (None, None) => DeleteSuccessor::None,
            (Some(successor), None) | (None, Some(successor)) => DeleteSuccessor::Single(successor),
            (Some(_), Some(_)) => {
                DeleteSuccessor::Double(self.find_in_order_successor(node_to_be_deleted))
            }
        };

        match delete_successor {
            DeleteSuccessor::Single(mut x) => {
                // convert to a box so it is dropped
                let boxed_node_to_be_deleted = Box::from_raw(node_to_be_deleted.as_ptr());

                // transplant color for successor
                x.set_color_mut(original_color);

                if let Some(direction) = optional_node_direction {
                    // if it has a direction it's safe to unwrap.
                    let mut parent = optional_parent.expect("unable to unwrap parent");
                    match direction {
                        Direction::Left => parent.as_mut().left = Some(x),
                        Direction::Right => parent.as_mut().right = Some(x),
                    };
                } else {
                    self.root = Some(x);
                }

                x.as_mut().parent = boxed_node_to_be_deleted.parent;

                self.len -= 1;
                // Take ownership of the inner value
                let inner = boxed_node_to_be_deleted.value;
                Some(inner)
            }
            // can be directly deleted
            DeleteSuccessor::None => {
                // convert to a box so it is dropped
                let boxed_node_to_be_deleted = Box::from_raw(node_to_be_deleted.as_ptr());
                if let Some(direction) = optional_node_direction {
                    // if it has a direction it's safe to unwrap.
                    let mut parent = optional_parent.expect("unable to unwrap parent");
                    match direction {
                        Direction::Left => parent.as_mut().left = None,
                        Direction::Right => parent.as_mut().right = None,
                    };
                } else {
                    // Mark the tree as empty if this is the last node.
                    self.root = None;
                }

                self.len -= 1;
                // Take ownership of the inner value
                let inner = boxed_node_to_be_deleted.value;
                Some(inner)
            }
            DeleteSuccessor::Double(in_order_successor) => {
                // convert to a box so it is dropped
                let boxed_node_to_be_deleted = Box::from_raw(node_to_be_deleted.as_ptr());
                let mut y =
                    in_order_successor.expect("in order successor is null on a two child delete");
                let y_direction = y.as_ref().direction().expect("y has no parent");

                let x = y.as_ref().right;
                let mut x_parent = y;
                let mut x_direction = Direction::Right;

                // If y is not a child of nodeToBeDeletedtransplant y with rightChild of y
                if y.as_ref().parent != Some(node_to_be_deleted) {
                    // safe to unwrap, y is guaranteed a parent by the sucessor check.
                    let mut y_parent = y.as_ref().parent.expect("y has no parent");
                    x_parent = y_parent;
                    x_direction = y_direction;

                    match y_direction {
                        Direction::Left => y_parent.as_mut().left = x,
                        Direction::Right => y_parent.as_mut().right = x,
                    }
                }

                // Transplant nodeToBeDeleted with y.
                // Set the color of y with originalColor.
                y.as_mut().parent = boxed_node_to_be_deleted.parent;
                match boxed_node_to_be_deleted.direction() {
                    // safe to unwrap parents because of direction check
                    Some(Direction::Left) => {
                        boxed_node_to_be_deleted.parent.unwrap().as_mut().left = Some(y)
                    }
                    Some(Direction::Right) => {
                        boxed_node_to_be_deleted.parent.unwrap().as_mut().right = Some(y)
                    }
                    None => self.root = Some(y),
                };

                y.as_mut().left = boxed_node_to_be_deleted.left;
                if let Some(mut left) = boxed_node_to_be_deleted.left {
                    left.as_mut().parent = Some(y);
                }

                y.set_color_mut(boxed_node_to_be_deleted.color());

                if original_color == Color::Black {
                    // safe to unwrap, cant reach unless x isn't root.
                    self.rebalance_on_deletion_mut(x, x_direction, Some(x_parent));
                }

                self.len -= 1;
                let inner = boxed_node_to_be_deleted.value;
                Some(inner)
            }
        }
    }

    unsafe fn find_in_order_successor(
        &self,
        node: NodeRef<K, V, Color>,
    ) -> Option<NodeRef<K, V, Color>> {
        let optional_right_child = node.as_ref().right;

        optional_right_child.and_then(|child| self.find_min_from(child))
    }

    unsafe fn rebalance_on_insertion_mut(&mut self, rebalance_operation: InsertRebalance<K, V>) {
        let mut next_step = Some(rebalance_operation);

        while let Some(step) = next_step {
            next_step = None;
            match step {
                InsertRebalance::LeftLeft(node) => {
                    self.handle_ll_mut(node);
                }
                InsertRebalance::LeftRight(node) => {
                    self.handle_lr_mut(node);
                }
                InsertRebalance::RightRight(node) => {
                    self.handle_rr_mut(node);
                }
                InsertRebalance::RightLeft(node) => {
                    self.handle_rl_mut(node);
                }
                InsertRebalance::Recolor(node) => next_step = self.recolor_on_insertion_mut(node),
            }
        }
    }

    unsafe fn needs_rebalance_after_insertion(
        &self,
        base_node: NodeRef<K, V, Color>,
    ) -> Option<InsertRebalance<K, V>> {
        // short-circuit to none if the base is root.
        let base = base_node.as_ref();
        let base_node_direction = base.direction()?;
        let parent = base.parent()?;
        let parent_direction = parent.direction()?;
        let uncle_color = base.uncle().color();

        if parent.color() == Color::Red {
            if uncle_color == Color::Red {
                Some(InsertRebalance::Recolor(base_node))
            } else {
                match (parent_direction, base_node_direction) {
                    (Direction::Left, Direction::Left) => {
                        Some(InsertRebalance::LeftLeft(base_node))
                    }
                    (Direction::Left, Direction::Right) => {
                        Some(InsertRebalance::LeftRight(base_node))
                    }
                    (Direction::Right, Direction::Left) => {
                        Some(InsertRebalance::RightLeft(base_node))
                    }
                    (Direction::Right, Direction::Right) => {
                        Some(InsertRebalance::RightRight(base_node))
                    }
                }
            }
        } else {
            None
        }
    }

    #[allow(unused_assignments)]
    unsafe fn rebalance_on_deletion_mut(
        &mut self,
        mut x: Option<NodeRef<K, V, Color>>,
        x_direction: Direction,
        mut optional_x_parent: Option<NodeRef<K, V, Color>>,
    ) {
        while optional_x_parent.is_some() && x.color() == Color::Black {
            let mut x_parent = optional_x_parent.unwrap();
            match x_direction {
                Direction::Left => {
                    let mut optional_w = x_parent.as_ref().right;
                    if let Some(mut w) = optional_w {
                        if w.color() == Color::Red {
                            w.set_color_mut(Color::Black);
                            x_parent.set_color_mut(Color::Red);
                            self.rotate_left_mut(x_parent);
                            optional_w = x_parent.as_ref().right;
                        }

                        let w_left_child = w.as_ref().left;
                        let w_left_child_color = w_left_child.color();
                        let w_right_child = w.as_ref().right;
                        let w_right_child_color = w_right_child.color();
                        if w_left_child_color == Color::Black && w_right_child_color == Color::Black
                        {
                            w.set_color_mut(Color::Red);
                            optional_x_parent = x_parent.as_ref().parent;
                            x = Some(x_parent)
                        } else {
                            if w_right_child_color == Color::Black {
                                if let Some(mut w_left_child) = w_left_child {
                                    w_left_child.set_color_mut(Color::Black);
                                }
                                w.set_color_mut(Color::Red);
                                self.rotate_right_mut(w);
                                optional_w = x_parent.as_ref().right;
                            }

                            w.set_color_mut(x_parent.color());
                            x_parent.set_color_mut(Color::Black);
                            if let Some(mut w_right_child) = w_right_child {
                                w_right_child.set_color_mut(Color::Black);
                            }
                            self.rotate_left_mut(x_parent);
                            x = self.root;
                            break;
                        }
                    }
                }
                Direction::Right => {
                    let mut optional_w = x_parent.as_ref().left;
                    if let Some(mut w) = optional_w {
                        if w.color() == Color::Red {
                            w.set_color_mut(Color::Black);
                            x_parent.set_color_mut(Color::Red);
                            self.rotate_right_mut(x_parent);
                            optional_w = x_parent.as_ref().left;
                        }

                        let w_left_child = w.as_ref().left;
                        let w_left_child_color = w_left_child.color();
                        let w_right_child = w.as_ref().right;
                        let w_right_child_color = w_right_child.color();
                        if w_left_child_color == Color::Black && w_right_child_color == Color::Black
                        {
                            w.set_color_mut(Color::Red);
                            optional_x_parent = x_parent.as_ref().parent;
                            x = Some(x_parent)
                        } else {
                            if w_right_child_color == Color::Black {
                                if let Some(mut w_left_child) = w_left_child {
                                    w_left_child.set_color_mut(Color::Black);
                                }
                                w.set_color_mut(Color::Red);
                                self.rotate_left_mut(w);
                                optional_w = x_parent.as_ref().left;
                            }

                            w.set_color_mut(x_parent.as_ref().color());
                            x_parent.set_color_mut(Color::Black);
                            if let Some(mut w_left_child) = w_left_child {
                                w_left_child.set_color_mut(Color::Black);
                            }
                            self.rotate_right_mut(x_parent);
                            x = self.root;
                            break;
                        }
                    }
                }
            }
        }
    }

    /// Rotates left from a root node, returning the new root NodeId.
    ///  x            z
    ///   \          /
    ///    z --->  x
    ///     \       \
    ///      y       y
    unsafe fn rotate_left_mut(&mut self, x: NodeRef<K, V, Color>) -> Option<NodeRef<K, V, Color>> {
        self.rotate_mut(x, Direction::Left)
    }

    /// Rotates right from a root node, returning the new root NodeId.
    ///      x  z
    ///     /     \
    ///    z --->   x
    ///   /        /
    ///  y        y
    unsafe fn rotate_right_mut(&mut self, x: NodeRef<K, V, Color>) -> Option<NodeRef<K, V, Color>> {
        self.rotate_mut(x, Direction::Right)
    }

    /// Rotates a node by a passed direction
    unsafe fn rotate_mut(
        &mut self,
        mut x_node_ref: NodeRef<K, V, Color>,
        direction: Direction,
    ) -> Option<NodeRef<K, V, Color>> {
        // if z or x aren't set return None
        let mut z = match direction {
            Direction::Left => x_node_ref.as_mut().right.take(),
            Direction::Right => x_node_ref.as_mut().left.take(),
        }?;

        let y = match direction {
            Direction::Left => z.as_mut().left.take(),
            Direction::Right => z.as_mut().right.take(),
        };

        let optional_upstream_parent = x_node_ref.as_ref().parent;

        if let Some(mut upstream_parent) = optional_upstream_parent {
            // Switch x with z on the upstream parent.
            // safe to unwrap
            let upstream_direction = x_node_ref.direction().unwrap();
            let parent = upstream_parent.as_mut();
            match upstream_direction {
                Direction::Left => parent.left.replace(z),
                Direction::Right => parent.right.replace(z),
            };
        } else {
            self.root = Some(z);
        }

        // Set the parent of z to the upstream parent and make x a child of z.
        z.as_mut().parent = optional_upstream_parent;
        {
            let z_ref = z.as_mut();
            match direction {
                Direction::Left => z_ref.left.replace(x_node_ref),
                Direction::Right => z_ref.right.replace(x_node_ref),
            };
        }

        // Set the parent of x to z and the inverse direction node of x to y if
        // it exists.
        {
            let x = x_node_ref.as_mut();
            x.parent = Some(z);
            match direction {
                Direction::Left => x.right = y,
                Direction::Right => x.left = y,
            };
        }

        // if y exists, set its parent to x.
        if let Some(mut y_node) = y {
            y_node.as_mut().parent = Some(x_node_ref);
        }

        Some(z)
    }

    unsafe fn recolor_on_insertion_mut(
        &mut self,
        base_node_ref: NodeRef<K, V, Color>,
    ) -> Option<InsertRebalance<K, V>> {
        let base_node = base_node_ref.as_ref();

        // set parent to black and return the id
        let mut parent = base_node.parent()?;
        parent.set_color_mut(Color::Black);

        // set uncle to black and return its id.
        let mut uncle = base_node.uncle()?;
        uncle.set_color_mut(Color::Black);

        // if grandparent is black, flip to red and recurse up.
        let mut grandparent = base_node.grandparent();
        match grandparent.color() {
            Color::Red => None,
            Color::Black => {
                grandparent.set_color_mut(Color::Red);
                grandparent
            }
        }
        .map(InsertRebalance::Recolor)
    }

    unsafe fn handle_ll_mut(&mut self, node: NodeRef<K, V, Color>) {
        let mut parent = node.as_ref().parent.unwrap();
        let mut grandparent = node.as_ref().grandparent().unwrap();

        // rotate grandfather right
        self.rotate_right_mut(grandparent);

        // flip the colors of the original grandparent and parent
        let grandparent_color = grandparent.color();
        grandparent.as_mut().set_color_mut(grandparent_color.flip());
        let parent_color = parent.color();
        parent.as_mut().set_color_mut(parent_color.flip());
    }

    unsafe fn handle_lr_mut(&mut self, node: NodeRef<K, V, Color>) {
        let parent = node.as_ref().parent.unwrap();

        // rotate parent left
        self.rotate_left_mut(parent);

        // rotated down.
        let new_child_node = parent;

        // then apply an LL case
        self.handle_ll_mut(new_child_node)
    }

    unsafe fn handle_rr_mut(&mut self, node: NodeRef<K, V, Color>) {
        let mut parent = node.as_ref().parent.unwrap();
        let mut grandparent = node.as_ref().grandparent().unwrap();

        // rotate grandfather left
        self.rotate_left_mut(grandparent);

        // flip the colors of the original grandparent and parent
        let grandparent_color = grandparent.color();
        grandparent.as_mut().set_color_mut(grandparent_color.flip());
        let parent_color = parent.color();
        parent.as_mut().set_color_mut(parent_color.flip());
    }

    unsafe fn handle_rl_mut(&mut self, node: NodeRef<K, V, Color>) {
        let parent = node.as_ref().parent.unwrap();
        // rotate parent right
        self.rotate_right_mut(parent);

        // rotated down.
        let new_child_node = parent;

        // then apply an RR case
        self.handle_rr_mut(new_child_node)
    }

    /// Returns the node with the left-most value (smallest) or `None` if the
    /// tree is empty.
    ///
    /// # Example
    ///
    /// ```
    /// use collections_ext::tree::redblack::KeyedRedBlackTree;
    ///
    /// let tree = KeyedRedBlackTree::new(5, 10).insert(15, 20);
    /// assert_eq!(Some((&5, &10)), tree.min());
    /// ```
    pub fn min(&self) -> Option<(&K, &V)> {
        unsafe {
            self.root
                .and_then(|base_node| self.find_min_from(base_node))
                .map(|node_ref| node_ref.as_ptr())
                .map(|node| (&(*node).key, &(*node).value))
        }
    }

    /// Returns the node with the left-most value (smallest) or `None`, if
    /// empty, starting from a given base node.
    unsafe fn find_min_from(&self, base: NodeRef<K, V, Color>) -> Option<NodeRef<K, V, Color>> {
        let mut current = Some(base);
        let mut left_most_node = current;
        while let Some(id) = current {
            left_most_node = current;
            current = id.as_ref().left;
        }
        left_most_node
    }

    /// Returns the node with the right-most value (largest) or `None` if the
    /// tree is empty.
    ///
    /// # Example
    ///
    /// ```
    /// use collections_ext::tree::redblack::KeyedRedBlackTree;
    ///
    /// let tree = KeyedRedBlackTree::new(5, 10).insert(15, 20);
    /// assert_eq!(Some((&15, &20)), tree.max());
    /// ```
    pub fn max(&self) -> Option<(&K, &V)> {
        unsafe {
            self.root
                .and_then(|base_node| self.find_max_from(base_node))
                .map(|node_ref| node_ref.as_ptr())
                .map(|node| (&(*node).key, &(*node).value))
        }
    }

    /// Returns the node with the right-most value (largest) or `None`, if
    /// empty, starting from a given base node.
    unsafe fn find_max_from(
        &self,
        base_node_id: NodeRef<K, V, Color>,
    ) -> Option<NodeRef<K, V, Color>> {
        let mut current = Some(base_node_id);
        let mut right_most_node = current;
        while let Some(id) = current {
            right_most_node = current;
            current = id.as_ref().right;
        }
        right_most_node
    }

    /// Returns an Iterator for traversing an array in order, returning the
    /// key/value mapping of the tree.
    ///
    /// # Example
    ///
    /// ```
    /// use collections_ext::tree::redblack::KeyedRedBlackTree;
    ///
    /// let tree = KeyedRedBlackTree::new(5, 10);
    /// assert_eq!(Some((&5, &10)), tree.traverse_in_order().next());
    /// ```
    pub fn traverse_in_order(&self) -> IterInOrderWithKeyValue<'_, K, V> {
        IterInOrderWithKeyValue::new(self)
    }
}

impl<K, V> Drop for KeyedRedBlackTree<K, V>
where
    K: PartialOrd + PartialEq,
{
    fn drop(&mut self) {
        let mut next = self.min();
        while let Some((next_key, _)) = next {
            unsafe {
                let node = self
                    .find_nearest_node(next_key)
                    .hit_then(|node| node)
                    .unwrap();
                let match_key = &node.as_ptr().as_ref().unwrap().key;
                self.remove_mut(match_key);

                next = self.min();
            }
        }

        self.root = None;
    }
}

impl<K, V> Default for KeyedRedBlackTree<K, V>
where
    K: PartialEq + PartialOrd,
{
    fn default() -> Self {
        Self { len: 0, root: None }
    }
}

pub struct IterInOrderWithKeyValue<'a, K, V>
where
    K: PartialEq + PartialOrd + 'a,
{
    inner: core::marker::PhantomData<&'a KeyedRedBlackTree<K, V>>,
    left_most_node: Option<NodeRef<K, V, Color>>,
    stack: Vec<NodeRef<K, V, Color>>,
}

impl<'a, K, V: 'a> IterInOrderWithKeyValue<'a, K, V>
where
    K: PartialEq + PartialOrd + 'a,
{
    pub fn new(inner: &'a KeyedRedBlackTree<K, V>) -> Self {
        Self {
            inner: core::marker::PhantomData,
            left_most_node: inner.root,
            stack: Vec::new(),
        }
    }
}

impl<'a, K, V: 'a> Iterator for IterInOrderWithKeyValue<'a, K, V>
where
    K: PartialEq + PartialOrd + 'a,
{
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(id) = self.left_most_node {
            self.stack.push(id);

            self.left_most_node = id.as_ref().left;
        }
        if let Some(up_from_current) = self.stack.pop() {
            self.left_most_node = up_from_current.as_ref().right;
            let node = unsafe { &(*up_from_current.as_ptr()) };

            Some((&node.key, &node.value))
        } else {
            None
        }
    }
}

pub struct IterInOrder<'a, T>
where
    T: PartialEq + PartialOrd + 'a,
{
    inner: IterInOrderWithKeyValue<'a, T, ()>,
}

impl<'a, T: 'a> IterInOrder<'a, T>
where
    T: PartialEq + PartialOrd + 'a,
{
    pub fn new(inner: &'a KeyedRedBlackTree<T, ()>) -> Self {
        Self {
            inner: IterInOrderWithKeyValue::new(inner),
        }
    }
}

impl<'a, T: 'a> Iterator for IterInOrder<'a, T>
where
    T: PartialEq + PartialOrd + 'a,
{
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|(value, _)| value)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    extern crate alloc;
    use alloc::vec;

    #[test]
    fn should_return_correct_empty_state_when_tree_has_values() {
        let tree = KeyedRedBlackTree::<usize, ()>::default();

        assert!(tree.is_empty());
        assert!(!tree.insert(5, ()).is_empty());
    }

    #[test]
    fn should_paint_newly_inserted_nodes_red() {
        let node_values = [10, 5, 15];
        let [root_val, left_val, right_val] = node_values;
        let tree = node_values
            .to_vec()
            .into_iter()
            .fold(KeyedRedBlackTree::default(), |tree, x| tree.insert(x, ()));

        let root = unsafe {
            tree.find_nearest_node(&root_val)
                .hit_then(|node| node.color())
        };
        let left = unsafe {
            tree.find_nearest_node(&left_val)
                .hit_then(|node| node.color())
        };
        let right = unsafe {
            tree.find_nearest_node(&right_val)
                .hit_then(|node| node.color())
        };

        assert_eq!(Some(Color::Black), root);
        assert_eq!(Some(Color::Red), left);
        assert_eq!(Some(Color::Red), right);
    }

    #[test]
    fn should_recolor_node_if_two_red_nodes_occur() {
        let node_values = [15, 20, 5, 10];
        let [grandparent_val, uncle_val, child_val, parent_val] = node_values;
        let tree = node_values
            .to_vec()
            .into_iter()
            .fold(KeyedRedBlackTree::default(), |tree, x| tree.insert(x, ()));

        let child = unsafe {
            tree.find_nearest_node(&child_val)
                .hit_then(|node| (node.as_ref().color(), node.as_ref().key))
        };

        let parent = unsafe {
            tree.find_nearest_node(&parent_val)
                .hit_then(|node| (node.as_ref().color(), node.as_ref().key))
        };

        let uncle = unsafe {
            tree.find_nearest_node(&uncle_val)
                .hit_then(|node| (node.as_ref().color(), node.as_ref().key))
        };

        let grandparent = unsafe {
            tree.find_nearest_node(&grandparent_val)
                .hit_then(|node| (node.as_ref().color(), node.as_ref().key))
        };

        assert_eq!(Some((Color::Black, child_val)), child);
        assert_eq!(Some((Color::Red, parent_val)), parent);
        assert_eq!(Some((Color::Black, uncle_val)), uncle);
        assert_eq!(Some((Color::Red, grandparent_val)), grandparent);
    }

    #[test]
    fn should_return_correct_parent_relationships_on_left_rotation() {
        let mut tree = vec![10, 5, 15]
            .into_iter()
            .fold(KeyedRedBlackTree::default(), |tree, x| tree.insert(x, ()));

        // rotate the root of the tree left
        unsafe { tree.rotate_left_mut(tree.root.unwrap()) };

        let ten = unsafe { tree.find_nearest_node(&10).hit_then(|node| node) }.unwrap();
        let five = unsafe { tree.find_nearest_node(&5).hit_then(|node| node) }.unwrap();
        let fifteen = unsafe { tree.find_nearest_node(&15).hit_then(|node| node) }.unwrap();

        // five's new parent should be the 10 node.
        assert_eq!(Some(ten), five.as_ref().parent);

        // ten's new parent should be the fifteen node and new child should be
        // 5.
        assert_eq!(Some(fifteen), ten.as_ref().parent);
        assert_eq!(Some(five), ten.as_ref().left);

        // fifteen is root and is the parent of 10 node.
        assert!(fifteen.as_ref().parent == None);
        assert_eq!(Some(ten), fifteen.as_ref().left);
    }

    #[test]
    fn should_return_correct_parent_relationships_on_right_rotation() {
        let mut tree = vec![10, 5, 15]
            .into_iter()
            .fold(KeyedRedBlackTree::default(), |tree, x| tree.insert(x, ()));

        // rotate the root of the tree right
        unsafe { tree.rotate_right_mut(tree.root.unwrap()) };

        let ten = unsafe { tree.find_nearest_node(&10).hit_then(|node| node) }.unwrap();
        let five = unsafe { tree.find_nearest_node(&5).hit_then(|node| node) }.unwrap();
        let fifteen = unsafe { tree.find_nearest_node(&15).hit_then(|node| node) }.unwrap();

        // five is root and is the parent of 10 node.
        assert!(five.as_ref().parent == None);
        assert_eq!(Some(ten), five.as_ref().right);

        // 10's new parent should be the 5 node and new child should be
        // 15.
        assert_eq!(Some(five), ten.as_ref().parent);
        assert_eq!(Some(fifteen), ten.as_ref().right);

        // fifteens's new parent should be the 10 node.
        assert_eq!(Some(ten), fifteen.as_ref().parent);
    }

    #[test]
    fn should_yield_correct_min_and_max_for_a_given_tree() {
        let tree = vec![10, 5, 15, 25, 20]
            .into_iter()
            .fold(KeyedRedBlackTree::default(), |tree, x| tree.insert(x, ()));

        assert_eq!(Some((&25, &())), tree.max());
        assert_eq!(Some((&5, &())), tree.min());

        let empty_tree = KeyedRedBlackTree::<usize, ()>::default();

        assert_eq!(None, empty_tree.max());
        assert_eq!(None, empty_tree.min());
    }

    #[test]
    fn should_traverse_in_order() {
        let tree = vec![10, 5, 15, 25, 20]
            .into_iter()
            .fold(KeyedRedBlackTree::default(), |tree, x| tree.insert(x, ()));

        let mut i = tree.traverse_in_order();

        assert_eq!(Some((&5, &())), i.next());
        assert_eq!(Some((&10, &())), i.next());
        assert_eq!(Some((&15, &())), i.next());
        assert_eq!(Some((&20, &())), i.next());
        assert_eq!(Some((&25, &())), i.next());
        assert_eq!(None, i.next());

        let tree = (0..1024)
            .rev()
            .fold(KeyedRedBlackTree::default(), |tree, x| tree.insert(x, ()));

        let received: Vec<u16> = tree.traverse_in_order().map(|(k, _)| k).copied().collect();
        let expected: Vec<u16> = (0..1024).collect();
        assert_eq!(expected, received);
    }

    #[test]
    fn should_remove_node_with_no_children() {
        let node_values = [10, 5, 1, 15];
        let tree = node_values
            .to_vec()
            .into_iter()
            .fold(KeyedRedBlackTree::default(), |tree, x| tree.insert(x, ()))
            .remove(&1);

        let left_child_of_root = unsafe { tree.find_nearest_node(&5).hit_then(|node| node) };

        assert_eq!(None, left_child_of_root.and_then(|c| c.as_ref().left));
    }

    #[test]
    fn should_remove_node_with_one_child_while_retaining_relationships() {
        let node_values = [10, 5, 1, 15];
        let tree = node_values
            .to_vec()
            .into_iter()
            .fold(KeyedRedBlackTree::default(), |tree, x| tree.insert(x, ()))
            .remove(&10);

        let root = unsafe { tree.find_nearest_node(&5).hit_then(|node| node) };
        let child_of_node_to_be_deleted =
            unsafe { tree.find_nearest_node(&15).hit_then(|node| node) };

        assert_eq!(
            root,
            child_of_node_to_be_deleted.and_then(|c| c.as_ref().parent)
        );

        assert_eq!(
            child_of_node_to_be_deleted,
            root.and_then(|c| c.as_ref().right)
        );
    }

    #[test]
    fn should_remove_node_with_two_childen_while_retaining_relationships() {
        let node_values = [10, 5, 1, 15];
        let tree = node_values
            .to_vec()
            .into_iter()
            .fold(KeyedRedBlackTree::default(), |tree, x| tree.insert(x, ()))
            .remove(&5);

        // the new root to replace the deleted root
        let new_root = unsafe { tree.find_nearest_node(&10).hit_then(|node| node) };

        let new_root_right_child = unsafe { tree.find_nearest_node(&15).hit_then(|node| node) };
        let new_root_left_child = unsafe { tree.find_nearest_node(&1).hit_then(|node| node) };

        assert_eq!(
            new_root,
            new_root_left_child.and_then(|c| c.as_ref().parent)
        );

        assert_eq!(new_root_left_child, new_root.and_then(|c| c.as_ref().left));

        assert_eq!(
            new_root,
            new_root_right_child.and_then(|c| c.as_ref().parent)
        );

        assert_eq!(
            new_root_right_child,
            new_root.and_then(|c| c.as_ref().right)
        );
    }

    #[test]
    fn should_retain_order_after_deletion() {
        let tree = (0..1024)
            .rev()
            .fold(KeyedRedBlackTree::default(), |tree, x| tree.insert(x, ()))
            .remove(&511)
            .remove(&512);

        let received: Vec<u16> = tree.traverse_in_order().map(|(k, _)| k).copied().collect();
        // skip 511 and 512
        let expected: Vec<u16> = (0..511).chain(513..1024).collect();
        assert_eq!(expected, received);
    }
}
