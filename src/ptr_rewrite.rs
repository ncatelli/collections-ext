use std::ptr::NonNull;

type NodeRef<V> = NonNull<Node<V>>;

/// Direction represents the directional branch that a given child is on for
/// a given node.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Direction {
    Left,
    Right,
}

/// Represents one of two actions that can trigger a rebalance/modification.
#[derive(Debug, Clone, Copy, PartialEq)]
enum Operation {
    /// A new node has been inserted into the tree.
    Insert,
    /*
    /// A node has been removed from the tree.
    Delete,
    */
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
    Recolor(NodeRef<V>),
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
    parent: Option<NodeRef<V>>,
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
        parent: Option<NodeRef<V>>,
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
    fn is_root(&self) -> bool {
        self.parent.is_none()
    }

    /// Returns a boolean signifying if the node is a leaf node (has no
    /// children)
    fn is_leaf(&self) -> bool {
        self.left.is_none() && self.right.is_none()
    }

    /// Returns the inner value of the Node.
    pub fn unwrap(self) -> V {
        self.inner
    }

    unsafe fn direction(&self) -> Option<Direction> {
        let parent = self.parent?.as_ref();

        match parent.left {
            Some(left_node) if left_node.as_ref().inner == self.inner => Some(Direction::Left),
            _ => Some(Direction::Right),
        }
    }

    unsafe fn sibling(&self) -> Option<NodeRef<V>> {
        let direction = self.direction()?;
        let parent = self.parent?.as_ref();

        match direction {
            Direction::Left => parent.right,
            Direction::Right => parent.left,
        }
    }

    unsafe fn grandparent(&self) -> Option<NodeRef<V>> {
        let parent = self.parent?.as_ref();
        parent.parent
    }

    unsafe fn uncle(&self) -> Option<NodeRef<V>> {
        let parent = self.parent?.as_ref();
        parent.sibling()
    }
}

/// SearchResult represents the results of a binary tree search.
#[derive(Debug)]
enum SearchResult<V> {
    /// Hit signifies the exact value was found in the tree and
    /// contains a reference to the NodeId for said value.
    Hit(NodeRef<V>),
    /// Miss represents the value was not found in the tree and represents the
    /// nearest parent node.
    Miss(NodeRef<V>),
    /// Empty represents an empty tree.
    Empty,
}

impl<V> SearchResult<V> {
    /// Calls `f` if the self is `SearchResult::Hit` returning the result of
    /// `f` wrapped in `Some` otherwise `None` is returned.
    fn hit_then<F, B>(self, f: F) -> Option<B>
    where
        F: Fn(NodeRef<V>) -> B,
    {
        match self {
            SearchResult::Hit(node) => Some(f(node)),
            _ => None,
        }
    }
}

/// An implementation of a Red-Black Tree
#[derive(Debug, Clone)]
pub struct RedBlackTree<V>
where
    V: PartialEq + PartialOrd,
{
    root: Option<NodeRef<V>>,
}

impl<V> RedBlackTree<V>
where
    V: PartialEq + PartialOrd,
{
    pub fn new(root: V) -> Self {
        let boxed_node = Box::new(Node::new(Color::Black, root, None, None, None));
        let root_ptr = NonNull::new(Box::into_raw(boxed_node));

        Self { root: root_ptr }
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
    unsafe fn find_nearest_node(&self, value: &V) -> SearchResult<V> {
        if let Some(root) = self.root {
            let mut next_step = root;
            loop {
                if value == &next_step.as_ref().inner {
                    return SearchResult::Hit(next_step);
                } else if value <= &next_step.as_ref().inner {
                    // if left leaf exists follow that direction.
                    match &next_step.as_ref().left {
                        Some(left) => {
                            let left = left.clone();
                            next_step = left
                        }
                        // return the parent
                        None => return SearchResult::Miss(next_step),
                    }
                } else {
                    // if right leaf exists follow that direction.
                    match &next_step.as_ref().right {
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
        unsafe { self.insert_mut_unchecked(value) }
    }

    unsafe fn insert_mut_unchecked(&mut self, value: V) {
        let nearest = self.find_nearest_node(&value);
        match nearest {
            SearchResult::Hit(_) => (),
            SearchResult::Empty => {
                let boxed_node = Box::new(Node::new(Color::Black, value, None, None, None));
                self.root = NonNull::new(Box::into_raw(boxed_node));
            }
            SearchResult::Miss(mut parent_node) => {
                let is_left = value < parent_node.as_ref().inner;
                let boxed_child =
                    Box::new(Node::new(Color::Red, value, Some(parent_node), None, None));
                let child_ptr = NonNull::new(Box::into_raw(boxed_child));
                if is_left {
                    parent_node.as_mut().left = child_ptr;
                } else {
                    parent_node.as_mut().right = child_ptr;
                }

                self.rebalance_mut(child_ptr.unwrap(), Operation::Insert)
            }
        };
    }

    unsafe fn rebalance_mut(&mut self, node: NodeRef<V>, action: Operation) {
        let mut next_step = match action {
            Operation::Insert => self.needs_rebalance_after_insertion(node),
        };

        while let Some(step) = next_step {
            next_step = None;
            match step {
                Rebalance::LeftLeft => {
                    self.handle_ll_mut(node);
                }
                Rebalance::LeftRight => {
                    self.handle_lr_mut(node);
                }
                Rebalance::RightRight => {
                    self.handle_rr_mut(node);
                }
                Rebalance::RightLeft => {
                    self.handle_rl_mut(node);
                }
                Rebalance::Recolor(base_id) => next_step = self.recolor_mut(base_id, action),
            }
        }
    }

    unsafe fn needs_rebalance_after_insertion(
        &self,
        base_node: NodeRef<V>,
    ) -> Option<Rebalance<V>> {
        // short-circuit to none if the base is root.
        let base = base_node.as_ref();
        let base_node_direction = base.direction()?;
        let parent = base.parent?.as_ref();
        let parent_direction = parent.direction()?;
        let uncle_color = base
            .uncle()
            .map_or(Color::Black, |uncle| uncle.as_ref().color);

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
    unsafe fn rotate_left_mut(&mut self, x: NodeRef<V>) -> Option<NodeRef<V>> {
        self.rotate_mut(x, Direction::Left)
    }

    /// Rotates right from a root node, returning the new root NodeId.
    ///      x  z
    ///     /     \
    ///    z --->   x
    ///   /        /
    ///  y        y
    unsafe fn rotate_right_mut(&mut self, x: NodeRef<V>) -> Option<NodeRef<V>> {
        self.rotate_mut(x, Direction::Right)
    }

    /// Rotates a node by a passed direction
    unsafe fn rotate_mut(
        &mut self,
        mut x_node_ref: NodeRef<V>,
        direction: Direction,
    ) -> Option<NodeRef<V>> {
        let x = x_node_ref.as_mut();

        // if z or x aren't set return None
        let mut z = match direction {
            Direction::Left => x.right.take(),
            Direction::Right => x.left.take(),
        }?;

        let y = match direction {
            Direction::Left => z.as_mut().left.take(),
            Direction::Right => z.as_mut().right.take(),
        };

        let optional_upstream_parent = x.parent;

        if let Some(mut upstream_parent) = optional_upstream_parent {
            // Switch x with z on the upstream parent.
            // safe to unwrap
            let upstream_direction = x.direction().unwrap();
            match upstream_direction {
                Direction::Left => upstream_parent.as_mut().left.replace(z),
                Direction::Right => upstream_parent.as_mut().right.replace(z),
            };
        } else {
            self.root = Some(z);
        }

        // Set the parent of z to the upstream parent and make x a child of z.
        z.as_mut().parent = optional_upstream_parent;
        match direction {
            Direction::Left => z.as_mut().left.replace(x_node_ref),
            Direction::Right => z.as_mut().right.replace(x_node_ref),
        };

        // Set the parent of x to z and the inverse direction node of x to y if
        // it exists.
        x.parent = Some(z);
        match direction {
            Direction::Left => x.right = y,
            Direction::Right => x.left = y,
        };

        // if y exists, set its parent to x.
        if let Some(mut y_node) = y {
            y_node.as_mut().parent = Some(x_node_ref);
        }

        Some(z)
    }

    #[allow(clippy::redundant_closure)]
    unsafe fn recolor_mut(
        &mut self,
        base_node: NodeRef<V>,
        action: Operation,
    ) -> Option<Rebalance<V>> {
        match action {
            Operation::Insert => self.recolor_on_insertion_mut(base_node),
        }
    }

    #[allow(clippy::redundant_closure)]
    unsafe fn recolor_on_insertion_mut(&mut self, base_node: NodeRef<V>) -> Option<Rebalance<V>> {
        let base = base_node.as_ref();

        // set parent to black and return the id
        let parent = base.parent?.as_mut();
        parent.color = Color::Black;

        // set uncle to black and return its id.
        let uncle = base.uncle()?.as_mut();
        uncle.color = Color::Black;

        // if grandparent is black, flip to red and recurse up.
        let grandparent = base.grandparent()?.as_mut();
        match grandparent.color {
            Color::Red => None,
            Color::Black => {
                grandparent.color = Color::Red;
                Some(base.grandparent()?)
            }
        }
        .map(Rebalance::Recolor)
    }

    unsafe fn handle_ll_mut(&mut self, node: NodeRef<V>) {
        let mut parent = node.as_ref().parent.unwrap();
        let mut grandparent = node.as_ref().grandparent().unwrap();

        // rotate grandfather right
        self.rotate_right_mut(grandparent);

        // flip the colors of the original grandparent and parent
        let grandparent_color = grandparent.as_ref().color;
        grandparent.as_mut().color = grandparent_color.flip();
        let parent_color = parent.as_ref().color;
        parent.as_mut().color = parent_color.flip();
    }

    unsafe fn handle_lr_mut(&mut self, node: NodeRef<V>) {
        let parent = node.as_ref().parent.unwrap();

        // rotate parent left
        self.rotate_left_mut(parent);

        // rotated down.
        let new_child_node = parent;

        // then apply an LL case
        self.handle_ll_mut(new_child_node)
    }

    unsafe fn handle_rr_mut(&mut self, node: NodeRef<V>) {
        let mut parent = node.as_ref().parent.unwrap();
        let mut grandparent = node.as_ref().grandparent().unwrap();

        // rotate grandfather left
        self.rotate_left_mut(grandparent);

        // flip the colors of the original grandparent and parent
        let grandparent_color = grandparent.as_ref().color;
        grandparent.as_mut().color = grandparent_color.flip();
        let parent_color = parent.as_ref().color;
        parent.as_mut().color = parent_color.flip();
    }

    unsafe fn handle_rl_mut(&mut self, node: NodeRef<V>) {
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
    pub unsafe fn min(&self) -> Option<NodeRef<V>> {
        self.root
            .and_then(|base_node| self.find_min_from(base_node))
    }

    /// Returns the node with the left-most value (smallest) or `None`, if
    /// empty, starting from a given base node.
    unsafe fn find_min_from(&self, base: NodeRef<V>) -> Option<NodeRef<V>> {
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
    pub unsafe fn max(&self) -> Option<NodeRef<V>> {
        self.root
            .and_then(|base_node| self.max_from_base_node(base_node))
    }

    /// Returns the node with the right-most value (largest) or `None`, if
    /// empty, starting from a given base node.
    unsafe fn max_from_base_node(&self, base_node_id: NodeRef<V>) -> Option<NodeRef<V>> {
        let mut current = Some(base_node_id);
        let mut right_most_node = current;
        while let Some(id) = current {
            right_most_node = current;
            current = id.as_ref().right;
        }
        right_most_node
    }

    /// Returns an Iterator for traversing an array in order.
    pub fn traverse_in_order(&self) -> IterInOrder<'_, V> {
        IterInOrder::new(self)
    }
}

impl<V> Drop for RedBlackTree<V>
where
    V: PartialOrd,
{
    fn drop(&mut self) {
        unsafe {
            while let Some(node) = self.min() {
                let direction = node.as_ref().direction();
                if let Some(mut parent) = node.as_ref().parent {
                    match direction {
                        Some(Direction::Left) => parent.as_mut().left = None,
                        Some(Direction::Right) => parent.as_mut().right = None,
                        None => self.root = None,
                    }
                } else {
                    // if current node is the root, make sure to clear the root field.
                    self.root = None
                }

                let node_ptr = node.as_ptr();
                Box::from_raw(node_ptr);
            }
        }
    }
}

impl<V> Default for RedBlackTree<V>
where
    V: PartialEq + PartialOrd,
{
    fn default() -> Self {
        Self { root: None }
    }
}

pub struct IterInOrder<'a, V>
where
    V: PartialEq + PartialOrd + 'a,
{
    inner: std::marker::PhantomData<&'a RedBlackTree<V>>,
    left_most_node: Option<NodeRef<V>>,
    stack: Vec<NodeRef<V>>,
}

impl<'a, V: 'a> IterInOrder<'a, V>
where
    V: PartialEq + PartialOrd + 'a,
{
    pub fn new(inner: &'a RedBlackTree<V>) -> Self {
        Self {
            inner: std::marker::PhantomData,
            left_most_node: inner.root,
            stack: Vec::new(),
        }
    }
}

impl<'a, V: 'a> Iterator for IterInOrder<'a, V>
where
    V: PartialEq + PartialOrd + Default + 'a,
{
    type Item = &'a V;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(id) = self.left_most_node {
            self.stack.push(id);

            self.left_most_node = unsafe { id.as_ref().left };
        }
        if let Some(up_from_current) = self.stack.pop() {
            self.left_most_node = unsafe { up_from_current.as_ref().right };
            Some(unsafe { &up_from_current.as_ref().inner })
        } else {
            None
        }
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

    #[test]
    fn should_paint_newly_inserted_nodes_red() {
        let node_values = [10, 5, 15];
        let [root_val, left_val, right_val] = node_values;
        let tree = node_values
            .to_vec()
            .into_iter()
            .fold(RedBlackTree::default(), |tree, x| tree.insert(x));

        let root = unsafe {
            tree.find_nearest_node(&root_val)
                .hit_then(|node| node.as_ref().color)
        };
        let left = unsafe {
            tree.find_nearest_node(&left_val)
                .hit_then(|node| node.as_ref().color)
        };
        let right = unsafe {
            tree.find_nearest_node(&right_val)
                .hit_then(|node| node.as_ref().color)
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
            .fold(RedBlackTree::default(), |tree, x| tree.insert(x));

        let child = unsafe {
            tree.find_nearest_node(&child_val)
                .hit_then(|node| (node.as_ref().color, node.as_ref().inner))
        };

        let parent = unsafe {
            tree.find_nearest_node(&parent_val)
                .hit_then(|node| (node.as_ref().color, node.as_ref().inner))
        };

        let uncle = unsafe {
            tree.find_nearest_node(&uncle_val)
                .hit_then(|node| (node.as_ref().color, node.as_ref().inner))
        };

        let grandparent = unsafe {
            tree.find_nearest_node(&grandparent_val)
                .hit_then(|node| (node.as_ref().color, node.as_ref().inner))
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
            .fold(RedBlackTree::default(), |tree, x| tree.insert(x));

        // rotate the root of the tree left
        unsafe { tree.rotate_left_mut(tree.root.unwrap()) };

        let ten = unsafe { tree.find_nearest_node(&10).hit_then(|node| node) }.unwrap();
        let five = unsafe { tree.find_nearest_node(&5).hit_then(|node| node) }.unwrap();
        let fifteen = unsafe { tree.find_nearest_node(&15).hit_then(|node| node) }.unwrap();

        // five's new parent should be the 10 node.
        assert_eq!(Some(ten), unsafe { five.as_ref().parent });

        // ten's new parent should be the fifteen node and new child should be
        // 5.
        assert_eq!(Some(fifteen), unsafe { ten.as_ref().parent });
        assert_eq!(Some(five), unsafe { ten.as_ref().left });

        // fifteen is root and is the parent of 10 node.
        assert!(unsafe { fifteen.as_ref().is_root() });
        assert_eq!(Some(ten), unsafe { fifteen.as_ref().left });
    }

    #[test]
    fn should_return_correct_parent_relationships_on_right_rotation() {
        let mut tree = vec![10, 5, 15]
            .into_iter()
            .fold(RedBlackTree::default(), |tree, x| tree.insert(x));

        // rotate the root of the tree right
        unsafe { tree.rotate_right_mut(tree.root.unwrap()) };

        let ten = unsafe { tree.find_nearest_node(&10).hit_then(|node| node) }.unwrap();
        let five = unsafe { tree.find_nearest_node(&5).hit_then(|node| node) }.unwrap();
        let fifteen = unsafe { tree.find_nearest_node(&15).hit_then(|node| node) }.unwrap();

        // five is root and is the parent of 10 node.
        assert!(unsafe { five.as_ref().is_root() });
        assert_eq!(Some(ten), unsafe { five.as_ref().right });

        // 10's new parent should be the 5 node and new child should be
        // 15.
        assert_eq!(Some(five), unsafe { ten.as_ref().parent });
        assert_eq!(Some(fifteen), unsafe { ten.as_ref().right });

        // fifteens's new parent should be the 10 node.
        assert_eq!(Some(ten), unsafe { fifteen.as_ref().parent });
    }

    #[test]
    fn should_yield_correct_min_and_max_for_a_given_tree() {
        let tree = vec![10, 5, 15, 25, 20]
            .into_iter()
            .fold(RedBlackTree::default(), |tree, x| tree.insert(x));
        let max_val = unsafe { tree.max().map(|node| node.as_ref().inner) };
        let min_val = unsafe { tree.min().map(|node| node.as_ref().inner) };

        assert_eq!(Some(25), max_val);
        assert_eq!(Some(5), min_val);

        let empty_tree = RedBlackTree::<usize>::default();

        assert_eq!(None, unsafe { empty_tree.max() });
        assert_eq!(None, unsafe { empty_tree.min() });
    }

    #[test]
    fn should_traverse_in_order() {
        let tree = vec![10, 5, 15, 25, 20]
            .into_iter()
            .fold(RedBlackTree::default(), |tree, x| tree.insert(x));

        let mut i = tree.traverse_in_order();

        assert_eq!(Some(&5), i.next());
        assert_eq!(Some(&10), i.next());
        assert_eq!(Some(&15), i.next());
        assert_eq!(Some(&20), i.next());
        assert_eq!(Some(&25), i.next());
        assert_eq!(None, i.next());

        let tree = (0..1024)
            .rev()
            .fold(RedBlackTree::default(), |tree, x| tree.insert(x));

        let received: Vec<u16> = tree.traverse_in_order().copied().collect();
        let expected: Vec<u16> = (0..1024).collect();
        assert_eq!(expected, received);
    }
}
