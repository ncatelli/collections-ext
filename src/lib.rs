use std::ptr::NonNull;

type NodeRef<V> = NonNull<Node<V>>;

/// Represents a type that has a Color representation in the tree.
trait Colored {
    /// Returns the color of a specific item.
    fn color(&self) -> Color;
}

/// A subtype of the `Colored` trait that allows for mutation of its color
trait ColoredMut: Colored {
    /// Sets the color of an object to a passed color.
    fn set_color_mut(&mut self, color: Color);
    /// Inverts the color of a node.
    /// i.e. Red -> Black, or Black -> Red
    fn set_flip_mut(&mut self);
}

impl<V> Colored for NodeRef<V> {
    fn color(&self) -> Color {
        let node = unsafe { self.as_ref() };
        node.color
    }
}

impl<V> ColoredMut for NodeRef<V> {
    fn set_color_mut(&mut self, color: Color) {
        let mut node = unsafe { self.as_mut() };
        node.color = color;
    }

    fn set_flip_mut(&mut self) {
        let node = unsafe { self.as_mut() };
        let current_color = node.color;
        node.set_color_mut(current_color.flip());
    }
}

impl<V> Colored for Option<NodeRef<V>> {
    fn color(&self) -> Color {
        match self {
            Some(noderef) => noderef.color(),
            None => Color::Black,
        }
    }
}

impl<V> ColoredMut for Option<NodeRef<V>> {
    fn set_color_mut(&mut self, color: Color) {
        if let Some(mut noderef) = self {
            noderef.set_color_mut(color)
        }
    }

    fn set_flip_mut(&mut self) {
        if let Some(mut noderef) = self {
            noderef.set_flip_mut()
        }
    }
}

/// Direction represents the directional branch that a given child is on for
/// a given node.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Direction {
    Left,
    Right,
}

/// Represents the three possible situations that a node can encounter on a delete,
#[derive(Clone, Copy, PartialEq)]
enum DeleteSuccessor<V> {
    /// Node has two children. Return the in-order successor.
    Double(Option<NodeRef<V>>),
    /// Node has a single child.
    Single(NodeRef<V>),
    /// Node has no children (is a leaf or root).
    /// Can be deleted directly.
    None,
}

/// InsertRebalance captures the states of an insertion rebalance operation.
enum InsertRebalance<V> {
    /// Represents a LeftLeft case of inbalance.
    LeftLeft(NodeRef<V>),
    /// Represents a LeftRight case of inbalance.
    LeftRight(NodeRef<V>),
    /// Represents a RightRight case of inbalance.
    RightRight(NodeRef<V>),
    /// Represents a RightLeft case of inbalance.
    RightLeft(NodeRef<V>),
    /// Contains the next base node for recoloring.
    Recolor(NodeRef<V>),
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

/// Node represents an interior node to the Red-Black Tree, storing
/// information about direct ancestor/descendent nodes as well as an inner
/// value denoted by type V.
#[derive(Debug, Clone)]
struct Node<V> {
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
    fn new(
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

impl<V> Colored for Node<V> {
    fn color(&self) -> Color {
        self.color
    }
}

impl<V> ColoredMut for Node<V> {
    fn set_color_mut(&mut self, color: Color) {
        self.color = color;
    }

    fn set_flip_mut(&mut self) {
        let current_color = self.color;
        self.set_color_mut(current_color.flip());
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
                        Some(left) => next_step = *left,
                        // return the parent
                        None => return SearchResult::Miss(next_step),
                    }
                } else {
                    // if right leaf exists follow that direction.
                    match &next_step.as_ref().right {
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

                if let Some(rebalance_operation) =
                    self.needs_rebalance_after_insertion(child_ptr.unwrap())
                {
                    self.rebalance_on_insertion_mut(rebalance_operation)
                }
            }
        };
    }

    pub fn remove(mut self, value: &V) -> Self {
        self.remove_mut(value);
        self
    }

    pub fn remove_mut(&mut self, value: &V) -> Option<V> {
        unsafe { self.remove_mut_unchecked(value) }
    }

    unsafe fn remove_mut_unchecked(&mut self, value: &V) -> Option<V> {
        let node_to_be_deleted = self.find_nearest_node(value).hit_then(|node| node)?;
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

                // Take ownership of the inner value
                let inner = boxed_node_to_be_deleted.inner;
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
                }

                // Take ownership of the inner value
                let inner = boxed_node_to_be_deleted.inner;
                Some(inner)
            }
            DeleteSuccessor::Double(in_order_successor) => {
                /*
                    Assign the minimum of right subtree of noteToBeDeleted into y.
                    Save the color of y in originalColor.
                    Assign the rightChild of y into x.
                    If y is a child of nodeToBeDeleted, then set the parent of x as y.
                    Else, transplant y with rightChild of y.
                    Transplant nodeToBeDeleted with y.
                    Set the color of y with originalColor.

                If the originalColor is BLACK, call DeleteFix(x).
                 */
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

                Some(boxed_node_to_be_deleted.inner)
            }
        }
    }

    unsafe fn find_in_order_successor(&self, node: NodeRef<V>) -> Option<NodeRef<V>> {
        let optional_right_child = node.as_ref().right;

        optional_right_child.and_then(|child| self.find_min_from(child))
    }

    unsafe fn rebalance_on_insertion_mut(&mut self, rebalance_operation: InsertRebalance<V>) {
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
        base_node: NodeRef<V>,
    ) -> Option<InsertRebalance<V>> {
        // short-circuit to none if the base is root.
        let base = base_node.as_ref();
        let base_node_direction = base.direction()?;
        let parent = base.parent?.as_ref();
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
        mut x: Option<NodeRef<V>>,
        x_direction: Direction,
        mut optional_x_parent: Option<NodeRef<V>>,
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

                            w.set_color_mut(x_parent.as_ref().color);
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
    unsafe fn recolor_on_insertion_mut(
        &mut self,
        base_node: NodeRef<V>,
    ) -> Option<InsertRebalance<V>> {
        let base = base_node.as_ref();

        // set parent to black and return the id
        let parent = base.parent?.as_mut();
        parent.color = Color::Black;

        // set uncle to black and return its id.
        let uncle = base.uncle()?.as_mut();
        uncle.color = Color::Black;

        // if grandparent is black, flip to red and recurse up.
        let grandparent = base.grandparent()?.as_mut();
        match grandparent.color() {
            Color::Red => None,
            Color::Black => {
                grandparent.color = Color::Red;
                Some(base.grandparent()?)
            }
        }
        .map(InsertRebalance::Recolor)
    }

    unsafe fn handle_ll_mut(&mut self, node: NodeRef<V>) {
        let mut parent = node.as_ref().parent.unwrap();
        let mut grandparent = node.as_ref().grandparent().unwrap();

        // rotate grandfather right
        self.rotate_right_mut(grandparent);

        // flip the colors of the original grandparent and parent
        let grandparent_color = grandparent.color();
        grandparent.as_mut().color = grandparent_color.flip();
        let parent_color = parent.color();
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
        let grandparent_color = grandparent.color();
        grandparent.as_mut().color = grandparent_color.flip();
        let parent_color = parent.color();
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
    pub fn min(&self) -> Option<&V> {
        unsafe {
            self.root
                .and_then(|base_node| self.find_min_from(base_node))
                .map(|node| &node.as_ref().inner)
        }
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
    pub fn max(&self) -> Option<&V> {
        unsafe {
            self.root
                .and_then(|base_node| self.find_max_from(base_node))
                .map(|node| &node.as_ref().inner)
        }
    }

    /// Returns the node with the right-most value (largest) or `None`, if
    /// empty, starting from a given base node.
    unsafe fn find_max_from(&self, base_node_id: NodeRef<V>) -> Option<NodeRef<V>> {
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
            while let Some(value) = self.min() {
                // if min returns a value, this is safe to unwrap
                let node = self.find_nearest_node(value).hit_then(|node| node).unwrap();
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
        assert!(unsafe { fifteen.as_ref().parent == None });
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
        assert!(unsafe { five.as_ref().parent == None });
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

        assert_eq!(Some(&25), tree.max());
        assert_eq!(Some(&5), tree.min());

        let empty_tree = RedBlackTree::<usize>::default();

        assert_eq!(None, empty_tree.max());
        assert_eq!(None, empty_tree.min());
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

    #[test]
    fn should_remove_node_with_no_children() {
        let node_values = [10, 5, 1, 15];
        let tree = node_values
            .to_vec()
            .into_iter()
            .fold(RedBlackTree::default(), |tree, x| tree.insert(x))
            .remove(&1);

        let left_child_of_root = unsafe { tree.find_nearest_node(&5).hit_then(|node| node) };

        assert_eq!(
            None,
            left_child_of_root.and_then(|c| unsafe { c.as_ref().left })
        );
    }

    #[test]
    fn should_remove_node_with_one_child_while_retaining_relationships() {
        let node_values = [10, 5, 1, 15];
        let tree = node_values
            .to_vec()
            .into_iter()
            .fold(RedBlackTree::default(), |tree, x| tree.insert(x))
            .remove(&10);

        let root = unsafe { tree.find_nearest_node(&5).hit_then(|node| node) };
        let child_of_node_to_be_deleted =
            unsafe { tree.find_nearest_node(&15).hit_then(|node| node) };

        assert_eq!(
            root,
            child_of_node_to_be_deleted.and_then(|c| unsafe { c.as_ref().parent })
        );

        assert_eq!(
            child_of_node_to_be_deleted,
            root.and_then(|c| unsafe { c.as_ref().right })
        );
    }

    #[test]
    fn should_remove_node_with_two_childen_while_retaining_relationships() {
        let node_values = [10, 5, 1, 15];
        let tree = node_values
            .to_vec()
            .into_iter()
            .fold(RedBlackTree::default(), |tree, x| tree.insert(x))
            .remove(&5);

        // the new root to replace the deleted root
        let new_root = unsafe { tree.find_nearest_node(&10).hit_then(|node| node) };

        let new_root_right_child = unsafe { tree.find_nearest_node(&15).hit_then(|node| node) };
        let new_root_left_child = unsafe { tree.find_nearest_node(&1).hit_then(|node| node) };

        assert_eq!(
            new_root,
            new_root_left_child.and_then(|c| unsafe { c.as_ref().parent })
        );

        assert_eq!(
            new_root_left_child,
            new_root.and_then(|c| unsafe { c.as_ref().left })
        );

        assert_eq!(
            new_root,
            new_root_right_child.and_then(|c| unsafe { c.as_ref().parent })
        );

        assert_eq!(
            new_root_right_child,
            new_root.and_then(|c| unsafe { c.as_ref().right })
        );
    }
}
