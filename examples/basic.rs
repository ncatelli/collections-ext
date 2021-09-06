use rbtree::RedBlackTree;

fn main() {
    let populated_tree = (0..1024).fold(RedBlackTree::default(), |tree, x| tree.insert(x));

    let min = populated_tree.min();
    let max = populated_tree.max();

    println!(
        "The min and max of the tree are: {} - {}",
        min.unwrap(),
        max.unwrap()
    )
}
