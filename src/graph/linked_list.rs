extern crate alloc;

use alloc::{vec, vec::Vec};

pub type NodeIdx = usize;

#[derive(Default)]
pub struct Node<D> {
    data: D,
    /// The index for the first edge in a linked list of edges.
    first_outgoing_edge: Option<EdgeIdx>,
}

impl<D> Node<D> {
    pub fn new(data: D) -> Self {
        Self {
            data,
            first_outgoing_edge: None,
        }
    }

    fn with_outgoing_edge_mut(&mut self, edge_idx: EdgeIdx) {
        self.first_outgoing_edge = Some(edge_idx);
    }
}

impl<D> AsRef<D> for Node<D> {
    fn as_ref(&self) -> &D {
        &self.data
    }
}

impl<D> AsMut<D> for Node<D> {
    fn as_mut(&mut self) -> &mut D {
        &mut self.data
    }
}

pub type EdgeIdx = usize;

pub trait IsEdge {
    fn new(target: NodeIdx) -> Self;
    fn new_with_adjacency(target: NodeIdx, adjacent: Option<EdgeIdx>) -> Self;
    fn next_adjacent_outgoing_edge(&self) -> Option<EdgeIdx>;
}

pub trait IsDirectedEdge: IsEdge {
    fn target(&self) -> NodeIdx;
}

pub struct UnconstrainedEdge {
    target: NodeIdx,

    /// The index for the first edge in a linked list of edges.
    next_outgoing_edge: Option<EdgeIdx>,
}

impl IsEdge for UnconstrainedEdge {
    fn new(target: NodeIdx) -> Self {
        Self {
            target,
            next_outgoing_edge: None,
        }
    }

    fn new_with_adjacency(target: NodeIdx, adjacent: Option<EdgeIdx>) -> Self {
        Self {
            target,
            next_outgoing_edge: adjacent,
        }
    }

    fn next_adjacent_outgoing_edge(&self) -> Option<EdgeIdx> {
        self.next_outgoing_edge
    }
}

impl IsDirectedEdge for UnconstrainedEdge {
    fn target(&self) -> NodeIdx {
        self.target
    }
}

pub struct Graph<ND, E: IsDirectedEdge> {
    nodes: Vec<Node<ND>>,
    edges: Vec<E>,
}

impl<D, E: IsDirectedEdge> Graph<D, E> {
    pub fn new(nodes: Vec<Node<D>>, edges: Vec<E>) -> Self {
        Self { nodes, edges }
    }

    fn node_cnt(&self) -> usize {
        self.nodes.len()
    }

    fn edge_cnt(&self) -> usize {
        self.edges.len()
    }

    pub fn insert_node_mut(&mut self, node: Node<D>) -> NodeIdx {
        let next_idx = self.node_cnt();
        self.nodes.push(node);

        next_idx
    }

    pub fn insert_edge_mut(&mut self, source: NodeIdx, target: NodeIdx) -> Option<EdgeIdx> {
        let new_head_edge_idx = self.edge_cnt();

        // short_circuit if target doesn't exist
        self.get_node(target)?;

        let source_node = self.nodes.get_mut(source)?;
        let prev_head_edge_idx = source_node.first_outgoing_edge;
        self.edges
            .push(<E>::new_with_adjacency(target, prev_head_edge_idx));

        source_node.with_outgoing_edge_mut(new_head_edge_idx);
        Some(new_head_edge_idx)
    }

    pub fn successors(&self, source: NodeIdx) -> Successors<D, E> {
        let first_outgoing_edge = self.nodes[source].first_outgoing_edge;
        Successors {
            graph: self,
            current_edge_idx: first_outgoing_edge,
        }
    }

    pub fn get_node(&self, idx: NodeIdx) -> Option<&Node<D>> {
        self.nodes.get(idx)
    }

    pub fn get_node_mut(&mut self, idx: NodeIdx) -> Option<&mut Node<D>> {
        self.nodes.get_mut(idx)
    }

    pub fn get_edge(&self, idx: EdgeIdx) -> Option<&E> {
        self.edges.get(idx)
    }
}

impl<D, E: IsDirectedEdge> Default for Graph<D, E> {
    fn default() -> Self {
        Self::new(vec![], vec![])
    }
}

pub struct Successors<'g, D, E: IsDirectedEdge> {
    graph: &'g Graph<D, E>,
    current_edge_idx: Option<EdgeIdx>,
}

impl<'g, D, E: IsDirectedEdge> Iterator for Successors<'g, D, E> {
    type Item = NodeIdx;

    fn next(&mut self) -> Option<Self::Item> {
        match self.current_edge_idx {
            None => None,
            Some(edge_idx) => {
                let edge = &self.graph.edges[edge_idx];
                self.current_edge_idx = edge.next_adjacent_outgoing_edge();
                Some(edge.target())
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn should_add_nodes() {
        let mut graph = Graph::<(), UnconstrainedEdge>::default();

        for i in 0..5 {
            let node_idx = graph.insert_node_mut(Node::new(()));
            assert_eq!(i, node_idx);
        }

        assert_eq!(5, graph.node_cnt())
    }

    #[test]
    fn should_fail_to_add_edge_to_non_existent_nodes() {
        let mut graph = Graph::<(), UnconstrainedEdge>::default();

        let n0 = graph.insert_node_mut(Node::new(()));
        let n1 = graph.insert_node_mut(Node::new(()));
        let n2 = 2;
        let n3 = 3;

        assert!(graph.insert_edge_mut(n0, n1).is_some());
        assert!(graph.insert_edge_mut(n0, n2).is_none());
        assert!(graph.insert_edge_mut(n0, n3).is_none());
    }

    #[test]
    fn should_traverse_node_successors_order() {
        let mut graph = Graph::<(), UnconstrainedEdge>::default();

        let n0 = graph.insert_node_mut(Node::new(()));
        let n1 = graph.insert_node_mut(Node::new(()));
        let n2 = graph.insert_node_mut(Node::new(()));
        let n3 = graph.insert_node_mut(Node::new(()));

        graph.insert_edge_mut(n0, n1); // n0 -> n1
        graph.insert_edge_mut(n1, n2); // n1 -> n2
        graph.insert_edge_mut(n0, n3); // n0 -> n3
        graph.insert_edge_mut(n3, n2); // n3 -> n2

        let successor_nodes: Vec<_> = graph.successors(n0).collect();

        assert_eq!(&[n3, n1], &successor_nodes[..]);
    }
}
