extern crate alloc;

use alloc::{vec, vec::Vec};

pub type NodeIdx = usize;

#[derive(Default)]
pub struct Node {
    /// The index for the first edge in a linked list of edges.
    first_outgoing_edge: Option<EdgeIdx>,
}

pub type EdgeIdx = usize;

pub struct Edge {
    target: NodeIdx,

    /// The index for the first edge in a linked list of edges.
    next_outgoing_edge: Option<EdgeIdx>,
}

pub struct Graph {
    nodes: Vec<Node>,
    edges: Vec<Edge>,
}

impl Graph {
    pub fn new(nodes: Vec<Node>, edges: Vec<Edge>) -> Self {
        Self { nodes, edges }
    }

    fn node_cnt(&self) -> usize {
        self.nodes.len()
    }

    fn edge_cnt(&self) -> usize {
        self.edges.len()
    }

    pub fn insert_node_mut(&mut self) -> NodeIdx {
        let next_idx = self.node_cnt();
        self.nodes.push(Node::default());

        next_idx
    }

    pub fn insert_edge_mut(&mut self, source: NodeIdx, target: NodeIdx) {
        let new_head_edge_idx = self.edge_cnt();
        let source_node = &mut self.nodes[source];
        let prev_head_edge_idx = source_node.first_outgoing_edge;
        self.edges.push(Edge {
            target,
            next_outgoing_edge: prev_head_edge_idx,
        });

        source_node.first_outgoing_edge = Some(new_head_edge_idx);
    }

    pub fn successors(&self, source: NodeIdx) -> Successors {
        let first_outgoing_edge = self.nodes[source].first_outgoing_edge;
        Successors {
            graph: self,
            current_edge_idx: first_outgoing_edge,
        }
    }
}

impl Default for Graph {
    fn default() -> Self {
        Self::new(vec![], vec![])
    }
}

pub struct Successors<'g> {
    graph: &'g Graph,
    current_edge_idx: Option<EdgeIdx>,
}

impl<'g> Iterator for Successors<'g> {
    type Item = NodeIdx;

    fn next(&mut self) -> Option<Self::Item> {
        match self.current_edge_idx {
            None => None,
            Some(edge_idx) => {
                let edge = &self.graph.edges[edge_idx];
                self.current_edge_idx = edge.next_outgoing_edge;
                Some(edge.target)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn should_add_nodes() {
        let mut graph = Graph::default();

        for i in 0..5 {
            let node_idx = graph.insert_node_mut();
            assert_eq!(i, node_idx);
        }

        assert_eq!(5, graph.node_cnt())
    }

    #[test]
    fn should_traverse_graph_in_expected_order() {
        let mut graph = Graph::default();

        let n0 = graph.insert_node_mut();
        let n1 = graph.insert_node_mut();
        let n2 = graph.insert_node_mut();
        let n3 = graph.insert_node_mut();

        graph.insert_edge_mut(n0, n1); // n0 -> n1
        graph.insert_edge_mut(n1, n2); // n1 -> n2
        graph.insert_edge_mut(n0, n3); // n0 -> n3
        graph.insert_edge_mut(n3, n2); // n3 -> n2

        let successor_nodes: Vec<_> = graph.successors(n0).collect();

        assert_eq!(&[n3, n1], &successor_nodes[..]);
    }
}
