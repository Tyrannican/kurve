use std::hash::Hash;
use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

/// Vertex on the Graph
type Node<K, T> = Rc<RefCell<Vertex<K, T>>>;

/// Edge with K key and usize weighting
type Edge<K> = (K, usize);

#[derive(PartialEq, Eq, Hash, Clone)]
pub struct Vertex<K, T> 
where
    K: PartialEq + Eq + Hash + Clone
{
    pub id: K,
    pub value: T,
}

impl<K, T> Vertex<K, T>
where
    K: PartialEq + Eq + Hash + Clone
{
    pub fn new(id: K, value: T) -> Self {
        Self { id, value }
    }
}

pub struct Kurve<K, T>
where
    K: PartialEq + Eq + Hash + Clone
{
    nodes: HashMap<K, Node<K, T>>,
    adj_list: HashMap<K, HashMap<K, usize>>,
}

impl<K, T> Kurve<K, T>
where
    K: PartialEq + Eq + Hash + Clone
{
    /// Creates a new Graph
    pub fn new() -> Self {
        Self {
            nodes: HashMap::new(),
            adj_list: HashMap::new(),
        }
    }

    /// Gets the size of the Graph
    pub fn size(&self) -> usize {
        return self.nodes.len();
    }

    /// Adds a node to the graph
    /// Also creates an entry in the adjacency list
    pub fn add_node(&mut self, id: K, value: T) {
        let node = Rc::new(RefCell::new(Vertex::new(id.clone(), value)));
        self.nodes.insert(id.clone(), Rc::clone(&node));
        self.adj_list.insert(id, HashMap::new());
    }

    /// Adds an edge between one node TO another
    /// This defaults the weighting for an edge to 1
    pub fn add_edge(&mut self, from: K, to: K) {
        if let Some(inner) = self.adj_list.get_mut(&from) {
            inner.insert(to, 1);
        }
    }

    /// Adds a weighted edge between one node to another
    pub fn add_weighted_edge(&mut self, from: K, to: K, weight: usize) {
        if let Some(inner) = self.adj_list.get_mut(&from) {
            inner.insert(to, weight);
        }
    }

    /// Gets a node from the graph
    pub fn get(&self, id: K) -> Option<Node<K, T>> {
        if let Some(node) = self.nodes.get(&id) {
            return Some(Rc::clone(&node));
        }

        return None;
    }

    /// Gets the assocaited neighbors for a given node
    pub fn get_neighbors(&self, node_id: K) -> Option<HashMap<K, usize>> {
        if let Some(neighbors) = self.adj_list.get(&node_id) {
            return Some(neighbors.clone());
        }

        return None;
    }

    /// Gets a copy of the Adj list
    pub fn get_all_neighbors(&self) -> HashMap<K, HashMap<K, usize>> {
        return self.adj_list.clone();
    }

    /// Remove a node from the graph
    pub fn remove(&mut self, id: K) -> Option<Node<K, T>> {
        let node = self.nodes.remove(&id);
        match self.adj_list.remove(&id) {
            Some(neighbors) => {
                for neighbor in neighbors.iter() {
                    let (neighbor_id, _) = neighbor;
                    let target_neighbors = self.adj_list.get_mut(neighbor_id);
                    if target_neighbors.is_none() {
                        continue;
                    }

                    let target_neighbors = target_neighbors.unwrap();
                    target_neighbors.remove(&id);
                }
            }
            None => {}
        }

        return node;
    }

    /// Djikstra pathing algorithm 
    pub fn djikstra(&self, from: usize, to: usize) -> Option<Vec<usize>> {
        return None;
    }

    /// A* pathing algorithm
    pub fn a_star(&self, from: usize, to: usize) -> Option<Vec<usize>> {
        return None;
    }

    /// Depth-First Search
    pub fn dfs(&self, from: usize, to: usize) -> Option<Vec<usize>> {
        return None;
    }

    /// Breadth-First Search
    pub fn bfs(&self, from: usize, to: usize) -> Option<Vec<usize>> {
        return None;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn adds_single_node() {
        let mut k: Kurve<String, i32> = Kurve::new();
        k.add_node("node1".to_string(), 100);

        assert!(k.size() == 1);
    }

    #[test]
    fn adds_a_bunch_of_nodes() {
        let mut k: Kurve<i32, i32> = Kurve::new();
        for i in 1..=100 {
            k.add_node(i, i as i32 * 20);
            assert!(k.adj_list.contains_key(&i));
        }

        assert!(k.nodes.len() == 100);
    }

    #[test]
    fn adds_an_edge() {
        let mut k: Kurve<i32, i32> = Kurve::new();

        k.add_node(0, 100);
        k.add_node(1, 200);
        k.add_node(2, 300);

        k.add_edge(0, 1);
        k.add_edge(0, 2);
        k.add_edge(1, 2);

        let n = k.get_all_neighbors();

        assert!(n[&0].contains_key(&1));
        assert!(n[&0].contains_key(&1));
        assert!(n[&1].contains_key(&2));

        assert!(!n[&2].contains_key(&0));
        assert!(!n[&2].contains_key(&1));
    }

    #[test]
    fn adds_a_weighted_edge() {
        let mut k: Kurve<i32, i32> = Kurve::new();

        k.add_node(0, 100);
        k.add_node(1, 200);
        k.add_node(2, 300);

        k.add_weighted_edge(0, 1, 2);
        k.add_weighted_edge(0, 2, 3);
        k.add_weighted_edge(2, 1, 4);

        let n = k.get_all_neighbors();

        let mut check = &n[&0];
        assert!(check[&1] == 2);
        assert!(check[&2] == 3);

        check = &n[&2];
        assert!(check[&1] == 4);
    }

    #[test]
    fn gets_a_node() {
        let mut k: Kurve<i32, i32> = Kurve::new();
        k.add_node(1, 1000);

        let result = k.get(1);
        assert!(result.is_some());

        let inner = result.unwrap();
        let node_ref = inner.borrow();

        assert!(node_ref.id == 1);
        assert!(node_ref.value == 1000);
    }

    #[test]
    fn get_a_string_id_node() {
        let mut k: Kurve<String, i32> = Kurve::new();
        k.add_node("node1".to_string(), 1000);

        let result = k.get("node1".to_string());
        assert!(result.is_some());

        let inner = result.unwrap();
        let node_ref = inner.borrow();

        assert!(node_ref.id == "node1".to_string());
        assert!(node_ref.value == 1000);
    }

    #[test]
    fn gets_neighbors_for_a_node() {
        let mut k: Kurve<i32, i32> = Kurve::new();

        k.add_node(0, 100);
        k.add_node(1, 200);
        k.add_node(2, 300);

        k.add_edge(0, 1);
        k.add_edge(0, 2);
        k.add_edge(1, 2);

        let mut n = k.get_neighbors(0);
        assert!(n.is_some());
        let mut inner = n.unwrap().keys().cloned().collect::<Vec<i32>>();
        inner.sort();
        assert_eq!(inner, vec![1, 2]);

        n = k.get_neighbors(1);
        assert!(n.is_some());
        inner = n.unwrap().keys().cloned().collect::<Vec<i32>>();
        inner.sort();
        assert_eq!(inner, vec![2]);

        n = k.get_neighbors(2);
        assert!(n.is_some());
        assert!(n.unwrap().len() == 0);
    }

    #[test]
    fn gets_neighbors_for_a_node_weighted() {
        let mut k: Kurve<i32, i32> = Kurve::new();

        k.add_node(0, 100);
        k.add_node(1, 200);
        k.add_node(2, 300);

        k.add_weighted_edge(0, 1, 2);
        k.add_weighted_edge(0, 2, 3);
        k.add_weighted_edge(1, 2, 4);

        let mut n = k.get_neighbors(0);
        assert!(n.is_some());
        let mut inner = n.unwrap()
            .iter()
            .map(|(k, v)| (*k, *v))
            .collect::<Vec<Edge<i32>>>();
        inner.sort_by_key(|k| k.0);
        assert_eq!(inner, vec![(1, 2), (2, 3)]);

        n = k.get_neighbors(1);
        assert!(n.is_some());
        inner = n.unwrap()
            .iter()
            .map(|(k, v)| (*k, *v))
            .collect::<Vec<Edge<i32>>>();
        inner.sort_by_key(|k| k.0);
        assert_eq!(inner, vec![(2, 4)]);

        n = k.get_neighbors(2);
        assert!(n.is_some());
        assert!(n.unwrap().len() == 0);
    }

    #[test]
    fn removes_a_node() {
        let mut k: Kurve<i32, i32> = Kurve::new();

        k.add_node(0, 100);
        k.add_node(1, 200);
        k.add_node(2, 300);

        k.add_edge(0, 1);
        k.add_edge(0, 2);
        k.add_edge(1, 2);

        assert!(k.size() == 3);
        let n = k.remove(0);
        assert!(n.is_some());
        assert!(k.size() == 2);

        let n = n.unwrap();
        let node_ref = n.borrow();
        assert!(node_ref.id == 0);
        assert!(node_ref.value == 100);

        let adj_list = k.get_all_neighbors();
        assert!(!adj_list.contains_key(&0));

        let mut check = &adj_list[&1];
        assert!(!check.contains_key(&0));
        assert!(check.contains_key(&2));

        check = adj_list.get(&2).unwrap();
        assert!(!check.contains_key(&0));
        assert!(!check.contains_key(&1));
    }
}
