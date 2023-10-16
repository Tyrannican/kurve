use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

type Node<T> = Rc<RefCell<Vertex<T>>>;

#[derive(PartialEq, Eq, Hash, Clone)]
pub struct Vertex<T> {
    pub id: usize,
    pub weight: usize,
    pub value: T,
}

impl<T> Vertex<T> {
    pub fn new(id: usize, value: T) -> Self {
        Self { id, value }
    }
}

pub struct Kurve<T> {
    nodes: HashMap<usize, Node<T>>,
    adj_list: HashMap<usize, HashSet<usize>>,
}

impl<T> Kurve<T> {
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
    pub fn add_node(&mut self, id: usize, value: T) {
        let node = Rc::new(RefCell::new(Vertex::new(id, value)));
        self.nodes.insert(id, Rc::clone(&node));
        self.adj_list.insert(id, HashSet::new());
    }

    /// Adds an edge between one node TO another
    /// In essence, a directed edge in the direction of `from` -> `to`
    pub fn add_edge(&mut self, from: usize, to: usize) {
        if let Some(inner) = self.adj_list.get_mut(&from) {
            inner.insert(to);
        }
    }

    /// Adds an undirected edge between two nodes
    /// Basically a two way direction between nodes
    pub fn add_twoway_edge(&mut self, from: usize, to: usize) {
        self.add_edge(from, to);
        self.add_edge(to, from);
    }

    /// Gets a node from the graph
    pub fn get(&self, id: usize) -> Option<Node<T>> {
        if let Some(node) = self.nodes.get(&id) {
            return Some(Rc::clone(&node));
        }

        return None;
    }

    /// Gets the assocaited neighbors for a given node
    pub fn get_neighbors(&self, node_id: usize) -> Option<HashSet<usize>> {
        if let Some(neighbors) = self.adj_list.get(&node_id) {
            return Some(neighbors.clone());
        }

        return None;
    }

    /// Gets a copy of the Adj list
    pub fn get_all_neighbors(&self) -> HashMap<usize, HashSet<usize>> {
        return self.adj_list.clone();
    }

    /// Remove a node from the graph
    pub fn remove(&mut self, id: usize) -> Option<Node<T>> {
        let node = self.nodes.remove(&id);
        match self.adj_list.remove(&id) {
            Some(neighbors) => {
                for neighbor in neighbors.iter() {
                    let target_neighbors = self.adj_list.get_mut(neighbor);
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
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn adds_single_node() {
        let mut k: Kurve<i32> = Kurve::new();
        k.add_node(0, 100);

        assert!(k.size() == 1);
    }

    #[test]
    fn adds_a_bunch_of_nodes() {
        let mut k: Kurve<i32> = Kurve::new();
        for i in 1..=100 {
            k.add_node(i, i as i32 * 20);
            assert!(k.adj_list.contains_key(&i));
        }

        assert!(k.nodes.len() == 100);
    }

    #[test]
    fn adds_an_edge() {
        let mut k: Kurve<i32> = Kurve::new();

        k.add_node(0, 100);
        k.add_node(1, 200);
        k.add_node(2, 300);

        k.add_edge(0, 1);
        k.add_edge(0, 2);
        k.add_edge(1, 2);

        let n = k.get_all_neighbors();

        assert!(n.get(&0).unwrap().contains(&1));
        assert!(n.get(&0).unwrap().contains(&2));
        assert!(n.get(&1).unwrap().contains(&2));

        assert!(!n.get(&2).unwrap().contains(&0));
        assert!(!n.get(&2).unwrap().contains(&1));
    }

    #[test]
    fn adds_a_twoway_edge() {
        let mut k: Kurve<i32> = Kurve::new();

        k.add_node(0, 100);
        k.add_node(1, 200);
        k.add_node(2, 300);

        k.add_twoway_edge(0, 1);
        k.add_twoway_edge(1, 2);

        let n = k.get_all_neighbors();

        assert!(n.get(&0).unwrap().contains(&1));
        assert!(n.get(&1).unwrap().contains(&0));
        assert!(n.get(&1).unwrap().contains(&2));
        assert!(n.get(&2).unwrap().contains(&1));
    }

    #[test]
    fn gets_a_node() {
        let mut k: Kurve<i32> = Kurve::new();
        k.add_node(1, 1000);

        let result = k.get(1);
        assert!(result.is_some());

        let inner = result.unwrap();
        let node_ref = inner.borrow();

        assert!(node_ref.id == 1);
        assert!(node_ref.value == 1000);
    }

    #[test]
    fn gets_neighbors_directed() {
        let mut k: Kurve<i32> = Kurve::new();

        k.add_node(0, 100);
        k.add_node(1, 200);
        k.add_node(2, 300);

        k.add_edge(0, 1);
        k.add_edge(0, 2);
        k.add_edge(1, 2);

        let mut n = k.get_neighbors(0);
        assert!(n.is_some());
        let mut inner = n.unwrap().iter().cloned().collect::<Vec<usize>>();
        inner.sort();
        assert_eq!(inner, vec![1, 2]);

        n = k.get_neighbors(1);
        assert!(n.is_some());
        inner = n.unwrap().iter().cloned().collect::<Vec<usize>>();
        inner.sort();
        assert_eq!(inner, vec![2]);

        n = k.get_neighbors(2);
        assert!(n.is_some());
        assert!(n.unwrap().len() == 0);
    }

    #[test]
    fn gets_neighbors_undirected() {
        let mut k: Kurve<i32> = Kurve::new();

        k.add_node(0, 100);
        k.add_node(1, 200);
        k.add_node(2, 300);

        k.add_twoway_edge(0, 1);
        k.add_twoway_edge(1, 2);

        let mut n = k.get_neighbors(0);
        assert!(n.is_some());
        let mut inner = n.unwrap().iter().cloned().collect::<Vec<usize>>();
        inner.sort();
        assert_eq!(inner, vec![1]);

        n = k.get_neighbors(1);
        assert!(n.is_some());
        inner = n.unwrap().iter().cloned().collect::<Vec<usize>>();
        inner.sort();
        assert_eq!(inner, vec![0, 2]);

        n = k.get_neighbors(2);
        assert!(n.is_some());
        inner = n.unwrap().iter().cloned().collect::<Vec<usize>>();
        inner.sort();
        assert_eq!(inner, vec![1]);
    }

    #[test]
    fn removes_a_node() {
        let mut k: Kurve<i32> = Kurve::new();

        k.add_node(0, 100);
        k.add_node(1, 200);
        k.add_node(2, 300);

        k.add_twoway_edge(0, 1);
        k.add_twoway_edge(0, 2);
        k.add_edge(1, 2);

        let n = k.remove(0);
        assert!(n.is_some());

        let n = n.unwrap();
        let node_ref = n.borrow();
        assert!(node_ref.id == 0);
        assert!(node_ref.value == 100);

        let adj_list = k.get_all_neighbors();
        assert!(!adj_list.contains_key(&0));

        let mut check = adj_list.get(&1).unwrap();
        assert!(!check.contains(&0));
        assert!(check.contains(&2));

        check = adj_list.get(&2).unwrap();
        assert!(!check.contains(&0));
        assert!(!check.contains(&1));
    }
}
