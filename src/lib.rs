use std::hash::Hash;
use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

type Node<K, T> = Rc<RefCell<Vertex<K, T>>>;
type Edge<K> = (K, usize);

#[derive(PartialEq, Eq, Hash, Clone)]
pub struct Vertex<K, T> 
where
    K: Eq + Hash + Clone
{
    pub id: K,
    pub value: T,
}

impl<K, T> Vertex<K, T>
where
    K: Eq + Hash + Clone
{
    pub fn new(id: K, value: T) -> Self {
        Self { id, value }
    }
}

pub struct Kurve<K, T>
where
    K: Eq + Hash + Clone
{
    nodes: HashMap<K, Node<K, T>>,
    adj_list: HashMap<K, HashSet<Edge<K>>>,
}

impl<K, T> Kurve<K, T>
where
    K: Eq + Hash + Clone
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
        self.adj_list.insert(id, HashSet::new());
    }

    /// Adds an edge between one node TO another
    /// In essence, a directed edge in the direction of `from` -> `to`
    pub fn add_edge(&mut self, from: K, to: K) {
        if let Some(inner) = self.adj_list.get_mut(&from) {
            inner.insert((to, 1));
        }
    }

    /// Adds a weighted edge between one node to another
    pub fn add_weighted_edge(&mut self, from: K, to: K, weight: usize) {
        if let Some(inner) = self.adj_list.get_mut(&from) {
            inner.insert((to, weight));
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
    pub fn get_neighbors(&self, node_id: K) -> Option<HashSet<Edge<K>>> {
        if let Some(neighbors) = self.adj_list.get(&node_id) {
            return Some(neighbors.clone());
        }

        return None;
    }

    /// Gets a copy of the Adj list
    pub fn get_all_neighbors(&self) -> HashMap<K, HashSet<Edge<K>>> {
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
                    let to_remove = target_neighbors.clone().into_iter()
                        .filter(|n| {
                            let (target_id, _) = n;
                            *target_id == id
                        })
                        .collect::<HashSet<Edge<K>>>();
                    
                    for edge in to_remove.iter() {
                        target_neighbors.remove(edge);
                    }
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

    // #[test]
    // fn adds_single_node() {
    //     let mut k: Kurve<i32> = Kurve::new();
    //     k.add_node(0, 100);

    //     assert!(k.size() == 1);
    // }

    // #[test]
    // fn adds_a_bunch_of_nodes() {
    //     let mut k: Kurve<i32> = Kurve::new();
    //     for i in 1..=100 {
    //         k.add_node(i, i as i32 * 20);
    //         assert!(k.adj_list.contains_key(&i));
    //     }

    //     assert!(k.nodes.len() == 100);
    // }

    // #[test]
    // fn adds_an_edge() {
    //     let mut k: Kurve<i32> = Kurve::new();

    //     k.add_node(0, 100);
    //     k.add_node(1, 200);
    //     k.add_node(2, 300);

    //     k.add_edge(0, 1);
    //     k.add_edge(0, 2);
    //     k.add_edge(1, 2);

    //     let n = k.get_all_neighbors();

    //     assert!(n.get(&0).unwrap().contains(&1));
    //     assert!(n.get(&0).unwrap().contains(&2));
    //     assert!(n.get(&1).unwrap().contains(&2));

    //     assert!(!n.get(&2).unwrap().contains(&0));
    //     assert!(!n.get(&2).unwrap().contains(&1));
    // }

    // #[test]
    // fn adds_a_twoway_edge() {
    //     let mut k: Kurve<i32> = Kurve::new();

    //     k.add_node(0, 100);
    //     k.add_node(1, 200);
    //     k.add_node(2, 300);

    //     k.add_twoway_edge(0, 1);
    //     k.add_twoway_edge(1, 2);

    //     let n = k.get_all_neighbors();

    //     assert!(n.get(&0).unwrap().contains(&1));
    //     assert!(n.get(&1).unwrap().contains(&0));
    //     assert!(n.get(&1).unwrap().contains(&2));
    //     assert!(n.get(&2).unwrap().contains(&1));
    // }

    // #[test]
    // fn gets_a_node() {
    //     let mut k: Kurve<i32> = Kurve::new();
    //     k.add_node(1, 1000);

    //     let result = k.get(1);
    //     assert!(result.is_some());

    //     let inner = result.unwrap();
    //     let node_ref = inner.borrow();

    //     assert!(node_ref.id == 1);
    //     assert!(node_ref.value == 1000);
    // }

    // #[test]
    // fn gets_neighbors_directed() {
    //     let mut k: Kurve<i32> = Kurve::new();

    //     k.add_node(0, 100);
    //     k.add_node(1, 200);
    //     k.add_node(2, 300);

    //     k.add_edge(0, 1);
    //     k.add_edge(0, 2);
    //     k.add_edge(1, 2);

    //     let mut n = k.get_neighbors(0);
    //     assert!(n.is_some());
    //     let mut inner = n.unwrap().iter().cloned().collect::<Vec<usize>>();
    //     inner.sort();
    //     assert_eq!(inner, vec![1, 2]);

    //     n = k.get_neighbors(1);
    //     assert!(n.is_some());
    //     inner = n.unwrap().iter().cloned().collect::<Vec<usize>>();
    //     inner.sort();
    //     assert_eq!(inner, vec![2]);

    //     n = k.get_neighbors(2);
    //     assert!(n.is_some());
    //     assert!(n.unwrap().len() == 0);
    // }

    // #[test]
    // fn gets_neighbors_undirected() {
    //     let mut k: Kurve<i32> = Kurve::new();

    //     k.add_node(0, 100);
    //     k.add_node(1, 200);
    //     k.add_node(2, 300);

    //     k.add_twoway_edge(0, 1);
    //     k.add_twoway_edge(1, 2);

    //     let mut n = k.get_neighbors(0);
    //     assert!(n.is_some());
    //     let mut inner = n.unwrap().iter().cloned().collect::<Vec<usize>>();
    //     inner.sort();
    //     assert_eq!(inner, vec![1]);

    //     n = k.get_neighbors(1);
    //     assert!(n.is_some());
    //     inner = n.unwrap().iter().cloned().collect::<Vec<usize>>();
    //     inner.sort();
    //     assert_eq!(inner, vec![0, 2]);

    //     n = k.get_neighbors(2);
    //     assert!(n.is_some());
    //     inner = n.unwrap().iter().cloned().collect::<Vec<usize>>();
    //     inner.sort();
    //     assert_eq!(inner, vec![1]);
    // }

    // #[test]
    // fn removes_a_node() {
    //     let mut k: Kurve<i32> = Kurve::new();

    //     k.add_node(0, 100);
    //     k.add_node(1, 200);
    //     k.add_node(2, 300);

    //     k.add_twoway_edge(0, 1);
    //     k.add_twoway_edge(0, 2);
    //     k.add_edge(1, 2);

    //     assert!(k.size() == 3);
    //     let n = k.remove(0);
    //     assert!(n.is_some());
    //     assert!(k.size() == 2);

    //     let n = n.unwrap();
    //     let node_ref = n.borrow();
    //     assert!(node_ref.id == 0);
    //     assert!(node_ref.value == 100);

    //     let adj_list = k.get_all_neighbors();
    //     assert!(!adj_list.contains_key(&0));

    //     let mut check = adj_list.get(&1).unwrap();
    //     assert!(!check.contains(&0));
    //     assert!(check.contains(&2));

    //     check = adj_list.get(&2).unwrap();
    //     assert!(!check.contains(&0));
    //     assert!(!check.contains(&1));
    // }
}
