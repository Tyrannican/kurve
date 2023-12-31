//! A basic implementation of an adjacency list Graph data structure.
//!
//! The graph can have weighted edges using the `add_weighted_edge` between two vertices
//! or unweighted using the `add_edge` between two vertices.
//!
//! The graph can be either directed or undirected depending on how you add edges between vertices.
//!
//! No bells, no whistles; just a simple graph to add / remove vertices and edges
//! with a Dijkstra pathing algorithm.
//! 
//! # Example - Unweighted Graph
//!
//! ```rust
//! use kurve::Kurve;
//!
//! // Create a graph with String IDs and i32 values
//! let mut graph: Kurve<String, i32> = Kurve::new();
//!
//! // Add a few vertices
//! graph.add_vertex("id_1".to_string(), 100);
//! graph.add_vertex("id_2".to_string(), 200);
//! graph.add_vertex("id_3".to_string(), 300);
//!
//! // Connect the edges with unweighted edges
//! graph.add_edge("id_1".to_string(), "id_2".to_string());
//! graph.add_edge("id_1".to_string(), "id_3".to_string());
//! graph.add_edge("id_2".to_string(), "id_3".to_string());
//!
//! // Remove a vertex from the graph
//! graph.remove("id_3".to_string());
//! 
//! // Get a vertex from the graph
//! let v = graph.get("id_2".to_string());
//! ```
//!
//! # Example - Weighted Graph
//!
//! ```rust
//! use kurve::Kurve;
//!
//! let mut graph: Kurve<String, i32> = Kurve::new();
//!
//! graph.add_vertex("id_1".to_string(), 100);
//! graph.add_vertex("id_2".to_string(), 200);
//! graph.add_vertex("id_3".to_string(), 300);
//! graph.add_vertex("id_4".to_string(), 400);
//!
//! // Add weighted edges
//! graph.add_weighted_edge("id_1".to_string(), "id_2".to_string(), 7);
//! graph.add_weighted_edge("id_1".to_string(), "id_3".to_string(), 3);
//! graph.add_weighted_edge("id_3".to_string(), "id_2".to_string(), 2);
//! graph.add_weighted_edge("id_2".to_string(), "id_4".to_string(), 5);
//!
//! // Use Dijkstra to find the shortest path
//! let path = graph.dijkstra("id_1".to_string(), "id_2".to_string());
//! assert!(path.is_some());
//! assert_eq!(
//!     path,
//!     Some(vec!["id_1".to_string(), "id_3".to_string(), "id_2".to_string()])
//! );
//! ```

mod queue;

use queue::MinDistanceQueue;

use std::hash::Hash;
use std::cmp::Ord;
use std::cell::{RefCell, Ref, RefMut};
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

/// Vertex on the graph
#[derive(PartialEq, Eq, Hash, Clone)]
pub struct Vertex<K, T> {
    /// Vertex ID
    pub id: K,

    /// Inner value
    pub value: T,
}

impl<K, T> Vertex<K, T>
where
    K: PartialEq + Eq + Hash + Clone + Ord
{
    /// Create a new Vertex
    pub fn new(id: K, value: T) -> Self {
        Self { id, value }
    }
}

/// Graph data structure
///
/// Allows for weighted and unweighted directional edges between vertices
/// using an adjacency list.
pub struct Kurve<K, T> {
    /// Mapping of Vertex ID to actual Vertex contents
    vertices: HashMap<K, Rc<RefCell<Vertex<K, T>>>>,

    /// Mapping of Vertex ID to a map of neighboring Vertex
    /// IDs and their associated weights
    adj_list: HashMap<K, HashMap<K, usize>>,
}

impl<K, T> Kurve<K, T>
where
    K: PartialEq + Eq + Hash + Clone + Ord
{
    /// Creates a new Graph
    ///
    /// # Examples
    ///
    /// ```rust
    /// use kurve::Kurve;
    ///
    /// let mut k: Kurve<String, i32> = Kurve::new();
    /// ```
    pub fn new() -> Self {
        Self {
            vertices: HashMap::new(),
            adj_list: HashMap::new(),
        }
    }

    /// Adds a vertex to the graph
    ///
    /// # Examples
    ///
    /// ```rust
    /// use kurve::Kurve;
    ///
    /// let mut k: Kurve<i32, i32> = Kurve::new();
    ///
    /// k.add_vertex(1, 1);
    /// ```
    pub fn add_vertex(&mut self, id: K, value: T) {
        let vertex = Rc::new(RefCell::new(Vertex::new(id.clone(), value)));
        self.vertices.insert(id.clone(), Rc::clone(&vertex));
        self.adj_list.insert(id, HashMap::new());
    }

    /// Adds an edge between one vertex to another
    ///
    /// The weighting for each edge added this way is equal to 1 (unweighted)
    ///
    /// # Examples
    ///
    /// ```rust
    /// use kurve::Kurve;
    ///
    /// let mut k: Kurve<i32, i32> = Kurve::new();
    /// k.add_vertex(1, 10);
    /// k.add_vertex(2, 40);
    ///
    /// k.add_edge(1, 2);
    /// ```
    pub fn add_edge(&mut self, from: K, to: K) {
        if let Some(inner) = self.adj_list.get_mut(&from) {
            inner.insert(to, 1);
        }
    }

    /// Adds a weighted edge between one vertex to another
    ///
    /// # Examples
    ///
    /// ```rust
    /// use kurve::Kurve;
    ///
    /// let mut k: Kurve<i32, i32> = Kurve::new();
    ///
    /// k.add_vertex(1, 10);
    /// k.add_vertex(2, 40);
    ///
    /// k.add_weighted_edge(1, 2, 30);
    /// ```
    pub fn add_weighted_edge(&mut self, from: K, to: K, weight: usize) {
        if let Some(inner) = self.adj_list.get_mut(&from) {
            inner.insert(to, weight);
        }
    }

    /// Gets an immutable reference to a vertex on the graph
    ///
    /// # Examples
    ///
    /// ```rust
    /// use kurve::Kurve;
    ///
    /// let mut k: Kurve<i32, i32> = Kurve::new();
    ///
    /// k.add_vertex(1, 100);
    /// let vertex = k.get(1);
    ///
    /// assert!(vertex.is_some());
    ///
    /// let inner = vertex.unwrap();
    ///
    /// assert_eq!(inner.id, 1);
    /// assert_eq!(inner.value, 100);
    /// ```
    pub fn get(&self, id: K) -> Option<Ref<'_, Vertex<K, T>>> {
        if let Some(vertex) = self.vertices.get(&id) {
            let vertex_ref = vertex.borrow();
            return Some(vertex_ref);
        }

        return None;
    }

    /// Gets a mutable reference to a vertex on the map
    ///
    /// # Example
    ///
    /// ```rust
    /// use kurve::Kurve;
    ///
    /// let mut k: Kurve<i32, i32> = Kurve::new();
    ///
    /// k.add_vertex(1, 100);
    ///
    /// let vtx = k.get_mut(1);
    /// assert!(vtx.is_some());
    ///
    /// let mut inner = vtx.unwrap();
    /// inner.id = 2;
    /// ```
    pub fn get_mut(&mut self, id: K) -> Option<RefMut<'_, Vertex<K, T>>> {
        if let Some(vertex) = self.vertices.get(&id) {
            let vertex_ref = vertex.borrow_mut();
            return Some(vertex_ref);
        }
        return None;
    }

    /// Gets the associated neighbors for a given vertex
    ///
    /// # Examples
    ///
    /// ```rust
    /// use kurve::Kurve;
    ///
    /// let mut k: Kurve<i32, i32> = Kurve::new();
    ///
    /// k.add_vertex(1, 10);
    /// k.add_vertex(2, 20);
    /// k.add_vertex(3, 30);
    ///
    /// k.add_edge(1, 2);
    /// k.add_edge(1, 3);
    ///
    /// let mut neighbors = k.get_neighbors(1);
    /// assert!(neighbors.is_some());
    ///
    /// let inner = neighbors.unwrap();
    /// assert!(inner.contains_key(&2));
    /// assert!(inner.contains_key(&3));
    /// ```
    pub fn get_neighbors(&self, id: K) -> Option<HashMap<K, usize>> {
        if let Some(neighbors) = self.adj_list.get(&id) {
            return Some(neighbors.clone());
        }

        return None;
    }

    /// Returns a copy of the adjacency list showing all neighbors for all vertices
    ///
    /// # Example
    ///
    /// ```rust
    /// use kurve::Kurve;
    ///
    /// let mut k: Kurve<i32, i32> = Kurve::new();
    ///
    /// k.add_vertex(1, 10);
    /// k.add_vertex(2, 20);
    ///
    /// let neighbors = k.get_all_neighbors();
    /// assert!(neighbors.contains_key(&1));
    /// assert!(neighbors.contains_key(&2));
    /// ```
    pub fn get_all_neighbors(&self) -> HashMap<K, HashMap<K, usize>> {
        return self.adj_list.clone();
    }

    /// Remove a vertex from the graph
    ///
    /// Also removes it from all connected neighbors
    ///
    /// # Example 
    ///
    /// ```rust
    /// use kurve::Kurve;
    ///
    /// let mut k: Kurve<i32, i32> = Kurve::new();
    ///
    /// k.add_vertex(1, 10);
    /// k.add_vertex(2, 20);
    ///
    /// let removed = k.remove(1);
    /// assert!(removed.is_some());
    /// assert!(!k.get_all_neighbors().contains_key(&1));
    ///
    /// let inner = removed.unwrap();
    /// assert_eq!(inner.id, 1);
    /// assert_eq!(inner.value, 10);
    /// ```
    pub fn remove(&mut self, id: K) -> Option<Vertex<K, T>> {
        let vertex = self.vertices.remove(&id);
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
        
        if let Some(vertex) = vertex {
            match Rc::try_unwrap(vertex) {
                Ok(refcell) => {
                    return Some(refcell.into_inner());
                },
                Err(_) => {
                    println!("unable to consume");
                }
            }
        }

        return None;
    }

    /// Finds the shortest path between vertices using Dijkstra's Algorithm.
    ///
    /// Uses a Priority Queue (Min Binary Heap) to determine the shortest cost between vertices
    /// during calculations
    ///
    /// # Example
    ///
    /// ```rust
    /// use kurve::Kurve;
    ///
    /// let mut k: Kurve<i32, i32> = Kurve::new();
    ///
    /// for i in 1..= 5 {
    ///     k.add_vertex(i, i * 10);
    /// }
    ///
    /// k.add_weighted_edge(1, 5, 1);
    /// k.add_weighted_edge(1, 4, 6);
    /// k.add_weighted_edge(1, 3, 4);
    /// k.add_weighted_edge(1, 2, 7);
    /// k.add_weighted_edge(5, 4, 1);
    /// k.add_weighted_edge(4, 2, 3);
    /// k.add_weighted_edge(3, 2, 2);
    /// k.add_weighted_edge(3, 4, 5);
    ///
    /// let path = k.dijkstra(1, 2);
    /// assert!(path.is_some());
    /// assert_eq!(path, Some(vec![1, 5, 4, 2]));
    /// ```
    pub fn dijkstra(&self, from: K, to: K) -> Option<Vec<K>> {
        let mut distances = HashMap::new();
        let mut predecessors = HashMap::new();
        let mut visited = HashSet::new();
        let mut queue: MinDistanceQueue<K> = MinDistanceQueue::new();

        queue.push(from.clone(), 0);

        for v in self.adj_list.keys() {
            distances.insert(v, usize::MAX);
            predecessors.insert(v, None);
        }

        distances.insert(&from, 0);

        while let Some(vertex) = queue.pop() {
            if vertex == to {
                let mut path = vec![to.clone()];

                let mut curr = to.clone();
                while predecessors[&curr] != Some(from.clone()) {
                    if let Some(prev) = &predecessors[&curr] {
                        path.push(prev.clone());
                        curr = prev.clone();
                    }
                }

                path.push(from.clone());
                path.reverse();

                return Some(path);
            }

            visited.insert(vertex.clone());

            if let Some(edges) = self.adj_list.get(&vertex) {
                for (neighbor, weight) in edges {
                    let new_dist = distances[&vertex] + *weight;

                    if !visited.contains(neighbor) && new_dist < distances[neighbor] {
                        distances.insert(neighbor, new_dist);
                        predecessors.insert(neighbor, Some(vertex.clone()));
                        queue.push(neighbor.clone(), new_dist);
                    }
                }
            }
        }

        return None;
    }

    /// Returns the size of the Graph
    ///
    /// # Examples
    ///
    /// ```rust
    /// use kurve::Kurve;
    ///
    /// let mut k: Kurve<i32, i32> = Kurve::new();
    /// assert_eq!(k.size(), 0);
    ///
    /// k.add_vertex(0, 100);
    ///
    /// assert_eq!(k.size(), 1);
    /// ```
    pub fn size(&self) -> usize {
        return self.vertices.len();
    }
}

#[cfg(test)]
mod kurve_tests {
    use super::*;
    type Edge<K> = (K, usize);

    #[test]
    fn adds_single_vertex() {
        let mut k: Kurve<String, i32> = Kurve::new();
        k.add_vertex("vertex1".to_string(), 100);

        assert!(k.size() == 1);
    }

    #[test]
    fn adds_a_bunch_of_vertices() {
        let mut k: Kurve<i32, i32> = Kurve::new();
        for i in 1..=100 {
            k.add_vertex(i, i as i32 * 20);
            assert!(k.adj_list.contains_key(&i));
        }

        assert!(k.vertices.len() == 100);
    }

    #[test]
    fn adds_an_edge() {
        let mut k: Kurve<i32, i32> = Kurve::new();

        k.add_vertex(0, 100);
        k.add_vertex(1, 200);
        k.add_vertex(2, 300);

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

        k.add_vertex(0, 100);
        k.add_vertex(1, 200);
        k.add_vertex(2, 300);

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
    fn gets_a_vertex() {
        let mut k: Kurve<i32, i32> = Kurve::new();
        k.add_vertex(1, 1000);

        let result = k.get(1);
        assert!(result.is_some());

        let inner = result.unwrap();

        assert!(inner.id == 1);
        assert!(inner.value == 1000);
    }

    #[test]
    fn gets_a_mutable_vertex() {
        let mut k: Kurve<i32, i32> = Kurve::new();
        k.add_vertex(1, 1000);

        let result = k.get_mut(1);
        assert!(result.is_some());

        let mut inner = result.unwrap();
        assert!(inner.id == 1);
        assert!(inner.value == 1000);

        inner.value = 2;

        drop(inner);

        let updated_result = k.get(1);
        assert!(updated_result.is_some());

        let updated_inner = updated_result.unwrap();
        assert!(updated_inner.value == 2);
    }

    #[test]
    fn get_a_string_id_vertex() {
        let mut k: Kurve<String, i32> = Kurve::new();
        k.add_vertex("vertex1".to_string(), 1000);

        let result = k.get("vertex1".to_string());
        assert!(result.is_some());

        let inner = result.unwrap();

        assert!(inner.id == "vertex1".to_string());
        assert!(inner.value == 1000);
    }

    #[test]
    fn gets_neighbors_for_a_vertex() {
        let mut k: Kurve<i32, i32> = Kurve::new();

        k.add_vertex(0, 100);
        k.add_vertex(1, 200);
        k.add_vertex(2, 300);

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
    fn gets_neighbors_for_a_vertex_weighted() {
        let mut k: Kurve<i32, i32> = Kurve::new();

        k.add_vertex(0, 100);
        k.add_vertex(1, 200);
        k.add_vertex(2, 300);

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
    fn removes_a_vertex() {
        let mut k: Kurve<i32, i32> = Kurve::new();

        k.add_vertex(0, 100);
        k.add_vertex(1, 200);
        k.add_vertex(2, 300);

        k.add_edge(0, 1);
        k.add_edge(0, 2);
        k.add_edge(1, 2);

        assert!(k.size() == 3);
        let n = k.remove(0);
        assert!(n.is_some());
        assert!(k.size() == 2);

        let vtx = n.unwrap();
        assert!(vtx.id == 0);
        assert!(vtx.value == 100);

        let adj_list = k.get_all_neighbors();
        assert!(!adj_list.contains_key(&0));

        let mut check = &adj_list[&1];
        assert!(!check.contains_key(&0));
        assert!(check.contains_key(&2));

        check = adj_list.get(&2).unwrap();
        assert!(!check.contains_key(&0));
        assert!(!check.contains_key(&1));
    }

    #[test]
    fn dijkstra_weighted() {
        let mut k: Kurve<String, i32> = Kurve::new();
        let to_name = |i| format!("vertex{i}");
        for i in 1..=5 {
            k.add_vertex(to_name(i), i * 100)
        }


        k.add_weighted_edge(to_name(1), to_name(5), 1);
        k.add_weighted_edge(to_name(1), to_name(4), 6);
        k.add_weighted_edge(to_name(1), to_name(3), 4);
        k.add_weighted_edge(to_name(1), to_name(2), 7);
        k.add_weighted_edge(to_name(5), to_name(4), 1);
        k.add_weighted_edge(to_name(4), to_name(2), 3);
        k.add_weighted_edge(to_name(3), to_name(2), 2);
        k.add_weighted_edge(to_name(3), to_name(4), 5);

        let path = k.dijkstra(to_name(1), to_name(2));
        assert!(path.is_some());
        assert!(path == Some(vec![to_name(1), to_name(5), to_name(4), to_name(2)]));
    }

    #[test]
    fn djikstra_unweighted() {
        let mut k: Kurve<String, i32> = Kurve::new();
        let to_name = |i| format!("vertex{i}");
        for i in 1..=5 {
            k.add_vertex(to_name(i), i * 100)
        }


        k.add_edge(to_name(1), to_name(5));
        k.add_edge(to_name(1), to_name(4));
        k.add_edge(to_name(1), to_name(3));
        k.add_edge(to_name(1), to_name(2));
        k.add_edge(to_name(5), to_name(4));
        k.add_edge(to_name(4), to_name(2));
        k.add_edge(to_name(3), to_name(2));
        k.add_edge(to_name(3), to_name(4));

        let path = k.dijkstra(to_name(1), to_name(2));
        assert!(path.is_some());
        assert!(path == Some(vec![to_name(1), to_name(2)]));
    }
}
