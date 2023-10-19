# Kurve

Simple adjacency list Graph data structure with Dijkstra pathing.

No bells, no whistles; just a graph with the ability to add / remove vertices with weighted / unweighted edges
with a simple pathing algorithm.

Performance? Not designed with that in mind but good enough for simple - intermediate cases.

## Usage

```rust
use kurve::Kurve;

// Create a graph with String IDs and i32 values
let mut graph: Kurve<String, i32> = Kurve::new();

// Add some vertices
graph.add_vertex("id_1".to_string(), 100);
graph.add_vertex("id_2".to_string(), 200);
graph.add_vertex("id_3".to_string(), 300);
graph.add_vertex("id_4".to_string(), 400);

// Add some edges
graph.add_edge("id_1".to_string(), "id_2".to_string());
graph.add_edge("id_1".to_string(), "id_3".to_string());
graph.add_edge("id_2".to_string(), "id_4".to_string());
graph.add_edge("id_4".to_string(), "id_3".to_string());

// Get neighbors of a node
let neighbors = graph.get_neighbors("id_1".to_string()); // ["id_2", "id_3"]

// Find paths
let path = graph.dijkstra("id_1".to_string(), "id_4".to_string()); // ["id_1", "id_2", "id_4"]
```
