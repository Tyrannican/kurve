//! Priority queue implemented using a Min Heap
//!
//! This is a helper data structure to make Dijkstra a bit more efficient.
//! 
//! Implemented as a Min Heap to allow for edges with the lowest weight to be
//! the highest priority when calculating the path for the algoirithm.
use std::cmp::Reverse;
use std::collections::BinaryHeap;

/// Priority Queue as a MinHeap
pub(crate) struct MinDistanceQueue<T> {
    /// Inner queue structure
    queue: BinaryHeap<Reverse<(usize, T)>>
}

impl<T> MinDistanceQueue<T>
where
    T: Ord + Clone
{
    /// Create a new Priority Queue
    pub fn new() -> Self {
        return Self { queue: BinaryHeap::new() };
    }

    /// Add an item to the queue with the given priority
    pub fn push(&mut self, item: T, priority: usize) {
        self.queue.push(Reverse((priority, item)));
    }

    /// Remove the item with the highest priority from the queue
    pub fn pop(&mut self) -> Option<T> {
        let Reverse((_, item)) = self.queue.pop()?;
        return Some(item);
    }
}

#[cfg(test)]
mod min_distance_queue_tests {
    use super::*;

    #[test]
    fn creates_an_empty_queue() {
        let q: MinDistanceQueue<i32> = MinDistanceQueue::new();
        assert!(q.queue.is_empty());
    }

    #[test]
    fn adding_items() {
        let mut q: MinDistanceQueue<String> = MinDistanceQueue::new();
        q.push("node1".to_string(), 1);
        q.push("node2".to_string(), 2);
        q.push("node3".to_string(), 3);
        q.push("node4".to_string(), 4);

        assert!(q.queue.len() == 4);
    }

    #[test]
    fn popping_items() { 
        let mut q: MinDistanceQueue<String> = MinDistanceQueue::new();
        q.push("node1".to_string(), 2);
        q.push("node2".to_string(), 3);
        q.push("node3".to_string(), 1);

        let mut item = q.pop();
        assert!(item.is_some());
        assert!(item.unwrap() == "node3");

        item = q.pop();
        assert!(item.is_some());
        assert!(item.unwrap() == "node1");

        item = q.pop();
        assert!(item.is_some());
        assert!(item.unwrap() == "node2");
    }

    #[test]
    fn clearing_queue() {
        let mut q: MinDistanceQueue<String> = MinDistanceQueue::new();

        for i in 1..=100 {
            q.push(format!("node{i}"), i);
        }

        assert!(q.queue.len() == 100);
        q.queue.clear();
        assert!(q.queue.len() == 0);
    }
}
