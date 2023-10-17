use std::cmp::Reverse;
use std::collections::BinaryHeap;

pub struct MinDistanceQueue<T> {
    queue: BinaryHeap<Reverse<(usize, T)>>
}

impl<T> MinDistanceQueue<T>
where
    T: Ord + Clone
{
    pub fn new() -> Self {
        return Self { queue: BinaryHeap::new() };
    }

    pub fn peek(&self) -> Option<&T> {
        let Reverse((_, item)) = self.queue.peek()?;
        return Some(item);
    }

    pub fn push(&mut self, item: T, priority: usize) {
        self.queue.push(Reverse((priority, item)));
    }

    pub fn pop(&mut self) -> Option<T> {
        let Reverse((_, item)) = self.queue.pop()?;
        return Some(item);
    }

    pub fn is_empty(&self) -> bool {
        return self.queue.is_empty();
    }

    pub fn size(&self) -> usize {
        return self.queue.len();
    }

    pub fn clear(&mut self) {
        self.queue.clear();
    }
}

#[cfg(test)]
mod min_distance_queue_tests {
    use super::*;

    #[test]
    fn creates_an_empty_queue() {
        let q: MinDistanceQueue<i32> = MinDistanceQueue::new();
        assert!(q.is_empty());
    }

    #[test]
    fn adding_items() {
        let mut q: MinDistanceQueue<String> = MinDistanceQueue::new();
        q.push("node1".to_string(), 1);
        q.push("node2".to_string(), 2);
        q.push("node3".to_string(), 3);
        q.push("node4".to_string(), 4);

        assert!(q.size() == 4);
    }

    #[test]
    fn peeking_item() {
        let mut q: MinDistanceQueue<String> = MinDistanceQueue::new();
        assert!(q.peek().is_none());
        q.push("node1".to_string(), 2);

        let mut item = q.peek();
        assert!(item.is_some());
        assert!(item.unwrap() == "node1");

        q.push("node2".to_string(), 1);
        item = q.peek();
        assert!(item.is_some());
        assert!(item.unwrap() == "node2");
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

        assert!(q.size() == 100);
        q.clear();
        assert!(q.size() == 0);
    }
}