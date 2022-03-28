extern crate alloc;
use alloc::{vec, vec::Vec};

pub struct SparseSet {
    elems: usize,
    dense: Vec<usize>,
    sparse: Vec<usize>,
}

impl SparseSet {
    /// Initializes a new set of taking a value representing the maximum size
    /// of the set.
    #[must_use]
    pub fn new(max_len: usize) -> Self {
        Self {
            elems: 0,
            dense: Vec::new(),
            sparse: vec![0; max_len],
        }
    }

    /// Returns `true` if the set contains no elements.
    pub fn is_empty(&self) -> bool {
        self.dense.is_empty()
    }

    /// Returns the number of elements that the set can hold without reallocating.
    pub fn capacity(&self) -> usize {
        self.sparse.capacity()
    }

    /// Returns the number of elements in the set.
    pub fn len(&self) -> usize {
        self.elems
    }

    /// Inserts a value into the set.
    pub fn insert(&mut self, val: usize) {
        if self.contains(&val) {
            return;
        }

        if self.sparse.capacity() <= val {
            // double the size.
            self.resize(val * 2)
        }

        let sparse_ptr = self.dense.len();
        self.dense.push(val);
        self.sparse[val] = sparse_ptr;
        self.elems += 1;
    }

    /// Inserts a value into the set.
    ///
    /// This is the unchecked alternative to `insert`.
    ///
    /// # Safety
    ///
    /// Callers of this function are responsible that these preconditions are
    /// satisfied:
    ///
    /// * The starting index must not exceed the max length of the set;
    ///
    /// Failing that will cause a panic.
    pub unsafe fn insert_unchecked(&mut self, val: usize) {
        let sparse_ptr = self.dense.len();
        self.dense.push(val);
        self.sparse[val] = sparse_ptr;
        self.elems += 1;
    }

    /// Returns `true` if the set contains a value.
    pub fn contains(&self, val: &usize) -> bool {
        self.sparse
            .get(*val)
            .map(|&dense_idx| self.dense.get(dense_idx) == Some(val))
            // if none, the bounds of the set are exceeded and thus doesn't
            // contain the value.
            .unwrap_or(false)
    }

    pub fn remove(&mut self, val: &usize) -> bool {
        if self.contains(val) {
            // safety guaranteed by above contains check
            unsafe { self.remove_unchecked(val) };
            true
        } else {
            false
        }
    }

    /// Inserts a value into the set.
    ///
    /// This is the unchecked alternative to `insert`.
    ///
    /// # Safety
    ///
    /// Callers of this function are responsible that these preconditions are
    /// satisfied:
    ///
    /// * The starting index must not exceed the max length of the set;
    ///
    /// Failing that will cause a panic.
    pub unsafe fn remove_unchecked(&mut self, val: &usize) {
        let dense_idx = self.sparse[*val];
        self.dense[dense_idx] = 0;
        self.elems -= 1;
    }

    /// Clears the set, removing all values.
    pub fn clear(&mut self) {
        self.dense.clear()
    }

    fn resize(&mut self, new_len: usize) {
        self.sparse.resize_with(new_len, || 0)
    }
}

impl core::ops::Deref for SparseSet {
    type Target = [usize];

    fn deref(&self) -> &Self::Target {
        &self.dense
    }
}

impl core::fmt::Debug for SparseSet {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "SparseSet({:?}", &self.dense)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn should_cause_resize_on_insert_with_bound_exceed() {
        let mut set = SparseSet::new(0);

        // set capacity is equivalent to provided max_len.
        assert!(set.capacity() == 0);

        set.insert(10);

        // after insert capacity is 2x largest insert value.
        assert!(set.capacity() == 20);
    }

    #[test]
    fn should_clear_value_on_delete() {
        let mut set = SparseSet::new(0);

        set.insert(1);
        assert!(set.contains(&1));
        assert_eq!(1, set.len());

        set.remove(&1);
        assert!(!set.contains(&1));
        assert_eq!(0, set.len());
    }
}
