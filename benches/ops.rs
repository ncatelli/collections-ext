use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use rbtree::RedBlackTree;

pub fn insertion(c: &mut Criterion) {
    let mut group = c.benchmark_group("insertion into the tree");

    (0..5)
        .map(|multiple| 2usize.pow(multiple))
        .for_each(|sample_size| {
            group.throughput(Throughput::Elements(sample_size as u64));
            group.bench_with_input(
                BenchmarkId::new("insertion into tree with nodes", sample_size),
                &sample_size,
                |b, &s| {
                    b.iter(|| {
                        let _populated_tree = (0..s)
                            .fold(RedBlackTree::default(), |tree, x| tree.insert(black_box(x)));
                    })
                },
            );
        })
}

criterion_group!(benches, insertion);
criterion_main!(benches);
