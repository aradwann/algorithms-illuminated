use algorithms_illuminated::sort::build_vec_from_txt;

fn main() {
    let filename = "src/hashmap/txt/problem12.4.txt";

    let vec = build_vec_from_txt(filename).unwrap();

    let num_of_distinct_pairs =
        algorithms_illuminated::hashmap::count_distinct_sums_in_range(&vec, -10000, 10000);
    println!("Number of distinct pairs: {}", num_of_distinct_pairs);
}
