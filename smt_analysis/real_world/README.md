# Real-World Code Patterns Dataset

Minimal Dafny programs inspired by real-world Python functions from CodeSearchNet.
Each program captures a common algorithmic pattern found in production software.

## Source

Functions selected from [CodeSearchNet](https://github.com/github/CodeSearchNet)
Python dataset (457K functions from open-source GitHub repositories).
Candidates stored in `candidates.json` with full provenance (repo, file path, GitHub URL).

Selection criteria:
- 5-25 lines of code
- Contains a loop (for/while)
- Works with basic data types
- Minimal external dependencies
- Clear algorithmic pattern

## Programs (30 total)

| File | Pattern | Source Example | Essential |
|------|---------|---------------|-----------|
| B1_1_count_matching | Count elements matching condition | django-glitter/process_actions | 2 (B1) |
| B1_2_running_sum | Cumulative/prefix sum | hic/qn, radix sort | 1 (B1) |
| B1_3_filter_list | Filter by predicate | geojsoncontour/keep_high_angle | 0 |
| B1_4_map_transform | Transform each element | experimental/translate | 2 (B1) |
| B1_5_flatten | Flatten nested sequences | geojsoncontour overlap | 2 (B1) |
| B1_6_reverse | Reverse a sequence | common utility | 0 |
| B1_7_dot_product | Dot product of vectors | numerical computing | 4 (B1) |
| B1_8_merge_sorted | Merge two sorted arrays | merge sort, log merging | 0 |
| B1_9_partition | Partition by predicate | data analysis, A/B testing | 2 (B1) |
| B1_10_sliding_window_max | Max in sliding window | monitoring, time series | 1 (B1) |
| B1_11_weighted_average | Weighted sum | ML, grading, portfolio | 4 (B1) |
| A1_1_linear_search | Linear search | config lookup, UI find | 0 |
| A1_2_find_max | Find maximum element | statistics, scoring | 0 |
| A1_3_contains | Check containment | membership testing | 0 |
| A1_4_binary_search | Binary search | sorted data lookup | 0 |
| A1_5_find_first_ge | Lower bound search | threshold lookup | 0 |
| A1_6_find_witness_complex | Multi-criteria search | database queries | 0 |
| A1_7_two_sum | Find pair summing to target | financial reconciliation | 0 |
| A2_1_validate_all | Validate all elements | input validation | 0 |
| A2_2_check_sorted | Check sorted order | data validation | 0 |
| A2_3_set_diff | Set difference | sync engines | 0 |
| A2_4_all_unique | Uniqueness check | duplicate detection | 0 |
| A2_5_monotonic_check | Monotonicity check | convergence checking | 0 |
| A2_6_permission_check | RBAC permission check | access control, API gateways | 1 (A1) |
| C1_1_area_computation | Area = w * h | geometry, layout | 0 |
| C1_2_grid_index | 2D to linear index | image processing | 0 |
| C1_3_total_revenue | Sum of products | e-commerce, billing | 4 (B1) |
| C1_4_matrix_bounds | Linear index bounds | matrix operations | 0* |
| D1_1_classify | Multi-branch classification | grading, risk assessment | 0 |
| D1_2_parse_tokens | Tokenize by type | lexing, CSV parsing | 0 |

*C1_4 uses a lemma call for NLA reasoning; not captured as an `assert` by ablation.

## Ablation Results

**23 essential assertions across 10 programs.**

| Quirk type | Programs | Assertions | Pattern |
|------------|----------|------------|---------|
| B1 (seq extensionality) | 9 | 22 | `a[..i+1] == a[..i] + [a[i]]`, `a[..\|a\|] == a` |
| A1 (existential) | 1 | 1 | `!HasPermission(...)` negated existential |

B1 dominates in real-world code. Any loop accumulating over a sequence with a recursive
ghost function invariant needs the extensionality hint. This covers the most common
operations: counting, summing, mapping, filtering, partitioning, dot products, weighted
averages, and revenue computation.

The other quirk types (A2, C1, D) do not produce essential assertions on these minimal
programs, though they manifest in more complex specifications (as in the Codeforces dataset).

## Reproduction

```bash
# Verify all programs
for f in programs/*.dfy; do
    dafny verify "$f" --verification-time-limit 30
done

# Run ablation (finds essential assertions)
python3 ablation.py
```
