# Stable Matching (Gale-Shapley)

## Description

Implement the Gale-Shapley algorithm for the stable matching problem. Given n men
and n women with preference lists, find a matching where each man is assigned to
a valid woman. The algorithm uses a bounded number of proposals to find matches,
with a fallback for any unmatched men.

## Input

- `n`: number of men and women (positive integer)
- `pref_m`: preference lists for men; `pref_m[i][j]` is man i's j-th choice
- `pref_w`: preference lists for women; `pref_w[i][j]` is woman i's j-th choice

All preferences are valid indices in [0, n) and men's preference lists have distinct entries.

## Output

An array `match_m` of length `n` such that:
- `0 <= match_m[i] < n` for all men (each man is assigned a valid woman)

## Examples

- `n=1`: `match_m[0] == 0`
- `n=2`: each man gets a woman in {0, 1}
- `n=3`: each man gets a woman in {0, 1, 2}
