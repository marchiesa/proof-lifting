# Real-World Code Patterns → SMT Quirks

Core patterns extracted from CodeSearchNet Python functions.
Each pattern is a common algorithmic idiom found in real software.

## B1: Sequence Extensionality Patterns

### B1-1: Count matching elements (actions_taken += 1)
Source: django-glitter/process_actions, google-alerts/obfuscate
Pattern: Iterate over sequence, count elements matching condition
Dafny quirk: needs `assert a[..i+1] == a[..i] + [a[i]]` for sum/count

### B1-2: Running sum / prefix sum
Source: hic/qn, python-libxdo/_radixPass
Pattern: Compute cumulative sum of array elements
Dafny quirk: needs sequence extensionality for Sum function unfolding

### B1-3: Filter list (keep matching elements)
Source: geojsoncontour/keep_high_angle, elife-tools/text_to_title
Pattern: Build new list by filtering elements from input
Dafny quirk: needs extensionality when proving filtered result properties

### B1-4: Map/transform list
Source: experimental/translate, acceptable/validate
Pattern: Transform each element of input list to new list
Dafny quirk: needs extensionality for element-wise properties

### B1-5: Concatenate/flatten
Source: geojsoncontour/contourf_to_geojson_overlap
Pattern: Flatten nested lists or concatenate sequences
Dafny quirk: sequence equality after append

### B1-6: String building from parts
Source: elife-tools/node_contents_str, tea/get_exception
Pattern: Build string by appending parts in a loop
Dafny quirk: same as B1-2 but with sequences of chars

## A1: Search/Find Patterns

### A1-1: Linear search for element
Source: imcut/__ordered_values_by_indexes
Pattern: Find first element matching condition in array
Dafny quirk: needs existential witness assert

### A1-2: Find index of element
Source: qpimage/find_sideband
Pattern: Find the index where condition holds
Dafny quirk: existential witness with index

### A1-3: Check containment
Source: atoml/contains_list
Pattern: Check if element exists in collection
Dafny quirk: existential witness

### A1-4: Find max/min element
Source: commah/acc_rate
Pattern: Find maximum or minimum in array
Dafny quirk: existential witness for "there exists i such that a[i] == max"

## A2: Predicate Instantiation Patterns

### A2-1: Validate all elements
Source: acceptable/validate, icontract/_kwargs_from_call
Pattern: Check that all elements satisfy a property
Dafny quirk: predicate not auto-evaluated

### A2-2: Check sorted order
Source: various sorting utilities
Pattern: Verify array is sorted
Dafny quirk: predicate instantiation for pairwise comparison

### A2-3: Diff/compare two collections
Source: amo2kinto/get_diff
Pattern: Find differences between two sets/lists
Dafny quirk: predicate check on membership

## C1: Nonlinear Arithmetic

### C1-1: Area/volume computation
Pattern: r = width * height, ensure r > 0
Dafny quirk: NLA, Z3 can't prove a*b > 0 from a>0 && b>0

### C1-2: Index computation
Pattern: index = row * cols + col
Dafny quirk: NLA for bounds checking

## D: Case Split / Conditional Chains

### D-1: Multi-branch classification
Source: mcpartools/_analyse_mat_sections
Pattern: Classify input based on multiple conditions
Dafny quirk: exhaustiveness proof

### D-2: State machine step
Source: puni/Note._expand_url
Pattern: Different processing based on current state
Dafny quirk: case exhaustiveness
