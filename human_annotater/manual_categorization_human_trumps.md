# Manual Categorization Summary (Human Trumps)

- Policy: human annotation overrides auto labels when present; brittle-skipped files are labeled `Brittle`.
- Source folder: `/Users/knut/Documents/code/ase_sprint/smt_quirks/human_annotater`
- Problems summarized: 37
- Assertion lines: 98
- Excluded files: 1
- Excluded `0133_1385_B`: unsound_due_to_unjustified_assumes
- Uncertain lines: 7

## Category Counts

- `B axiom`: 35
- `A forall`: 7
- `A exists`: 29
- `Other`: 5
- `Brittle`: 23

## Combination Counts

- `A exists`: 28
- `A exists, A forall`: 1
- `A forall`: 6
- `B axiom`: 35
- `Brittle`: 23
- `Other`: 5

## Per Problem

### `0000_1013_A`

- Line 101: `Other` :: `assert s[1..][..|(s[1..])|-1] == s[1..|s|-1];`
- Line 237: `B axiom` [uncertain] :: `assert x[..i+1] == x[..i] + [x[i]];` | looks like B, maybe this requires another axiom
- Line 242: `B axiom` :: `assert x[..|x|] == x;` | Looks like B, Take Full
- Line 250: `A exists, A forall` :: `assert y[..i+1] == y[..i] + [y[i]];`
- Line 255: `B axiom` :: `assert y[..|y|] == y;` | Same as above on 242

### `0003_1028_A`

- Line 108: `Brittle` :: `assert false;`
- Line 110: `Brittle` :: `assert ly == gcr - ghalf;`
- Line 120: `Brittle` :: `assert false;`
- Line 126: `Brittle` :: `assert false;`
- Line 128: `Brittle` :: `assert ry == gcr + ghalf + 1;`
- Line 136: `Brittle` :: `assert CellInSquare(ly, gcc - ghalf, gcr, gcc, ghalf);`
- Line 142: `Brittle` :: `assert grid[ly][lx] == 'W';`
- Line 143: `Brittle` :: `assert false;`
- Line 154: `Brittle` :: `assert !CellInSquare(ly, rx, gcr, gcc, ghalf);`
- Line 155: `Brittle` :: `assert grid[ly][rx] == 'W';`
- Line 156: `Brittle` :: `assert false;`
- Line 161: `Brittle` :: `assert CellInSquare(ly, rx, gcr, gcc, ghalf);`
- Line 162: `Brittle` :: `assert grid[ly][rx] == 'B';`
- Line 163: `Brittle` :: `assert false;`
- Line 165: `Brittle` :: `assert rx == gcc + ghalf + 1;`
- Line 173: `Brittle` :: `assert ly + ry == 2 * gcr + 1;`
- Line 177: `Brittle` :: `assert r - 1 == gcr;`
- Line 178: `Brittle` :: `assert c - 1 == gcc;`
- Line 179: `Brittle` :: `assert 1 <= r <= n;`
- Line 180: `Brittle` :: `assert 1 <= c <= m;`
- Line 181: `Brittle` :: `assert IsBlackSquareCenteredAt(n, m, grid, r - 1, c - 1, ghalf);`

### `0006_1017_A`

- Line 56: `A forall` :: `assert scores[1..i+1] == scores[1..i] + [scores[i]];`

### `0008_1056_A`

- Line 57: `A exists` :: `assert newResult[w] == result[idx];` | A exists, proves the existential inside the InSeq predicate
- Line 62: `A exists` :: `assert newResult[|oldNR|] == result[i];` | A exists, same as above
- Line 93: `A exists` :: `assert forall x :: (forall m | 0 <= m < k + 1 :: InSeq(x, stops[m])) ==> InSeq(x, newResult)` | A exists, proves the existential inside the InSeq(s, newResult)
- Line 99: `A exists` :: `assert InSeq(x, result);`

### `0009_1041_A`

- Line 170: `B axiom` :: `assert a[..i+1][..i] == a[..i];` | Looks like B taketake
- Line 179: `B axiom` :: `assert a[..|a|] == a;` | Looks like B take full

### `0012_1060_A`

- Line 50: `B axiom` :: `assert digits[..i+1] == digits[..i] + [digits[i]];` | Looks like B takeappend
- Line 55: `B axiom` :: `assert digits[..|digits|] == digits;` | Looks like B take full

### `0024_1091_A`

- Line 26: `A exists` :: `assert ValidChoice(y, b, r, m, m + 1, m + 2);` | A exists proves: exists ny | 0 <= ny <= y :: ValidChoice(y, b, r, ny, ny + 1, ny + 2) && total == ny + (ny + 1) + (ny + 2)

### `0030_1106_A`

- Line 76: `A forall` [uncertain] :: `assert counted == crossSet;` | Unsure. Looks like extensionality

### `0031_1130_A`

- Line 70: `B axiom` :: `assert a[..i+1] == a[..i] + [a[i]];` | Looks like B append take
- Line 80: `B axiom` :: `assert a[..n] == a;` | Looks like B take full

### `0036_1015_A`

- Line 63: `Brittle` :: `assert A[p] == A_before[p];`
- Line 94: `Brittle` :: `assert forall q | 0 <= q < |old_result| :: result[q] == old_result[q];`

### `0040_1159_A`

- Line 47: `B axiom` :: `assert s[..i+1] == s[..i] + [s[i]];` | Looks like B append take
- Line 66: `B axiom` :: `assert s[..|s|] == s;` | Looks like B take full
- Line 69: `A exists` :: `assert ValidExecution(s, absorbed);` | when commenting out both of these verification fails. This assertion is an A exists for first post condition

### `0041_1143_A`

- Line 39: `B axiom` :: `assert doors[..i+1][..i] == doors[..i];` | Looks like B take take
- Line 47: `B axiom` :: `assert doors[..n] == doors;` | Looks like B take full
- Line 59: `B axiom` :: `assert doors[..i+1][..i] == doors[..i];` | Looks like B take full
- Line 72: `Other` [uncertain] :: `assert CanExitAfter(doors, n);` | unsure, we be related to unfolding/fuel.

### `0045_1146_A`

- Line 45: `B axiom` :: `assert s[..i+1][..i] == s[..i];` | Looks like B take take
- Line 51: `B axiom` :: `assert s[..|s|] == s;` | Looks like B take full

### `0053_1230_A`

- Line 24: `A exists` :: `assert FriendSum(a1, a2, a3, a4, true, true, false, false) ==` | A exists. Proves existential inside: CanDistributeEqually(a1, a2, a3, a4)
- Line 27: `A exists` :: `assert FriendSum(a1, a2, a3, a4, true, false, true, false) ==` | A exists. Proves existential inside: CanDistributeEqually(a1, a2, a3, a4)
- Line 30: `A exists` :: `assert FriendSum(a1, a2, a3, a4, true, false, false, true) ==` | A exists. Proves existential inside: CanDistributeEqually(a1, a2, a3, a4)
- Line 33: `A exists` :: `assert FriendSum(a1, a2, a3, a4, false, false, false, true) ==` | A exists. Proves existential inside: CanDistributeEqually(a1, a2, a3, a4)
- Line 36: `A exists` :: `assert FriendSum(a1, a2, a3, a4, false, false, true, false) ==` | A exists. Proves existential inside: CanDistributeEqually(a1, a2, a3, a4)
- Line 39: `A exists` :: `assert FriendSum(a1, a2, a3, a4, false, true, false, false) ==` | A exists. Proves existential inside: CanDistributeEqually(a1, a2, a3, a4)
- Line 43: `A exists` :: `assert FriendSum(a1, a2, a3, a4, true, false, false, false) ==` | A exists. Proves existential inside: CanDistributeEqually(a1, a2, a3, a4)

### `0054_1189_A`

- Line 72: `B axiom` :: `assert s[..i+1][..i] == s[..i];` | Looks like B take take
- Line 80: `B axiom` :: `assert s[..|s|] == s;` | Looks like B take full

### `0056_1178_A`

- Line 98: `B axiom` :: `assert a[..i+1] == a[..i] + [a[i]];` | Looks like B append take

### `0061_1191_A`

- Line 49: `Other` :: `assert CategoryRank(x + 0) == 0;`

### `0066_1236_A`

- Line 33: `A exists` :: `assert Feasible(a, b, c, rem, c2);` | A exists, proves the exists from the first postcondition

### `0068_1196_A`

- Line 45: `A exists` :: `assert CandiesAfterDivision(b, c, a, s) == maxCandies;` | A exists, proves existential formula inside IsAchievable
- Line 50: `A exists` :: `assert CandiesAfterDivision(a, c, b, s) == maxCandies;` | A exists, proves existential formula inside IsAchievable
- Line 55: `A exists` :: `assert CandiesAfterDivision(a, b, c, s) == maxCandies;` | A exists, proves existential formula inside IsAchievable

### `0069_1200_A`

- Line 176: `B axiom` :: `assert events[..idx + 1][..idx] == events[..idx];` | Looks like B take take
- Line 179: `B axiom` :: `assert events[..idx] == events;` | Looks like B take full

### `0074_1220_A`

- Line 182: `B axiom` :: `assert s[..|s|] == s;` | Looks like B take full

### `0077_1244_A`

- Line 62: `A exists` :: `assert ValidAssignment(pens, pencils, a, b, c, d, k);` | Looks like A exists, proves second post condition by proving Feasibility
- Line 65: `A forall` :: `assert forall x0, y0 :: !ValidAssignment(x0, y0, a, b, c, d, k) by {` | A, neither triggering exists or forall but used to prove the forall

### `0078_1269_A`

- Line 14: `A exists` :: `assert a % 3 == 0;` | A exists, proves the existential inside the IsComposite predicate
- Line 15: `A exists` :: `assert b % 2 == 0;` | A exists, proves the existential inside the IsComposite predicate

### `0079_1216_A`

- Line 127: `B axiom` :: `assert s[..i] + [s[i], s[i + 1]] == s[..i + 2];` | Looks like B. But is more complex so adding axioms for this is hard
- Line 139: `B axiom` :: `assert s[..|s|] == s;` | Looks like B take full

### `0080_1281_A`

- Line 88: `Other` :: `assert results == ClassifyAll(sentences[..i]) + [ClassifySentence(sentences[i])];` | At least one of these three must be included. The next assertion would not be necessary with a append take axiom
- Line 93: `B axiom` :: `assert sentences[..|sentences|] == sentences;` | Looks like B take full

### `0085_1257_A`

- Line 81: `A exists` [uncertain] :: `assert SwapCost(a, b, la, lb) == da + db;` | Likely A exists, proves the existential inside IsAchievable
- Line 93: `A exists` [uncertain] :: `assert SwapCost(a, b, lb, la) == da + db;` | Likely A exists, proves the existential inside IsAchievable

### `0096_1316_A`

- Line 65: `B axiom` :: `assert a[..|a|] == a;` | Looks like B take full

### `0097_1311_A`

- Line 41: `A exists` :: `assert ValidStep(a, c);` | A exists proves existential inside Reachable

### `0101_116_A`

- Line 56: `B axiom` :: `assert a[..i+1] == a[..i] + [a[i]];` | Looks like B append take
- Line 57: `B axiom` :: `assert b[..i+1] == b[..i] + [b[i]];` | Looks like B append take

### `0103_1305_A`

- Line 148: `B axiom` :: `assert sorted == sorted[..i] + sorted[i..];` | Looks like B append take
- Line 163: `B axiom` :: `assert s[..i + 1] == s[..i] + [s[i]];` | Looks like B append take
- Line 167: `A forall` :: `assert s[..|s|] == s;` | Looks llike B take full
- Line 186: `A forall` [uncertain] :: `assert |x| == |a| by {` | Not sure, could be triggering an axiom, or extensionality
- Line 190: `A forall` :: `assert |y| == |b| by {` | similar as above

### `0107_1294_A`

- Line 47: `A exists` :: `assert ValidDistribution(a, b, c, n, des - a, des - b, des - c);` | A exists proves existential formula inside CanDistribute poredicate.

### `0121_1370_A`

- Line 57: `A exists` :: `assert Gcd(wa, wb) == wa;` | A exists, proves the first post condition, about feasibility

### `0126_14_A`

- Line 284: `A exists` :: `assert exists c {:trigger grid[bottom - 1][c]} | left <= c < right :: grid[bottom - 1][c] == '*' by {` | A exists, constructing witness inside by block
- Line 321: `Other` [uncertain] :: `assert IsMinimalBoundingBox(grid, result, top, bottom, left, right);` | Not sure

### `0132_1385_A`

- Line 44: `A exists` :: `assert IsValidSolution(x, y, z, a, b, c);` | A exists proves SolutionExists by constructing witness

### `0136_1411_A`

- Line 23: `B axiom` :: `assert s[..|s|] == s;` | Looks like B take full
- Line 28: `B axiom` :: `assert s[..i + 1][..i] == s[..i];` | Looks like B take take

### `0138_1413_A`

- Line 52: `B axiom` :: `assert a[..i] + [a[i]] == a[..i + 1];` | Looks like B append take
- Line 56: `B axiom` :: `assert a[..i] + [a[i]] == a[..i + 1];` | Looks like B append take
- Line 61: `B axiom` :: `assert a[..|a|] == a;` | Looks like B take full

### `0142_1360_A`

- Line 96: `A exists` :: `assert IsMinimalSide(a, b, val);` | A exists proves the existential formula in the post condition

