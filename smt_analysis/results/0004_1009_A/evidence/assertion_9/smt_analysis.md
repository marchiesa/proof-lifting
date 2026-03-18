## Assertion: GreedyBuyOptimal(c[i..], a[j..]);

### Dafny → Boogie translation
- Lemma call generates: `call Call$$_module.__default.GreedyBuyOptimal(Seq#Drop(c#0, i#0), Seq#Drop(a#0, j#0))`
- Assumed postcondition: `MaxPurchases($LS($LS($LZ)), c[i..], a[j..]) == 1 + MaxPurchases($LS($LS($LZ)), c[i..][1..], a[j..][1..])`

### What the failing VC contains
After loop invariant assumption (with `$LS($LZ)` fuel):
```
count + MaxPurchases($LS($LZ), Seq#Drop(c#0, i#0), Seq#Drop(a#0, j#0)) == MaxPurchases($LS($LZ), c#0, a#0)
```

Branch condition: `a[j] >= c[i]`

Goal (invariant maintenance after count++, j++, i++):
```
(count+1) + MaxPurchases($LS($LS($LZ)), Seq#Drop(c#0, i+1), Seq#Drop(a#0, j+1)) == MaxPurchases($LS($LS($LZ)), c#0, a#0)
```

### What Z3 can derive
Z3 CAN unfold MaxPurchases one step via the definition axiom (trigger: `MaxPurchases($LS(ly), c, a)`):
```
MaxPurchases(c[i..], a[j..]) = Max(1 + MaxPurchases(c[i..][1..], a[j..][1..]), MaxPurchases(c[i..][1..], a[j..]))
```

### What Z3 cannot derive
To resolve the Max to `1 + MaxPurchases(c[i..][1..], a[j..][1..])`, Z3 must prove:
```
1 + MaxPurchases(c[1..], a[1..]) >= MaxPurchases(c[1..], a)
```

This is the `ExtraBillBounded` lemma: "one extra bill adds at most 1 to the number of purchases." It requires:
1. Induction on `|c|`
2. The `MoreGamesNoWorse` lemma (monotonicity)

### The gap
**Type: Induction gap (Max resolution requires inductive bound property)**

Z3 can unfold `MaxPurchases` to get `Max(1 + X, Y)` but cannot prove `1 + X >= Y` because this
requires the inductively-proven `ExtraBillBounded` property. Z3 cannot perform induction over
arbitrary sequence lengths. The `GreedyBuyOptimal` lemma call injects this conclusion as an
assumed postcondition, bypassing the need for Z3 to reason inductively.

This is NOT a trigger gap or fuel issue — the definition axiom fires correctly. The gap is that
resolving `Max(buy_count, skip_count)` to `buy_count` requires a quantitative relationship
between recursive calls that can only be established by induction.
