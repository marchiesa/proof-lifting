## Assertion: MaxPurchasesBound(c, a);

### Dafny → Boogie translation
- Lemma call generates: `call Call$$_module.__default.MaxPurchasesBound(c#0, a#0)`
- Assumed postconditions:
  - `0 <= MaxPurchases($LS($LS($LZ)), c#0, a#0)`
  - `MaxPurchases($LS($LS($LZ)), c#0, a#0) <= Seq#Length(c#0)`
  - `MaxPurchases($LS($LS($LZ)), c#0, a#0) <= Seq#Length(a#0)`

### What the failing VC contains
After the loop, Z3 has:
- Loop invariants: `0 <= i <= |c|`, `0 <= j <= |a|`, `count >= 0`
- Main invariant: `count + MaxPurchases(c[i..], a[j..]) == MaxPurchases(c, a)`
- Loop exit: `i >= |c| || j >= |a|`

Z3 CAN derive `count == MaxPurchases(c, a)` (unfolding MaxPurchases on empty sequences gives 0).

### What Z3 cannot derive
The postconditions `0 <= count <= |c|` and `count <= |a|` require:
- `0 <= MaxPurchases(c, a) <= |c|`
- `MaxPurchases(c, a) <= |a|`

For symbolic `c` and `a` of unknown length, the definition axiom unfolds one step:
```
MaxPurchases(c, a) = if |c|==0 || |a|==0 then 0
  else if a[0] >= c[0] then Max(1 + MaxPurchases(c[1..], a[1..]), MaxPurchases(c[1..], a))
  else MaxPurchases(c[1..], a)
```

To prove `MaxPurchases(c, a) <= |c|`, Z3 would need `MaxPurchases(c[1..], ...) <= |c| - 1`
for the recursive terms — this is exactly the induction hypothesis.

### The gap
**Type: Induction gap (bounds on recursively-defined function)**

Z3 cannot perform structural induction over sequence lengths. The property
`0 <= MaxPurchases(c, a) <= |c|` and `MaxPurchases(c, a) <= |a|` requires induction on `|c|`
with three recursive cases. The fuel mechanism ($LS($LS($LZ)) = 2 unfolding levels) handles
concrete small cases but not the general inductive argument.

The MaxPurchasesBound lemma is proved in its own VC using recursive calls (= inductive hypothesis).
When called in GameShopping, Boogie simply assumes its postconditions, injecting the inductive
conclusion as a free fact.
