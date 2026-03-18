# Evidence Bundle: assert y[..i+1] == y[..i] + [y[i]];
**Line 241**

## The Assertion
```dafny
assert y[..i+1] == y[..i] + [y[i]];
```

**SMT encoding:**
- LHS: `y[..i+1]` → `Seq#Take(y, i+1)`
- RHS: `y[..i] + [y[i]]` → `Seq#Append(Seq#Take(y, i), Seq#Build(Seq#Index(y, i)))`

## What Breaks Without It
**Dafny error:** this invariant could not be proved to be maintained by the loop

## Counterexample Model (spurious)
Z3 result: `unknown`

**Variable assignments:**
```
  Seq#Empty = T@Seq!val!0
  i#4@0 = 0
  i#4@1 = 2721
  i#4@2 = 0
  i#4@3 = 0
  i#4@4 = 2449
  i#4@5 = 2450
  result#0@0 = false
  result#0@1 = false
  s##0_0@1 = T@Seq!val!2
  s##1_0@1 = T@Seq!val!3
  v##0_0@1 = 0
  v##1_0@1 = 8221
  x#0 = T@Seq!val!1
  xSum#0@0 = 0
  xSum#0@1 = 6268
  xSum#0@2 = 0
  y#0 = T@Seq!val!2
  ySum#0@0 = 0
  ySum#0@1 = (- 374)
  ySum#0@2 = 7847
```

**Sequence lengths:**
```
  |Seq#Empty| = 0
  |T@Seq!val!10| = 2
  |T@Seq!val!11| = 1
  |T@Seq!val!12| = 1649
  |T@Seq!val!13| = 1
  |T@Seq!val!14| = 1
  |T@Seq!val!15| = 1484
  |T@Seq!val!16| = 1
  |T@Seq!val!17| = 1484
  |T@Seq!val!18| = 1
  |T@Seq!val!4| = 1485
  |T@Seq!val!5| = 4387
  |T@Seq!val!6| = 1
  |T@Seq!val!7| = 4388
  |T@Seq!val!8| = 1650
  |T@Seq!val!9| = 1485
  |s##0_0@1| = 1
  |s##1_0@1| = 1485
  |x#0| = 1485
```

**Seq#Take interpretation:**
```
  Seq#Take(x#0 0) = Seq#Empty
  Seq#Take(x#0 1485) = s##1_0@1
  Seq#Take(T@Seq!val!4 (- 4924)) = Seq#Empty
  Seq#Take(T@Seq!val!4 1486) = T@Seq!val!8
  Seq#Take(T@Seq!val!4 1485) = T@Seq!val!9
  Seq#Take(T@Seq!val!9 (- 1)) = T@Seq!val!10
  Seq#Take(T@Seq!val!7 4387) = T@Seq!val!5
  Seq#Take(T@Seq!val!8 1649) = T@Seq!val!12
  Seq#Take(x#0 1) = T@Seq!val!13
  Seq#Take(Seq#Empty (- 1)) = T@Seq!val!14
  Seq#Take(T@Seq!val!4 1484) = T@Seq!val!15
  Seq#Take(s##1_0@1 1484) = T@Seq!val!17
```

**Sum interpretation:**
```
  Seq#Empty -> 0
  T@Seq!val!4 -> (- 2)
  x#0 -> 1
  Seq#Empty -> 0
  Seq#Empty -> 0
  T@Seq!val!14 -> 0
  T@Seq!val!4 -> (- 2)
  T@Seq!val!15 -> (- 122)
  T@Seq!val!15 -> (- 122)
  T@Seq!val!4 -> (- 2)
  x#0 -> 1
  x#0 -> 1
```

**AllNonNeg interpretation:**
```
  x#0 -> true
  T@Seq!val!4 -> true
```

## Relevant Axioms (21 found)

These are all axioms in the SMT preamble whose primary trigger
pattern involves the same operations as the assertion:

### Axiom 1
- **Trigger:** `Seq#Contains (Seq#Build _seq_ _box_`
- **Body:** `(= (Seq#Contains (Seq#Build _seq_ _box_) _box_)  (or (= _box_ _box_) (Seq#Contains $gene`
- **QID:** `outputbpl.3277:15`

### Axiom 2
- **Trigger:** `Seq#Drop (Seq#Build _seq_ _box_`
- **Body:** `(= (Seq#Drop (Seq#Build _seq_ _box_) _int_) (Seq#Build (Seq#Drop _seq_ TORDINAL`
- **Body:** `(= (ValidRemoval#requires $generated@@482 $generated@@483 $generated@@484) true))
 :qid |outputbpl.4440:15|
 :skolemid |633|
 :pattern ( (ValidRemoval`
- **QID:** `outputbpl.3251:15`

### Axiom 3
- **Trigger:** `Seq#Take (Seq#Append _seq_ _seq_`
- **Body:** `(= (Seq#Take (Seq#Append _seq_ _seq_) _int_) _seq_) (= (Seq#Drop (Seq#Append $generate`
- **Body:** `(= (Seq#Drop (Seq#Append _seq_ _seq_) _int_) _seq_)))
 :qid |outputbpl.1421:15|
 :skolemid |250|
 `
- **QID:** `outputbpl.3999:27`

### Axiom 4
- **Trigger:** `Seq#Take (Seq#FromArray $generated@@629 _T@ref_`
- **Body:** `(= (Seq#Take (Seq#FromArray $generated@@629 _T@ref_) _int_) (Seq#Build (Seq#Take (Seq#FromArray $generated@@`
- **Body:** `(= (LegalStep $generated@@655 $generated@@656)  (and (= (Seq#Length $generated@@655) (Seq#Length $generated@@656)) (or (exists (($generat`
- **QID:** `outputbpl.3674:19`

### Axiom 5
- **Trigger:** `$Is_40737 (Seq#Build _seq_ _box_`
- **Body:** `(= (Seq#Length (Seq#Create $generated@@797 $generated@@798 $generated@@799 $generated@@800)) $generated@@799))
 :qid |outputbpl.1468:15|
 :sk`
- **QID:** `outputbpl.2952:15`

### Axiom 6
- **Trigger:** `Seq#Index (Seq#Take _seq_ _int_`
- **Body:** `(= (Seq#Index (Seq#Take _seq_ _int_) _int_) (Seq#Index _seq_ _int_)))
 :qid |output`
- **Body:** `(= (Seq#Length (Seq#Drop $generated@@853 $generated@@854)) (- (Seq#Length $generated@@853) $generated@@854)))
 :qid |outputbpl.1407:15|`
- **QID:** `outputbpl.2457:15`

### Axiom 7
- **Trigger:** `Seq#Rank (Seq#Take _seq_ _int_`
- **Body:** `(= (Seq#Length $generated@@901) (Seq#Length $generated@@902)) (and (AllNonNeg#canCall $generated@@901) (=> (AllNonNeg $generated@@901) (an`
- **Body:** `(= (CanTransform $generated@@901 $generated@@902)  (and (and (and (= (Seq#Length $generated@@901) (Seq#Length $generated@@902)) ($generated`
- **QID:** `outputbpl.3704:24`

### Axiom 8
- **Trigger:** `Seq#Build _seq_ _box_`
- **Body:** `(= (Seq#Length (Seq#Build _seq_ _box_)) (+ 1 (Seq#Length _seq_)))
 :qid |outputbpl.1302:15|
 :skolemid |22`
- **Body:** `(= (Seq#Index (Seq#Create $generated@@950 $generated@@951 $generated@@952 $generated@@953) $generated@@954) (Apply1 TInt $`
- **QID:** `outputbpl.285:18`

### Axiom 9
- **Trigger:** `Seq#Length (Seq#Append _seq_ _seq_`
- **Body:** `(= (Seq#Length (Seq#Append _seq_ _seq_)) (+ (Seq#Length _seq_) (Seq#Length _seq_)))
 :qid`
- **Body:** `(= (Seq#Index (Seq#Build $generated@@1183 $generated@@1185) $generated@@1184) $generated@@1185)) (=> (not (= $generated@@1184 ($generated@@`
- **QID:** `outputbpl.1271:15`

### Axiom 10
- **Trigger:** `Seq#Index (Seq#Build _seq_ _box_`
- **Body:** `(= (Seq#Index (Seq#Build _seq_ _box_) _int_) _box_)) (=> (not (= _int_ ($generated@@`
- **Body:** `(= (Seq#Index (Seq#Build _seq_ _box_) _int_) (Seq#Index _seq_ _int_))))
 :qid |`
- **QID:** `outputbpl.2667:15`

### Axiom 11
- **Trigger:** `Seq#Contains (Seq#Append _seq_ _seq_`
- **Body:** `(= (Seq#Contains (Seq#Append _seq_ _seq_) _box_)  (or (Seq#Contains _seq_ _box_) ($g`
- **Body:** `(= (Seq#Contains (Seq#Take $generated@@1235 $generated@@1236) $generated@@1237) (exists (($generated@@1238 Int) ) (!  (and (and (and (<= 0 $`
- **QID:** `outputbpl.1339:15`

### Axiom 12
- **Trigger:** `Seq#Equal _seq_ _seq_`
- **QID:** `outputbpl.2473:15`

### Axiom 13
- **Trigger:** `Seq#Length (Seq#Take _seq_ _int_`
- **Body:** `(= (Seq#Length (Seq#Take _seq_ _int_)) _int_))
 :qid |outputbpl.1396:15|
 :skolemid |245|
 :pattern ( ($ge`
- **Body:** `(= (Sum#requires $generated@@1419 $generated@@1420) true))
 :qid |outputbpl.3887:15|
 :skolemid |597|
 :pattern ( (Sum#requires $generated@@1419`
- **QID:** `outputbpl.139:18`

### Axiom 14
- **Trigger:** `Seq#Take (Seq#Update _seq_ _int_ _box_`
- **Body:** `(= (Seq#Take (Seq#Update _seq_ _int_ _box_) _int_) (Seq#Take _seq_ $generate`
- **Body:** `(= (IsValidPath ($generated@@1531))  (and (>= (Seq#Length ($generated@@1531)) (LitInt 1)) (forall (($gene`
- **QID:** `outputbpl.1524:15`

### Axiom 15
- **Trigger:** `Seq#Rank (Seq#Append (Seq#Take _seq_ _int_`
- **QID:** `outputbpl.2682:15`

### Axiom 16
- **Trigger:** `Seq#Build _seq_ _box_`
- **Body:** `(= (Seq#Build_inv0 (Seq#Build _seq_ _box_)) _seq_) (= (Seq#Build_inv1 (Seq#Build _seq_ $ge`
- **Body:** `(= (Seq#Build_inv1 (Seq#Build _seq_ _box_)) _box_))
 :qid |outputbpl.1297:15|
 :skolemid |224|
 :pattern ( ($`
- **QID:** `outputbpl.2397:15`

### Axiom 17
- **Trigger:** `MultiSet#FromSeq (Seq#Build _seq_ _box_`
- **QID:** `outputbpl.1992:15`

### Axiom 18
- **Trigger:** `Seq#Index (Seq#Append _seq_ _seq_`
- **Body:** `(= (Seq#Index (Seq#Append _seq_ _seq_) _int_) (Seq#Index _seq_ _int_))) (=> (<= `
- **Body:** `(= (Seq#Index (Seq#Append _seq_ _seq_) _int_) (Seq#Index _seq_ (- _int_ ($genera`
- **QID:** `outputbpl.2338:15`

### Axiom 19
- **Trigger:** `MultiSet#FromSeq (Seq#Append _seq_ _seq_`
- **Body:** `(= (Seq#Length $generated@@2058) 0) (= $generated@@2058 Seq#Empty))
 :qid |outputbpl.1289:15|
 :skolemid |223|
 :pattern ( (Seq#Length $`
- **Body:** `(= (Seq#Take $generated@@2059 $generated@@2060) Seq#Empty))
 :qid |outputbpl.1453:15|
 :skolemid |257|
 :pattern ( (Seq#Take $gene`
- **QID:** `outputbpl.1128:15`

### Axiom 20
- **Trigger:** `Seq#Take _seq_ _int_`
- **Body:** `(= (Seq#Take _seq_ _int_) Seq#Empty))
 :qid |outputbpl.1453:15|
 :skolemid |257|
 :pattern ( (Seq#Take $gene`
- **QID:** `outputbpl.3555:19`

### Axiom 21
- **Trigger:** `Seq#Take (Seq#Update _seq_ _int_ _box_`
- **Body:** `(= (Seq#Take (Seq#Update _seq_ _int_ _box_) _int_) (Seq#Update (Seq#Take $generate`
- **QID:** `outputbpl.2580:15`

## Trigger Gap Analysis (heuristic)
**Pattern:** `slice_extension`
**Description:** No axiom decomposes Seq#Take(s, n) into Seq#Append(Seq#Take(s, n-1), Seq#Build(Seq#Index(s, n-1))). Axioms exist for Seq#Take(Seq#Append(s,t), |s|) → s (composition direction) but not the decomposition direction. The trigger Seq#Take(s, n) only fires an axiom for the n==0 case.
**Needed:** `Seq#Take(y, i+1) == Seq#Append(Seq#Take(y, i), Seq#Build(Seq#Index(y, i)))`
**Missing:** `Seq#Take(s, n) → Seq#Append(Seq#Take(s, n-1), Seq#Build(Seq#Index(s, n-1)))`

## Diagnosis Question

Given the axioms above, explain precisely why the Z3 solver
cannot derive `y[..i+1] == y[..i] + [y[i]]` on its own.
What specific axiom or trigger pattern is missing from the
SMT encoding that would allow the solver to derive this equality?
Is this a fundamental limitation of the axiomatization, or a
trigger/e-matching gap that could be fixed?