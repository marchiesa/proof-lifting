# Evidence Bundle: assert a + b == (a + b[..|b|-1]) + [b[|b|-1]];
**Line 97**

## The Assertion
```dafny
assert a + b == (a + b[..|b|-1]) + [b[|b|-1]];
```

**SMT encoding:**
- LHS: `a + b` → `Seq#Append(a, b)`
- RHS: `(a + b[..|b|-1]) + [b[|b|-1]]` → `Seq#Append(Seq#Append(a, Seq#Take(b, Seq#Length(b)-1)), Seq#Build(Seq#Index(b, |b|-1)))`

## What Breaks Without It
**Dafny error:** a postcondition could not be proved on this return path
**Related:** this is the postcondition that could not be proved
**Failing condition:** `ensures Sum(s) >= 0` (postcondition)

## Counterexample Model (spurious)
Z3 result: `unknown`

**Variable assignments:**
```
  Seq#Empty = T@Seq!val!0
  a#0 = T@Seq!val!0
  b##1_0@0 = T@Seq!val!2
  b#0 = T@Seq!val!1
  s##1_0@0 = T@Seq!val!3
  v##1_0@0 = 334
```

**Sequence lengths:**
```
  |Seq#Empty| = 0
  |T@Seq!val!11| = 2582
  |T@Seq!val!4| = 1
  |T@Seq!val!5| = 2582
  |T@Seq!val!6| = 2581
  |T@Seq!val!7| = 2580
  |T@Seq!val!8| = 2580
  |b##1_0@0| = 2581
  |b#0| = 2582
  |s##1_0@0| = 2581
```

**Seq#Take interpretation:**
```
  Seq#Take(b#0 2581) = b##1_0@0
  Seq#Take(T@Seq!val!5 2581) = s##1_0@0
  Seq#Take(T@Seq!val!11 2581) = T@Seq!val!6
  Seq#Take(s##1_0@0 2580) = T@Seq!val!7
  Seq#Take(b##1_0@0 2580) = T@Seq!val!8
  Seq#Take(Seq#Empty (- 1)) = T@Seq!val!9
  Seq#Take(T@Seq!val!6 2580) = T@Seq!val!10
  Seq#Take(T@Seq!val!8 2579) = T@Seq!val!12
  Seq#Take(T@Seq!val!7 2579) = T@Seq!val!13
  Seq#Take(T@Seq!val!4 0) = Seq#Empty
```

**Sum interpretation:**
```
  T@Seq!val!11 -> (- 5742)
  Seq#Empty -> 0
  b#0 -> (- 5741)
  T@Seq!val!5 -> (- 5741)
  s##1_0@0 -> (- 6075)
  b##1_0@0 -> (- 6075)
  Seq#Empty -> 0
  b##1_0@0 -> (- 6075)
  s##1_0@0 -> (- 6075)
  T@Seq!val!4 -> 334
  T@Seq!val!5 -> (- 5741)
  Seq#Empty -> 0
  T@Seq!val!9 -> 0
  T@Seq!val!10 -> 0
  T@Seq!val!6 -> (- 6076)
```

## Relevant Axioms (28 found)

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
- **Trigger:** `$Is_41666 _T@HandleType_ (Tclass._System.___hTotalFunc3 _type_ _type_ _type_ _type_`
- **QID:** `outputbpl.3232:15`

### Axiom 6
- **Trigger:** `$Is_40737 (Seq#Build _seq_ _box_`
- **Body:** `(= (Seq#Length (Seq#Create $generated@@797 $generated@@798 $generated@@799 $generated@@800)) $generated@@799))
 :qid |outputbpl.1468:15|
 :sk`
- **QID:** `outputbpl.2952:15`

### Axiom 7
- **Trigger:** `Seq#Length (Seq#Create _type_ $generated@@798 _int_ _T@HandleType_`
- **Body:** `(= (Seq#Length (Seq#Create _type_ $generated@@798 _int_ _T@HandleType_)) _int_))
 :qid |outputbpl.1468:15|
 :sk`
- **Body:** `(= (Seq#Index (Seq#Take $generated@@832 $generated@@833) $generated@@834) (Seq#Index $generated@@832 $generated@@834)))
 :qid |output`
- **QID:** `outputbpl.1400:15`

### Axiom 8
- **Trigger:** `Seq#Index (Seq#Take _seq_ _int_`
- **Body:** `(= (Seq#Index (Seq#Take _seq_ _int_) _int_) (Seq#Index _seq_ _int_)))
 :qid |output`
- **Body:** `(= (Seq#Length (Seq#Drop $generated@@853 $generated@@854)) (- (Seq#Length $generated@@853) $generated@@854)))
 :qid |outputbpl.1407:15|`
- **QID:** `outputbpl.2457:15`

### Axiom 9
- **Trigger:** `Seq#Length (Seq#Drop _seq_ _int_`
- **Body:** `(= (Seq#Length (Seq#Drop _seq_ _int_)) (- (Seq#Length _seq_) _int_)))
 :qid |outputbpl.1407:15|`
- **Body:** `(= (Seq#Length $generated@@877) (LitInt 0))) (Sum#canCall (Seq#Take $generated@@877 (- (Seq#Length $generated@@877) 1)))) (=`
- **QID:** `outputbpl.1520:15`

### Axiom 10
- **Trigger:** `Seq#Rank (Seq#Take _seq_ _int_`
- **Body:** `(= (Seq#Length $generated@@901) (Seq#Length $generated@@902)) (and (AllNonNeg#canCall $generated@@901) (=> (AllNonNeg $generated@@901) (an`
- **Body:** `(= (CanTransform $generated@@901 $generated@@902)  (and (and (and (= (Seq#Length $generated@@901) (Seq#Length $generated@@902)) ($generated`
- **QID:** `outputbpl.3704:24`

### Axiom 11
- **Trigger:** `Seq#Build _seq_ _box_`
- **Body:** `(= (Seq#Length (Seq#Build _seq_ _box_)) (+ 1 (Seq#Length _seq_)))
 :qid |outputbpl.1302:15|
 :skolemid |22`
- **Body:** `(= (Seq#Index (Seq#Create $generated@@950 $generated@@951 $generated@@952 $generated@@953) $generated@@954) (Apply1 TInt $`
- **QID:** `outputbpl.285:18`

### Axiom 12
- **Trigger:** `Seq#Length (Seq#Append _seq_ _seq_`
- **Body:** `(= (Seq#Length (Seq#Append _seq_ _seq_)) (+ (Seq#Length _seq_) (Seq#Length _seq_)))
 :qid`
- **Body:** `(= (Seq#Index (Seq#Build $generated@@1183 $generated@@1185) $generated@@1184) $generated@@1185)) (=> (not (= $generated@@1184 ($generated@@`
- **QID:** `outputbpl.1271:15`

### Axiom 13
- **Trigger:** `Seq#Index (Seq#Build _seq_ _box_`
- **Body:** `(= (Seq#Index (Seq#Build _seq_ _box_) _int_) _box_)) (=> (not (= _int_ ($generated@@`
- **Body:** `(= (Seq#Index (Seq#Build _seq_ _box_) _int_) (Seq#Index _seq_ _int_))))
 :qid |`
- **QID:** `outputbpl.2667:15`

### Axiom 14
- **Trigger:** `Seq#Contains (Seq#Append _seq_ _seq_`
- **Body:** `(= (Seq#Contains (Seq#Append _seq_ _seq_) _box_)  (or (Seq#Contains _seq_ _box_) ($g`
- **Body:** `(= (Seq#Contains (Seq#Take $generated@@1235 $generated@@1236) $generated@@1237) (exists (($generated@@1238 Int) ) (!  (and (and (and (<= 0 $`
- **QID:** `outputbpl.1339:15`

### Axiom 15
- **Trigger:** `Seq#Equal _seq_ _seq_`
- **QID:** `outputbpl.2473:15`

### Axiom 16
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

### Axiom 17
- **Trigger:** `Seq#Take (Seq#Update _seq_ _int_ _box_`
- **Body:** `(= (Seq#Take (Seq#Update _seq_ _int_ _box_) _int_) (Seq#Take _seq_ $generate`
- **Body:** `(= (IsValidPath ($generated@@1531))  (and (>= (Seq#Length ($generated@@1531)) (LitInt 1)) (forall (($gene`
- **QID:** `outputbpl.1524:15`

### Axiom 18
- **Trigger:** `Seq#Length _seq_`
- **Body:** `(= (IsValidPath ($generated@@1531))  (and (>= (Seq#Length ($generated@@1531)) (LitInt 1)) (forall (($gene`
- **QID:** `outputbpl.75:15`

### Axiom 19
- **Trigger:** `Seq#Rank (Seq#Append (Seq#Take _seq_ _int_`
- **QID:** `outputbpl.2682:15`

### Axiom 20
- **Trigger:** `Seq#Length (Seq#Update _seq_ _int_ _box_`
- **Body:** `(= (Seq#Length (Seq#Update _seq_ _int_ _box_)) (Seq#Length _seq_)))
 :qid |outputbpl.1325:15|`
- **Body:** `(= (Seq#Length (Seq#FromArray $generated@@1799 $generated@@1800)) (_System.array.Length $generated@@1800))
 :qid |outputbpl.1481:15|
 :skolemid |262|`
- **QID:** `outputbpl.2087:15`

### Axiom 21
- **Trigger:** `Seq#Length (Seq#FromArray $generated@@1799 _T@ref_`
- **Body:** `(= (Seq#Length (Seq#FromArray $generated@@1799 _T@ref_)) (_System.array.Length _T@ref_))
 :qid |outputbpl.1481:15|
 :skolemid |262|`
- **Body:** `(= (Seq#Build_inv0 (Seq#Build $generated@@1828 $generated@@1829)) $generated@@1828) (= (Seq#Build_inv1 (Seq#Build $generated@@1828 $ge`
- **QID:** `outputbpl.2706:15`

### Axiom 22
- **Trigger:** `Seq#Build _seq_ _box_`
- **Body:** `(= (Seq#Build_inv0 (Seq#Build _seq_ _box_)) _seq_) (= (Seq#Build_inv1 (Seq#Build _seq_ $ge`
- **Body:** `(= (Seq#Build_inv1 (Seq#Build _seq_ _box_)) _box_))
 :qid |outputbpl.1297:15|
 :skolemid |224|
 :pattern ( ($`
- **QID:** `outputbpl.2397:15`

### Axiom 23
- **Trigger:** `MultiSet#FromSeq (Seq#Build _seq_ _box_`
- **QID:** `outputbpl.1992:15`

### Axiom 24
- **Trigger:** `Seq#Index (Seq#Append _seq_ _seq_`
- **Body:** `(= (Seq#Index (Seq#Append _seq_ _seq_) _int_) (Seq#Index _seq_ _int_))) (=> (<= `
- **Body:** `(= (Seq#Index (Seq#Append _seq_ _seq_) _int_) (Seq#Index _seq_ (- _int_ ($genera`
- **QID:** `outputbpl.2338:15`

### Axiom 25
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

### Axiom 26
- **Trigger:** `Seq#Length _seq_`
- **Body:** `(= (Seq#Length _seq_) 0) (= _seq_ Seq#Empty))
 :qid |outputbpl.1289:15|
 :skolemid |223|
 :pattern ( (Seq#Length $`
- **Body:** `(= (Seq#Take $generated@@2059 $generated@@2060) Seq#Empty))
 :qid |outputbpl.1453:15|
 :skolemid |257|
 :pattern ( (Seq#Take $gene`
- **QID:** `outputbpl.3555:19`

### Axiom 27
- **Trigger:** `Seq#Take _seq_ _int_`
- **Body:** `(= (Seq#Take _seq_ _int_) Seq#Empty))
 :qid |outputbpl.1453:15|
 :skolemid |257|
 :pattern ( (Seq#Take $gene`
- **QID:** `outputbpl.3555:19`

### Axiom 28
- **Trigger:** `Seq#Take (Seq#Update _seq_ _int_ _box_`
- **Body:** `(= (Seq#Take (Seq#Update _seq_ _int_ _box_) _int_) (Seq#Update (Seq#Take $generate`
- **QID:** `outputbpl.2580:15`

## Trigger Gap Analysis (heuristic)
**Pattern:** `concat_last_element_decomposition`
**Description:** No axiom decomposes Seq#Append(a, b) by peeling the last element: Seq#Append(a, b) == Seq#Append(Seq#Append(a, Seq#Take(b, |b|-1)), Seq#Build(Seq#Index(b, |b|-1))). This requires relating two different Seq#Append forms.
**Needed:** `Seq#Append(a, b) == Seq#Append(Seq#Append(a, Seq#Take(b, Seq#Length(b)-1)), Seq#Build(Seq#Index(b, |b|-1)))`
**Missing:** `Seq#Append(a, b) → Seq#Append(Seq#Append(a, Seq#Take(b, |b|-1)), Seq#Build(Seq#Index(b, |b|-1)))`

## Diagnosis Question

Given the axioms above, explain precisely why the Z3 solver
cannot derive `a + b == (a + b[..|b|-1]) + [b[|b|-1]]` on its own.
What specific axiom or trigger pattern is missing from the
SMT encoding that would allow the solver to derive this equality?
Is this a fundamental limitation of the axiomatization, or a
trigger/e-matching gap that could be fixed?