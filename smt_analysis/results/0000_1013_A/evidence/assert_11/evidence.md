# Evidence Bundle: assert x == [x[0]] + x[1..];
**Line 156**

## The Assertion
```dafny
assert x == [x[0]] + x[1..];
```

**SMT encoding:**
- LHS: `x` → `x`
- RHS: `[x[0]] + x[1..]` → `Seq#Append(Seq#Build(Seq#Index(x, 0)), Seq#Drop(x, 1))`

## What Breaks Without It
**Dafny error:** assertion could not be proved

## Counterexample Model (spurious)
Z3 result: `timeout`

## Relevant Axioms (49 found)

These are all axioms in the SMT preamble whose primary trigger
pattern involves the same operations as the assertion:

### Axiom 1
- **Trigger:** `Seq#Index _seq_ $generated@@84`
- **Body:** `(= (Seq#Length (_seq_)) (Seq#Length (_seq_))) (=> (forall (($generated@@84 Int) ) (!  (=> (and`
- **Body:** `(= (ValidRemoval (_seq_) (_seq_) (LitInt _int_))  (and (and (= (Seq#Length ($ge`
- **QID:** `outputbpl.3409:15`

### Axiom 2
- **Trigger:** `Seq#Index _seq_ $generated@@94`
- **Body:** `(= (IsValidPath _seq_)  (and (>= (Seq#Length _seq_) (LitInt 1)) (forall (($generated@@95 Int) ($generated@@96 Int) ) `
- **QID:** `outputbpl.3474:19`

### Axiom 3
- **Trigger:** `Seq#Index _seq_ $generated@@424`
- **Body:** `(= (Seq#Length _seq_) (Seq#Length _seq_)) (=> (forall (($generated@@424 Int) ) (!  (=> (and (<= (LitInt 0) $genera`
- **Body:** `(= (ValidRemoval _seq_ _seq_ _int_)  (and (and (= (Seq#Length _seq_) (Seq#Length _seq_)) (`
- **QID:** `outputbpl.821:15`

### Axiom 4
- **Trigger:** `Seq#Drop (Seq#Build _seq_ _box_`
- **Body:** `(= (Seq#Drop (Seq#Build _seq_ _box_) _int_) (Seq#Build (Seq#Drop _seq_ TORDINAL`
- **Body:** `(= (ValidRemoval#requires $generated@@482 $generated@@483 $generated@@484) true))
 :qid |outputbpl.4440:15|
 :skolemid |633|
 :pattern ( (ValidRemoval`
- **QID:** `outputbpl.3251:15`

### Axiom 5
- **Trigger:** `Seq#Index (Seq#Update _seq_ _int_ _box_`
- **Body:** `(= (Seq#Index (Seq#Update _seq_ _int_ _box_) _int_) _box_)) (=> (not (= _int_ $g`
- **Body:** `(= (Seq#Index (Seq#Update _seq_ _int_ _box_) _int_) (Seq#Index _seq_ _int_)`
- **QID:** `outputbpl.903:15`

### Axiom 6
- **Trigger:** `Seq#Take (Seq#Append _seq_ _seq_`
- **Body:** `(= (Seq#Take (Seq#Append _seq_ _seq_) _int_) _seq_) (= (Seq#Drop (Seq#Append $generate`
- **Body:** `(= (Seq#Drop (Seq#Append _seq_ _seq_) _int_) _seq_)))
 :qid |outputbpl.1421:15|
 :skolemid |250|
 `
- **QID:** `outputbpl.3999:27`

### Axiom 7
- **Trigger:** `Seq#Index _seq_ $generated@@614`
- **Body:** `(= (AllNonNeg _seq_) (forall (($generated@@614 Int) ) (!  (=> (and (<= (LitInt 0) $generated@@614) (< $generated@@614 ($genera`
- **Body:** `(= (Seq#Take (Seq#FromArray $generated@@629 $generated@@630) $generated@@632) (Seq#Build (Seq#Take (Seq#FromArray $generated@@`
- **QID:** `outputbpl.191:1`

### Axiom 8
- **Trigger:** `Seq#Take (Seq#FromArray $generated@@629 _T@ref_`
- **Body:** `(= (Seq#Take (Seq#FromArray $generated@@629 _T@ref_) _int_) (Seq#Build (Seq#Take (Seq#FromArray $generated@@`
- **Body:** `(= (LegalStep $generated@@655 $generated@@656)  (and (= (Seq#Length $generated@@655) (Seq#Length $generated@@656)) (or (exists (($generat`
- **QID:** `outputbpl.3674:19`

### Axiom 9
- **Trigger:** `Seq#Index _seq_ $generated@@657`
- **Body:** `(= (LegalStep _seq_ _seq_)  (and (= (Seq#Length _seq_) (Seq#Length _seq_)) (or (exists (($generat`
- **Body:** `(= (Seq#Length _seq_) (Seq#Length _seq_)) (or (exists (($generated@@657 Int) ) (!  (and (and (and (<= (LitInt 0) $`
- **QID:** `outputbpl.1796:15`

### Axiom 10
- **Trigger:** `Seq#Drop (Seq#Update _seq_ _int_ _box_`
- **Body:** `(= (Seq#Drop (Seq#Update _seq_ _int_ _box_) _int_) (Seq#Update (Seq#Drop TagChar`
- **Body:** `(= (Seq#Drop $generated@@710 $generated@@711) $generated@@710))
 :qid |outputbpl.1451:15|
 :skolemid |256|
 :pattern ( (Seq#Drop $genera`
- **QID:** `outputbpl.1866:15`

### Axiom 11
- **Trigger:** `Seq#Drop _seq_ _int_`
- **Body:** `(= (Seq#Drop _seq_ _int_) _seq_))
 :qid |outputbpl.1451:15|
 :skolemid |256|
 :pattern ( (Seq#Drop $genera`
- **QID:** `outputbpl.312:15`

### Axiom 12
- **Trigger:** `select $generated@@755 $generated@@757`
- **QID:** `outputbpl.1607:15`

### Axiom 13
- **Trigger:** `Math#clip _int_`
- **Body:** `(= (Seq#Length (Seq#Create $generated@@797 $generated@@798 $generated@@799 $generated@@800)) $generated@@799))
 :qid |outputbpl.1468:15|
 :sk`
- **QID:** `outputbpl.1468:15`

### Axiom 14
- **Trigger:** `Seq#Index (Seq#Take _seq_ _int_`
- **Body:** `(= (Seq#Index (Seq#Take _seq_ _int_) _int_) (Seq#Index _seq_ _int_)))
 :qid |output`
- **Body:** `(= (Seq#Length (Seq#Drop $generated@@853 $generated@@854)) (- (Seq#Length $generated@@853) $generated@@854)))
 :qid |outputbpl.1407:15|`
- **QID:** `outputbpl.2457:15`

### Axiom 15
- **Trigger:** `Seq#Length (Seq#Drop _seq_ _int_`
- **Body:** `(= (Seq#Length (Seq#Drop _seq_ _int_)) (- (Seq#Length _seq_) _int_)))
 :qid |outputbpl.1407:15|`
- **Body:** `(= (Seq#Length $generated@@877) (LitInt 0))) (Sum#canCall (Seq#Take $generated@@877 (- (Seq#Length $generated@@877) 1)))) (=`
- **QID:** `outputbpl.1520:15`

### Axiom 16
- **Trigger:** `Seq#Index _seq_ $generated@@882`
- **Body:** `(= (Seq#Equal _seq_ _seq_)  (and (= (Seq#Length _seq_) (Seq#Length _seq_)) (forall (($generated@`
- **Body:** `(= (Seq#Length _seq_) (Seq#Length _seq_)) (forall (($generated@@882 Int) ) (!  (=> (and (<= 0 $generated@@882) (< $generat`
- **QID:** `outputbpl.2697:15`

### Axiom 17
- **Trigger:** `Seq#Rank (Seq#Take _seq_ _int_`
- **Body:** `(= (Seq#Length $generated@@901) (Seq#Length $generated@@902)) (and (AllNonNeg#canCall $generated@@901) (=> (AllNonNeg $generated@@901) (an`
- **Body:** `(= (CanTransform $generated@@901 $generated@@902)  (and (and (and (= (Seq#Length $generated@@901) (Seq#Length $generated@@902)) ($generated`
- **QID:** `outputbpl.3704:24`

### Axiom 18
- **Trigger:** `Seq#Rank (Seq#Drop _seq_ _int_`
- **Body:** `(= (Seq#Length (Seq#Build $generated@@944 $generated@@945)) (+ 1 (Seq#Length $generated@@944)))
 :qid |outputbpl.1302:15|
 :skolemid |22`
- **Body:** `(= (Seq#Index (Seq#Create $generated@@950 $generated@@951 $generated@@952 $generated@@953) $generated@@954) (Apply1 TInt $`
- **QID:** `outputbpl.285:18`

### Axiom 19
- **Trigger:** `DtRank ($Unbox_41386 (Seq#Index _seq_ _int_`
- **Body:** `(= (Seq#Index (Seq#Create $generated@@950 $generated@@951 $generated@@952 $generated@@953) $generated@@954) (Apply1 TInt $`
- **QID:** `outputbpl.285:18`

### Axiom 20
- **Trigger:** `Seq#Index (Seq#Create _type_ $generated@@951 _int_ _T@HandleType_`
- **Body:** `(= (Seq#Index (Seq#Create _type_ $generated@@951 _int_ _T@HandleType_) _int_) (Apply1 TInt $`
- **QID:** `outputbpl.285:18`

### Axiom 21
- **Trigger:** `Seq#Index _seq_ $generated@@1109`
- **Body:** `(= (AllNonNeg (_seq_)) (forall (($generated@@1109 Int) ) (!  (=> (and (<= (LitInt 0) $generated@@1109) (< $gen`
- **Body:** `(= (Seq#Index (Seq#Drop $generated@@1118 $generated@@1119) $generated@@1120) (Seq#Index $generated@@1118 (+ $generated@@1120 $generat`
- **QID:** `outputbpl.1640:15`

### Axiom 22
- **Trigger:** `Seq#Index (Seq#Drop _seq_ _int_`
- **Body:** `(= (Seq#Index (Seq#Drop _seq_ _int_) _int_) (Seq#Index _seq_ (+ _int_ $generat`
- **QID:** `outputbpl.566:15`

### Axiom 23
- **Trigger:** `Seq#Length (Seq#Append _seq_ _seq_`
- **Body:** `(= (Seq#Length (Seq#Append _seq_ _seq_)) (+ (Seq#Length _seq_) (Seq#Length _seq_)))
 :qid`
- **Body:** `(= (Seq#Index (Seq#Build $generated@@1183 $generated@@1185) $generated@@1184) $generated@@1185)) (=> (not (= $generated@@1184 ($generated@@`
- **QID:** `outputbpl.1271:15`

### Axiom 24
- **Trigger:** `Seq#Index (Seq#Build _seq_ _box_`
- **Body:** `(= (Seq#Index (Seq#Build _seq_ _box_) _int_) _box_)) (=> (not (= _int_ ($generated@@`
- **Body:** `(= (Seq#Index (Seq#Build _seq_ _box_) _int_) (Seq#Index _seq_ _int_))))
 :qid |`
- **QID:** `outputbpl.2667:15`

### Axiom 25
- **Trigger:** `Seq#Index _seq_ $generated@@1188`
- **Body:** `(= (GreedyKeep ($LS $generated@@1208) $generated@@1209 $generated@@1210) (GreedyKeep $generated@@1208 $generated@@1209 $generated`
- **Body:** `(= (Seq#Index (Seq#FromArray $generated@@1211 $generated@@1212) $generated@@1213) (select (select $generated@@1211 $generated@@1212) ($generate`
- **QID:** `outputbpl.3295:15`

### Axiom 26
- **Trigger:** `Seq#Contains (Seq#Append _seq_ _seq_`
- **Body:** `(= (Seq#Contains (Seq#Append _seq_ _seq_) _box_)  (or (Seq#Contains _seq_ _box_) ($g`
- **Body:** `(= (Seq#Contains (Seq#Take $generated@@1235 $generated@@1236) $generated@@1237) (exists (($generated@@1238 Int) ) (!  (and (and (and (<= 0 $`
- **QID:** `outputbpl.1339:15`

### Axiom 27
- **Trigger:** `Seq#Index _seq_ $generated@@1238`
- **Body:** `(= (Seq#Contains (Seq#Take _seq_ _int_) _box_) (exists (($generated@@1238 Int) ) (!  (and (and (and (<= 0 $`
- **Body:** `(= (Seq#Index _seq_ $generated@@1238) _box_))
 :qid |outputbpl.1362:19|
 :skolemid |236|
 :pattern ( (Seq#Index $gener`
- **QID:** `outputbpl.4609:15`

### Axiom 28
- **Trigger:** `Seq#Index _seq_ $generated@@1261`
- **Body:** `(= (Seq#Contains _seq_ _box_) (exists (($generated@@1261 Int) ) (!  (and (and (<= 0 $generated@@1261) (< $generated@@1261 ($g`
- **Body:** `(= (Seq#Index _seq_ $generated@@1261) _box_))
 :qid |outputbpl.1342:19|
 :skolemid |231|
 :pattern ( (Seq#Index $gener`
- **QID:** `outputbpl.531:15`

### Axiom 29
- **Trigger:** `Seq#Drop (Seq#Update _seq_ _int_ _box_`
- **Body:** `(= (Seq#Drop (Seq#Update _seq_ _int_ _box_) _int_) (Seq#Drop _seq_ $generate`
- **QID:** `outputbpl.1713:15`

### Axiom 30
- **Trigger:** `Seq#Equal _seq_ _seq_`
- **QID:** `outputbpl.2473:15`

### Axiom 31
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

### Axiom 32
- **Trigger:** `Seq#Take (Seq#Update _seq_ _int_ _box_`
- **Body:** `(= (Seq#Take (Seq#Update _seq_ _int_ _box_) _int_) (Seq#Take _seq_ $generate`
- **Body:** `(= (IsValidPath ($generated@@1531))  (and (>= (Seq#Length ($generated@@1531)) (LitInt 1)) (forall (($gene`
- **QID:** `outputbpl.1524:15`

### Axiom 33
- **Trigger:** `Seq#Index _seq_ $generated@@1533`
- **Body:** `(= (IsValidPath (_seq_))  (and (>= (Seq#Length (_seq_)) (LitInt 1)) (forall (($gene`
- **QID:** `outputbpl.81:15`

### Axiom 34
- **Trigger:** `Seq#Rank (Seq#Append (Seq#Take _seq_ _int_`
- **QID:** `outputbpl.2682:15`

### Axiom 35
- **Trigger:** `Seq#Index _seq_ $generated@@1603`
- **QID:** `outputbpl.219:18`

### Axiom 36
- **Trigger:** `TISet _type_`
- **QID:** `outputbpl.221:18`

### Axiom 37
- **Trigger:** `TISet _type_`
- **QID:** `outputbpl.221:18`

### Axiom 38
- **Trigger:** `Seq#Index _seq_ $generated@@1879`
- **Body:** `(= (Seq#Contains (Seq#Drop _seq_ _int_) _box_) (exists (($generated@@1879 Int) ) (!  (and (and (and (<= 0 $`
- **Body:** `(= (Seq#Index _seq_ $generated@@1879) _box_))
 :qid |outputbpl.1369:19|
 :skolemid |238|
 :pattern ( (Seq#Index $gener`
- **QID:** `outputbpl.1650:15`

### Axiom 39
- **Trigger:** `Seq#Index _seq_ _int_`
- **Body:** `(= (Seq#Index (Seq#Drop _seq_ _int_) (- _int_ _int_)) (Seq#Index _seq_ $genera`
- **QID:** `outputbpl.1182:15`

### Axiom 40
- **Trigger:** `Seq#Drop (Seq#Drop _seq_ _int_`
- **Body:** `(= (Seq#Drop (Seq#Drop _seq_ _int_) _int_) (Seq#Drop _seq_ (+ _int_ $gener`
- **Body:** `(= (Seq#SameUntil $generated@@1959 $generated@@1960 $generated@@1961) (forall (($generated@@1962 Int) ) (!  (=> (and (<= 0 $generated@@1962) (< $ge`
- **QID:** `outputbpl.547:15`

### Axiom 41
- **Trigger:** `Seq#Index _seq_ $generated@@1962`
- **Body:** `(= (Seq#SameUntil _seq_ _seq_ _int_) (forall (($generated@@1962 Int) ) (!  (=> (and (<= 0 $generated@@1962) (< $ge`
- **Body:** `(= (Seq#Index _seq_ $generated@@1962) (Seq#Index _seq_ $generated@@1962)))
 :qid |outputbpl.1390:19|
 :skolemid |243|
`
- **QID:** `outputbpl.2572:15`

### Axiom 42
- **Trigger:** `Seq#Index (Seq#Append _seq_ _seq_`
- **Body:** `(= (Seq#Index (Seq#Append _seq_ _seq_) _int_) (Seq#Index _seq_ _int_))) (=> (<= `
- **Body:** `(= (Seq#Index (Seq#Append _seq_ _seq_) _int_) (Seq#Index _seq_ (- _int_ ($genera`
- **QID:** `outputbpl.2338:15`

### Axiom 43
- **Trigger:** `Math#clip _int_`
- **QID:** `outputbpl.142:18`

### Axiom 44
- **Trigger:** `Seq#Index _seq_ $generated@@2022`
- **Body:** `(= (LegalStep (_seq_) (_seq_))  (and (= (Seq#Length (_seq_)) ($`
- **Body:** `(= (Seq#Length (_seq_)) (Seq#Length (_seq_))) (or (exists (($generated@@2022 Int) ) (!  (a`
- **QID:** `outputbpl.1791:15`

### Axiom 45
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

### Axiom 46
- **Trigger:** `Seq#Take _seq_ _int_`
- **Body:** `(= (Seq#Take _seq_ _int_) Seq#Empty))
 :qid |outputbpl.1453:15|
 :skolemid |257|
 :pattern ( (Seq#Take $gene`
- **QID:** `outputbpl.3555:19`

### Axiom 47
- **Trigger:** `$IsBox _box_ (TISet _type_`
- **QID:** `outputbpl.365:15`

### Axiom 48
- **Trigger:** `Seq#Take (Seq#Update _seq_ _int_ _box_`
- **Body:** `(= (Seq#Take (Seq#Update _seq_ _int_ _box_) _int_) (Seq#Update (Seq#Take $generate`
- **QID:** `outputbpl.2580:15`

### Axiom 49
- **Trigger:** `Seq#Index _seq_ $generated@@2199`
- **QID:** `outputbpl.342:15`

## Trigger Gap Analysis (heuristic)
**Pattern:** `cons_decomposition`
**Description:** No axiom decomposes a non-empty sequence into its head and tail: s == Seq#Append(Seq#Build(Seq#Index(s, 0)), Seq#Drop(s, 1)). The solver has both terms in the e-graph but no trigger connects them.
**Needed:** `x == Seq#Append(Seq#Build(Seq#Index(x, 0)), Seq#Drop(x, 1))`
**Missing:** `s → Seq#Append(Seq#Build(Seq#Index(s, 0)), Seq#Drop(s, 1))`

## Diagnosis Question

Given the axioms above, explain precisely why the Z3 solver
cannot derive `x == [x[0]] + x[1..]` on its own.
What specific axiom or trigger pattern is missing from the
SMT encoding that would allow the solver to derive this equality?
Is this a fundamental limitation of the axiomatization, or a
trigger/e-matching gap that could be fixed?