# ERDŐS #287 — END-TO-END CLOSURE REPORT

**Erdős #287 is NOT solved here.**  What follows is an audit of what is kernel-checked in
this repository after this pass, what was repaired, and exactly which statement is still
missing.  Everything asserted below is backed by a Lean declaration that compiles without
`sorry`; anything not backed by such a declaration is marked OPEN or NOT BANKED and is
never used as an input to a proved theorem.

---

## A. Exact public statement / Lean statement

The public problem: for every finite strictly increasing sequence `1 < n₁ < ⋯ < n_k` with
`∑ 1/nᵢ = 1`, some consecutive gap is `≥ 3`.

Lean (`RequestProject/Erdos287/ProblemStatement.lean`):

```lean
structure Erdos287Counterexample (A : Finset ℕ) : Prop where
  card_ge    : 2 ≤ A.card
  one_lt     : ∀ a ∈ A, 1 < a
  sum_one    : ∑ a ∈ A, (1 : ℚ) / a = 1
  gap_le_two : ∀ a ∈ A, (∃ b ∈ A, a < b) → (a + 1 ∈ A ∨ a + 2 ∈ A)

def Erdos287Statement : Prop := ∀ A : Finset ℕ, ¬ Erdos287Counterexample A
```

and the ordered form, proved from the set form:

```lean
theorem erdos287_seq_of_no_counterexample
    (hno : ∀ A : Finset ℕ, ¬ Erdos287Counterexample A)
    (k : ℕ) (n : ℕ → ℕ)
    (hmono : ∀ i j, i < j → j < k → n i < n j)
    (hone  : ∀ i, i < k → 1 < n i)
    (hsum  : ∑ i ∈ Finset.range k, (1 : ℚ) / (n i) = 1) :
    ∃ i, i + 1 < k ∧ n i + 3 ≤ n (i + 1)
```

`k ≥ 2` is **derived** inside that proof (`k = 1` forces `1/n₀ = 1`, i.e. `n₀ = 1`,
contradicting `1 < n₀`), so no cardinality hypothesis is smuggled in.

**Bridge (one way only, as instructed).**  `Erdos287Counterexample.toGap2CE` maps an exact
counterexample to the historical compiler type `Gap2CE`.  The converse is **false** and is
not attempted: `gap2CE_one : Gap2CE` is the junk inhabitant `A = {1}`, and
`not_erdos287Counterexample_one` shows it is not an exact counterexample.  Two further
facts about the exact type are proved and used: `three_le_max` and `four_le_max`
(`max A ≤ 3` forces `A ⊆ {2,3}`, whose reciprocal sum is `5/6`).

## B. Baseline finite V1/V2 results (regression)

`lake build` passed **before** any edit (8080 jobs) and passes now (8086 jobs).  Nothing
was deleted, renamed or weakened.  All the named results are still present and still
kernel-checked; their axiom prints are re-run in
`RequestProject/Status/Erdos287EndToEndStatus.lean`:

`Gap2CE.halfRange_min_le`, `topExp_le_one_of_lt_sq`, `topHalf_prime_hole`,
`q_and_two_mul_q_holes`, `Gap2CE.v2_plus_sophie_blocker`, `Gap2CE.v2_minus_sophie_blocker`,
`Gap2CE.v2_finite_compiler`, `Gap2CE.v2_exact_compiler`, `no_Gap2CE_M_eq_104`,
`sophieWitness_sweep`, `no_Gap2CE_of_M_in_39_250`.

### B.1 Patched finite Sophie interface (sign-sensitive)

`RequestProject/Erdos287/FiniteMasterReduction.lean`:

```lean
def PlusSophieWitness  (M q : ℕ) : Prop := q.Prime ∧ 5 ≤ q ∧ M < 3*q ∧ 2*q+1 ≤ M ∧ (2*q+1).Prime
def MinusSophieWitness (M q : ℕ) : Prop := q.Prime ∧ 5 ≤ q ∧ M < 3*q ∧ 2*q   ≤ M ∧ (2*q-1).Prime
def SophieWitness (M : ℕ) : Prop := (∃ q, PlusSophieWitness M q) ∨ (∃ q, MinusSophieWitness M q)
```

with `plus_interval_floor` / `minus_interval_floor` proving these are literally
`M/3 < q ≤ (M-1)/2` and `M/3 < q ≤ ⌊M/2⌋` in integer floors.  The common endpoint is gone,
`5 ≤ q` closes the small-`M` hole, and the word "maximal" is no longer used for the old
common interval; `sophieWitness_imp` shows the old coarser predicate implies the new one.

Master theorem (§4 of the request):

```lean
theorem no_Erdos287Counterexample_of_sophieWitness {A : Finset ℕ}
    (h : Erdos287Counterexample A) (hs : SophieWitness (A.max' h.nonempty)) : False
```

The `39 ≤ M ≤ 250` result is retained and re-proved against the repaired interface
(`sophieWitnessB_sweep`, `no_Erdos287Counterexample_of_max_in_39_250`).

### B.2 New free finite blocker — maximum-divisor prime

```lean
theorem Gap2CE.maxDivisorPrime_blocker {q : ℕ}
    (hq : q.Prime) (hq3 : 3 < q) (hdvd : q ∣ ce.M) (hM3 : ce.M < 3 * q) : False
```

Consequences: `Gap2CE.no_Gap2CE_of_prime_max` (no counterexample has a prime maximum),
`Gap2CE.no_Gap2CE_of_max_eq_two_mul_prime` (none has `M = 2q`, `q > 3` prime), and
`no_Erdos287Counterexample_of_prime_max` for the exact type.  Note the hypothesis `q² > M`
suggested in the request is **not needed**: it follows from `M < 3q` and `q ≥ 4`, so it was
dropped rather than carried.

## C. Extended finite range — the interval-certificate engine

This is the main new mathematics of this pass.

`RequestProject/Erdos287/FiniteRemainder.lean` defines the certified numerator table
`CVal` (`C 0…C 9 ≤ 1,1,3,11,25,137,137,1019,2143,7129`, proved by `C_le_CVal` from the
banked `C_one … C_nine`) and proves

```lean
theorem Gap2CE.blocker_window {x pu au pv av L U : ℕ}
    (hpu : pu.Prime) (hpv : pv.Prime) (hau : 1 ≤ au) (hav : 1 ≤ av)
    (hdu : pu ^ au ∣ x) (hdv : pv ^ av ∣ (x + 1))
    (hwu : U / pu ^ au ≤ 9) (hcu : CVal (U / pu ^ au) < pu)
    (hwv : U / pv ^ av ≤ 9) (hcv : CVal (U / pv ^ av) < pv)
    (hUx : U ≤ 2 * x) (hxL : x + 1 ≤ L)
    (h1 : L ≤ ce.M) (h2 : ce.M ≤ U) : False
```

One certificate kills an **interval** `[L,U]` of maxima, because the window
`⌊M/p^e⌋` is monotone in `M` and `C` is monotone (`C_mono`), while `M ≤ 2x` places both
holes above `N` via `halfRange_min_le`.  Since each certificate reaches from `L ≈ x` to
`U = 2x`, the covered range doubles per certificate.

`RequestProject/Erdos287/FiniteRangeExtension.lean` contains a chain of **34** such
certificates and proves

* `Gap2CE.no_of_M_le_4e9` — no gap-`≤2` counterexample with `3 ≤ M ≤ 4·10⁹`;
* `no_Erdos287Counterexample_of_max_le_4e9` — no exact counterexample with
  `max A ≤ 4·10⁹`.

**Exact largest verified interval: `3 ≤ M ≤ 4 000 000 000`** (previously `39 ≤ M ≤ 250`).
The endpoint is limited only by the size of primality certificates the kernel accepts:
all primality side conditions are discharged by `norm_num` (largest prime used:
`1 546 710 859`); there is no `native_decide` and no large-number `decide`.
Elaboration of the whole chain takes ≈ 25 s.

## D–J. Fresh R9 leakage, H = 70, fresh c₉, convolution, f + δ, Full-Nine bridge, SW2 shell

**NOT BANKED — source unavailable in this repository.**

These sections all require the *actual* Ford–Maynard definitions (Definition 4.3 for
`R(P)`/`C(R)`, equation (7.17) for `G(m;n)`, `H(n) = ∑_{d∣n} G(d;n)`, Proposition 7.22, the
grouped equation (7.23), Theorem 8.3 for `R(P_ε)`).  Those definitions exist neither as
Lean objects in this project nor as source text inside it, and the instruction —
correctly — forbids instantiating them from a later schematic model or citing a prose
result.  Therefore:

* **R9-LEAKAGE45**: NOT BANKED.  First blocking item: the Lean definition of the
  fundamental region `R(P)` and its coagulation closure `C(R(P))` from Definition 4.3.
* **H = 70**: NOT BANKED, and deliberately *not* softened.  The primary-source firewall
  demanded in the request cannot even be started, because step 1 (the canonical split
  `d = m₁m₂` with `P⁺(m₁) < n^σ ≤ P⁻(m₂)` from (7.17)) has no source definition here.
  What *is* banked is only the finite combinatorics, and it is labelled as such in
  `RequestProject/TrustedBank/R9/Certificate.lean`: `altSum_eq` (`∑_{j=5}^{9} (-1)^j C(9,j)
  = -70`), and newly `lowSum_eq` (`∑_{j=0}^{4} (-1)^j C(9,j) = 70`) with
  `lowSum_add_altSum` (the two halves cancel).  These are binomial identities, **not**
  `H(n) = 70`.
* **FM-R9-GENERATED-LEAKAGE45 (fresh c₉)**, **R9-EPS-COMPAT45**, **convolution /
  factorial multiplicity**, **f + δ normalisation and prime-power sparsity**,
  **physical Full-Nine bridge**, **SW2 determinant shell**: NOT BANKED, same reason.
  No schematic substitute was created, no "capacity" was promoted to an estimate, and no
  structure with an unprovable field was inhabited.

The provenance-role correction requested (balanced R9 to be treated as a *Ford-generated
leakage packet* for the proof-specific Prop-7.22 / eq-(7.23) lane, never advertised as a
universal Type-II source) is recorded here and in the R9 file's docstring, and no existing
R9 material was deleted.

## K–P. Gate-1B supplement socket, Gate-1B, generated packet census, Gate-1A necessity, generated-(7.23), C_FM

**OPEN / NOT CONSTRUCTED.**  A `Gate1B287Supplement` structure whose fields are literal
source outputs cannot be written without the literal source; writing one with invented
field types would be exactly the circularity the request forbids.  Likewise the 287
generated-packet census requires reading off every generated one-variable factor of the
actual Ford–Maynard rerun.  No census, no `FM287Generated723Bound`, and no `C_FM` audit is
claimed.  `GATE1A_REQUIRED_FOR_287` is therefore **UNKNOWN** (it can only be answered by
the census).

## Q–U. Comparison (b.1)/(b.2)/(w), Gate-0 Type I, N2 sector

**OPEN.**  No weighted maximal Bombieri–Vinogradov input, no uniform multivariate PNT
input, no collar two-linear-form sieve and no aggregate N2 replacement is present or
assumed.  These were left uninhabited rather than declared "standard".

## V. Compatible epsilon

Only one rational item from this block is checkable here and it is proved:
`Erdos287.one_sixth_gt_margin : (1 : ℚ)/6 > 1663/10000`.  A full `CompatibleEpsilon287`
would have to reference the analytic inputs above, which do not exist here; it is not
defined, so nothing pretends to select an ε.

## W–Y. Ford lower-bound compiler, prime-power removal, analytic → Sophie bridge

**OPEN** as analytic statements.  What *is* proved is the arithmetic end of the bridge, in
a stronger form than requested: any Sophie prime in the band `M/3 < q ≤ (M-1)/2` (plus
sign) or `M/3 < q ≤ ⌊M/2⌋` (minus sign) contradicts an exact counterexample with maximum
`M` (`no_Erdos287Counterexample_of_sophieWitness`), and moreover such a prime is only one
special case of the weaker `WindowPairSupply` interface (§Z below).

## Z. Effective large-M theorem and the exact remaining input

`RequestProject/Erdos287/ClosureInputs.lean`:

```lean
def WindowPairSupply (M : ℕ) : Prop :=
  ∃ x pu au pv av : ℕ,
    pu.Prime ∧ pv.Prime ∧ 1 ≤ au ∧ 1 ≤ av ∧
    pu ^ au ∣ x ∧ pv ^ av ∣ (x + 1) ∧
    M / pu ^ au ≤ 9 ∧ CVal (M / pu ^ au) < pu ∧
    M / pv ^ av ≤ 9 ∧ CVal (M / pv ^ av) < pv ∧
    M ≤ 2 * x ∧ x + 1 ≤ M

theorem Gap2CE.no_of_windowPairSupply (h : WindowPairSupply ce.M) : False
theorem windowPairSupply_of_sophieWitness {M : ℕ} (h : SophieWitness M) : WindowPairSupply M

structure Erdos287ClosureInputs where
  M0                : ℕ
  threshold_covered : M0 ≤ 4000000000
  supply            : ∀ M : ℕ, M0 ≤ M → WindowPairSupply M

theorem no_Erdos287Counterexample_of_closure (I : Erdos287ClosureInputs) : Erdos287Statement
theorem erdos287_seq_of_closure (I : Erdos287ClosureInputs) : … (ordered form)
```

No field of `Erdos287ClosureInputs` is, or definitionally implies, the conclusion; the only
mathematical field is a statement about prime-power divisors of consecutive integers, with
an explicit finite threshold.  **No inhabitant is constructed.**

Content of the missing statement, in plain terms: for every large `M` there are two
consecutive integers `x, x+1` in `[⌈M/2⌉, M]` such that each has a prime-power divisor
`p^e > M/10` with `p` above the (tiny) certified numerator bound of its window.  This is
weaker than the Sophie-Germain-type supply (proved: `windowPairSupply_of_sophieWitness`),
but it is still an assertion about almost-primes at consecutive integers of
Ford–Maynard difficulty.  It is **not** proved here and is **not** assumed as an axiom.

## AA. Finite remainder

The certificate mechanism of §C *is* the finite-remainder engine: certificate entries are
intervals `[L,U]` covered by one witness, chained by `L_{i+1} = U_i + 1`, and no subset
enumeration over denominators is used anywhere.  It currently covers `[3, 4·10⁹]`; pushing
the top endpoint further is a matter of larger primality certificates, not of new
mathematics.  Below `M = 3` there is nothing to cover: `four_le_max` shows every exact
counterexample has `max A ≥ 4`.

## AB. Exact final theorem status

**`erdos287` is NOT declared.**  Firewall item 1 fails (no inhabitant of
`Erdos287ClosureInputs`), and items 3–4 fail with it.  The conditional theorem
`no_Erdos287Counterexample_of_closure` is available and is clearly conditional.

## AC. Axiom audit

`RequestProject/Status/Erdos287EndToEndStatus.lean` prints axioms for every principal new
theorem and re-prints the preserved V1/V2 bank.  Result for all of them:

```
[propext, Classical.choice, Quot.sound]
```

Project-wide scan: **SORRY: none. ADMIT: none. USER AXIOMS: none. UNSAFE: none.
NATIVE_DECIDE: none. @[implemented_by]: none.**  `lake build` completes successfully
(8086 jobs).

## AD. First remaining blocker

`Erdos287ClosureInputs.supply` — i.e. `∀ M ≥ M₀, WindowPairSupply M` with an explicit
effective `M₀ ≤ 4·10⁹`.

---

# QUESTION-RESOLUTION MATRIX

**Q1. Is the public Erdős-287 statement represented exactly in Lean?**  Yes —
`Erdos287Counterexample` / `Erdos287Statement`, with the ordered-sequence form
`erdos287_seq_of_no_counterexample` proved from it.

**Q2. Is the existing `Gap2CE` type exactly equivalent, or only a broader compiler type?**
Only broader.  `gap2CE_one` inhabits `Gap2CE` with `A = {1}`;
`not_erdos287Counterexample_one` shows it is not an exact counterexample.  Only the needed
direction `Erdos287Counterexample → Gap2CE` is proved.

**Q3. What unconditional finite `M`-range is kernel closed?**  `3 ≤ M ≤ 4 000 000 000`
(and vacuously below, since `max A ≥ 4`).

**Q4. Is balanced R9 genuinely derived from Ford source?**  No — NOT BANKED; the Ford
source definitions are not present in this repository.

**Q5. Is `H(n) = 70` kernel proved?**  No.  Only the binomial identities `∑_{j=0}^{4}
(-1)^j C(9,j) = 70` and `∑_{j=5}^{9} (-1)^j C(9,j) = -70` are proved.  First failure: the
source definition of `G(m;n)` from equation (7.17) is unavailable.

**Q6. Is the fresh c₉ leakage identity kernel proved?**  No — NOT BANKED (same cause).

**Q7. Is R9 compatible with the same fixed ε used downstream?**  Unknown — R9-EPS-COMPAT45
cannot be started without Theorem 8.3 as a formal object.

**Q8. Is the nine-coordinate Full-Nine bridge physical, not schematic?**  Not applicable —
no physical R9 sources exist here; the bridge remains schematic and is not claimed.

**Q9. Is the determinant shell `C_J a_J − dpℓ = −2` source exact?**  No — not constructed.

**Q10. Has literal shifted TT* been supplied by the Pro supplement?**  No.

**Q11. What is the actual shifted multiplier law?**  Unknown here.

**Q12. Is Gate 1B fully closed?**  No — OPEN.

**Q13. Exactly which Ford-generated (7.23) packets occur for 287?**  Unknown — the census
requires the source rerun; not attempted rather than guessed.

**Q14. Does the final 287 proof actually require Gate 1A?**  UNKNOWN (answerable only by
the census).

**Q15. Does every generated Type-II packet have a proved provider?**  No — no census, no
providers.

**Q16. Is Gate 0 Type I proved or still an external weighted-BV input?**  External and
uninhabited.

**Q17. Is (b.2) uniformity fully proved?**  No — uninhabited input.

**Q18. Is the N2 local factor fully closed?**  No.

**Q19. Is the uniform two-linear-form upper sieve proved?**  No.

**Q20. Is `AggregateN2Replacement287` proved?**  No.

**Q21. Is `C_FM` complete invocation-by-invocation?**  No — not constructed.

**Q22. Is one fixed ε simultaneously compatible with every estimate?**  Not established;
only the rational comparison `1/6 > 1663/10000` is proved.

**Q23. Is the Ford positive lower-bound step formalised or external?**  External.

**Q24. Is the weighted prime-mass lower bound proved?**  No.

**Q25. Are proper prime powers rigorously removed?**  Not applicable — there is no proved
prime-mass statement to remove them from; not claimed.

**Q26. Does the resulting `q` satisfy the V2 SophieWitness predicate?**  There is no
analytically produced `q`.  What is proved is the converse direction of the interface:
any Sophie witness (sign-sensitive, `q ≥ 5`) refutes a counterexample, and every Sophie
witness yields the weaker `WindowPairSupply` witness.

**Q27. Is the sufficiently-large threshold effective?**  The threshold in
`Erdos287ClosureInputs` is an explicit natural number bounded by the verified finite range,
so *if* the supply field is ever inhabited with an effective `M₀ ≤ 4·10⁹`, the conclusion
is unconditional.  No ineffective threshold is hidden anywhere.

**Q28. Is every `M` below that threshold covered by a kernel certificate?**  Yes for every
`M ≤ 4·10⁹`, by the 34-certificate chain.

**Q29. Is an unconditional theorem `erdos287` now available?**  No.

**Q30. If not, what is the FIRST EXACT remaining theorem/input?**
`∀ M ≥ M₀, Erdos287.WindowPairSupply M` (the `supply` field of
`Erdos287.Erdos287ClosureInputs`).

---

# COUNTERGUARD CHECK

A–M: respected.  In particular the finite compiler is never confused with an asymptotic
supply (A); no R9/Gate1B/Type-II claim is made at all (B–F); no proof-specific replacement
is called a Ford theorem (G); no N2 closure is claimed (H–I); no capacity is promoted to an
estimate (J); "all sufficiently large" is never turned into "all" — the conditional
theorem carries its hypothesis explicitly (K–L); and finite verification through `4·10⁹` is
stated as exactly that, not as a solution of #287 (M).

---

# FINAL VERDICT

```
ERDOS287_ALL_INTERNAL_COMPILERS_CLOSED_EXTERNAL_ANALYTIC_INPUTS_REMAIN
```

(The internal, deterministic and finite compilers of *this* repository are closed and
kernel-checked end to end; the Ford/Gate-1A/Gate-1B lanes are not internal compilers here —
they have no source objects in the project — and are reported OPEN above.)

```
PUBLIC ERDOS-287 STATEMENT:
MATCH  (Erdos287.Erdos287Counterexample / Erdos287Statement, ordered form proved)

REGRESSION:
PASS  (no existing theorem edited, renamed, weakened or deleted)

BUILD:
PASS  (lake build, 8086 jobs)

SORRY:
NONE (also: ADMIT none, ADMIT-like placeholders none)

USER AXIOMS:
NONE (all new theorems: propext, Classical.choice, Quot.sound)

FINITE RANGE:
3 ≤ M ≤ 4 000 000 000  (34-certificate chain, kernel-checked, no native_decide)

FRESH R9:
NOT BANKED — Ford source definitions absent from the repository

H=70:
NOT BANKED — only the binomial identities ∑_{j≤4}(-1)^j C(9,j)=70, ∑_{j≥5}(-1)^j C(9,j)=-70;
first failure: G(m;n) from equation (7.17) has no source definition here

FRESH c9:
NOT BANKED

FULL-NINE PHYSICAL BRIDGE:
NOT BANKED (schematic only, not claimed)

SW2 DETERMINANT SHELL:
NOT BANKED

GATE1B SUPPLEMENT:
NOT CONSTRUCTED (would require literal source outputs)

GATE1B:
OPEN

287 GENERATED PACKET CENSUS:
OPEN (not attempted rather than guessed)

GATE1A REQUIRED:
UNKNOWN

GENERATED-(7.23):
OPEN

C_FM:
OPEN

GATE0 TYPE I:
OPEN (external weighted-BV input, uninhabited)

(b.2):
OPEN (uniform multivariate PNT input, uninhabited)

N2:
OPEN

FIXED EPSILON:
NOT SELECTED (only 1/6 > 1663/10000 proved)

FORD LOWER BOUND:
EXTERNAL / OPEN

PRIME MASS:
OPEN

SOPHIE WITNESS:
REPAIRED AND PROVED as a finite compiler — sign-sensitive, q ≥ 5, endpoints
M/3 < q ≤ (M-1)/2 (plus) and M/3 < q ≤ ⌊M/2⌋ (minus); master theorem proved against the
exact public predicate; strictly stronger interface WindowPairSupply also proved

LARGE-M EXCLUSION:
CONDITIONAL ONLY (Erdos287ClosureInputs → Erdos287Statement)

EFFECTIVE THRESHOLD:
EXPLICIT IN THE INTERFACE (M0 ≤ 4·10⁹ required by the structure); no ineffective threshold
is used anywhere

FINITE REMAINDER:
COVERED for all M ≤ 4·10⁹ (and vacuous below 4, since max A ≥ 4)

ERDOS287:
NOT PROVED

FIRST EXACT REMAINING BLOCKER:
Erdos287.Erdos287ClosureInputs.supply  :  ∀ M ≥ M₀, Erdos287.WindowPairSupply M

NEXT BEST MATHEMATICAL ATTACK:
Prove WindowPairSupply M for all large M in the special shape "x = c·p, x+1 = c'·p′ with
p, p′ > M/10 and c, c′ ≤ 9" — i.e. an almost-prime-pair statement at consecutive integers,
which is the weakest form of the supply that the finite engine accepts.
```
