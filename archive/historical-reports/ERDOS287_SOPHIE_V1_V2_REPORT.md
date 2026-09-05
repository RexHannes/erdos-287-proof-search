# Erdős #287 — Sophie blocker packages: V1 (C-threshold) and V2 (finite / top-layer)

Machine-checked report.  **Erdős #287 is not claimed solved**, and nothing here asserts
anything about the supply of Sophie-Germain-type primes for large `M`.  Every claim below is
either a theorem in the project (named, kernel-checked) or is explicitly flagged as
unverified exploration.

---

## 0. Files (append-only; no earlier statement edited, weakened or deleted)

New:

| file | contents |
|---|---|
| `RequestProject/Erdos287/SophieOptimal.lean` | V1: automatic placement, cofactor-two window, plus/minus Sophie blockers |
| `RequestProject/Erdos287/SophieBandCompiler.lean` | V1: fixed rational band `(7/10, 24/25)·⌊M/2⌋`, conditional compiler |
| `RequestProject/Erdos287/V2SophieFinite.lean` | V2: finite placement `N ≤ ⌊M/2⌋`, top-layer hole lemmas, V2 blockers |
| `RequestProject/Erdos287/V2SophieBand.lean` | V2: fixed band `3X/4 < q < 4X/5`, V2 finite compiler |
| `RequestProject/Erdos287/V2BandSupplyChecks.lean` | V2: maximal-band compiler, `decide`-checked sweep `39 ≤ M ≤ 250`, supply-gap witnesses |
| `RequestProject/Status/Erdos287V2Status.lean` | status ledger + `#print axioms` for every new theorem |

Modified: `RequestProject/Main.lean` (import lines only).

---

## A. Source map — exact banked pins

| role | exact name | file | literal hypothesis shape |
|---|---|---|---|
| `Gap2CE` structure | `Erdos287.Gap2CE` | `Erdos287/Counterexample.lean` | fields `A : Finset ℕ`, `hne : A.Nonempty`, `hpos : ∀ a ∈ A, 0 < a`, `hsum : ∑ a ∈ A, (1:ℚ)/a = 1`, `hgap : ∀ a ∈ A, a ≠ A.max' hne → (a+1 ∈ A ∨ a+2 ∈ A)` |
| `N`, `M` | `Erdos287.Gap2CE.N`, `.M` | same | `A.min' hne`, `A.max' hne`; `N_mem`, `M_mem`, `mem_Icc` |
| global size inequality | `Erdos287.Gap2CE.exp_lower` | same | `Real.exp 1 * ((N:ℝ) - 1) < (M:ℝ)` |
| upper size bound | `Erdos287.Gap2CE.exp_upper` | same | `(M:ℝ) ≤ Real.exp 1 ^ 2 * ((N:ℝ) + 1)` |
| **isolated holes** | `Erdos287.Gap2CE.holes_isolated` | same | `∀ n, N ≤ n → n+1 ≤ M → (n ∈ A ∨ n+1 ∈ A)`; hole = `∉ A`; window closed `[N,M]` |
| **top-layer congruence** | `Erdos287.topLayer_congruence` | `Erdos287/TopLayer.lean` | `(A : Finset ℕ) (p : ℕ) (hp : p.Prime) (hpos : ∀ a ∈ A, 0 < a) (hsum : ∑ a ∈ A, (1:ℚ)/a = 1) (he : 1 ≤ topExp A p)` ⟹ `∑ a ∈ topLayer A p, ((ordCompl[p] a : ℕ) : ZMod p)⁻¹ = 0` |
| singleton obstruction | `Erdos287.topLayer_card_ne_one` | same | same hypotheses ⟹ `(topLayer A p).card ≠ 1` |
| pair obstruction | `Erdos287.topLayer_two_obstruction` | same | `+ (ha : topLayer A p = {a₁,a₂}) (hne : a₁ ≠ a₂)` ⟹ `p ∣ ordCompl[p] a₁ + ordCompl[p] a₂` |
| triple obstruction | `Erdos287.topLayer_three_obstruction` | same | analogous ⟹ `p ∣ m₁m₂+m₁m₃+m₂m₃` |
| prime-power window | `Erdos287.primePower_window_exclusion` | `Erdos287/Window.lean` | `(hp : p.Prime) (hpos) (hAM : ∀ a ∈ A, a ≤ M) (hsum) (he : 1 ≤ e) (hqM : p^e ≤ M) (hpC : C (M / p^e) < (p:ℤ))` ⟹ `∀ a ∈ A, ¬ p^e ∣ a` |
| threshold `C` | `Erdos287.C` | `Erdos287/Defs.lean` | `C j` = max reduced numerator of `∑_{s∈S} 1/s` over nonempty `S ⊆ {1,…,j}` (list fold, kernel-reducing) |
| `C(2)` | `Erdos287.C_two` | `Erdos287/Cnum.lean` | `C 2 = 3`, proved by kernel `decide` |
| exclusion predicate | `Erdos287.ExcludedPP`, `.not_dvd_mem`, `excludedPP_of_le`, `excludedPP_self_of_large` | `Erdos287/Blocker.lean` | `∃ p e, p.Prime ∧ 1 ≤ e ∧ q = p^e ∧ C (M/q) < (p:ℤ)` |
| blocker pair | `Erdos287.Gap2CE.blockerPair_contradiction`, `.excludedPP_blockerPair` | `Erdos287/PrimeFree.lean`, `Blocker.lean` | two adjacent holes in `[N,M]` ⟹ `False` |
| pre-existing Sophie blocker | `Erdos287.Gap2CE.safePrime_blocker` | `Erdos287/Blocker.lean` | `p = 2r+1`, both prime, `N+1 ≤ p ≤ M`, `M < 2p`, `r > 25 = C 4` ⟹ `False` |

`TL_PIN`: `Erdos287.topLayer_congruence` (with corollaries `topLayer_card_ne_one`,
`topLayer_two_obstruction`) — found, exact, general (not specialised to small fibres),
nonemptiness implicit in `1 ≤ topExp A p`, no coprimality hypothesis needed since cofactors
are `ordCompl[p] a`.

`ISOLATED_HOLES_PIN`: `Erdos287.Gap2CE.holes_isolated` — found, exact, closed window `[N,M]`.

No `SOURCE_PIN_FAIL`.

---

## B. Automatic placement (V1) — mismatch check and result

Hostile check requested: is the `e` of the archive's size inequality Euler's number or a
named constant?  **It is literally `Real.exp 1`** (`Erdos287.Gap2CE.exp_lower`), so
`2 < Real.exp 1` is legitimately available and no mismatch report is required.

Proved: `Erdos287.Gap2CE.N_le_of_M_lt_two_mul : ce.M < 2 * x → ce.N ≤ x`
(`SophieOptimal.lean`).  This is the weakest exact statement the bank justifies, and it
removes the `N ≤ p` / `N + 1 ≤ p` hypotheses carried by the banked good-prime blockers.

---

## C. The cofactor-two threshold (V1) — `C2_PIN_PASS`

* Literal definition of `C`: greatest reduced numerator of `∑_{s∈S} 1/s` over nonempty
  `S ⊆ {1,…,j}` (`Erdos287.C`), with faithfulness proved (`num_le_C`, `C_attained`,
  `C_spec : IsGreatest …`, `C_mono`).
* `C 2 = 3` is **theorem-proved by kernel `decide`** (`Erdos287.C_two`), not definitional and
  not merely bounded.
* The window theorem requires: `p` prime and `q = p^e` with `e ≥ 1` (a prime *power*, not
  necessarily a prime); window `⌊M/q⌋` (floor); the **strict** inequality `C ⌊M/q⌋ < p`
  (threshold on the *base* `p`, not on `q`); `A ⊆ [1,M]`, all elements positive,
  reciprocal sum `1`.  The hypothesis `p^e ≤ M` is present but unused (documented in the
  archive).  There is no coprimality-to-another-parameter, parity or endpoint hypothesis.
* It excludes **every multiple** of `q`, hence both `q` and `2q`.

Verdict: **`C2_PIN_PASS`**.

Derived and proved: `Erdos287.excludedPP_of_window_two` — `q` prime, `q > 3`, `M < 3q` ⟹
`ExcludedPP M q`.

---

## D/E. The V1 plus/minus Sophie blockers — proved

* `Erdos287.Gap2CE.plus_sophie_blocker` : `q` prime, `q > 3`, `p = 2q+1` prime, `p ≤ M`,
  `M < 3q` ⟹ `False`.
* `Erdos287.Gap2CE.minus_sophie_blocker` : `q` prime, `q > 3`, `p = 2q-1` prime (as
  `p + 1 = 2q`), `p + 1 ≤ M`, `M < 3q` ⟹ `False`.

Every inequality of the intended chain was proved in the archive's own `ℕ` ordering (no
coercion): `M < 3q ⟹ ⌊M/q⌋ ≤ 2`; `M < 3q < 2p`; `M < 3q < 2(p-1)` (plus case) resp.
`M < 2p` (minus case) for placement; and `p-1, p` (resp. `p, p+1`) verified to lie in the
closed window `[N,M]` on which `holes_isolated` applies.  These are strictly stronger than
the banked `safePrime_blocker` (`r > 25 = C 4` plus a placement hypothesis), because the band
hypothesis `M < 3q` sharpens the window from `2d = 4` to `2`.

---

## F/G. Band geometry and optimality (V1)

* `Erdos287.band_hypotheses` : for `M ≥ 25`, `7·⌊M/2⌋ < 10q` and `25q < 24·⌊M/2⌋` imply
  `q > 3`, `M < 3q`, `2q+1 ≤ M`.  All floor/parity endpoints discharged by `omega`.
* `Erdos287.band_hypotheses_three_quarters` : the prose pair `(3/4, 4/5)` also works, from
  `M ≥ 20`, on a much narrower band.
* `Erdos287.band_exact` : the two blocker requirements are *equivalent* to
  `⌊M/3⌋ < q ∧ 2q < M`, i.e. the maximal band is `M/3 < q ≤ (M-1)/2`.
* `Erdos287.window_ge_two_of_two_mul_le` : any architecture using the denominator `2q ≤ M`
  necessarily has `⌊M/q⌋ ≥ 2`.  This is optimality **within** the stated `2q` architecture
  only; no global optimality is claimed.
* `Erdos287.no_Gap2CE_of_sophieBandSupply` : conditional compiler taking the band-supply
  statement as an explicit hypothesis (a `def`-ined `Prop`, **not** an axiom).

---

## H. The V2 route (finite / top-layer only)

Superseded inputs deliberately avoided: `exp_lower` (`e(N-1) < M`) and the `C` threshold
(including `C 2 = 3`).  Both remain in the bank untouched as historical, redundant lemmas;
the V2 theorems do not depend on them (verified by the dependency structure of the files —
`V2SophieFinite.lean` imports only `TopLayer.lean` and `Counterexample.lean`, and uses only
`topLayer_congruence`'s corollaries and `holes_isolated`).

New theorems:

| name | statement |
|---|---|
| `Erdos287.Gap2CE.halfRange_min_le` | `2 ≤ M → N ≤ ⌊M/2⌋` |
| `Erdos287.topExp_le_one_of_lt_sq` | `M < q²`, `A ⊆ [1,M]` ⟹ `topExp A q ≤ 1` |
| `Erdos287.topHalf_prime_hole` | `p` prime, `M < 2p` ⟹ `p ∉ A` (singleton top layer) |
| `Erdos287.q_and_two_mul_q_holes` | `q > 3` prime, `M < q²`, `M < 3q` ⟹ `q ∉ A ∧ 2q ∉ A` |
| `Erdos287.Gap2CE.holes_q_two_q`, `.hole_topHalf_prime` | the `Gap2CE` specialisations |
| `Erdos287.Gap2CE.v2_plus_sophie_blocker` | `q > 3`, `p = 2q+1` prime, `p ≤ M`, `M < 3q`, `M < q²` ⟹ `False` |
| `Erdos287.Gap2CE.v2_minus_sophie_blocker` | `q > 3`, `p = 2q-1` prime, `p+1 ≤ M`, `M < 3q`, `M < q²` ⟹ `False` |
| `Erdos287.v2Band_hypotheses` | `M ≥ 9` and `3⌊M/2⌋ < 4q`, `5q < 4⌊M/2⌋` ⟹ `q > 3`, `M < 3q`, `2q+1 ≤ M`, `M < q²` |
| `Erdos287.Gap2CE.v2_band_plus_blocker`, `.v2_band_minus_blocker`, `.v2_finite_compiler` | the banded V2 compilers |
| `Erdos287.Gap2CE.v2_exact_compiler` | maximal band: `q > 3` prime, `M < 3q`, `2q+1 ≤ M`, `2q±1` prime ⟹ `False` |
| `Erdos287.no_Gap2CE_M_eq_104` | concrete instance (`q = 41`, `2q+1 = 83`) |
| `Erdos287.sophieWitness_sweep`, `Erdos287.no_Gap2CE_of_M_in_39_250` | `decide`-checked sweep: no gap-`≤2` counterexample has `39 ≤ M ≤ 250` |
| `Erdos287.not_sophieWitness_35`, `Erdos287.v2Band_supply_gap_152` | negative finite witnesses |

**Repair recorded (hostile finding).**  The *fixed* bands are not always populated: the
`(7/10, 24/25)` band and the `(3/4, 4/5)` band both admit `M` with no Sophie prime inside
(kernel-checked witness: `Erdos287.v2Band_supply_gap_152`, at `M = 152`).  The finite sweep
therefore uses the **maximal** band `M/3 < q ≤ (M-1)/2`, for which the supply gap at small
`M` ends at `M = 38` (kernel-checked negative witness at `M = 35`).  A scan suggesting that
the maximal band is populated for all `39 ≤ M ≤ 3000` was exploratory only; the
*kernel-verified* range is `39 ≤ M ≤ 250`.

**Repair recorded (statement fix).**  `halfRange_min_le` is **false without `2 ≤ M`**:
`A = {1}` satisfies every field of `Gap2CE` (its single element is the maximum, so `hgap`
is vacuous) and there `N = 1 > 0 = ⌊M/2⌋`.  The hypothesis `2 ≤ M` is included and is
automatically available in every downstream use.

---

## I. Kernel audit

```
BUILD:            success — `lake build` completes (8080 jobs), all files compile
TL_PIN:           Erdos287.topLayer_congruence (RequestProject/Erdos287/TopLayer.lean)
ISOLATED_HOLES:   Erdos287.Gap2CE.holes_isolated (RequestProject/Erdos287/Counterexample.lean)
AXIOMS:           every new theorem: [propext, Classical.choice, Quot.sound] only
                  (two report even less: `window_ge_two_of_two_mul_le` = [propext],
                   `band_hypotheses` = [propext, Quot.sound]);
                  printed in RequestProject/Status/Erdos287V2Status.lean
SORRY/ADMIT:      none in the new files; none anywhere in RequestProject/**.lean
UNSAFE/NATIVE:    none; all finite certifications use kernel `decide`
NEW THEOREMS:     as listed in sections B–H above
REUSED BANKED:    topLayer_congruence, topLayer_card_ne_one, topLayer_two_obstruction,
                  holes_isolated, blockerPair_contradiction, excludedPP_blockerPair,
                  excludedPP_self_of_large, excludedPP_of_le, C_two, C_mono, exp_lower (V1 only)
FAILED CANDIDATES: none of the target statements failed; see the two repairs above
OBSOLETE DEPS REMOVED FROM V2: exp_lower / N_le_of_M_lt_two_mul (analytic placement);
                  C, C_two, primePower_window_exclusion, ExcludedPP (numerator threshold)
```

Verdicts:

* V1 package: **`ERDOS287_SOPHIE_FINITE_COMPILER_PASS_WITH_REPAIRS`**
  (repair: the fixed band's supply gaps; the compiler itself is unconditional and proved).
* V2 package: **`ERDOS287_V2_FINITE_COMPILER_PASS_WITH_REPAIRS`**
  (repair: `halfRange_min_le` needs `2 ≤ M`; fixed band replaced by the maximal band).

### Exact surviving analytic interface

Finite landing theorem (Lean): `Erdos287.Gap2CE.v2_exact_compiler`, and its packaged form
`Erdos287.no_Gap2CE_of_sophieWitness`.

Mathematically: for a hypothetical gap-`≤2` counterexample with maximum denominator `M`,

  ∃ prime q with  M/3 < q ≤ (M−1)/2  and  (2q−1 prime or 2q+1 prime)   ⟹   contradiction.

Everything to the left of the arrow is finite and decidable for each fixed `M`; it is
verified for `39 ≤ M ≤ 250`.  Its validity for all large `M` is **not** claimed, proved or
assumed anywhere in this project.
