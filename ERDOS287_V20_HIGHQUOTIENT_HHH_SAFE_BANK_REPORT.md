# ERDŐS #287 — V20 SAFE BANK

## HIGH-CONDUCTOR CHARACTER GRAM / CONDUCTOR ROUTER / HHH FRONTIER

Scope: Erdős #287 only. Append-only continuation of the existing repository.

**Nothing in this report claims Erdős #287, Balanced7, or any analytic theorem.**
No `axiom`, `sorry`, `admit`, `opaque`, `unsafe`, `native_decide` or `@[implemented_by]`
is introduced. Every external analytic input is an *uninhabited* structure carrying only
its intended-bound metadata.

---

## A. REGRESSION

Pre-edit state was checked with `git status`, `git branch --show-current`,
`git log --oneline`, and a full `lake build`.

* Branch: `main`; working tree clean before edits.
* Baseline build: **success, 8140 jobs, 0 errors.**
* Post-V20 build: **success, 8148 jobs, 0 errors, 0 warnings.**

The V16–V19 tree was surveyed before writing any new declaration. Reused, not duplicated:

| Reused V16–V19 asset | Module |
| --- | --- |
| factorial/Euler polarization endpoint | `RequestProject/Erdos287/FactorialEndpoint3221Adapter.lean` |
| labelled `1+2+2+2` five-box source | `RequestProject/Erdos287/PrePoissonDensity3221.lean` |
| pre-Poisson density | `RequestProject/Erdos287/PrePoissonDensity3221.lean` |
| high-conductor variance, `cHat`, `cHigh`, `highSet`, `samplePoint` | `RequestProject/Erdos287/HighConductorVariance3221.lean` |
| V19 character Gram | `RequestProject/Erdos287/CharacterGram3221.lean` |
| Balanced7 compiler / endpoint certificate | `RequestProject/Erdos287/BalancedSeven3221Compiler.lean`, `BalancedSevenV19Compiler.lean` |
| comparison interface `MuLogComparisonLowCondMatch` | `RequestProject/Erdos287/BalancedSevenV19Compiler.lean` |
| status graph | `RequestProject/Status/Erdos287V19Status.lean` |

V20 files are additive; no existing declaration was edited, renamed or removed.

**Files added**

```
RequestProject/Erdos287/HighConductorCharacterGram3221.lean
RequestProject/Erdos287/FiveBoxCharacterFactorization3221.lean
RequestProject/Erdos287/ConductorRouter3221.lean
RequestProject/Erdos287/HighQuotientShiftedGram3221.lean
RequestProject/Erdos287/HighConductorSixthMoment3221.lean
RequestProject/Erdos287/BalancedSevenV20Compiler.lean
RequestProject/Status/Erdos287V20Status.lean
RequestProject/Status/AxiomAuditErdos287V20.lean
ERDOS287_V20_HIGHQUOTIENT_HHH_SAFE_BANK_REPORT.md
```

**File modified:** `RequestProject/Main.lean` (import lines appended only).

---

## B. FRONTIER RESET

The controlling first exact analytic residual is now

```
3221-HIGHQUOTIENT-FIVEBOX-SHIFTED-GRAM45
```

realised in Lean as the *exact, assumption-free* object
`Erdos287.V20HHH.hhhGram` with open socket
`Erdos287.V20HHH.HighQuotientFiveBoxShiftedGram3221Input`.

`3221-HIGHCOND-RESIDUE-SIXTH-MOMENT45` is banked as a **stronger sufficient**
alternative only. It is deliberately *not* promoted to controlling frontier: the machine
ledger theorem `Erdos287.V20Status.sixthMoment_not_controlling` pins this.

---

## C. INVERSE-SAMPLED CHARACTER EXPANSION (Phase A)

Module `RequestProject/Erdos287/HighConductorCharacterGram3221.lean`,
namespace `Erdos287.V20Gram`.

The high-conductor character set is **data, not a `Prop` field**: `highSet q Dcut` is the
literal finset `{χ mod q : Dcut < conductor χ}`, characterised by

* `mem_highSet_iff_lt_conductor`
* `sum_highSet_eq_sum_ite`

The affine sample `a_m = −s·(2m)⁻¹ mod q` is the literal definition `affineSample q s m`,
tied to the V19 `samplePoint` by `affineSample_eq_samplePoint`, with

* `affineSample_mul_eq_one`, `affineSample_isUnit`, `affineSample_inv`.

Exact character identity, with the repository's own conjugation convention and **all**
hypotheses explicit (`s² = 1`, `2m` a unit mod `q`):

```lean
theorem inverseSample_character_identity (hs : s ^ 2 = 1)
    (hu : IsUnit ((2 * m : ℕ) : ZMod q)) (chi : DirichletCharacter ℂ q) :
    (starRingEnd ℂ) (chi (affineSample q s m))
      = chi ((-2 * s : ℤ) : ZMod q) * chi ((m : ℕ) : ZMod q)
```

with the unconjugated companion `affineSample_character_factor`, and the supporting
`conj_char_apply`, `conj_char_eq_inv_char`.

High-conductor expansion compiler (§4), with literal character coefficients
`highCoeff q Dcut Wbox c χ = 1_{Dcut < cond χ} · ĉ_q(χ)`:

```lean
theorem cHigh_inverseSampled_expansion :
    cHigh q Dcut Wbox c (affineSample q s m)
      = (q.totient : ℂ)⁻¹ * ∑ chi ∈ highSet q Dcut,
          chi ((-2*s : ℤ) : ZMod q) * chi ((m : ℕ) : ZMod q) * cHat q Wbox c chi
```

Every ingredient is a literal Dirichlet-character construction from the repository's own
infrastructure, so:

```
3221-HIGHCOND-CHARACTER-EXPANSION45 : LEAN_PROVED_FINITE.
```

No analytic estimate appears in this phase.

---

## D. FIVE-BOX FACTORISATION (Phase B)

Module `RequestProject/Erdos287/FiveBoxCharacterFactorization3221.lean`,
namespace `Erdos287.V20FiveBox`.

The labelled `1+2+2+2` five-box source of V18/V19 is reused verbatim; the internal
five-box label `ℓ` is kept notationally distinct from any external modulus.

Proved by finite convolution and character multiplicativity only:

* `sum_mul_sum5` — the five-fold product/sum interchange;
* `blockSum`, `pairBlockSum`, `pairBlockSum_eq_mul` — a labelled two-prime block's
  transform is literally the product of its two single-prime transforms;
* `fiveBox_characterTransform_eq_prod_five` —
  `ĉ_λ(χ) = ∏_{i=1}^{5} S_{i,λ}(χ)`;
* `fiveBox_characterTransform_factor` —
  `ĉ_λ(χ) = Eta_λ(χ) · Beta_λ(χ) · Gamma_λ(χ)`, obtained as a regrouping of the
  five-fold product;
* `highCoeff_fiveBox`, `highCoeff_of_not_high` — the high-conductor cut applied to the
  five-box transform.

No character-sum bound is used or stated.

```
3221-FIVEBOX-CHARACTER-FACTORIZATION45 : LEAN_PROVED_FINITE.
```

---

## E. EXACT m-GRAM (Phase C)

Same module, `Erdos287.V20Gram`.

* `unitBox q Mset` — the unit sector `{m ∈ Mbox : (m,q) = 1}`, with
  `mem_unitBox_isUnit`;
* `shortMGram q Mset Phi ξ = ∑_{m ∈ unitBox} Φ(m) · ξ(m)`;
* `autocorr q F ξ = ∑_χ F(χ) · conj(F(χ·ξ⁻¹))`, with the reindexing lemma
  `autocorr_reindex`;
* `charSrc`, `charSrc_eq_cHigh_inverseSampled` — the character-side source equals the
  literal high-conductor projection at the inverse sample.

**The central V20 finite theorem** (regrouping by `ξ = χ·ψ⁻¹`), stated for the literal
inverse-sampled variance:

```lean
theorem inverseSampledVariance_eq_characterGram :
    ∑ q ∈ Qbox, wt q * ∑ m ∈ unitBox q Mset,
        Phi m * (cHigh q Dcut Wbox c (affineSample q s m) *
                 conj (cHigh q Dcut Wbox c (affineSample q s m)))
      = ∑ q ∈ Qbox, wt q * ((q.totient : ℂ)⁻¹ ^ 2 *
          ∑ xi, xi ((-2*s : ℤ) : ZMod q) *
            shortMGram q Mset Phi xi * autocorr q (highCoeff q Dcut Wbox c) xi)
```

proved from the per-modulus identity `charSource_variance_eq_gram`. **No Cauchy, no
Burgess, no large sieve** occurs in the proof.

Same-primitive lift firewall (§10), stated only at a *fixed* modulus:

* `fixedModulus_samePrimitive_induced_unique` — a primitive character of conductor `r ∣ q`
  determines a unique induced character mod `q`;
* `fixedModulus_ne_of_lift_ne` — contrapositive form.

```
m-SAMPLED CHARACTER GRAM : LEAN_PROVED_FINITE.
```

---

## F. DIAGONAL CHILD (Phase D)

* `characterGram_diag_split` — the exact finite split `V_hi = V_diag + V_offdiag` by
  separating `ξ = 1`;
* `autocorr_principal_eq_energy` — `A_q(1) = ∑_χ |F(χ)|²`;
* `autocorr_principal_highCoeff` — the same restricted to `χ` of high conductor,
  i.e. `A_q(1) = ∑_{χ high} |ĉ_q(χ)|²`.

No analytic bound is attached to these.

External analytic input (`RequestProject/Erdos287/ConductorRouter3221.lean`):

```lean
structure PrimitiveConductorLargeSieve3221Input
    (Qmod R W5 logC cL2 energy Dcut B0 : ℝ) : Prop
```

**uninhabited**; it records the intended external estimate
`E(R) ≤ log^C · (Q/R) · (R² + W5) · ‖c‖₂²` as metadata and carries the cutoff data
`Dcut`, `B0` explicitly. The classical multiplicative large sieve is *not* axiomatised
and *not* proved here. `largeSieve_not_automatic` states that the input is not derivable
from the ambient data alone (there is no closed term producing it).

Conditional compiler: `highCondDiagonal_of_largeSieve`.

Exponent ledger (§14), Lean-proved rational/real arithmetic:

* `diagonal_fixed_power_room : ℚ := 4 / 35`;
* `diagonal_power_room_rational` — `1 − 39/35 = −4/35`;
* `diagonal_power_room_rpow` — from `M·W5 = X` and `M·W5²/Q = X^(39/35)`,
  `X / X^(39/35) = X^(−4/35)`.

```
3221-HIGHCOND-DIAGONAL45 :
    EXTERNAL-ANALYTIC CLOSED / CONDITIONAL COMPILER.
```

Not relabelled `LEAN_PROVED` analytic.

---

## G. LOW-QUOTIENT CHILD (Phase E)

* `lowConductor_card_le` — for a modulus `q`,
  `#{ξ mod q : cond ξ ≤ L} ≤ ∑_{r ∣ q, r ≤ L} φ(r)`,
  proved from the change-of-level/primitive-character factorisation together with the
  cardinality of the character group. This is a *finite* divisor/conductor count; no
  logarithmic asymptotic is claimed.
* `lowQuotient_child_le` — the abstract finite-algebra compiler: from
  `|A_q(ξ)| ≤ E_q`, `|G_{q,M}(ξ)| ≤ M` and a low-quotient multiplicity bound, the
  low-quotient Gram child is bounded by `lowMult · M · E_q`.
* `lowQuotient_child_of_diagonal_budget` — the same wired to the diagonal energy budget.

```
3221-LOWQUOTIENT-CONDUCTOR-COLLAPSE45 :
    CONDITIONAL / EXTERNAL CLOSED.
```

---

## H. SEPARATE-L2 DEATH CERTIFICATE (Phase F)

Exact finite harmonic analysis, all Lean-proved:

* `gram_parseval` — `∑_ξ |G_{q,M}(ξ)|² = φ(q) · ∑_{m ∈ unitBox} |Φ(m)|²`, by character
  orthogonality;
* `energy_shift_invariant`, `autocorr_sup_le` — pointwise control of the autocorrelation;
* `autocorr_l2_sq_le` — the Young-type bound `‖A_q‖₂ ≤ √(φ(q)) · E_q` in its exact
  normalised square form;
* `separateL2_compiler` — the source-blind separate-L² route obtained by combining the
  previous two exact inequalities;
* `separateGramL2_capacity_deficit` — `51/35 − 39/35 = 12/35 > 0`.

The deficit is a *capacity* statement about the route, not a bound on the Gram.

```
3221-SEPARATE-GRAM-L2-45 :
    CAPACITY NONCLOSING BY 12/35.
```

Permanent anti-loop firewall: the separate-L² route cannot close, by proved arithmetic.

---

## I. BURGESS CAPACITY FIREWALL (Phase G)

Burgess is **not** formalised and **not** axiomatised. The module provides only the
uninhabited metadata carrier

```lean
structure PointwiseBurgess3221Input (Mlen Rcond burgessConst delta value : ℝ) : Prop
```

with `pointwiseBurgess_not_automatic`, plus the Lean-proved audit arithmetic

* `pointwiseBurgess_capacity_deficit` — `879/560 − 624/560 = 51/112 > 0`.

```
3221-POINTWISE-BURGESS45 :
    EXTERNAL CAPACITY NONCLOSING GLOBALLY.
```

---

## J. CONDUCTOR-PAIR ROUTER (Phase H)

* `ConductorCell` — explicit finite/dyadic cell data `R1 ~ cond χ`, `R2 ~ cond ψ`,
  `Rxi ~ cond(χψ̄)`, together with `W5`, `M` and a positive margin;
* `RouterCondition cell` — the router inequality
  `√((R1²+W5)(R2²+W5)) ≤ W5·√M·Rxi^(−3/16)·margin`, encoded as a nonnegative
  cleared-denominator inequality so no real powers are needed;
* `LargeSieveConductorFactor3221Input`, `BurgessConductorFactor3221Input` —
  uninhabited external factor inputs;
* `conductorCell_routed` — the conditional compiler
  `router condition + external inputs ⇒ conductor cell power closed`.
  Neither external input is inhabited anywhere.

Special router arithmetic, exact rationals plus an abstract positive `eps`
(`RoutedExponentPair e1 e2 eps := e1 + e2 ≤ 417/560 − eps`, with a decidability
instance):

* `router_case_A` — `R1, R2 ≤ X^(5/14)` ⇒ routed;
* `router_case_B` — one conductor `≤ X^(5/14)`, the other `≤ X^(31/80−eps)` ⇒ routed;
* `router_case_C` — both larger, but `R1·R2 ≤ X^(417/560−eps)` ⇒ routed;
* `router_threshold_identity` — `5/14 + 31/80 = 417/560`;
* `router_case_A_slack` — `2·(5/14) = 400/560 < 417/560`.

```
3221-BURGESS-CONDUCTOR-PAIR-ROUTER45 : CONDITIONAL EXTERNAL PASS.
MODERATE CONDUCTOR CELLS : ROUTED CONDITIONALLY ON EXTERNAL INPUTS.
```

---

## K. HHH SURVIVING REGION (Phase I)

Module `RequestProject/Erdos287/HighQuotientShiftedGram3221.lean`,
namespace `Erdos287.V20HHH`.

```lean
structure SurvivingHHHConductorCell (Dcut Lcut : ℕ) (xi chi : DirichletCharacter ℂ q) : Prop
```

with four **explicit inequality/data** fields — no free `Prop`:

1. `Dcut < cond χ`;
2. `Dcut < cond (χ · ξ⁻¹)`;
3. `Lcut < cond ξ`;
4. the conductor triple lies outside the routed region (`¬ RouterCondition` of the
   associated cell).

Supporting: `survivingChiSet`, `mem_survivingChiSet_iff`, `survivingCell_of_mem`,
`highQuotientSet`.

---

## L. HHH GRAM SOCKET (Phase I, §25–26)

```lean
noncomputable def hhhGram (D : HHHGramData) : ℂ
```

is the exact object

```
∑_q μ²(q)/φ(q)² ∑_{ξ high quotient} ξ(−2s) · G_{q,M}(ξ)
    · ∑_{χ high, χξ̄ high, outside routed cells} ∏_{i=1}^{5} S_i(χ) · conj(S_i(χξ̄))
```

built from `survivingFiveBoxAutocorr`. **All cutoffs and support data are explicit fields
of `HHHGramData`, and the definition contains no analytic assumption whatsoever.**
Non-vacuity of the definition is witnessed by the concrete `probeHHHData` together with
`probeHHHData_gram : hhhGram probeHHHData = 0`.

The current analytic input is the **uninhabited**

```lean
structure HighQuotientFiveBoxShiftedGram3221Input (D : HHHGramData) (bound : ℝ) : Prop
```

stating only the required bound on the exact object, with
`hhhGram_input_not_automatic`.

```
3221-HIGHQUOTIENT-FIVEBOX-SHIFTED-GRAM45 :
    OPEN_ANALYTIC — FIRST EXACT RESIDUAL.
```

---

## M. LOGVAR REASSEMBLY (§27)

`LogVarChannelDecomposition` keeps every error/budget channel explicit (diagonal,
low-quotient, routed moderate cells, HHH), and

```lean
theorem logVar_of_four_channels : … → (target logvar bound)
```

is the conditional compiler

```
diagonal input + low-quotient input + router inputs + HHH Gram input
    ⇒ 3221-INVERSE-SAMPLED-HIGHCOND-LOGVAR45.
```

There is no circular dependence on LOGVAR itself, and
`logVar_does_not_construct_hhh` records that the compiler cannot manufacture its own HHH
antecedent.

```
3221-INVERSE-SAMPLED-HIGHCOND-LOGVAR45 : REDUCED / CONDITIONAL COMPILER.
```

---

## N. SIXTH-MOMENT SUFFICIENT BRIDGE (Phase J)

Module `RequestProject/Erdos287/HighConductorSixthMoment3221.lean`,
namespace `Erdos287.V20Sixth`.

* `unitResidues`, `sixthMoment Qbox C = ∑_q ∑_{a unit} |C_q^{>D}(a)|⁶` — a pure finite
  definition — with `sixthMoment_nonneg`;
* `injOn_affineSample` — using only the bankable fact `M < q`, the map
  `m ↦ −s(2m)⁻¹ mod q` is injective on the physical `m`-box under the stated
  interval/unit hypotheses;
* `sampled_sixth_le`, `sixthMoment_holder_at` — the finite Hölder inequality
  `∑_m |C_q(a_m)|² ≤ (#m)^(2/3) · (∑_a |C_q(a)|⁶)^(1/3)`, banked in cube form to keep the
  statement free of real exponents;
* `sixthMoment_holder_over_q` — Hölder over `q`;
* `HighCondResidueSixthMoment3221Input` — **uninhabited**, intended bound
  `M6 ≤ Q²T³·polylog`, with `sixthMoment_input_not_automatic`;
* `sixthMoment_variance_exponent` — that input would give the variance with exponent
  `116/105`;
* `sixthMoment_power_margin` — `117/105 − 116/105 = 1/105 > 0`.

```
3221-HIGHCOND-RESIDUE-SIXTH-MOMENT45 : STRONGER SUFFICIENT / OPEN.
```

This route is **not** promoted to controlling frontier despite the `1/105` conditional
margin; `Erdos287.V20Status.sixthMoment_not_controlling` enforces this in the ledger.

---

## O. SAME-B0 COMPARISON FIREWALL (Phase K)

Module `RequestProject/Erdos287/BalancedSevenV20Compiler.lean`.

* `highConductorCutoff B0 X = (log X)^B0`, with `highConductorCutoff_mono`;
* `MuLogComparisonAtCutoff X Dcut B0 hard model err` — the comparison interface now
  *records the cutoff `B0` and the induced `Dcut` in its type*, with
  `comparisonAtCutoff_to_base` connecting it to the existing V19
  `MuLogComparisonLowCondMatch`;
* `comparison_cutoff_must_match` — the load-bearing anti-retuning firewall: a comparison
  supplied at `Dcut'` is usable only when `Dcut' = Dcut`, so `B0` cannot be re-tuned after
  the fact;
* `comparisonAtCutoff_not_automatic` — the comparison is not derivable.

```
AFFINE287-MULOG-COMPARISON-LOWCOND-MATCH45 : SOURCE_OPEN.
```

---

## P. BALANCED7 COMPILER (Phase L)

```lean
theorem balancedSeven_of_v20_package … : BalancedSevenPacketInput …
```

threads **the same** `Dcut` and `B0` through the large-sieve input, the routed children,
the exact high-conductor reassembly, the HHH Gram input and the physical comparison, and
concludes the existing endpoint certificate. `v20_package_cutoff_consistent` records the
cutoff agreement.

**No antecedent of this compiler is claimed or inhabited.** Balanced7 remains OPEN.

---

## Q. NON-VACUITY / ANTI-CIRCULARITY (§35)

Banked:

* `hhh_input_not_automatic_v20` — the HHH Gram input is not automatic;
* `sixthMoment_input_not_automatic_v20` — the sixth-moment input is not automatic;
* `comparison_not_automatic_v20` — comparison is not automatic;
* `logVar_cannot_construct_hhh` / `logVar_does_not_construct_hhh` — the LOGVAR compiler
  cannot construct the HHH analytic input;
* `balancedSeven_compiler_cannot_construct_comparison` — the Balanced7 compiler cannot
  construct the comparison;
* `largeSieve_not_automatic`, `pointwiseBurgess_not_automatic`;
* `probeHHHData_gram` — a concrete finite witness showing the HHH Gram *object* is a real
  computable quantity, so the socket is a statement about something non-vacuous.

The ledger theorem `Erdos287.V20Status.capacity_firewalls_are_not_proofs` records that the
`12/35` and `51/112` deficits are capacity certificates, not proofs of any bound.

---

## R. BUILD / TRUST (§36)

* `lake build`: **success — 8148 jobs, 0 errors, 0 warnings.**
* Placeholder scan over the eight new files for
  `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, `native_decide`, `@[implemented_by]`:
  **no occurrences in code.** The only textual matches are the words `sorry-free`,
  `axiom` and `native_decide` inside the audit/status *documentation prose*.
* `RequestProject/Status/AxiomAuditErdos287V20.lean` runs `#print axioms` on every
  principal new declaration. Every result is either
  `[propext, Classical.choice, Quot.sound]` or *no axioms at all*
  (the seven ledger theorems, which are kernel `decide` computations).
  No non-standard axiom appears.
* No source or analytic interface is inhabited — via `Classical.choice` or otherwise.
  `Classical.choice` occurs only through ordinary Mathlib `noncomputable` machinery
  (finite sums over character groups, `Real`/`Complex` arithmetic), never as a
  constructor for an external input.

---

## S. FINAL LEDGER

Machine-readable: `RequestProject/Status/Erdos287V20Status.lean`
(namespace `Erdos287.V20Status`; `Node`/`Label` inductives with `DecidableEq`, `Fintype`,
`Repr`; the `ledger` function; all invariants discharged by `decide +kernel`).

| Node | Label |
| --- | --- |
| FACTORIAL EULER | `LEAN_PROVED` |
| FIVE-BOX FACTORISATION | `LEAN_PROVED_FINITE` |
| HIGHCOND CHARACTER EXPANSION | `LEAN_PROVED_FINITE` |
| m-SAMPLED CHARACTER GRAM | `LEAN_PROVED_FINITE` |
| HIGHCOND DIAGONAL | `EXTERNAL ANALYTIC CLOSED / CONDITIONAL COMPILER` |
| LOW-QUOTIENT COLLAPSE | `EXTERNAL ANALYTIC CLOSED / CONDITIONAL COMPILER` |
| SEPARATE-GRAM L2 | `CAPACITY NONCLOSING BY 12/35` |
| POINTWISE BURGESS | `EXTERNAL CAPACITY NONCLOSING GLOBALLY` |
| BURGESS CONDUCTOR-PAIR ROUTER | `CONDITIONAL EXTERNAL PASS` |
| MODERATE CONDUCTOR CELLS | `ROUTED CONDITIONALLY ON EXTERNAL INPUTS` |
| HIGHQUOTIENT-FIVEBOX-SHIFTED-GRAM45 | `OPEN_ANALYTIC / FIRST EXACT RESIDUAL` |
| HIGHCOND RESIDUE SIXTH MOMENT | `STRONGER SUFFICIENT / OPEN` |
| INVERSE-SAMPLED HIGHCOND LOGVAR | `REDUCED / CONDITIONAL COMPILER` |
| COMPARISON | `SOURCE_OPEN` |
| BALANCED7 | `OPEN` |
| FCL | `OPEN` |
| GATE2 | `OPEN` |
| WINDOWPAIRSUPPLY | `OPEN` |
| ERDOS287 | `OPEN` |

---

## T. FIRST SOURCE OPEN

```
AFFINE287-MULOG-COMPARISON-LOWCOND-MATCH45 : SOURCE_OPEN,
```

now pinned to the *same* high-conductor cutoff `B0` as the analytic decomposition
(`MuLogComparisonAtCutoff`, `comparison_cutoff_must_match`).

---

## U. FIRST ANALYTIC OPEN

```
3221-HIGHQUOTIENT-FIVEBOX-SHIFTED-GRAM45,
```

socket `HighQuotientFiveBoxShiftedGram3221Input` on the exact object `hhhGram`.

---

## V. NEXT UNIQUE ACTION

Attack the surviving high-high-high shifted five-box character Gram **without** separating
the short-`m` Gram from the five-box autocorrelation — the separated route is proved
nonclosing by `separateGramL2_capacity_deficit` (`12/35`), and the global pointwise
Burgess route by `pointwiseBurgess_capacity_deficit` (`51/112`).

---

```
ERDOS287: OPEN.

BALANCED7: OPEN.

FIRST EXACT ANALYTIC RESIDUAL:
    3221-HIGHQUOTIENT-FIVEBOX-SHIFTED-GRAM45.

STRONGER SUFFICIENT ALTERNATIVE:
    3221-HIGHCOND-RESIDUE-SIXTH-MOMENT45 — OPEN.

COMPARISON:
    SOURCE_OPEN.

NEXT UNIQUE ACTION:
    attack the surviving high-high-high shifted five-box character Gram
    without separating the short-m Gram from the five-box autocorrelation.
```
