# TRUSTED_BANK_EXTENDED — audit report

**Headline: `TRUSTED_BANK_EXTENDED`.**

Erdős #287 is **OPEN**. Gate 1A is **OPEN**. Gate 1B is **OPEN**. Nothing in this
report claims otherwise, and no file in `RequestProject/TrustedBank/` depends on any
open analytic statement.

---

## 1. Repository archaeology (state *before* this run)

```
TOOLCHAIN_VERSION : leanprover/lean4:v4.28.0        (unchanged)
MATHLIB_REVISION  : v4.28.0 (vendored under .lake/packages/mathlib)  (unchanged)
BUILD BEFORE EDITS: `lake build` succeeded (8045 jobs)
```

The lakefile builds the glob `RequestProject.+`, so **every** file added below is built
by a plain `lake build` — nothing is hidden behind an unbuilt target.

```
EXISTING_PROVED
  RequestProject/Erdos287/{Defs,Cnum,TopLayer,Window,Counterexample,PrimeFree,
    Uniform,Blocker,Fiber,Universal,BadPrimes,Chain,SFTAudit,ChenP2Audit,
    CeilingCRT,RoughPrime,NonAdjacentHoles,KernelAPBlocker}.lean   (+ Main.lean)
  ~130 theorems/lemmas, all kernel-checked.  Load-bearing items reused here:
    Erdos287.topLayer_congruence, topLayer_card_ne_one, topLayer_two_obstruction,
    topLayer_three_obstruction, topLayer_symm_congruence,
    Erdos287.C_values (C(1..8) = 1,3,11,25,137,137,1019,2143 by `decide`),
    Erdos287.C_seven_witness (C(7)=1019 attained by {1,2,3,4,5,7}),
    Erdos287.primePower_window_exclusion,
    Erdos287.Gap2CE.{blockerPair_contradiction, primeFree,
                     goodPrime_blocker_sub, goodPrime_blocker_add}.

EXISTING_SORRIES  (3, all in RequestProject/Erdos287/Uniform.lean)
  Erdos287.C_le_lcm_mul_harmonic
  Erdos287.harmonic_le_nat
  Erdos287.C_le_U
  → ALL THREE ARE NOW PROVED IN THIS RUN.  The project is now sorry-free.

DUPLICATE_THEOREMS
  No duplicated theorem.  One duplicated *definition*:
    Erdos287.lcmUpto  (Universal.lean, line 24)
    Erdos287.lcmUpTo  (RoughPrime.lean, line 28)
  Both are literally `(Finset.Icc 1 j).lcm id`.  They differ only by the capital `T`,
  which is a genuine readability hazard.  They are NOT merged in this run (merging
  would silently rewrite existing statements); see section E.

STALE_OR_RETRACTED_THEOREMS
  None found.  No theorem in the pre-existing package asserts a closure of #287,
  Gate 1A or Gate 1B; every #287 statement is conditional on a `Gap2CE`
  counterexample structure or on explicit numerical hypotheses.
```

## 2. Trust policy compliance

* `rg -n "sorry|admit|native_decide|^axiom |unsafe " RequestProject/` returns **no Lean
  hits** anywhere in the project (only prose occurrences inside `.md` files).
* No `debug.skipKernelTC`, no `@[implemented_by]`, no `axiom` declarations.
* `native_decide` is used nowhere; the `C(1..8)` certification uses ordinary `decide`
  (kernel-replayable).
* No file under `TrustedBank/` imports anything under `Challenges/` (checked
  mechanically).
* `RequestProject/Audit/BankStatus.lean` runs `#print axioms` on every banked theorem;
  every report is a subset of `{propext, Classical.choice, Quot.sound}`
  (`Erdos287.C_values` depends on **no** axioms at all).

## 3. Theorem table

Legend: STATUS = PROVED / REPAIRED_AND_PROVED / FALSE / OPEN.
All PROVED rows are SORRY-FREE = yes and AXIOMS = `propext, Classical.choice, Quot.sound`
(or fewer) unless stated.

### Bank A — fixed-affine integer normal form (`TrustedBank/FixedAffine/Basic.lean`)

| THEOREM | STATUS | INFORMAL MEANING | USED DOWNSTREAM BY |
|---|---|---|---|
| `TrustedBank.FixedAffine.lin`, `det` | def | `lin a b n = a*n+b`, `det = a₁b₂−a₂b₁` | all of Bank A |
| `affine_cross_identity` | PROVED | `a₁·L₂(n) = a₂·L₁(n) + Δ` over any commutative ring | root transport |
| `affine_cross_identity_int` | PROVED | the same over `ℤ` | — |
| `root_transport` | PROVED | if `m = L₁(n)` then `a₁·L₂(n) = a₂·m + Δ` | `second_root_iff` |
| `first_root_iff` | PROVED | `L₁(n)=0 ↔ m=0` | `zmod_forbidden_pair` |
| `second_root_iff` | PROVED | in a field, `L₂(n)=0 ↔ m = −Δ/a₂` | `zmod_forbidden_pair` |
| `normUnit`, `normUnit_second_root`, `normUnit_image_roots`, `normUnit_ne_zero` | PROVED | multiplication by `−α = −a₂/Δ` sends the two forbidden roots to the canonical pair `{0,1}` | Challenges/AffineSourceGlue |
| `zmod_forbidden_pair` | PROVED | the good-prime statement over `ZMod p` | Challenges/AffineSourceGlue |

No analytic prime-distribution consequence is stated in Bank A.

### Bank B — unit / finite-sum transport (`FixedAffine/UnitTransport.lean`, `Interfaces/FiniteSumTransport.lean`)

| THEOREM | STATUS | INFORMAL MEANING | USED DOWNSTREAM BY |
|---|---|---|---|
| `unitMul_bijective` | PROVED | multiplication by a unit is a bijection | `sum_unitMul` |
| `sum_unitMul` | PROVED | finite sums are invariant under that reindexing | `kloostermanLike_unit_change` |
| `unitMul_eq_zero_iff` | PROVED | `u·x = 0 ↔ x = 0` | Bank C |
| `l2_energy_perm`, `sum_perm` | PROVED | ℓ² energy / finite sums invariant under a permutation | — |
| `kloostermanLike`, `kloostermanLike_unit_change` | PROVED | `S(A,B;q) = S(Aλ, Bλ⁻¹; q)` for a unit `λ`, as an exact reindexing identity | Challenges/Gate1B |
| `sum_equiv_transport`, `sum_le_transport`, `twisted_fibre_bound_transport` | PROVED | transport of finite sums / bounds along an equivalence and along a unit twist | Challenges/Gate1A |

Note: Mathlib (at this revision) has **no** `kloostermanSum` definition, so the
convention `S(A,B;q) = Σ_{x ∈ (ZMod q)ˣ} ψ(A x⁻¹ + B x)` is defined here against an
abstract additive character `ψ`; the banked theorem is the pure reindexing statement,
not an analytic bound.

### Bank C — abstract SB fixed-unit portability (`Interfaces/ZeroSetTransport.lean`)

| THEOREM | STATUS | INFORMAL MEANING |
|---|---|---|
| `twist`, `zeroSet` | def | `twist κ F i = κ·F i`; simultaneous zero set of `(F₁,F₂)` |
| `twist_eq_zero_iff` | PROVED | `κ·F i = 0 ↔ F i = 0` |
| `twist_simultaneous_zero_iff` | PROVED | simultaneous vanishing is preserved exactly |
| `twist_zeroSet_eq`, `twist_zeroSet_card_eq` | PROVED | equality of zero sets and of their cardinalities |
| `twist_zeroSet_weighted_sum_eq` | PROVED | the weighted version, weight unchanged |

**Explicitly NOT stated:** "SB-ν for twins implies SB-ν for all fixed affine sources".
That implication needs the source glue, which lives in
`Challenges/AffineSourceGlue.lean` and is **open**.

### Bank D — bounded-cofactor Bézout parametrisation (`Erdos287/BoundedCofactor.lean`)

| THEOREM | STATUS | INFORMAL MEANING |
|---|---|---|
| `Bez` | structure | `d,e > 0`, `e·v − d·u = 1` |
| `P`, `Q` | def | `P n = e·n + u`, `Q n = d·n + v` |
| `key_identity` | PROVED | `e·Q(n) − d·P(n) = 1` |
| `dP_add_one` | PROVED | `d·P(n) + 1 = e·Q(n)` |
| `isCoprime_d_e / _u_e / _v_d / _e_u / _d_v`, `gcd_d_e / gcd_u_e / gcd_v_d` | PROVED | `gcd(d,e)=gcd(u,e)=gcd(v,d)=1` (both `IsCoprime` and `Int.gcd` forms) |

### Bank E — local admissibility criterion (`Erdos287/BoundedCofactor.lean`)

`Admissible B : Prop := ∀ p prime, ∃ n : ℤ, ¬(p ∣ P n) ∧ ¬(p ∣ Q n)` — stated
explicitly, not hidden in prose.

| THEOREM | STATUS | INFORMAL MEANING |
|---|---|---|
| `exists_good_residue_of_three_le` | PROVED | for `p ≥ 3` a good residue always exists (covers `p∣e`, `p∣d`, and `p ∤ de` with the two roots distinct because the determinant is 1) |
| `odd_of_two_dvd_e`, `odd_of_two_dvd_d` | PROVED | the `p = 2` bookkeeping |
| `exists_good_residue_two` | PROVED | if `2 ∣ de`, exactly one forbidden residue mod 2 remains |
| `two_obstructs_of_odd` | PROVED | if `d,e` both odd, the two distinct roots cover `F₂` |
| **`admissible_iff`** | PROVED | **`Admissible ↔ 2 ∣ d·e`** |
| `admissible_iff'` | PROVED | the same with the (already automatic) `gcd(d,e)=1` conjunct, for interface clarity |
| `sophie` (d,e,u,v = 1,2,1,1), `oddPair` (1,3,2,1) | tested | `sophie` admissible; `oddPair` not admissible |

### Bank F — local singular factors (`FixedAffine/SingularFactors.lean`)

No infinite Euler product is formalized, by design.

| THEOREM | STATUS | INFORMAL MEANING |
|---|---|---|
| `rootSet`, `nu` | def | forbidden residues mod `ℓ` and their count |
| `rootSet_eq_union`, `bez_zmod`, `not_dvd_of_isCoprime` | PROVED | supporting identities |
| **`nu_eq_one`** | PROVED | `ν(ℓ) = 1` when `ℓ ∣ d·e` |
| **`nu_eq_two`** | PROVED | `ν(ℓ) = 2` when `ℓ ∤ d·e` |
| `localFactor`, `localFactor_ratio`, `localFactor_of_dvd` | PROVED | the finite rational correction `(ℓ−1)/(ℓ−2)` for odd `ℓ ∣ d·e` |

### Bank G — cofactor intensity optimality (`FixedAffine/CofactorIntensity.lean`)

`J n = (1/n) · ∏_{odd primes p ∣ n} (p−1)/(p−2)`, a finite rational proxy.

| THEOREM | STATUS | INFORMAL MEANING |
|---|---|---|
| `two_mul_prod_le` | PROVED | the key finite-product induction step |
| `J_two` | PROVED | `J 2 = 1/2` |
| `J_le_half`, `J_lt_half` | PROVED | `J n ≤ 1/2`, strict for `n ≠ 2` |
| **`J_le_J_two`**, **`J_eq_J_two_iff`** | PROVED | `J n ≤ J 2` with equality **iff** `n = 2` |
| **`de_eq_two`** | PROVED | for a `Bez` pair with `d·e = 2`: `{d,e} = {1,2}` |

This is the precise *finite* content behind "the 1\|2 cofactor is density-optimal".
It is **not** an analytic density statement.

### Bank H — symmetric ± projection (`FixedAffine/SymmetricPacket.lean`)

| THEOREM | STATUS | INFORMAL MEANING |
|---|---|---|
| `odd_char_pair_cancel` | PROVED | `χ(1) + χ(−1) = 0` when `χ(−1) = −1` |
| `odd_char_symm_pair`, `odd_char_symm_pair_weighted` | PROVED | the ± pair at `a` cancels, also with an unchanged weight |
| `dirichlet_odd_symm_pair(_weighted)` | PROVED | instantiation for `DirichletCharacter ℂ m` with `χ.Odd` |

Banked meaning: **the odd-character contribution of the exact symmetric ± pair cancels
algebraically.** No analytic saving is claimed.

### Erdős #287 bank — carry tower (`TrustedBank/Erdos287/CarryTower.lean`)

| THEOREM | STATUS | INFORMAL MEANING |
|---|---|---|
| `factorization_lcm_apply`, `factorization_finset_lcm` | PROVED | `v_p(lcm A) = max_{a∈A} v_p(a)` |
| `two_le_card_topLayer`, `exists_two_topLayer` | PROVED | the top `p`-adic layer has at least two elements (reciprocal-sum-1 sets) |
| `pow_topExp_dvd_of_mem_topLayer` | PROVED | `p^e ∣ a` for `a` in the top layer |
| `level`, `level_succ_subset`, `topLayer_subset_level`, `level_succ_topExp_eq_empty` | PROVED | the `p`-adic level filtration and its termination |
| **`lcm_sq_dvd_prod`** | PROVED | `lcm(A)² ∣ ∏_{a∈A} a` for a finite set of positive integers with `Σ 1/a = 1` |
| `pairs`, `mem_pairs` | def/PROVED | unordered pairs of `A` |
| **`lcm_dvd_pairwise_diff_prod`** | PROVED | `lcm(A) ∣ ∏_{{a,b}} (b − a)` under the same hypothesis |
| `lcm_sq_not_dvd_prod_general`, `lcm_not_dvd_diff_general` | PROVED (counterexamples) | with `A = {2,3}` both claims **fail** without the reciprocal-sum hypothesis |

### Erdős #287 bank — generalized fixed-cofactor blocker (`TrustedBank/Erdos287/TopLayerConsequences.lean`)

| THEOREM | STATUS | INFORMAL MEANING |
|---|---|---|
| `blocker_of_excluded_neighbour_sub/_add` | PROVED | if `p` and a prime power dividing `p∓1` are both window-excluded, a gap-`≤2` counterexample is impossible |
| `fixedCofactor_blocker_sub`, `fixedCofactor_blocker_add` | REPAIRED_AND_PROVED | all numerical hypotheses explicit (`q = r^e`, `r` prime, `e ≥ 1`, `j ≥ 1`, `p = j·q ± 1`, `N < p ≤ M`, `M < 2p`, `M < q²`), with threshold **`C(2j) < r`** |
| `fixedCofactor_blocker_sub_sharpWindow`, `fixedCofactor_blocker_add_sharpWindow` | REPAIRED_AND_PROVED | the prompt's threshold `C(2j−1) < r`, made correct by the **added** window hypothesis `⌊M/q⌋ ≤ 2j−1` |

### Uniform numerator bounds — the three former sorries (`RequestProject/Erdos287/Uniform.lean`)

| THEOREM | STATUS | INFORMAL MEANING |
|---|---|---|
| `Erdos287.C_le_lcm_mul_harmonic` | PROVED (was `sorry`) | `C j ≤ lcm(1,…,j) · H_j` |
| `Erdos287.harmonic_le_nat` | PROVED (was `sorry`) | `H_j ≤ j` |
| `Erdos287.C_le_U` | PROVED (was `sorry`) | `C j ≤ j · j!` |
| `Erdos287.primePower_window_exclusion_U`, `Gap2CE.forcedHole_not_mem`, `Gap2CE.forcedHole_pair_contradiction` | PROVED | were already proved but rested on the three sorries; now unconditional |

## 4. Challenges (open lines — never imported by `TrustedBank/`)

These files contain **no `sorry` and no `axiom`**: the open statements are encoded as
`Prop`-valued definitions and interface structures, so nothing is asserted.

* `Challenges/Gate1A_SBNu.lean` — `TwoViewSource`, `fibre`, `fibreCount`,
  `SubpolynomialFibre` (the SB-ν target: `N_ν = X^{o(1)}` for each fixed nonzero ν),
  `UnitTwisted`; **proved**: `fibreCount_twist`, `subpolynomialFibre_twist` (fixed-unit
  portability of the target). The authoritative Gate-1A source data (ω, τ, Σᵢ, Fᵢ, g,
  clean cells, physical ranges) is **not present in this repository**, so the challenge
  is stated against an abstract two-view interface; this is recorded in the file.
* `Challenges/Gate1B_SourceOpenedSWYang.lean` — the exact ONE-COMPLETION source with
  `β_{D,P} = μ_D · Λ_P`; **proved**: `beta_add_left/right`,
  `beta_double_sum_factorises` (β stays bilinear/linear in each argument),
  `reciprocal_source_unit_invariance`, `budget_closes` and `margin_pos` (the exact
  rational `1/104` margin), `gate1B_conclusion_of_interface` (the Gate conclusion
  follows from an explicit `ConvolutionBVInterface` hypothesis bundle). **Open**:
  `SourceToInterface`. NPCF-2C38 is recorded **DEAD** and is not revived.
* `Challenges/AffineSourceGlue.lean` — `affine_normal_form_at_good_prime` (proved),
  `UnitGlued`, `zeroSet_eq_of_unitGlued`, `card_eq_of_unitGlued` (proved), and the
  **open** `AffineTransference`.
* `Challenges/FordBlockerCompiler.lean` — a *dependency specification only*.
  `BlockerSupplySub/Add` (what a Ford-type theorem must deliver), the **proved**
  `no_Gap2CE_of_blockerSupplySub/Add`, and the external `FordSupply` predicate with
  `no_large_Gap2CE_of_FordSupply`. Ford–Maynard is **not** postulated as a Lean fact.

  Recorded dependency sheet for the symmetric-Sophie sequence
  `a_m = W(m/X)·[Λ(2m−1)+Λ(2m+1)]/log X`:
  TYPE-I INPUT / TYPE-II INPUT / MAIN TERM / LOCAL DENSITY /
  SPARSE-CERTIFICATE INPUT / CONCLUSION REQUIRED FOR #287 = a positive lower bound,
  i.e. the existence of a blocker in every sufficiently large dyadic interval.
  This remains an **external theorem dependency**, not a bank item.

## 5. External validation package

`RequestProject/Validation/BankStatements.lean` restates 26 banked theorems as
standalone `example`s in **unfolded** form (definitions expanded where feasible), each
discharged by the corresponding banked name. It is suitable for an independent Lean
comparator: the statements are fixed verbatim in the file and the proofs do not modify
them.

`RequestProject/Audit/BankStatus.lean` is the machine-readable axiom report
(94 `#print axioms` lines).

## 6. Required report sections

**A. What is now permanently Lean-banked.**
Banks A–H exactly as tabulated above (fixed-affine normal form and good-prime root
transport; unit/finite-sum transport including the Kloosterman-style unit-change
reindexing; abstract fixed-unit zero-set portability; the Bézout parametrisation
`e·Q − d·P = 1` with its coprimality package; the local admissibility criterion
`Admissible ↔ 2 ∣ d·e`; the local root counts `ν(ℓ) ∈ {1,2}` and the `(ℓ−1)/(ℓ−2)`
correction; the finite optimality `J n ≤ J 2` with equality iff `n = 2`, hence
`{d,e} = {1,2}`; the odd-character ± cancellation), plus, on the #287 side, the carry
tower (`lcm² ∣ ∏`, `lcm ∣ ∏ pairwise differences`) and the generalized fixed-cofactor
blocker; plus the three previously `sorry`-ed uniform numerator bounds.

**B. Candidate statements that were false or needed repair.**
1. *Fixed-cofactor blocker threshold.* The prompt's hypothesis "`q` exceeds the
   certified subset-numerator threshold `C(2j−1)`" is **not sufficient on its own**: with
   `p = j·q ± 1` and `M < 2p` the window `⌊M/q⌋` can equal `2j`, not `2j−1`. Repair:
   `fixedCofactor_blocker_sub/_add` use the correct threshold `C(2j)`; the
   `…_sharpWindow` variants keep `C(2j−1)` but carry the extra hypothesis
   `⌊M/q⌋ ≤ 2j−1`. Both forms are proved; nothing was weakened silently.
2. *Carry-tower "LCM" claims.* `lcm(A)² ∣ ∏ a` and `lcm(A) ∣ ∏ (b−a)` are **false for
   general finite sets** — `A = {2,3}` is a counterexample to both, itself banked as
   `lcm_sq_not_dvd_prod_general` / `lcm_not_dvd_diff_general`. They are **true** under
   the reciprocal-sum-1 hypothesis (via the non-singleton top layer), and that is the
   form banked.
3. No other candidate statement in the prompt was found false.

**C. Exact source-glue statements still open.**
`Challenges.AffineGlue.AffineTransference` (base-source packet → fixed-affine packet as
unit reindexings + finitely many bad-prime cells; every source coefficient,
normalisation and exception must be mapped) and
`Challenges.Gate1B.SourceToInterface` (authoritative source ⟹ a populated
`ConvolutionBVInterface`).

**D. Exact analytic statements still open.**
`Challenges.Gate1A.SubpolynomialFibre` (SB-ν: `X^{o(1)}` synchronized two-view fibre
multiplicity for each fixed nonzero ν); the convolution-BV input at exponent
`1/2 + 1/104` abstracted by `ConvolutionBVInterface`; and the Ford-type blocker supply
`Challenges.Ford.FordSupply`.

**E. Should any existing theorem be retired?**
No theorem needs retiring. The only hygiene item is the duplicated definition
`Erdos287.lcmUpto` (Universal.lean) vs `Erdos287.lcmUpTo` (RoughPrime.lean) — identical
bodies, confusable names. Recommended (not done here, to avoid silently rewriting
existing statements): keep `lcmUpto`, make `lcmUpTo` an abbreviation for it, or
deprecate it.

**F. First remaining theorem for Gate 1A.**
Instantiate `Challenges.Gate1A.TwoViewSource` with the authoritative source data
(ω, τ, Σᵢ, Fᵢ, g, clean cells, physical ranges — currently absent from this repo) and
prove `SubpolynomialFibre` for that family, or the explicit divisor-type finite-parameter
substitute that is genuinely sufficient for TF4. The first *real* analytic subgoal is the
divisor-type bound on the synchronized fibre; formalisation stops there and no axiom was
added.

**G. First remaining theorem for Gate 1B.**
`Challenges.Gate1B.SourceToInterface`: derive a `ConvolutionBVInterface` from the exact
one-completion source (β = μ_D·Λ_P still linear), via source-opened q-side SW/Yang or
the v-side labelled-convolution fallback. The published convolution-BV theorem itself
remains an external dependency, deliberately isolated behind the interface structure so
that no theorem name is hand-waved.

**H. First remaining theorem for Erdős #287.**
Supply a blocker pair at every large scale: prove
`Challenges.Ford.BlockerSupplySub M j` (equivalently `BlockerSupplyAdd`) for all
sufficiently large `M`, i.e. produce, in every sufficiently large window, a prime
`p = j·q ± 1` with `q` a prime power above the certified numerator threshold. Given that
input, `no_Gap2CE_of_blockerSupplySub` already closes the gap-`≤2` case in Lean. This
input is a prime-distribution statement of Ford–Maynard type and is **not** available in
Mathlib.

## 7. Build status

```
lake build                       → Build completed successfully (8062 jobs)
sorry / admit / axiom / unsafe /
native_decide in RequestProject/ → none
#print axioms (Audit/BankStatus) → every banked theorem depends only on
                                   propext, Classical.choice, Quot.sound
```

**Final headline: `TRUSTED_BANK_EXTENDED`.** Erdős #287, Gate 1A and Gate 1B remain
open.
