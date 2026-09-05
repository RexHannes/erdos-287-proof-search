# Erdős #287 — effectivity certificate bank + P0 `B_src` normalisation repair

All statements below were checked by `lake build` on the whole project
(8437 jobs, no errors).

---

## LEAN FILES

New:

```
RequestProject/Erdos287/SourceWeights.lean
RequestProject/Erdos287/GcdDescent.lean
RequestProject/Erdos287/BernoulliKernel.lean
RequestProject/Erdos287/MediumKSource.lean
RequestProject/Erdos287/RepeatedCores.lean
RequestProject/Erdos287/DirectedLedger.lean
RequestProject/Erdos287/FloorInterface.lean
RequestProject/Erdos287/Bank.lean
RequestProject/Status/CurrentStatusErdos287CertificateBank.lean
```

Edited (surgical, no proved bank deleted):

```
RequestProject/CurrentProgramme/Erdos287September4BsrcLocalMobiusCollapse.lean
      — P0 normalisation notice added; §4.4/§4.5 headings retyped as ABSTRACT model;
        `literal_S2_mu_form_fails` renamed
        `abstractLocalNormalisation_S2_mu_form_fails`
RequestProject/Status/AxiomAuditErdos287September4SignedFloorBank.lean
      — `#print axioms` line updated to the new name
RequestProject/Main.lean
      — two imports appended
```

NO SORRY: **YES** (none anywhere in the project; only the word appears in prose).
NO CUSTOM AXIOMS: **YES** (no `axiom`, no `@[implemented_by]`, no `native_decide`,
no `unsafe`, no `opaque`).

LAKE BUILD: **PASS**.

---

## PART A — P0 REPAIR

### P0 BUG LOCATED

In `Erdos287September4BsrcLocalMobiusCollapse.lean` the source weight is a **purely local
product**

```
Bsrc Bloc d = ∏_{p ∣ d} Bloc p            beta bloc k = ∏_{p ∣ k} bloc p
```

and the constant `S₂` enters only through the *local* hypothesis

```
hnorm : ∀ p ∈ q.primeFactors, bloc p − Bloc p = −S₂ .
```

`interiorLocalMobiusCollapse45` evaluates the divisor sum to `∏_{p ∣ q} (bloc p − Bloc p)`;
substituting `hnorm` multiplies the **global** constant once per prime factor and therefore
yields `S₂^{ω(q)}·μ(q)`.

**So the diagnosis in the request is confirmed exactly: the global `S₂` was inserted into
every local prime factor and then multiplied over `primeFactors(q)`.**  The theorems
themselves are true — the bug is a normalisation/type mismatch with the physical source, not
a mathematical error.

### OLD FALSE PHYSICAL THEOREM: **RETYPED**

No theorem was deleted (all are kernel-true statements about the abstract model).  Instead:

* the module docstring now carries a **P0 NORMALISATION NOTICE** stating that the module
  describes an artificially locally-normalised model and pointing at the physical identity;
* `§4.4` is retitled *the **abstract** locally-normalised form (NOT the physical
  normalisation)*, and `interiorCollapse_normalized`'s docstring is marked **Abstract model
  only**;
* the `q = 15` counterexample is **renamed**
  `literal_S2_mu_form_fails → abstractLocalNormalisation_S2_mu_form_fails`
  and retyped as a counterexample to the *over-general abstract* model (its witness uses the
  artificial local values `Bloc ≡ 0`, `bloc ≡ −2`, `S₂ = 2`, which are not the physical
  `(p−1)/(p−2)`, `1/(p−2)`).

There are now **no two contradictory physical theorems**: exactly one physical local-collapse
theorem exists.

### CORRECT PHYSICAL `B_src` DEFINITION

`RequestProject/Erdos287/SourceWeights.lean`:

```lean
def beta (n : ℕ) : ℚ := ∏ p ∈ n.primeFactors, (1 / ((p : ℚ) - 2))
def B0   (n : ℕ) : ℚ := ∏ p ∈ n.primeFactors, (((p : ℚ) - 1) / ((p : ℚ) - 2))
def Bsrc (S2 : ℚ) (n : ℕ) : ℚ := S2 * B0 n
def lam  (n : ℕ) : ℚ := ∏ p ∈ n.primeFactors, (((p : ℚ) - 1) / ((p : ℚ) - 2) ^ 2)
```

Typed relation (`B_src` is **not** naively multiplicative):
`Bsrc_mul_typed : S₂ · B_src(ab) = B_src(a)·B_src(b)` for coprime `a,b`.
`B0`, `beta`, `lam` are multiplicative on coprime nonzero arguments.
`lam_eq_B0_mul_beta : λ(n) = B0(n)·β(n)`.

### CORRECT LOCAL COLLAPSE: **KERNEL-PROVED**

```
beta_sub_B0_prime             : p odd prime → β(p) − B0(p) = −1
beta_sub_B0_two               : β(2) − B0(2) = 0        (why oddness is required)
normalizedB0MobiusCollapse45  : q odd squarefree → ∑_{d∣q} μ(d) B0(d) β(q/d) = μ(q)
physicalBsrcMobiusCollapse45  : q odd squarefree → ∑_{d∣q} μ(d) B_src(d) β(q/d) = S₂·μ(q)
```

### q = 15 REGRESSION: **KERNEL-PROVED**

```
regression_q15_normalized : β(15) − B0(3)β(5) − B0(5)β(3) + B0(15) = 1
                            (1/3 − 2/3 − 4/3 + 8/3 = 1)
regression_q15_physical   : ∑_{d ∣ 15} μ(d) B_src(d) β(15/d) = S₂     ( = S₂·μ(15) )
```

The old alleged counterexample no longer appears as a *physical* counterexample.

### AFFECTED DECLARATIONS (dependency DAG)

```
interiorLocalMobiusCollapse45            (abstract, TRUE, unchanged)
  ├── Status.row_interiorMobiusCollapse_backed        (unchanged, still valid)
  └── SourceWeights.normalizedB0MobiusCollapse45      (NEW, physical instance)
        └── SourceWeights.physicalBsrcMobiusCollapse45
              └── SourceWeights.regression_q15_physical
              └── GcdDescent.local_coefficient_identity  (uses B_src/β/λ, not the
                    collapse itself)

interiorCollapse_normalized  (S₂^{ω(q)}, ABSTRACT)
interiorCollapse_S2_mu
interiorCollapse_S2_mu_of_prime
abstractLocalNormalisation_S2_mu_form_fails   (renamed)
  └── referenced ONLY by AxiomAuditErdos287September4SignedFloorBank (`#print axioms`)
```

No physical compiler ever depended on the `S₂^{ω(q)}` form, so **no theorem had to be
downgraded or removed**.

### UNAFFECTED BANK REBUILT: **PASS**

Full `lake build` of all 8437 targets succeeds: `W` definition/support/endpoints,
monotonicity, `eVariationOn W = 2`, `C_W = 4`, canonical-state sign, threshold-crossing
invariance, T0–T2 decomposition, `r = 2u` reindexing, deep-even cancellation, signed `−4`
derivation, large-`L` tail monotonicity, boundary checker infrastructure and all firewalls
recompile unchanged.

---

## PART B — CERTIFICATE BANK

### CORE

```
COPRIME MOBIUS INDICATOR              : KERNEL-PROVED  (coprime_indicator_mobius)
BETA MULTIPLICATIVITY                 : KERNEL-PROVED  (beta_mul)
BSRC MULTIPLICATIVITY                 : KERNEL-PROVED  (Bsrc_mul_typed — typed form
                                        S₂·B_src(ab) = B_src(a)B_src(b); B0_mul for B0)
LAMBDA LOCAL FACTOR                   : KERNEL-PROVED  (lam_mul, lam_eq_B0_mul_beta,
                                        beta_sub_B0_prime)
SQUAREFREE GCD DESCENT                : KERNEL-PROVED  (squarefree_gcd_descent,
                                        squarefree_gcd_descent_map / _real,
                                        local_coefficient_identity,
                                        descentIndex_coprime,
                                        onePrime_shared_cancellation)
PHASE DESCENT                         : KERNEL-PROVED  (phase_descent, phase_descent_apply,
                                        W_argument_descent,
                                        derivative_argument_descent)
HYPERBOLA SUPPORT DESCENT             : KERNEL-PROVED  (hyperbola_support_gcd_descent,
                                        hyperbola_support_gcd_descent_nat)
MEDIUM-k EXACT SOURCE NORMAL FORM     : KERNEL-PROVED, CONDITIONAL on the finite
                                        truncation (U,K) of the source support
                                        (mediumK_source_normal_form,
                                        Rmed_descended_window)
NO-LATTICE JOINT KERNEL               : KERNEL-PROVED  (jointKernel_noLattice)
REPEATED-CORE LEDGER DISJOINTNESS     : KERNEL-PROVED  (repeated_core_ledger_disjoint,
                                        repeated_core_ledger_total,
                                        repeated_core_p2_p3_disjoint,
                                        repeated_noLattice_only_global)
```

Notes.

* The descent is stated for arbitrary coefficient rings via a ring hom `φ : ℚ →+* R`,
  with `R = ℚ` and `R = ℝ` instances; `gcd(q,v)` is deliberately **unconstrained** and the
  available coprimality `gcd(b, q·v) = 1` is a separate theorem.
* `jointKernel_noLattice` is proved by **exact integration by parts** — no Euler-summation
  lemma is used and none is assumed.  The proof needs, and takes as explicit hypotheses,
  `z²/X ≤ 9/10`, `W(9/10) = 0` (from `supp W ⊆ [7/10,9/10]`; a helper
  `endpoint_vanishes_of_support` derives it from vanishing outside `(7/10,9/10)`),
  `HasDerivAt W (W' y) y`, and interval integrability of `W'`.  Inside the no-lattice region
  the sawtooth argument never crosses an integer, which is what makes the identity exact.
* API firewall recorded in `BernoulliKernel.lean`: the physical `k`-consumer is
  `jointKernel`; no theorem licenses bounding `bernoulliEndpoint` and `bernoulliDerivative`
  separately and summing them over `k`.
* The `r = 1 / p² / p³` classification is carried abstractly by `CoreTag`; it is not reproved.
* `0.9` is always the exact rational `9/10`.

### CERTIFICATE

```
SMALL-k NUMERICAL INPUT     : EXTERNAL-CERT  (recorded exactly: 1913023635 / 10^16)
NO-LATTICE NUMERICAL INPUT  : EXTERNAL-CERT  (recorded exactly: 1641148117 / 10^16)
REPEATED p2 INPUT           : EXTERNAL-CERT  (recorded exactly: 1663866835 / 10^16)
REPEATED p3 INPUT           : EXTERNAL-CERT  (recorded exactly:      83528 / 10^15)
DRIFT INPUT                 : EXTERNAL-CERT  (recorded exactly:         81 / 10^17)
q = 3 physical row          : EXTERNAL-CERT  (recorded exactly:        217 / 10^10;
                              it is a sub-item of the k ≤ 31 total and is NOT added again —
                              certQ3Row_le_certSmallK is kernel-proved)
```

No compact machine certificate is attached to the project, so the five analytic estimates are
`EXTERNAL MACHINE-CERTIFICATE INPUT`s: what is kernel-checked is the **arithmetic performed
on them**.  Nothing was turned into an axiom.

```
CERTIFIED SUBTOTAL          : 52188738751 / 10^17  =  5.2188738751e-7
                              (certifiedSubtotal_correct)
PRINTED 5.218873872e-7 CONSISTENT : NO
        the printed value is STRICTLY SMALLER than the exact outward sum,
        short by exactly 3.1e-16 (printed_subtotal_gap), so it is not a
        valid outward subtotal.
REMAINING CAPACITY          : 36417761249 / 10^17  =  3.6417761249e-7
                              (target = 886065/10^12 = 8.86065e-7)
PRINTED 3.641776128e-7 CONSISTENT : NO
        the printed value OVERSTATES the true capacity by 3.1e-16
        (printed_remaining_overstates_capacity).
```

**Use `3.6417761249e-7` (or the strict outward-safe `3.641776124e-7`) as the budget, not the
printed figure.**

```
LARGE-SIEVE INPUT CONSTANTS
  ∑_b λ(b)/√b < 7/2      : NOT AVAILABLE / EXTERNAL-CERT (recorded as
                           lambdaSqrtSumBound; infinite Euler product, no certificate)
  ∑_q β(q)² < 241/100    : NOT AVAILABLE / EXTERNAL-CERT (recorded as betaSqSumBound)
  sawtooth DFT L² mass   : KERNEL-CHECKED.
      sawtooth_sq_mean    : (1/q)·∑_{a<q} (a/q − 1/2)² = (q²+2)/(12q²)
                            — the Parseval-equivalent real content of
                              ∑_{h mod q} |ψ̂_q(h)|² = (q²+2)/(12q²)
                              under the strict-endpoint convention
      sawtooth_l2_mass_le : q ≥ 3 → (q²+2)/(12q²) ≤ 11/108
```

```
q = 3 CERTIFICATE INTERFACE : format + checker interface formalised
      (Q3PrefixCertificate, Q3PrefixCertificate.Claim, q3Certificate = ⟨10^6, 4.5e9, 2/5⟩,
       q3_normalised_bound).  The 4.5e9 segmented sieve is NOT replayed in Lean and the
       claim is NOT asserted — only downstream consequences, conditionally.

CONDITIONAL BUDGET THEOREM  : KERNEL-PROVED
      mediumK_gap_budget_implies_boundary_target
      boundary_target_of_ledger_budget      (ledger numbers substituted)
      boundary_target_with_Rempty           (|R_∅|/B_X < 8.56e-8 as a hypothesis only)
      open_nodes_imply_boundary_target
```

### OPEN

```
MEDIUM-k JOINT BERNOULLI : OPEN   (predicate MediumKJointBernoulliClosed only)
TWO-HIGH a ≤ 180         : OPEN   (predicate TwoHighA180Closed only)
SIGNED B_src FLOOR       : OPEN   (predicate SignedBsrcFloorClosed only)
MAYNARD                  : NOT ENTERED (no predicate, no statement, nothing)
ERDŐS #287               : OPEN   (nothing here claims it)
```

FIRST EXACT REMAINING NODE:
`ERDOS287-TOT-BSRC-SQFREE-LATTICEBEARING-MEDIUMK-GCDDESCENT-JOINT-BERNOULLI-DIRECTED45`

PARALLEL SECOND NODE:
`ERDOS287-TOT-BSRC-SQFREE-TWOHIGH-A180-NONLINEAR-MELLIN-LATTICEBEARING45`

---

## AXIOM AUDIT

`RequestProject/Erdos287/Bank.lean` runs `#print axioms` on every major theorem of the
package.  Every one reports exactly

```
[propext, Classical.choice, Quot.sound]
```

with no `sorryAx` and no custom axiom.
