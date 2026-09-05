# Erdős #287 — V13 run report: the canonical singleton structural reduction

**Erdős #287 remains OPEN. Nothing in this run proves it.**
No theorem in this run claims Gate 1A/1B analytic closure, H8/H9 smallness, the seven-prime
analytic Kummer bound, the fixed-certificate full leakage, the Ford lower-bound application
for the #287 affine sequence, `WindowPairSupply` for all large `M`, or the Twin Prime
Conjecture.

---

## 0. Workspace check (requested precondition)

All six named files are present in the working tree at the resumed commit:

| file | present |
|---|---|
| `RequestProject/Erdos287/FixedCertificateFordData.lean` | yes |
| `RequestProject/Erdos287/FixedCertificateThreeError.lean` | yes |
| `RequestProject/Erdos287/FixedCertificateSmoothParity.lean` | yes |
| `RequestProject/Erdos287/FixedCertificateOrderCounterguard.lean` | yes |
| `RequestProject/Erdos287/KummerDegeneracyRouters.lean` | yes |
| `RequestProject/Status/Erdos287GoldV12Status.lean` | yes |

Every declaration reported by the previous run was re-checked in place.
`ERDOS287_ARISTOTLE_WORKSPACE_MISMATCH` does **not** apply.

---

## A. Source archaeology (completed before any edit)

```
OBJECT:      nu0
LEAN NAME:   Erdos287.FordData.nu0
FILE:        RequestProject/Erdos287/FixedCertificateFordData.lean
LITERAL TYPE: ℚ  (:= 16623 / 100000)
AXIOMS:      n/a (definition)
USED BY:     nu0_bounds, twoVarLow, twoVarLow_eq, twoVarWindow_nonempty,
             twoVarWindow_width, fordCandidate_two_sample(_out);
             now also Erdos287.Singleton.nu0R_eq_cast_nu0
STATUS:      PRESENT
```

```
OBJECT:      shrink parameter eps / epsilonStar
LEAN NAME:   (none)
FILE:        —
LITERAL TYPE: —
AXIOMS:      —
USED BY:     —
STATUS:      ABSENT.  The only shrink object in the tree is
             Erdos287.FordData.shrink (delta : ℚ) (g : List ℚ → ℚ), an abstract
             (1 − δ) rescaling with no effective δ.  No ε/εStar exists.
             This run introduces Erdos287.Singleton.AdmissibleEps as the ledger
             range 0 < ε < ν₀/100, not as a pinned source value.
```

```
OBJECT:      gStar (fixed Ford certificate g*)
LEAN NAME:   (none)
FILE:        —
STATUS:      ABSENT.  Only the transcribed branch table
             Erdos287.FordData.fordCandidate (c2 : ℚ) : List ℚ → ℚ exists,
             together with the never-inhabited predicate
             Erdos287.FordData.CertificatePinned.  There is no H_{g*}, no G_*,
             no canonical split, no splitting threshold.
```

```
OBJECT:      truncMobius
LEAN NAME:   Erdos287.SmoothParity.truncMobius
FILE:        RequestProject/Erdos287/FixedCertificateSmoothParity.lean
LITERAL TYPE: (n T : ℕ) → ℤ,
             := ∑ d ∈ n.divisors.filter (· ≤ T), ArithmeticFunction.moebius d
USED BY:     truncMobius_one, truncMobius_prime, truncMobius_eq_zero_of_le,
             FixedCertificateSmoothParityPacket.cell_identity,
             smoothParity_missing_source;
             now also Erdos287.Singleton.K0CellIdentitySource
STATUS:      PRESENT
```

```
OBJECT:      FixedCertificateSmoothParityPacket
LEAN NAME:   Erdos287.SmoothParity.FixedCertificateSmoothParityPacket
FILE:        RequestProject/Erdos287/FixedCertificateSmoothParity.lean
LITERAL TYPE: (sector : Finset ℕ) (Hs : ℕ → ℤ) (cut : ℕ → ℕ) (f : ℕ → ℝ) (E : ℝ)
             : Prop, with fields cut_pos, cell_identity, analytic_bound
USED BY:     smoothParity_prime_normalization, smoothParity_inactive_cut;
             now also Erdos287.Singleton.smoothParity_of_singletonTypeII
STATUS:      PRESENT, UNINHABITED
```

```
OBJECT:      cell_identity field
LEAN NAME:   Erdos287.SmoothParity.FixedCertificateSmoothParityPacket.cell_identity
LITERAL TYPE: ∀ n ∈ sector, Hs n = truncMobius n (cut n)
STATUS:      UNINHABITED / SOURCE_BLOCKED
```

```
OBJECT:      parent leakage compiler
LEAN NAME:   Erdos287.SmoothParity.parent_leakage_of_children,
             Erdos287.SmoothParity.parent_leakage_two_children,
             Erdos287.SmoothParity.parent_prime_mass_pos
FILE:        RequestProject/Erdos287/FixedCertificateSmoothParity.lean
AXIOMS:      propext, Classical.choice, Quot.sound
STATUS:      PRESENT, PROVED.  Reused unchanged by this run.
```

```
OBJECT:      three-error transference theorem
LEAN NAME:   Erdos287.Transference4.sum_a_P_identity4, sum_a_P_lower4,
             sum_a_P_pos4, sum_a_P_pos4_fraction, transference4_nonvacuous
FILE:        RequestProject/Erdos287/FixedCertificateThreeError.lean
AXIOMS:      propext, Classical.choice, Quot.sound
STATUS:      PRESENT, PROVED.  Reused unchanged (three channels ET / EL / E2 kept
             separate, plus the margin EM).
```

```
OBJECT:      balanced-cell counterguard
LEAN NAME:   Erdos287.Counterguard.balancedCellWeight, balancedCellWeight_eq,
             balancedCellWeight_ne_zero, balancedCellCut, halfCut,
             counterguard_k7 … counterguard_k12,
             balancedCellWeight_halfCut_ne_zero, finite_H8H9_only_census_fails
FILE:        RequestProject/Erdos287/FixedCertificateOrderCounterguard.lean
AXIOMS:      propext, Classical.choice, Quot.sound
STATUS:      PRESENT, PROVED.  Not modified.
```

```
OBJECT:      Ford factorisation / canonical split
LEAN NAME:   (none)
STATUS:      ABSENT.  No definition of a canonical high/low prime split, no
             Ford weight factorisation, no G_* / H_* source formula anywhere in
             RequestProject.  ⇒ K0_CELL_IDENTITY_SOURCE_STILL_EXTERNAL.
```

```
OBJECT:      structures representing an external analytic input
LEAN NAME:   Erdos287.FordData.CertificatePinned (Prop, uninhabited)
             Erdos287.FordData.PositiveComparisonMargin (Prop, uninhabited)
             Erdos287.KummerWeil.QuadraticKummerCorrelationBound (uninhabited)
             TrustedBank.Gate1B.SourceMMDRequirements (uninhabited)
             Challenges.Gate1B.ConvolutionBVInterface (uninhabited)
STATUS:      PRESENT, all UNINHABITED.  This run adds two more
             (SingletonGeneratedTypeIIInput, SingletonPacketReduction) and
             inhabits none of them.
```

No coagulation / partition / forbidden-region geometric abstraction exists in the
repository (Part C, second half). **Missing object recorded, not built:** an abstraction
of the coagulated forbidden region for smooth vectors. No large new geometry library was
created for this run.

---

## B. Verdict on the old `cell_identity`

`K0_CELL_IDENTITY_SOURCE_STILL_EXTERNAL`.

The canonical split and the Ford `G_*` definition are not encoded (see archaeology above),
so the specialization "on the `k = 0`, `J = ∅` smooth branch with `σ = ν₀ − 2ε`,
`γ = 1/2 − ε`, `P⁺(n) ≤ n^σ`, the high-prime component is empty and `H_*(n)` reduces to
`∑_{d ∣ n, d ≤ n^γ} μ(d)`" cannot be *proved*; it could only be assumed.  Therefore:

* no fake Ford factorisation definition was introduced;
* the `cell_identity` field is left uninhabited;
* the missing statement is named exactly as `Erdos287.Singleton.K0CellIdentitySource`;
* every downstream theorem carries it as an explicit antecedent.

---

## O. Required end-of-run block

```text
WORKSPACE / COMMIT:
  branch main, resumed in place (all six named files verified present).

FILES ADDED:
  RequestProject/Erdos287/FixedCertificateSingletonParameters.lean
  RequestProject/Erdos287/FixedCertificateSingletonFragment.lean
  RequestProject/Erdos287/FixedCertificateSingletonCompiler.lean
  RequestProject/Status/Erdos287SingletonV13Status.lean
  ERDOS287_SINGLETON_V13_REPORT.md

FILES EDITED:
  RequestProject/Main.lean  (four import lines only)
  No historical theorem statement was edited, renamed, weakened or deleted.

NEW THEOREMS:
  -- Part D, parameter ledger (exact rationals, no floating point)
  Erdos287.Singleton.nu0R_eq_cast_nu0
  Erdos287.Singleton.nu0R_pos
  Erdos287.Singleton.nu0R_lt_one_sixth
  Erdos287.Singleton.admissibleEps_pos
  Erdos287.Singleton.admissibleEps_lt
  Erdos287.Singleton.admissibleEps_nonempty
  Erdos287.Singleton.sigma_pos
  Erdos287.Singleton.sigma_le_nu0
  Erdos287.Singleton.epsilon_lt_sigma
  Erdos287.Singleton.epsilon_lt_sigma_div_three
  Erdos287.Singleton.sigma_lt_one_sixth
  Erdos287.Singleton.two_sigma_div_three_lt_one
  Erdos287.Singleton.two_sigma_lt_one
  Erdos287.Singleton.sigma_lt_epsilon_add_sigma
  Erdos287.Singleton.six_sigma_lt_one
  Erdos287.Singleton.seven_mul_sigma_gt_one
  Erdos287.Singleton.sigma_div_three_lt_sigma
  Erdos287.Singleton.epsilon_le_one
  -- Part C, normalised smooth-vector lemma
  Erdos287.Singleton.exists_subset_sum_in_typeII_window
  Erdos287.Singleton.exists_singleton_subset_sum_in_typeII_window
  -- Parts E/F, fragmentation and canonical singleton
  Erdos287.Singleton.FordSmoothFragmentCertificate.zu_le_sigma
  Erdos287.Singleton.FordSmoothFragmentCertificate.zv_le_sigma
  Erdos287.Singleton.FordSmoothFragmentCertificate.total_le_card_mul_sigma
  Erdos287.Singleton.fragment_seven_le_card
  Erdos287.Singleton.fragment_not_both_singleton
  Erdos287.Singleton.fragment_singleton_terminal_contradiction
  Erdos287.Singleton.fragment_r_ge_of_s_eq_one
  Erdos287.Singleton.chosen_nonterminal
  Erdos287.Singleton.canonical_singleton_typeII
  Erdos287.Singleton.canonical_singleton_card_eq_one
  Erdos287.Singleton.singleton_supersedes_depth_five
  Erdos287.Singleton.chosenClass_mobius_iff
  -- Part G, real-power translation
  Erdos287.Singleton.singleton_real_power_window
  Erdos287.Singleton.singleton_real_power_window_shifted
  -- Part H, complement depth
  Erdos287.Singleton.fragment_depth_le_40
  Erdos287.Singleton.two_le_fragment_depth
  Erdos287.Singleton.singleton_complement_depth_le_39
  -- Parts B/J, conditional compiler
  Erdos287.Singleton.k0CellIdentitySource_is_cell_identity
  Erdos287.Singleton.smoothParity_of_singletonTypeII
  Erdos287.Singleton.parentLeakage_of_singletonTypeII
  Erdos287.Singleton.primeMassPos_of_singletonTypeII
  -- non-vacuity guards
  Erdos287.Singleton.epsWitness_admissible
  Erdos287.Singleton.fragmentWitness_depth
  Erdos287.Singleton.fragmentWitness_chosen

  New definitions: nu0R, sigmaOf, AdmissibleEps, SingletonClass,
  FordSmoothFragmentCertificate, chosenSize, chosenClass, chosenLabel,
  chosenTypeIISet, fragmentDepth, K0CellIdentitySource,
  SingletonGeneratedTypeIIInput, SingletonPacketReduction, epsWitness,
  fragmentWitness.

FAILED TARGETS:
  none.

SOURCE-BLOCKED TARGETS:
  K0-SMOOTH-LEAKAGE-SOURCE45 / cell_identity
    (Erdos287.Singleton.K0CellIdentitySource) — the Ford canonical split is not
    encoded in the repository.
  SingletonPacketReduction — the structural dissection linking the packet sum to
    the Type-II bilinear sum.

EXTERNAL PUBLISHED INPUTS:
  Ford–Maynard Lemma 7.17 (MU-SPLITTABLE45), represented only by the
  never-inhabited FordSmoothFragmentCertificate.
  Classification: CONDITIONAL_INTERFACE / PUBLISHED_SOURCE.

OPEN ANALYTIC INPUTS:
  287-SMOOTH-PARITY-SINGLETON-GENERATED-TYPEII45
    = Erdos287.Singleton.SingletonGeneratedTypeIIInput (uninhabited).
```

### `#print axioms` for every principal new theorem

All 41 principal new theorems print

```
depends on axioms: [propext, Classical.choice, Quot.sound]
```

The prints are emitted by `RequestProject/Status/Erdos287SingletonV13Status.lean` at build
time, so they are checkable rather than transcribed.  No user axiom appears anywhere.

### Repository-wide searches

| pattern | Lean-code matches | documentation-prose matches |
|---|---|---|
| `sorry` | 0 | 1 (`Audit/BankStatus.lean` header comment) |
| `admit` | 0 | 0 |
| `axiom` | 0 | 8 (all in doc comments / status headers) |
| `opaque` | 0 | 0 |
| `unsafe` | 0 | 1 (doc comment) |
| `native_decide` | 0 | 4 (doc comments stating it is *not* used) |
| `@[implemented_by]` | 0 | 0 |

### `lake build`

```
Build completed successfully (8105 jobs).
```

---

## Final ledger

```text
K0-SMOOTH-LEAKAGE-SOURCE45                          SOURCE_BLOCKED
MU-SPLITTABLE45 (Ford–Maynard Lemma 7.17)           PUBLISHED_EXTERNAL_INPUT
FordSmoothFragmentCertificate (s, r ≤ 20)           CONDITIONAL_INTERFACE
SINGLETON PARAMETER LEDGER (exact ℚ)                PROVED_ALGEBRAIC
NORMALISED SMOOTH-VECTOR LEMMA                      PROVED_ALGEBRAIC
CANONICAL-SINGLETON-E45                             PROVED_ALGEBRAIC
SINGLETON-COMPLEMENT-DEPTH39                        PROVED_FINITE
REAL-POWER TRANSLATION                              PROVED_ALGEBRAIC
287-SMOOTH-PARITY-FRAGMENT-TO-SINGLETON-TYPEII45    PROVED_COMPILER
287-SMOOTH-PARITY-SINGLETON-GENERATED-TYPEII45      OPEN_ANALYTIC
SMOOTH-PARITY                                       CONDITIONAL_INTERFACE / OPEN_ANALYTIC
FCL                                                 OPEN_ANALYTIC
ERDOS287                                            OPEN_ANALYTIC
```

Verdict for Part F: `CANONICAL_SINGLETON_E45_KERNEL_PASS`.
Part G did **not** need the fallback `SINGLETON_EXPONENT_KERNEL_PASS_REAL_POWER_TRANSLATION_PENDING`:
both the base and the shifted real-power forms are proved.

The hostile-check answers (Part N, items 1–10) are recorded in the module docstring of
`RequestProject/Status/Erdos287SingletonV13Status.lean`.  Item 3 is a **downgrade**: the
`1 ≤ 2σ/3` route for "`s = r = 1` impossible" is not valid under the interface's terminal
convention without the extra hypothesis that both singleton sides are terminal, so the
unconditional size bound `s + r ≥ 7` is used instead and the terminal route is kept as a
separate, hypothesis-bearing lemma.
