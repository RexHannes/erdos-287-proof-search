# ERDŐS #287 — C0 SOURCE-LIFT SAFE BANK REPORT

Append-only delta.  No previously banked file was edited or deleted, no previously proved
statement was altered or weakened, and no historical status layer was replaced.  The only
change to an existing file is six new `import` lines appended at the end of the import block of
`RequestProject/Main.lean`.

## FILES CREATED

- `RequestProject/CurrentProgramme/Erdos287A0C0SourceLift.lean`
- `RequestProject/CurrentProgramme/Erdos287ReducedProjectivePair.lean`
- `RequestProject/CurrentProgramme/Erdos287BPrimeH0Energy.lean`
- `RequestProject/CurrentProgramme/Erdos287ConditionedInverseConvInterface.lean`
- `RequestProject/Status/CurrentStatusErdos287C0SourceLift.lean`
- `RequestProject/Status/AxiomAuditErdos287C0SourceLift.lean`
- `ERDOS287_C0_SOURCELIFT_SAFE_BANK_REPORT.md` (this file)

The audit module was placed in `RequestProject/Status/` rather than `RequestProject/`, matching
the existing repository convention for every other `AxiomAudit*` module.

## FILES MODIFIED

- `RequestProject/Main.lean` — six appended `import` lines only.

## LEAN COMPILE STATUS

`lake build` on the default target: **PASS**, 8290 jobs, 0 errors.
No `sorry`, `admit`, `axiom`, `unsafe`, `native_decide`, `opaque` or `implemented_by` occurs as
a code construct in any new module; the words appear only in docstring prose in the audit file.
Decidable ledger facts use `decide +kernel`.

## SOURCE DATA STRUCTURE

`Erdos287.SourceLift.SourceRow` carries `s, s', Delta0, Delta0' : ℤ` (no sign assumption) and
`e, e', r1, r2, r1', r2', z, z', b, b', r, m, r', m', ell0', d2, k : ℕ`, plus the positivity
fields `hb, hb', hr, hm, hr', hm', hell0'`.  All natural slots are cast into `ℤ` at the point of
use, so no `Nat` subtraction ever occurs.  Derived definitions:
`u = r m`, `u' = r' m'`, `Gamma1 = 2 e r1 r2 z b`, `Gamma2 = 2 e' r1' r2' z' b'`,
`beta2 = u' ell0'`, `A0row = s Delta0 Gamma2 beta2`, `C0 = s' Delta0' Gamma1`.

## UNCONDITIONAL THEOREMS

`Erdos287.SourceLift` (primitive source forms and the row representative):

- `SourceRow.erdos287_gamma1_primitive`
- `SourceRow.erdos287_gamma2_primitive`
- `SourceRow.erdos287_A0row_primitive`
- `SourceRow.erdos287_C0_primitive`
- `SourceRow.erdos287_u_pos`, `SourceRow.erdos287_u'_pos`, `SourceRow.erdos287_b_pos`
- `erdos287_Q2_dvd`  (`x ∣ d1' * v * x`)
- `erdos287_A0pre_sub_A0row`, `erdos287_A0pre_dvd_sub`
- `erdos287_A0pre_congr_A0row`  (`A0pre ≡ A0row [ZMOD x]`)
- `erdos287_A0pre_congr_A0row_row` (the same for the data of a `SourceRow`)

`Erdos287.ReducedProjective` (raw → reduced pair, collision equivalence, depth):

- `erdos287_F_pos`, `erdos287_F_ne_zero` (`F = b u' > 0`; cancellation is never performed
  without this)
- `erdos287_Praw_factor`  (`Praw = F · Pnat`)
- `erdos287_Rraw_factor`  (`Rraw = F · Rnat`)
- `projective_collision_iff_of_row_factor` (abstract integral-domain cancellation, two
  independent factors `F₁, F₂`)
- `erdos287_raw_projective_collision_iff_reduced`
- `projective_collision_invariant_under_row_scaling`
- `erdos287_Pnat_slot_product`, `erdos287_Rnat_slot_product` (`b'`-absorption: the literal
  eight-slot product forms)
- `erdos287_numerator_depth`, `erdos287_denominator_depth` (both `= 8`)
- `erdos287_fixed_depth_exponent` (`(8+8)^2 − 2 = 254`, arithmetic record only)
- `row_factors_may_differ` (witness that `F₁ ≠ F₂` is possible)

`Erdos287.BPrimeEnergy` (generic finite product-fibre `L²` lemma):

- `product_fibre_l2_bound_of_fibre_card` — for finite-support complex `ω`,
  `∑_{n ∈ N} |C(n)|² ≤ D · ∑_{p ∈ S} |ω(p)|²` whenever every fibre `{p ∈ S : p₁p₂ = n}` has at
  most `D` elements.  The hypothesis bounds the **fibre cardinality**, not a pointwise divisor
  maximum.
- `productFibre_card_le_of_second_mem` — fibres over `n ≠ 0` inject into the set of admissible
  `ℓ₀'`.
- `product_fibre_l2_bound_of_second_cardinality` — the instantiation with `D ≥ #L`.
- `bprime_h0_global_energy` — the same with `D = d₁'`.
- `product_fibre_l2_bound_of_filtered`, `bprime_h0_global_energy_congruence_filter` — the
  optional congruence filter `u' ℓ₀' ≡ b' [MOD d₁']`; restriction only shrinks the fibre, so the
  bound is unchanged.  No Möbius cancellation is used and `ω` is an arbitrary complex
  coefficient.

`Erdos287.ConditionedInverseConv` (firewall witnesses):

- `conditionedInverseConv_hypothesis_not_automatic`
- `conditionedInverseConv_hypothesis_satisfiable`
- `omegaH_normalization_not_automatic`

`Erdos287.C0SourceLiftStatus` (ledger): `banked_children_are_unconditional`, `open_owners`,
`global_rows_not_closed`, `no_analytic_row_is_banked`, `depth_bound_not_formalised`,
`sourcelift_pass_does_not_imply_c0_closure`, `commonX_ledger_still_preserved`.

## CONDITIONAL THEOREMS (explicit named hypotheses only)

- `Erdos287.BPrimeEnergy.energy_transfer_of_depth_bound` — hypothesis `d₁' ≤ Lparam ^ K`.
- `Erdos287.BPrimeEnergy.bprime_h0_global_energy_with_depth_bound` — same hypothesis.
- `Erdos287.ConditionedInverseConv.erdos287_C0_after_conditioned_transfer` — hypothesis
  `ConditionedInverseConvHypothesis`.  Its conclusion is the level-summed form of exactly what
  is assumed; it does **not** close C0.
- `Erdos287.ConditionedInverseConv.omegaH_energy_of_normalization` — hypothesis
  `OmegaHNormalizationHypothesis`.

`d₁' ≤ L^K` is **not** asserted anywhere as an arithmetic fact.  `Ω_H` is **not** normalised
anywhere.  Both shells are proved non-automatic, so neither can be silently discharged.

## AXIOM AUDIT

`#print axioms` is run in `RequestProject/Status/AxiomAuditErdos287C0SourceLift.lean` on every
declaration of this delta, including all items required by the audit list: the two primitive
`Γ` identities, the `A0row` and `C0` primitive identities, the `A0pre`/`A0row` congruence, the
`Praw` and `Rraw` factorisations, the raw/reduced projective collision equivalence, and the
generic `b'`/`ℓ₀'` product-fibre `L²` lemma.

Every declaration depends only on a subset of `propext`, `Classical.choice`, `Quot.sound`;
several depend on no axioms at all.  No custom axiom was introduced.

## HOSTILE AUDIT CHECKLIST

1. Coercions: every natural slot is cast explicitly into `ℤ`; no `Nat` subtraction occurs.
2. Signs: `s, s', Δ₀, Δ₀'` are integers with no positivity or sign hypothesis.
3. `F = b u'` is never cancelled without `erdos287_F_ne_zero`, which is derived from the
   positivity fields of the row.
4. The equivalence is stated and proved for two *independent* row factors `F₁, F₂`;
   `row_factors_may_differ` exhibits a pair with `F₁ ≠ F₂`.
5. No accidental assumption `b = b'`, `u = u'` or `F₁ = F₂` occurs: these are separate fields of
   two separate rows and appear nowhere as hypotheses.
6. The `L²` lemma bounds the **fibre cardinality** (`(productFibre S n).card ≤ D`), and the
   instantiation derives it from injectivity of `p ↦ p.2` on fibres over `n ≠ 0`.
7. `d₁' ≤ L^K`, the `Ω_H` normalisation and the conditioned transfer occur only as explicit
   hypotheses.
8. No theorem states or implies that C0 is closed or that Erdős #287 is proved; the ledger rows
   `c0Branch`, `exactProductCollisionBranch`, `doubleTypeIIBranch` are `partialOpen` and
   `erdos287` is `open_`, and this is proved (`global_rows_not_closed`,
   `no_analytic_row_is_banked`).

## NEW SAFE BANK

```
A0C0-PRIMITIVE-SOURCEFORM45     : PASS   (banked, unconditional)
A0C0-SOURCELIFT45               : CLOSED (banked, unconditional)
A0C0-BPRIME-ABSORPTION45        : PASS   (banked, unconditional)
BPRIME-H0-GLOBALENERGY45        : PASS   (banked, unconditional)
PROJECTIVE-RAW-TO-REDUCED45     : PASS   (banked, unconditional)
FIXED DEPTH (8,8)               : BANKED ARITHMETIC
```

OPEN ANALYTIC OWNER:
`EXACTPRODUCT-CONDITIONED-INVERSECONV-LEVELLS45`.

OPEN FORMAL OWNER:
`SHAREDGCD-OMEGAH-NORMALISATION-SOURCEPIN45`.

C0: PARTIAL.

ERDOS287: OPEN.

## STRICT FINAL VERDICT

```
A0C0 SOURCE ARITHMETIC             : FORMALISED
RAW-TO-REDUCED PROJECTIVE PAIR     : FORMALISED
PROJECTIVE COLLISION EQUIVALENCE   : FORMALISED
BPRIME-H0 FINITE ENERGY LEMMA      : FORMALISED
FIXED DEPTH (8,8)                  : BANKED ARITHMETIC
CONDITIONED INVERSE-CONVOLUTION    : OPEN HYPOTHESIS
OMEGA_H NORMALISATION              : OPEN SOURCE PIN
EXACT PRODUCT COLLISION            : PARTIAL
DOUBLE TYPE II                     : PARTIAL
C0                                 : PARTIAL
ERDOS287                           : OPEN
```
