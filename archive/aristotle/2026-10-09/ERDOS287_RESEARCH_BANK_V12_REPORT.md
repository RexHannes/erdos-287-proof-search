# Erdős #287 — Research Bank V12 report (concrete repaired Type-II/HB specialization)

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 remains OPEN.**

The previously missing concrete Type-II/HB formulas have now been supplied.

The previously missing concrete Type-II/HB margins have now been supplied and formalized.

The endpoint-only HB coverage claim is formally refuted.

The endpoint-only HB argument remains formally refuted.

The repaired support routing covers every declared HB support box.

The repaired Type-II/HB support routing now covers the full declared support region.

The compatible-cell improvement is exact combinatorics; the spectral estimate
remains an external analytic provider.

The compatible-cell saving is exact combinatorics; the spectral estimate remains an explicit external provider.

The concrete asymptotic composition is conditional on visible external providers.

The asymptotic composition remains conditional on visible external analytic providers.

Erdős #287 remains OPEN.

---

## 0. Audit findings (read first)

Two of the supplied statements are **false as literally stated**, and two supplied quantities could
not be reconstructed.  Everything else in §3–§16 of the request is kernel-proved.

1. **First false statement — Case III `g1 ≥ 4/13 − μ + θ₀/2 + (337/2)ζ` on the whole Type-II
   window `r + s ≥ d* − ζ`.**  Concrete counterexample (`HBCaseIII.g1_337_fails_on_full_window`):
   `μ = 3/10`, `θ = θ₀`, `ν = 1/10`, `r = r*(ν)`, `s = B − ζ − r*(ν)`.  This is a legal Case-III box,
   `d* = B`, `r + s = d* − ζ`, and
   `g1 = 4/13 − μ + θ₀/2 + 168ζ` exactly, i.e. `ζ/2` below the claimed bound.
   *What is true* (all proved):
   * `g1_ge_of_ge_B`: on `r + s ≥ B`, `g1 ≥ 4/13 − μ + θ₀/2 + (337/2)ζ > 0` — so the `(337/2)ζ`
     form is correct on `r + s ≥ d*` whenever `d* = B`;
   * `g1_ge_window_B`: on `r + s ≥ B − ζ`, `g1 ≥ 4/13 − μ + θ₀/2 + 168ζ` (sharp);
   * `g1_ge_window_lam`: on `r + s ≥ λ − ζ`, `g1 ≥ 3(θ₀ − θ) + 98ζ`;
   * **`g1_pos_on_typeII_window`: `g1 > 0` on the entire Type-II window** — this is all the routing
     needs, so the routing theorem is unaffected.
2. **Second false instance — the same `(337/2)ζ` bound in the `d* = λ` branch.**
   `g1_337_fails_in_lam_branch`: at `μ = 4/13 − θ₀/2`, `θ = θ₀`, `ν = 1 − 3μ` (top corner) one has
   `g1 = 3θ₀/4 + (197/2)ζ`, which is below `4/13 − μ + θ₀/2 + (337/2)ζ = θ₀ + (337/2)ζ`.
   In that branch Type I already covers every legal box (`typeI_covers_all_in_lam_branch`), so again
   routing is unaffected.
3. **Not reconstructed:** the Case-III Type-I reserve `G5 ≥ 19ζ`.  The formula for `G5` was not
   printed in the supplied material.  The proved substitute is `typeI_level_reserve`
   (`(1 + 2μ − λ − 7θ)/2 − (r + s) ≥ 9ζ` on the Type-I side `r + s ≤ d* + ζ`).
4. **Not reconstructed:** the exact five domain margins of the frozen Type-I theorem (Case I).
   They were not printed, and the frozen Type-I bank (V10 `SmoothTypeIInput`) has no explicit domain
   predicate for them.  They are therefore "not reconstructed from the supplied source".  What *is*
   proved: the supplied reserve `μ − 3θ − s ≥ ζ` (`HBCaseI.reserve`), the supplied rapid-decay
   margin `μ − θ − r − s ≥ ζ` when `r < θ` (`rapidDecay_declared_margin`), and four natural
   geometric facts (`typeI_domain_facts`: `r + s ≤ λ`, `θ ≤ r`, `sI ≥ 4/13 − 3θ₀ − ζ > 0`,
   `r ≤ rI < 1/4`).  These four are not claimed to be the frozen theorem's margins.

The ledger records items 1–2 as `FALSE STATEMENT` rows (with finite fixtures) and items 3–4 as
`NOT SUPPLIED` rows.

## 1. Files (append-only)

All new; no pre-existing file was modified (`git diff --name-status` against the pre-V12 commit
shows only `A` entries).  `ARISTOTLE_SUMMARY.md` was not edited.

* `RequestProject/Erdos287/ResearchBankV12.lean` (aggregator)
* `RequestProject/Erdos287/ResearchBankV12/`
  `ConcreteParameters`, `EndpointCounterfixture`, `CompatibleCellsConcrete`,
  `RestoredTypeIIEnvelope`, `TypeIIWholeRectangle`, `HBSelectionConcrete`, `HBCaseI`, `HBCaseII`,
  `HBCaseIII`, `HBFullSupportConcrete`, `RoughSeedConcrete`, `ConcreteAsymptoticGate`, `Ledger`,
  `AxiomAudit` (`.lean`)

Layout is exactly the requested one.  §7 (high-H/low-H) lives in `RestoredTypeIIEnvelope`, §9
(`smallBV`) in `ConcreteParameters`, §14 (well-factorability firewall) in `HBFullSupportConcrete`.
Namespaces `Erdos287.ResearchBankV12.<File>`.  As with V10/V11 the files do not start with
`module`, because a `module` file cannot import the non-module V9–V11 files.

## 2. Principal theorems

### §3 `ConcreteParameters`
`theta0 = 1/25000 + 1/625000000` (`theta0_eq : = 25001/625000000`), `epsilon0 = 1/100000`,
`zeta = epsilon0/100` (`zeta_eq : = 1/10^7`), `lam = vartheta = 7/13 − 3θ₀ − ε₀`.
Proved: `theta0_lt` (`θ₀ < 1/1000`), `epsilon0_le`, `loss_eq` (`3θ₀+ε₀ = 81253/625000000`),
`loss_lt` (`< 1/1885`), `vartheta_eq` (`= 4373943711/8125000000`), `vartheta_gt` (`> 78/145`),
`pair_gap` (`145/39 − 2/ϑ = 52426455/18953756081 > 0`).  All exact `ℚ`, `norm_num`; no floats.
`concreteParams_eq_repaired`, `agrees_with_v10`: these values are *definitionally* the V10 ones.
`smallBV θ r s := θ + r + s ≤ 1/2 − 10ζ` (`smallBV_iff_InBV`).

### §4 `EndpointCounterfixture` (permanent regression firewall)
Point `θ = 0, ν = 1/13, r = 14995777969/32500000000, s = 1/20`:
`point_in_support` (inside the old WF rectangle, `r ≤ r*(ν)`, `s ≤ s*(ν)`),
`point_not_smallBV` (`r + s = 16620777969/32500000000 > 1/2`, not `smallBV`),
`point_margin_negative` (old second margin `= −1161037617/65000000000 < 0`),
`top_corner_margin_positive`, **`endpointOnlyHBArgument_false`**, `topCorner_check_does_not_cover`
(the statement "checking the top corners covers the whole WF support" is refuted).

### §5 `CompatibleCellsConcrete`
Detector `n₁ ≡ α (mod |k|)`, `n₂ ≡ α (mod |k|d)`, `d = C q₁ q₂`.
`detectorClasses_card` (for `k ≠ 0` and fixed `n₁`: exactly `d` classes mod `|k|d`, not `|k|d`),
`mem_detectorClasses_iff`, `lift_injective` (the logical reason: the `n₁` congruence fixes `α` mod
`|k|`, leaving `d` lifts), `detector_n₂_compatible`, `old_count_wrong`, `saving_factor`, fixtures
`fixtureA_card`, `fixtureB_card`, `fixtureB_classes`, `old_count_fails_concrete` (with `|k| > 1`).
Reuses V10 `compatibleAlpha_card_eq_d`.

### §6–7 `RestoredTypeIIEnvelope`
Layer A: exponents `e1 e2 e3` and `e_eq_neg_g` / `term{1,2,3}_eq` (the three envelope terms equal
`x^{−g_i}` in exact exponent algebra).  Layer B: `envelope`, `envelope_le`, `envelope_nonneg`,
`cauchy_compatible_factor`.  Layer C: `structure RestoredTypeIISpectralProvider` with fields
`highH_bound`, `lowH_bound`, `diagonal_bound`; **`restoredTypeII_of_provider`** and
`caseII_powerSaving_of_provider` take it as an explicit hypothesis; no instance is created
(`spectralProvider_not_automatic`; `spectralProvider_zero` only shows the structure is consistent in
the zero model).  §7: `indexMap_concrete`, `lowH_index`, `highHNorm`, `lowHNorm`,
`leading_le_highHNorm`, **`prefactor_comparison`**
(`(P_lo/P_hi)² · (H N²)/(Q⁻² N² H²) = H/(C² Q²)`), **`lowH_cheaper`** (`H < Q²`, `1 ≤ C` ⇒
`H/(C²Q²) < 1`), **`diagonal_cheaper`** (`H/(C Q²) < 1`), and fixture `lowH_without_prefactor_fails`.

### §10 `TypeIIWholeRectangle`, `HBCaseII`
`g1_lower`, `g2_lower`, `g3_lower`: the three supplied lower bounds hold on the **entire** clipped
rectangle `0 ≤ r ≤ r*, 0 ≤ s ≤ s*`, `0 ≤ θ ≤ θ₀`, outside `smallBV` (proved by linear arithmetic
over the whole region, not by corner checks; `g1_is_affine`, `g1_bound_attained` document the
affine structure and sharpness).  **`worst_case_margins`** (`1/8 ≤ ν ≤ 1/4`):
`g1 ≥ 1/208`, `g2 ≥ 9/208 − θ₀`, `g3 ≥ 7/208`.  `nu_sub_s` (`ν − s ≥ ζ`), `s_sub_two_theta`
(`s − 2θ > 0`), `one_sub_pos` (`1 − 4θ − 2r − ν > 0`), `all_gaps_ge`.  `caseII_routed`,
`caseII_reaches_outside_BV`.

### §8 `HBSelectionConcrete`
**`concrete_selection`**: the trichotomy Case I / Case II / Case III is *proved* from the finite
factor data (V10 `HBData`), not assumed.  **Minimum classification hypothesis**: the smooth/Möbius
label of each factor with "Möbius exponents `≤ 1/4`" (`HBData.mobius_le`).
`mobius_label_is_minimal` shows that dropping it (or `∑ = 1`) breaks the trichotomy;
`selection_without_length_bound` shows `≤ 8` factors is not needed.  Fixtures for each case;
`caseIII_fixture_only` shows Case III is genuinely needed.

### §11 `HBCaseI`
`sI`, `rI`, `sI_add_rI`, `caseIRoute`, `rI_neg_no_box`, `rI_neg_iff`, `rapidDecay_margin`,
**`rapidDecay_declared_margin`** (`μ − θ − r − s ≥ ζ` for `r < θ`), `typeI_domain_facts`,
**`reserve`** (`μ − 3θ − s ≥ ζ`), **`caseI_routed`**, `mu_one_rapidDecay`.  See §0 item 4.

### §12 `HBCaseIII`
`B`, `dStar = min(λ, B)`, `dStar_eq_v10`, **`overlap`** (Type I on `r+s ≤ d*+ζ`, Type II on
`r+s ≥ d*−ζ`, overlap length `2ζ`), `g1_ge_of_ge_B`, `g1_ge_window_B`, `g1_ge_window_lam`,
**`g1_pos_on_typeII_window`**, `g1_ge_of_ge_dStar`, `g1_337_pos`, `typeI_level_reserve`,
`g1_337_fails_on_full_window`, `typeI_covers_all_in_lam_branch`, `g1_337_fails_in_lam_branch`.
See §0 items 1–3.

### §13–14 `HBFullSupportConcrete`
**`every_actual_HB_box_routed`**: every `ActualHBBox` (HB data, `θ ∈ [0, θ₀]`, `r, s ≥ 0`, the
explicit classification hypothesis, legal factorization bounds) lies in `smallBV ∨ InTypeI ∨
InTypeII`.  `every_actual_HB_box_routed_with_margins` attaches the proved margins.  The proof uses
only rational geometry and the classification hypothesis, which is always satisfiable
(`selection_available`).  `fixtureBox_routed`.
§14: **`wf_truncation_firewall`** (re-exports V10: well-factorable at level `D` does not imply an
arbitrary truncation is well-factorable at level `D'`) and `legal_cutoff_dataflow` (choose a legal
factorization at the original level, insert the product cutoff afterwards, separate it).

### §15 `RoughSeedConcrete`
`rho_z_identity` (`ρ_z = 1 * (μ · 1_{P⁺ ≤ z})`), `mu_rho_z_identity` (`μ * ρ_z = μ · 1_{P⁺≤z}`),
`rho_z_apply`, `mu_rho_z_apply` in the repository's `ArithmeticFunction` Dirichlet convolution.
`roughSeedSW_external`: the rough-seed Siegel–Walfisz estimate stays an external hypothesis.

### §16 `ConcreteAsymptoticGate`
**`mtSpecificAsymptotic_concrete`**: its hypotheses visibly include the frozen V9/V10 algebra, the
Type-I analytic provider (`SmoothTypeIInput`), `RestoredTypeIISpectralProvider` (one per Type-II
box), the ordinary BV provider, the rough-seed SW provider and the conductor/root/base provider;
conclusion: the concrete MT-specific asymptotic pair-distribution statement at
`ϑ = 7/13 − 3θ₀ − ε₀`.  **`exact_gate`**: `ϑ > 78/145` and `∃ ξ > 0, 2/ϑ + ξ < 145/39`.
`concrete_hypotheses_satisfiable` (consistency in the zero model only),
`composition_does_not_construct_constants` (V11 `currentConstants = none`, `current_M_an = none`).

### Ledger
`v12_preserves_v11_ledger` (embedded V11 ledger is a prefix of the V12 ledger and the embedding is
injective), `v11_finite_architecture_history_preserved` (the V11 row "finite architecture: OPEN" is
kept verbatim), `v12_frontier`, `v12New_no_closed`, `v12_leanBank_implies_kernel`,
`v12_external_not_kernel`, `no_ledger_path_closes_erdos287_v12`.

## 3. Status (V12)

| item | status |
|---|---|
| concrete repaired parameters, gates 78/145 and 145/39 | LEAN BANK |
| endpoint-only HB coverage claim | FALSE (finite fixture) |
| compatible-cell saving `d` | LEAN BANK (exact combinatorics) |
| restored Type-II spectral estimate | EXTERNAL PROVIDER |
| high/low-H prefactor & diagonal comparison | LEAN BANK |
| Case II whole-rectangle margins | LEAN BANK |
| HB three-way selection | LEAN BANK |
| Case I reserve, rapid-decay margin | LEAN BANK |
| frozen Type-I five domain margins | NOT SUPPLIED |
| Case III overlap, `g1 > 0` on Type-II window | LEAN BANK |
| Case III `(337/2)ζ` on `r+s ≥ d*` (branch `d* = B`) | LEAN BANK |
| Case III `(337/2)ζ` on full window / in `d* = λ` branch | FALSE (finite fixtures) |
| Case III `G5 ≥ 19ζ` | NOT SUPPLIED |
| full HB support routing | LEAN BANK |
| rough-seed identities | LEAN BANK |
| rough-seed SW | EXTERNAL PROVIDER |
| concrete asymptotic composition | LEAN COMPOSITION FROM PROVIDERS |
| Erdős #287 | OPEN |

## 4. Build, axioms, checker

See the V13 report §6 for the combined build / leanchecker record (V13 imports V12).

* `lake build RequestProject.Erdos287.ResearchBankV12`: success, 8201 jobs, exit 0, no warnings in
  V12 files (9 warnings, all in pre-existing files).
* `lake env leanchecker RequestProject.Erdos287.ResearchBankV12`: exit 0, no output (2m30s).
* Full `lake build`: success, 8709 jobs (details in the V13 report §6).
* `AxiomAudit.lean` prints axioms for **all 126 V12 theorems**; union =
  `{propext, Classical.choice, Quot.sound}` (several use none).  No `sorryAx`, no
  `Lean.ofReduceBool`, no `Lean.trustCompiler`, no custom axiom.
* Token scan of the new files for `sorry, admit, axiom, unsafe, native_decide, bv_decide, opaque,
  implemented_by, debug.skipKernelTC`: occurrences only in comments/docstrings and in the
  `#print axioms` commands.

Erdős #287 remains OPEN.
