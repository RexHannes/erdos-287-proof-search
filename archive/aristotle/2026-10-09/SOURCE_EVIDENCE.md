# Source evidence — unchanged excerpts from archive (6)

Archive SHA-256: `83a78efe591391ce61e3c4b37937223291eade43cf5778369d651a9cc136564d`

Line numbers below refer to the ORIGINAL inner source file. These are source inspection, not fresh Lean build outputs.

## `ERDOS287_TOPLAYER_PACKAGE_REAUDIT.md`

SHA-256: `378119749cfddd049da745930777a9276d25807fe643e583853767830093b1fc`

Lines 1–34:

```text
   1: # Erdős #287 — top-layer / prime-power exclusion package: re-audit (2026-10-08)
   2: 
   3: This is not a claim that #287 is solved. It re-checks only the elementary structural package.
   4: 
   5: ## Files (no Lean source was changed in this audit)
   6: - `RequestProject/Erdos287/Defs.lean`: `topExp`, `topLayer`, and the computable `C`
   7: - `RequestProject/Erdos287/TopLayer.lean`
   8: - `RequestProject/Erdos287/Cnum.lean`
   9: - `RequestProject/Erdos287/Window.lean`
  10: - `RequestProject/Erdos287/Counterexample.lean`: the `Gap2CE` structure
  11: - `RequestProject/Erdos287/PrimeFree.lean`
  12: - `RequestProject/Erdos287/Blocker.lean`
  13: 
  14: ## Theorems, all proved
  15: | Item | Lean name |
  16: |---|---|
  17: | 1 | `Erdos287.topLayer_congruence` |
  18: | 2 | `Erdos287.topLayer_card_ne_one`, `Erdos287.topLayer_two_obstruction`, `Erdos287.topLayer_three_obstruction` |
  19: | 3 | `Erdos287.C_values` (by kernel `decide`), `Erdos287.C_seven_witness` (num of 1+1/2+1/3+1/4+1/5+1/7 = 1019/420 is 1019), `Erdos287.C_spec` (`C j` is the greatest numerator), `Erdos287.C_mono`; extra: `C_nine : C 9 = 7129` |
  20: | 4 | `Erdos287.primePower_window_exclusion` |
  21: | 5 | `Gap2CE.holes_isolated`, `Gap2CE.N_mem`, `Gap2CE.M_mem`, `Gap2CE.exp_lower`, `Gap2CE.exp_upper`, `Gap2CE.N_gt_M_div_eight` |
  22: | 6 | `Gap2CE.primeFree` (needs `8152 ≤ M`) |
  23: | 7 | `Gap2CE.blockerPair_contradiction`, and `Gap2CE.excludedPP_blockerPair` (the two holes come from excluded prime powers) |
  24: 
  25: ## Checks
  26: - `lake build` of the seven modules above succeeds. The only warning is the unused hypothesis `hqM` in the window theorem, which was kept because the statement asks for it.
  27: - `#print axioms` for every theorem above gives only `propext`, `Classical.choice` and `Quot.sound`. `C_values` uses no axioms.
  28: - These files contain no `sorry`, `admit`, `axiom`, `unsafe`, `implemented_by`, `native_decide` or `bv_decide`.
  29: - No statement failed, so there is no counterexample to report.
  30: 
  31: ## Formalization notes
  32: - The `Gap2CE` gap condition is: every `a ≠ max A` in `A` has `a+1 ∈ A` or `a+2 ∈ A`. This is the same as saying all consecutive gaps are `≤ 2`.
  33: - `C j` is computed exactly with rational arithmetic over sublists of `[1..j]`. It is linked to `Rat.num` by `numOf_eq_num`.
  34: - `primePower_window_exclusion` keeps the hypothesis `q ≤ M` from the requested statement, but the proof does not use it.
```

## `ERDOS287_PARAMETER_SOURCEFIT_JUNCTION_REPORT.md`

SHA-256: `7918d38aee07908219339cec1078c798338a075076fd818e755de441a271130f`

Lines 1–97:

```text
   1: # Erdős #287: closing the parameter and source-fit junction
   2: 
   3: **Erdős #287 is still open. This report does not claim Tail287, and provider-free `Tail287` is not declared.**
   4: 
   5: ## Verdicts
   6: - **PHYSICAL FACTORIZATION CLOSED**: proved for the actual source in the small-ε₀ regime `CritRegime`. Ordering-B composition: the source-exact identity is proved. The remaining analytic providers are stated in full below.
   7: - **EFFECTIVE ARITHMETIC CLOSED**: `lcm(1..h) ≤ 4^(h-1)` is proved for every h. Uniform hinge positivity and the finite-bank certification remain explicit, unproved inputs.
   8: 
   9: ## Priority 1: actual parameters (`Physical/Factorization/ActualParams.lean`)
  10: - `Dlow_eq_rpow_beta`: proves `D_low = X^β` with `β = 59ε₀/(100(1+ε₀+ε₀⁹))`.
  11: - `CritRegime S κ` is the regime `0<κ<10⁻⁵`, `T ≥ 100/κ`, `T ≥ 2`, `X > 1`. It is **not** arbitrary `Good`.
  12: - `critRegime_Tchoice`: `T = ⌈100/κ⌉₊+2` is a compatible fixed choice.
  13: - `beta_lt_kappa`: `β < κ/100`.
  14: - `Dlow_sq_le`: `D_low² ≤ X^{κ/2}`.
  15: - `CritCell S κ N` is the range `X^{3κ} ≤ N ≤ X^{1/3+κ/2}`. On it:
  16:   - `crit_N_lo` gives `X^{2κ} ≤ N/D_low`;
  17:   - `crit_N_hi` gives `N ≤ X^{1/3+κ}`;
  18:   - `atomParams_of_crit` gives `AtomParams S κ N`.
  19: 
  20: **Before and after**
  21: - Before:
  22:   ```
  23:   atom_factorization_clean (hA : AtomParams S δ N) (hlow : S.Dlow ^ 2 ≤ S.X ^ (δ / 2)) (hP) (hb) (hq)
  24:   ```
  25: - After:
  26:   ```
  27:   atom_factorization_actual (h : CritRegime S κ) (hN : CritCell S κ N) (hP) (hb) (hq)
  28:   ```
  29: - Removed hypotheses: `AtomParams S δ N` and `D_low² ≤ X^{δ/2}`. Here δ = κ.
  30: 
  31: ## Priority 2: source fit (`TypeII/ProviderDictionary.lean`)
  32: **Decision.** Prop. 5.2 is used only to produce the (5.3) factorization. The downstream trilinear input needs only:
  33: - one-bounded sequences supported on `q ≤ Q`, `s ≤ S`, `r ≤ R`;
  34: - the three boxed range conditions of spec §18.
  35: 
  36: The source supplies the factorization directly, so literal membership of `b∏q_i` in `𝒟⁺` is **not** retained as a blocker.
  37: 
  38: This reading rests on the spec's §18 description of what Prop. 4.4 consumes. Pascadi's full text is not in the repository.
  39: 
  40: **Proved**
  41: - `boxed_one`, `boxed_two`, `boxed_three` and `boxed_mono`.
  42: - `physCoefAtom_eq_dict`: the coefficient equals `σ·a₁(l)·(a₂*a₃)(r)`.
  43: - `physAtom_provider_contract`, which gives:
  44:   - one-boundedness;
  45:   - the supports `≤ Q = N X^{-κ}`, `≤ S = E₁` and `≤ R = E₂`;
  46:   - pairwise coprime supports;
  47:   - `|σ| ≤ |Γ|w`;
  48:   - the three boxed inequalities with ε = κ/2000.
  49: 
  50: ## Priority 3: Ordering-B composition (`TypeII/SourceComposed.lean`)
  51: - `scalarTypeII_eq_cells`: proves the exact identity `scalarTypeII = ∑_{J,P,χ} ∑_{i,i'<n} T(physCell …) + physUrem`. It preserves:
  52:   - the signs `(-1)^J` and the box multiplicities;
  53:   - the residue `c` mod `f` and `(A,B)`;
  54:   - Γ and the cutoff `lr<K`.
  55:   
  56:   The atom coefficient is selected before Cauchy.
  57: - `packet_typeII_eq_cells`: the same identity summed once over `Ξ = XiAll`. The designated pair is part of the packet index and is not summed again.
  58: - `physCell_contract`: the support, norm and size-range contract for each cell.
  59: 
  60: ## Remaining analytic providers (`TypeII/RemainingProviders.lean`, all unproved `Prop`s)
  61: - `PascadiCriticalCellProvider κ`: **Pascadi's beyond-half estimate** for the critical cells. The moduli go up to `X^{59/100}`, so this is not BV/BDH.
  62: - `OrdinaryBVUremProvider κ`: the `h_l U_r` part. Only `f·l` with `l ≤ X^{1/3}` carries a congruence, so this is **ordinary BV/BDH** range.
  63: - `SWSeq`: the Siegel–Walfisz hypothesis on α.
  64: - `scalarTypeII_bound_of_providers` is proved conditionally on the two providers.
  65: - Still outside this file: non-critical routing, Heath–Brown and partial summation from `R_Σ^P`, BaseSW, and the seven-block framework (existing names in `ERDOS287_MINIMAL_ANALYTIC_INTERFACE.md`).
  66: 
  67: ## Priority 4: effective arithmetic (`Effective/LcmBound.lean`, `Effective/V103Comparison.lean`)
  68: **lcm bound and log height**
  69: - `Lh_le_four_pow`: `lcm(1..h) ≤ 4^(h-1)` for every h. The proof uses Kummer's theorem via `Lh_dvd_Lh_mul_choose`.
  70: - `mul_Bh_lt_eight_pow`: `h·B_h < 8^h`.
  71: - `log_height`: `8^h ≤ M ⇒ h ≤ H_*(M)`.
  72: - `log_height_real` and `floor_log_le_Hstar`: `⌊log M/log 8⌋ ≤ H_*(M)`.
  73: 
  74: **Before and after**
  75: - Before:
  76:   ```
  77:   log_height_of_lcm_bound (hL : LcmBound3) (hM : 9 ^ h < M) : h ≤ Hstar M
  78:   ```
  79:   This is kept.
  80: - After:
  81:   ```
  82:   log_height_nine (hM : 9 ^ h < M) : h ≤ Hstar M
  83:   ```
  84: - Removed hypothesis: `LcmBound3`.
  85: 
  86: **V103 comparison.** V103's text is not in the repository, so only structural facts about the Lean definitions are proved:
  87: - multiplicity: `sbMeasure_prime_pow`;
  88: - support: `sbMeasure_eq_zero_of_not_dvd`;
  89: - normalization: `sbMeasure_sum` and `hingeT_le_two_mul_card`;
  90: - moving endpoint: `Hstar_mono`.
  91: 
  92: A literal comparison still needs V103's definitions.
  93: 
  94: ## Verification
  95: - `lake build RequestProject.Erdos287.SourceChain` succeeds (8146 jobs), as does `RequestProject.Erdos287.Effective.Audit`.
  96: - `JunctionAudit.lean` and `Effective/Audit.lean` run `#print axioms` on the composed theorems. All report only `propext`, `Classical.choice` and `Quot.sound`.
  97: - The new files contain no `sorry`, `axiom`, `native_decide`, `unsafe` or `implemented_by`.
```

## `RequestProject/Erdos287/Blocker.lean`

SHA-256: `e110d13ee05481b203bf38fd18ee52acea7936acbcc65be7629a34b43f73f983`

Lines 30–105:

```text
  30: /-! ## The excluded-prime-power predicate -/
  31: 
  32: /-- `ExcludedPP M q` : `q` is a prime power `p^e` (`e ≥ 1`) such that the largest
  33: reciprocal-sum numerator over subsets of `{1,…,⌊M/q⌋}` is `< p`.  By
  34: `primePower_window_exclusion`, no element of a reciprocal-sum-`1` set `A ⊆ [1,M]` is
  35: divisible by `q`. -/
  36: def ExcludedPP (M q : ℕ) : Prop :=
  37:   ∃ p e : ℕ, p.Prime ∧ 1 ≤ e ∧ q = p ^ e ∧ C (M / q) < (p : ℤ)
  38: 
  39: /-
  40: A prime power `r^e` is excluded whenever the window numerator bound at some
  41: `j ≥ ⌊M/r^e⌋` is below the base `r`.
  42: -/
  43: theorem excludedPP_of_le {M r e j : ℕ} (hr : r.Prime) (he : 1 ≤ e)
  44:     (hj : M / r ^ e ≤ j) (hC : C j < (r : ℤ)) : ExcludedPP M (r ^ e) := by
  45:   exact ⟨ r, e, hr, he, rfl, lt_of_le_of_lt ( C_mono hj ) hC ⟩
  46: 
  47: /-
  48: A prime `p` with `M/2 < p ≤ M` is excluded (`q = p`, window `⌊M/p⌋ = 1`,
  49: `C 1 = 1 < p`).
  50: -/
  51: theorem excludedPP_self_of_large {M p : ℕ} (hp : p.Prime) (hpM : p ≤ M)
  52:     (hM2 : M < 2 * p) : ExcludedPP M p := by
  53:   use p, 1;
  54:   exact ⟨ hp, by norm_num, by norm_num, by rw [ show M / p = 1 by exact Nat.le_antisymm ( Nat.le_of_lt_succ <| Nat.div_lt_of_lt_mul <| by linarith ) ( Nat.div_pos hpM hp.pos ) ] ; exact by have := Erdos287.C_one; norm_num at *; linarith [ hp.two_le ] ⟩
  55: 
  56: /-
  57: **Excluded prime powers are never denominators.**  If `ExcludedPP M q` and
  58: `q ∣ x`, then `x` cannot belong to a reciprocal-sum-`1` set `A ⊆ [1,M]`.
  59: -/
  60: theorem ExcludedPP.not_dvd_mem {M q : ℕ} (hq : ExcludedPP M q)
  61:     {A : Finset ℕ} (hpos : ∀ a ∈ A, 0 < a) (hAM : ∀ a ∈ A, a ≤ M)
  62:     (hsum : ∑ a ∈ A, (1 : ℚ) / a = 1) {x : ℕ} (hxA : x ∈ A) (hqx : q ∣ x) : False := by
  63:   obtain ⟨ p, e, hp, he, rfl, hpC ⟩ := hq;
  64:   apply primePower_window_exclusion A M p e hp hpos hAM hsum he (Nat.le_trans (Nat.le_of_dvd (hpos x hxA) hqx) (hAM x hxA)) hpC x hxA hqx
  65: 
  66: /-! ## Specialization to a gap-`≤2` counterexample -/
  67: 
  68: namespace Gap2CE
  69: 
  70: variable (ce : Gap2CE)
  71: 
  72: /-
  73: An excluded prime-power multiple is a hole of the counterexample.
  74: -/
  75: theorem notMem_of_excludedPP {q x : ℕ} (hq : ExcludedPP ce.M q) (hqx : q ∣ x) :
  76:     x ∉ ce.A := by
  77:   exact fun hx => ExcludedPP.not_dvd_mem hq ce.hpos (fun a ha => Finset.le_max' _ _ ha) ce.hsum hx hqx
  78: 
  79: /-
  80: **Reusable blocker pair.**  If `x, x+1 ∈ [N, M]`, `q₁` and `q₂` are excluded
  81: prime powers with `q₁ ∣ x` and `q₂ ∣ x+1`, then no `Gap2CE` exists.
  82: -/
  83: theorem excludedPP_blockerPair {x q₁ q₂ : ℕ}
  84:     (hx0 : ce.N ≤ x) (hx1 : x + 1 ≤ ce.M)
  85:     (hq1 : ExcludedPP ce.M q₁) (hq2 : ExcludedPP ce.M q₂)
  86:     (hd1 : q₁ ∣ x) (hd2 : q₂ ∣ x + 1) : False := by
  87:   exact ce.blockerPair_contradiction hx0 hx1 ( ce.notMem_of_excludedPP hq1 ( by simpa using hd1 ) ) ( ce.notMem_of_excludedPP hq2 ( by simpa using hd2 ) )
  88: 
  89: /-! ### Propagation rules -/
  90: 
  91: /-
  92: A hole at `n` inside `[N, M]` forces its right neighbour `n+1` into `A`.
  93: -/
  94: theorem forced_right {n : ℕ} (hn0 : ce.N ≤ n) (hn1 : n + 1 ≤ ce.M)
  95:     (hhole : n ∉ ce.A) : n + 1 ∈ ce.A := by
  96:   exact Or.resolve_left ( ce.holes_isolated n hn0 hn1 ) hhole
  97: 
  98: /-
  99: A hole at `n+1` inside `[N, M]` forces its left neighbour `n` into `A`.
 100: -/
 101: theorem forced_left {n : ℕ} (hn0 : ce.N ≤ n) (hn1 : n + 1 ≤ ce.M)
 102:     (hhole : n + 1 ∉ ce.A) : n ∈ ce.A := by
 103:   have := ce.holes_isolated n hn0 hn1; aesop;
 104: 
 105: end Gap2CE
```

## `RequestProject/Erdos287/ProblemStatement.lean`

SHA-256: `3a8fc68e8cf4e12a1518bd1f6c9a151f7d29049914f0fca197b0b27ed8026162`

Lines 4–68:

```text
   4: # Erdős Problem #287 — the exact problem statement
   5: 
   6: The published problem asks: for every finite strictly increasing sequence of integers
   7: 
   8:   `1 < n₁ < n₂ < ⋯ < n_k`  with  `∑ 1/nᵢ = 1`,
   9: 
  10: is some consecutive gap `n_{i+1} - n_i` at least `3`?
  11: 
  12: This file introduces the **exact** project-local predicate `Erdos287Counterexample A`
  13: describing a hypothetical counterexample and relates it to the broader historical
  14: compiler type `Gap2CE`:
  15: 
  16: * `Erdos287Counterexample` requires `2 ≤ A.card`, `1 < a` for every `a ∈ A`,
  17:   `∑_{a ∈ A} 1/a = 1` and all consecutive gaps `≤ 2`;
  18: * `Gap2CE` only requires positivity (`0 < a`), so it admits irrelevant objects such as
  19:   `A = {1}` (`gap2CE_one`, banked below as an explicit witness).  The two types are
  20:   therefore **not** equivalent; the bridge goes one way only
  21:   (`Erdos287Counterexample.toGap2CE`), which is the direction the reduction needs.
  22: 
  23: We also give the ordered-sequence formulation (`erdos287_seq_of_no_counterexample`),
  24: literally matching the public statement.
  25: -/
  26: 
  27: open scoped BigOperators
  28: 
  29: namespace Erdos287
  30: 
  31: /-- **The exact Erdős #287 counterexample predicate.**  A finite set `A` of integers `> 1`
  32: whose reciprocals sum to `1`, with at least two elements, in which every non-maximal
  33: element is followed within distance `2` (i.e. every consecutive gap of the sorted list of
  34: `A` is at most `2`). -/
  35: structure Erdos287Counterexample (A : Finset ℕ) : Prop where
  36:   /-- At least two denominators. -/
  37:   card_ge : 2 ≤ A.card
  38:   /-- Every denominator exceeds `1`. -/
  39:   one_lt : ∀ a ∈ A, 1 < a
  40:   /-- The reciprocals sum to `1`. -/
  41:   sum_one : ∑ a ∈ A, (1 : ℚ) / a = 1
  42:   /-- Every non-maximal element is followed within distance `2`. -/
  43:   gap_le_two : ∀ a ∈ A, (∃ b ∈ A, a < b) → (a + 1 ∈ A ∨ a + 2 ∈ A)
  44: 
  45: namespace Erdos287Counterexample
  46: 
  47: variable {A : Finset ℕ} (h : Erdos287Counterexample A)
  48: 
  49: include h
  50: 
  51: /-- The underlying set is nonempty. -/
  52: theorem nonempty : A.Nonempty := Finset.card_pos.1 (by have := h.card_ge; omega)
  53: 
  54: /-- **Bridge to the historical compiler type.**  Every exact counterexample is in
  55: particular a `Gap2CE`. -/
  56: def toGap2CE : Gap2CE where
  57:   A := A
  58:   hne := h.nonempty
  59:   hpos := fun a ha => lt_trans Nat.zero_lt_one (h.one_lt a ha)
  60:   hsum := h.sum_one
  61:   hgap := by
  62:     intro a ha hne
  63:     refine h.gap_le_two a ha ⟨A.max' h.nonempty, Finset.max'_mem _ _, ?_⟩
  64:     exact lt_of_le_of_ne (Finset.le_max' _ _ ha) hne
  65: 
  66: @[simp] theorem toGap2CE_A : (h.toGap2CE).A = A := rfl
  67: 
  68: @[simp] theorem toGap2CE_M : (h.toGap2CE).M = A.max' h.nonempty := rfl
```

Lines 104–150:

```text
 104: /-! ## Non-vacuity guards
 105: 
 106: The predicate is not accidentally unsatisfiable for trivial reasons: each family of fields
 107: is separately realisable, and it is only their *conjunction* that is at stake. -/
 108: 
 109: /-- `{2,3,4}` satisfies every field except the reciprocal-sum one (its sum is `13/12`). -/
 110: theorem sanity_gap_fields_satisfiable :
 111:     2 ≤ ({2, 3, 4} : Finset ℕ).card ∧ (∀ a ∈ ({2, 3, 4} : Finset ℕ), 1 < a) ∧
 112:       (∀ a ∈ ({2, 3, 4} : Finset ℕ), (∃ b ∈ ({2, 3, 4} : Finset ℕ), a < b) →
 113:         (a + 1 ∈ ({2, 3, 4} : Finset ℕ) ∨ a + 2 ∈ ({2, 3, 4} : Finset ℕ))) ∧
 114:       ∑ a ∈ ({2, 3, 4} : Finset ℕ), (1 : ℚ) / a = 13 / 12 := by
 115:   refine ⟨by decide, by decide, by decide, ?_⟩
 116:   norm_num
 117: 
 118: /-- `{2,3,6}` satisfies every field except the gap one (`3` and `6` are `3` apart). -/
 119: theorem sanity_sum_field_satisfiable :
 120:     2 ≤ ({2, 3, 6} : Finset ℕ).card ∧ (∀ a ∈ ({2, 3, 6} : Finset ℕ), 1 < a) ∧
 121:       ∑ a ∈ ({2, 3, 6} : Finset ℕ), (1 : ℚ) / a = 1 ∧
 122:       ¬ (∀ a ∈ ({2, 3, 6} : Finset ℕ), (∃ b ∈ ({2, 3, 6} : Finset ℕ), a < b) →
 123:         (a + 1 ∈ ({2, 3, 6} : Finset ℕ) ∨ a + 2 ∈ ({2, 3, 6} : Finset ℕ))) := by
 124:   refine ⟨by decide, by decide, ?_, by decide⟩
 125:   norm_num
 126: 
 127: 
 128: /-- The historical type `Gap2CE` is genuinely broader: `A = {1}` inhabits it.  (This is why
 129: the reduction is phrased against `Erdos287Counterexample` and only *maps into* `Gap2CE`.) -/
 130: def gap2CE_one : Gap2CE where
 131:   A := {1}
 132:   hne := ⟨1, by simp⟩
 133:   hpos := by intro a ha; simp at ha; omega
 134:   hsum := by simp
 135:   hgap := by
 136:     intro a ha hne
 137:     simp at ha
 138:     exact absurd (by simp [ha]) hne
 139: 
 140: /-- ... and it is not an exact counterexample. -/
 141: theorem not_erdos287Counterexample_one : ¬ Erdos287Counterexample {1} := by
 142:   intro h
 143:   have := h.one_lt 1 (by simp)
 144:   omega
 145: 
 146: /-! ## The ordered-sequence formulation -/
 147: 
 148: /-- **Public statement, ordered form.**  If no finite set is an `Erdos287Counterexample`,
 149: then every finite strictly increasing sequence `1 < n 0 < n 1 < ⋯ < n (k-1)` whose
 150: reciprocals sum to `1` has a consecutive gap of at least `3`. -/
```

## `RequestProject/Erdos287/CurrentTail/TailBoundary.lean`

SHA-256: `297fae3ade52cbee26c27abb8f358fed2303c4a2292794ef9d598e1c86233da0`

Lines 28–77:

```text
  28: namespace Erdos287.CurrentTail
  29: 
  30: open Erdos287 Erdos287.PostV71V87 Erdos287.PostV87V90R
  31: 
  32: /-- **The asymptotic tail statement** (existential onset). -/
  33: def Tail287Statement : Prop :=
  34:   ∃ M0 : ℕ, ∀ A : Finset ℕ, ∀ hA : Erdos287Counterexample A, A.max' hA.nonempty < M0
  35: 
  36: variable {ι : Type*}
  37: 
  38: /-- **Seven-block tail framework (structural input, status `Candidate`).** -/
  39: structure SevenBlockTailFramework (S : TailSourceFamily ι) : Prop where
  40:   scale : ∀ X0 : ℕ, ∃ M0 : ℕ, ∀ W : ExactWord, 1 < W.a → M0 ≤ W.M →
  41:     ∃ X ≥ X0, ∃ (K : ℕ) (C : AffineContactCompiler 7 2 K) (F : FiniteWeights) (H : ℕ),
  42:       SevenBlockMainTermDictionary F (blockCount C) ((S.T X).RSigmaP) (S.target X) ∧
  43:       ∀ t ∈ F.T, 0 < F.w t → WindowControl C W.a W.M H t
  44: 
  45: /-- **Framework + `R_Σ^P = o(𝒩_X I)` ⟹ asymptotic tail.** -/
  46: theorem tail_of_remainder_littleO (S : TailSourceFamily ι) (Fw : SevenBlockTailFramework S)
  47:     (h : IsLittleOTarget (fun X => (S.T X).RSigmaP) S.target) : Tail287Statement := by
  48:   obtain ⟨X0, hX0⟩ := h 1 one_pos
  49:   obtain ⟨M0, hM0⟩ := Fw.scale X0
  50:   refine ⟨M0, fun A hA => ?_⟩
  51:   by_contra hlt
  52:   push_neg at hlt
  53:   set W := ofCounterexample hA
  54:   have ha : 1 < W.a := ofCounterexample_one_lt_a hA
  55:   have hM : M0 ≤ W.M := by rw [ofCounterexample_M]; exact hlt
  56:   obtain ⟨X, hX, K, C, F, H, D, hctrl⟩ := hM0 W ha hM
  57:   have hR : |(S.T X).RSigmaP| ≤ S.target X := by simpa using hX0 X hX
  58:   exact seven_block_contact_false_of_remainder W C F D hR hctrl
  59: 
  60: /-- **Conditional tail theorem `Tail287_of_AnalyticProviders`.**  Kernel-proved implication
  61: from: the seven-block framework, the Ordering-B source dictionary, and the analytic providers
  62: (`MaynardE1Estimate`, `PascadiE2Printed`, `QuantitativeTH`, `BDHFamily`,
  63: `SpectatorMomentFamily`, `BaseSWProvider`, `AuxPieceProviders`).  NOT an unconditional result. -/
  64: theorem Tail287_of_AnalyticProviders (S : TailSourceFamily ι)
  65:     {θ σlo σhi δ A0 A θQ θR θH δ2 : ℝ} {B E : ℕ} {Q0 Q Xmax : ℕ → ℕ}
  66:     {Bf : ℕ → ℝ → ℝ → ℝ} {Cm : ℕ → ℝ}
  67:     (Fw : SevenBlockTailFramework S)
  68:     (D : OrderingBSourceDictionary S (MaynardE1Estimate θ σlo σhi δ B A0 A)
  69:       (PascadiE2Printed θQ θR θH δ2) (QuantitativeTH θQ θR θH δ2) (BDHFamily S Q0 Q Bf)
  70:       (SpectatorMomentFamily E Xmax Cm))
  71:     (hE1 : MaynardE1Estimate θ σlo σhi δ B A0 A)
  72:     (hE2p : PascadiE2Printed θQ θR θH δ2) (hE2q : QuantitativeTH θQ θR θH δ2)
  73:     (hBDH : BDHFamily S Q0 Q Bf) (hMom : SpectatorMomentFamily E Xmax Cm)
  74:     (hBase : BaseSWProvider S) (hAux : AuxPieceProviders S) :
  75:     Tail287Statement :=
  76:   tail_of_remainder_littleO S Fw
  77:     (RSigmaP_littleO_of_providers S D hE1 hE2p hE2q hBDH hMom hBase hAux)
```

## `RequestProject/Erdos287/SourceChain/Physical/Factorization/ActualParams.lean`

SHA-256: `e37e0f27e82500bb034ab58b165573864273f4a7a48b3e07128354d4894737dc`

Lines 1–100:

```text
   1: import RequestProject.Erdos287.SourceChain.Physical.TypeII.Constructed
   2: 
   3: /-!
   4: # Erdős #287 — discharging the actual physical atom parameters
   5: 
   6: **ERDŐS #287 REMAINS OPEN.  TAIL-287 IS NOT BANKED.**
   7: 
   8: The scalar levels are those of `Scalar/Weights.lean`:
   9: `D_low = D_int^{ε₀}`, `D_int = D_tot^{1/(1+ε₀+τ)}`, `D_tot = X^{59/100}`, `τ = ε₀⁹`, `ε₀ = 1/T`.
  10: 
  11: * `Dlow_eq_rpow_beta` — `D_low = X^β` with `β = 59 ε₀ / (100 (1 + ε₀ + ε₀⁹))` (proved, not
  12:   defined that way).
  13: * `CritRegime S κ` — the **small-`ε₀` regime** of `sources/physical_spec.md` §18 for the
  14:   critical-range parameter `κ`: `0 < κ < 10⁻⁵`, `T ≥ 100/κ` (and the standing `T ≥ 2`, `X > 1`).
  15:   This is **not** an arbitrary `ScalarParams.Good`.
  16: * `Tchoice κ = ⌈100/κ⌉₊ + 2` and `critRegime_Tchoice` — a compatible fixed `T` exists for every
  17:   `κ ∈ (0, 10⁻⁵)` and every `X > 1`.
  18: * `beta_lt_kappa` — `β < κ/100` in the regime.
  19: * `Dlow_sq_le` — `D_low² ≤ X^{κ/2}` in the regime (Pascadi `δ = κ`), **no hypothesis**.
  20: * `CritCell S κ N` — the actual critical individual-variable range
  21:   `X^{3κ} ≤ N ≤ X^{1/3+κ/2}`.
  22: * `atomParams_of_crit` — every `AtomParams` field for `δ = κ`, in particular
  23:   `X^{2δ} ≤ N / D_low` and `N ≤ X^{1/3+δ}`.
  24: * `atom_factorization_actual` — `atom_factorization_clean` for the actual source with **both**
  25:   former parameter hypotheses (`AtomParams S δ N` and `D_low² ≤ X^{δ/2}`) discharged.
  26: -/
  27: 
  28: open Finset Real
  29: 
  30: set_option autoImplicit false
  31: 
  32: namespace Erdos287.Physical.Sieve.ScalarParams
  33: 
  34: open Erdos287.Physical.Factor
  35: 
  36: variable {S : ScalarParams}
  37: 
  38: /-- `β = 59 ε₀ / (100 (1 + ε₀ + ε₀⁹))`, the exponent of `D_low`. -/
  39: noncomputable def beta (S : ScalarParams) : ℝ :=
  40:   59 * S.eps0 / (100 * (1 + S.eps0 + S.eps0 ^ 9))
  41: 
  42: /-- **`D_low = X^β`**. -/
  43: theorem Dlow_eq_rpow_beta (hS : S.Good) : S.Dlow = S.X ^ S.beta := by
  44:   have hX : 0 ≤ S.X := by linarith [hS.X_gt]
  45:   have he := expo_pos hS
  46:   unfold Dlow Dint Dtot beta
  47:   rw [← Real.rpow_mul hX, ← Real.rpow_mul hX]
  48:   congr 1
  49:   unfold tau
  50:   field_simp
  51: 
  52: theorem beta_pos (hS : S.Good) : 0 < S.beta := by
  53:   unfold beta
  54:   have := eps0_pos hS
  55:   positivity
  56: 
  57: theorem beta_le (hS : S.Good) : S.beta ≤ 59 / 100 * S.eps0 := by
  58:   unfold beta
  59:   have he := eps0_pos hS
  60:   have h9 : 0 ≤ S.eps0 ^ 9 := by positivity
  61:   rw [div_le_iff₀ (by positivity)]
  62:   nlinarith
  63: 
  64: /-- **The small-`ε₀` regime** for the critical-range parameter `κ`. -/
  65: structure CritRegime (S : ScalarParams) (κ : ℝ) : Prop where
  66:   good : S.Good
  67:   κ_pos : 0 < κ
  68:   κ_small : κ < 1 / 100000
  69:   T_large : 100 / κ ≤ (S.T : ℝ)
  70: 
  71: /-- A compatible fixed choice of `T` for `κ`. -/
  72: noncomputable def Tchoice (κ : ℝ) : ℕ := ⌈100 / κ⌉₊ + 2
  73: 
  74: /-- **Existence of a compatible `T`**: for every `κ ∈ (0, 10⁻⁵)` and every `X > 1`, the
  75: parameters `(X, Tchoice κ)` lie in the regime. -/
  76: theorem critRegime_Tchoice {κ X : ℝ} (hκ : 0 < κ) (hκ' : κ < 1 / 100000) (hX : 1 < X) :
  77:     CritRegime ⟨X, Tchoice κ⟩ κ := by
  78:   refine ⟨⟨show 2 ≤ Tchoice κ by unfold Tchoice; omega, hX⟩, hκ, hκ', ?_⟩
  79:   show 100 / κ ≤ ((⌈100 / κ⌉₊ + 2 : ℕ) : ℝ)
  80:   push_cast
  81:   linarith [Nat.le_ceil (100 / κ)]
  82: 
  83: theorem eps0_le_of_regime {κ : ℝ} (h : CritRegime S κ) : S.eps0 ≤ κ / 100 := by
  84:   have hT := T_pos h.good
  85:   have hκ := h.κ_pos
  86:   unfold eps0
  87:   rw [div_le_div_iff₀ hT (by norm_num)]
  88:   have := h.T_large
  89:   rw [div_le_iff₀ hκ] at this
  90:   linarith
  91: 
  92: /-- **`β < κ/100`** in the small-`ε₀` regime. -/
  93: theorem beta_lt_kappa {κ : ℝ} (h : CritRegime S κ) : S.beta < κ / 100 := by
  94:   have h1 := beta_le h.good
  95:   have h2 := eps0_le_of_regime h
  96:   have := h.κ_pos
  97:   nlinarith
  98: 
  99: /-- **`D_low² ≤ X^{κ/2}`** (no hypothesis beyond the regime). -/
 100: theorem Dlow_sq_le {κ : ℝ} (h : CritRegime S κ) : S.Dlow ^ 2 ≤ S.X ^ (κ / 2) := by
```

## `RequestProject/Erdos287/SourceChain/Physical/TypeII/ProviderDictionary.lean`

SHA-256: `3243145913607881159bae9ccc386197b032c1a6958ed4ea84f9dba549fede1c`

Lines 155–196:

```text
 155: /-- **Coefficient dictionary** of the constructed Type-II coefficient. -/
 156: theorem physCoefAtom_eq_dict (δ N Γ : ℝ) (f J : ℕ) (P : Fin J → Fin S.H)
 157:     (χ : Fin S.Kc → Fin 3) (l r : ℕ) [Decidable (S.BoxAdm J P ∧ Nat.Coprime f (l * r))] :
 158:     physCoefAtom S δ N Γ f J P χ l r =
 159:       if S.BoxAdm J P ∧ Nat.Coprime f (l * r) then
 160:         (Γ * ((-1 : ℝ) ^ J * S.atomWeight J P (S.atomColour δ N J P))) *
 161:           S.lowFactor J P (S.atomColour δ N J P) χ l *
 162:           ∑ x ∈ r.divisorsAntidiagonal, S.colFactor J P (S.atomColour δ N J P) χ 1 x.1 *
 163:             S.colFactor J P (S.atomColour δ N J P) χ 2 x.2
 164:       else 0 := by
 165:   unfold physCoefAtom
 166:   split_ifs <;> simp [ArithmeticFunction.mul_apply, mul_assoc]
 167: 
 168: /-- **Provider contract of every admissible sector of an actual critical cell.**
 169: With `Q = N X^{-κ}`, `S = E₁`, `R = E₂` (box-endpoint products of colours 1 and 2),
 170: the three one-bounded factor sequences have the stated supports, pairwise coprime supports,
 171: the sign/weight scalar is bounded by `|Γ| w`, and the three boxed range conditions hold
 172: with `ε = κ/2000`. -/
 173: theorem physAtom_provider_contract {κ N : ℝ} (h : CritRegime S κ) (hN : CritCell S κ N)
 174:     (Γ : ℝ) {J : ℕ} {P : Fin J → Fin S.H} (hP : S.BoxAdm J P) (χ : Fin S.Kc → Fin 3) :
 175:     let c := S.atomColour κ N J P
 176:     let Q := N * S.X ^ (-κ)
 177:     let Sb := cprod (S.boxVec J P) c 1 J
 178:     let R := cprod (S.boxVec J P) c 2 J
 179:     -- one-boundedness
 180:     (∀ n, |S.lowFactor J P c χ n| ≤ 1) ∧ (∀ n, |S.colFactor J P c χ 1 n| ≤ 1) ∧
 181:       (∀ n, |S.colFactor J P c χ 2 n| ≤ 1) ∧
 182:     -- supports
 183:       (∀ n, S.lowFactor J P c χ n ≠ 0 → (n : ℝ) ≤ Q) ∧
 184:       (∀ n, S.colFactor J P c χ 1 n ≠ 0 → (n : ℝ) ≤ Sb) ∧
 185:       (∀ n, S.colFactor J P c χ 2 n ≠ 0 → (n : ℝ) ≤ R) ∧
 186:     -- coprime supports
 187:       (∀ a s, S.lowFactor J P c χ a ≠ 0 → S.colFactor J P c χ 1 s ≠ 0 → Nat.Coprime a s) ∧
 188:       (∀ a t, S.lowFactor J P c χ a ≠ 0 → S.colFactor J P c χ 2 t ≠ 0 → Nat.Coprime a t) ∧
 189:       (∀ s t, S.colFactor J P c χ 1 s ≠ 0 → S.colFactor J P c χ 2 t ≠ 0 → Nat.Coprime s t) ∧
 190:     -- scalar
 191:       |Γ * ((-1 : ℝ) ^ J * S.atomWeight J P c)| ≤ |Γ| * S.atomWeight J P c ∧
 192:     -- boxed range conditions
 193:       N ^ 2 * R ^ 2 * Sb ≤ S.X ^ (1 - 8 * (κ / 2000)) ∧
 194:       N ^ ((71 : ℝ) / 50) * R * Sb ^ ((93 : ℝ) / 50) ≤ S.X ^ (1 - 16 * (κ / 2000)) ∧
 195:       N ^ ((39 : ℝ) / 25) * Q ^ ((11 : ℝ) / 25) * R ^ 2 * Sb ^ 5 ≤
 196:         S.X ^ (2 - 32 * (κ / 2000)) := by
```

## `RequestProject/Erdos287/SourceChain/Physical/TypeII/SourceComposed.lean`

SHA-256: `558f3355be7c61ae0e07a43fa877f158870077e9139f78e607e4a6663438c0fd`

Lines 39–77:

```text
  39: open Classical in
  40: /-- The residue mask `1_{v ≡ c (mod f)}`. -/
  41: noncomputable def resMask (f c v : ℕ) : ℝ := if v ≡ c [MOD f] then 1 else 0
  42: 
  43: variable (S : ScalarParams)
  44: 
  45: open Classical in
  46: /-- **The scalar Type-II source of one packet.** -/
  47: noncomputable def scalarTypeII (Γ : ℝ) (f c A : ℕ) (B : ℤ) (K K' : ℕ)
  48:     (α β : ArithmeticFunction ℝ) : ℝ :=
  49:   Γ * ∑ d ∈ Ico 1 K, if Nat.Coprime f d then
  50:     S.ellX d * ∑ v ∈ range K', (α * β) v * (resMask f c v * (Iz A B d v - Uz d v)) else 0
  51: 
  52: /-- The constructed atom coefficient with the source cutoff `l r < K`. -/
  53: noncomputable def physCoefCut (δ N Γ : ℝ) (f K J : ℕ) (P : Fin J → Fin S.H)
  54:     (χ : Fin S.Kc → Fin 3) (l r : ℕ) : ℝ :=
  55:   if l * r < K then physCoefAtom S δ N Γ f J P χ l r else 0
  56: 
  57: /-- **The actual Ordering-B cell** of the atom `(J, P, χ)` at scales `(L, R, N_n, M)`. -/
  58: noncomputable def physCell (δ N Γ : ℝ) (f c A : ℕ) (B : ℤ) (K L R Nn M J : ℕ)
  59:     (P : Fin J → Fin S.H) (χ : Fin S.Kc → Fin 3) (α β : ArithmeticFunction ℝ) : OBData where
  60:   f := f
  61:   c := c
  62:   A := A
  63:   B := B
  64:   L := L
  65:   R := R
  66:   N := Nn
  67:   M := M
  68:   coef := physCoefCut S δ N Γ f K J P χ
  69:   alpha := α
  70:   beta := β
  71: 
  72: /-- The `h_l U_r` part of the exact Type-II split. -/
  73: noncomputable def physUrem (δ N Γ : ℝ) (f c A : ℕ) (B : ℤ) (K K' : ℕ)
  74:     (α β : ArithmeticFunction ℝ) : ℝ :=
  75:   ∑ J ∈ range (S.T ^ 2 + 1), ∑ P : Fin J → Fin S.H, ∑ χ : Fin S.Kc → Fin 3,
  76:     ∑ l ∈ Ico 1 K, ∑ r ∈ Ico 1 K, physCoefCut S δ N Γ f K J P χ l r *
  77:       ∑ v ∈ range K', (α * β) v * (resMask f c v * (hz A B l v * Uz r v))
```

Lines 118–139:

```text
 118: open Classical in
 119: /-- **Exact composed Type-II source identity for one packet.** -/
 120: theorem scalarTypeII_eq_cells (hS : S.Good) (δ N Γ : ℝ) (f c A : ℕ) (B : ℤ) {K n : ℕ}
 121:     (hKn : K ≤ 2 ^ n) {Nn M K' : ℕ} (α β : ArithmeticFunction ℝ)
 122:     (hα : ∀ m, α m ≠ 0 → Nn ≤ m ∧ m < 2 * Nn) (hβ : ∀ m, β m ≠ 0 → M ≤ m ∧ m < 2 * M)
 123:     (hK' : 4 * Nn * M ≤ K') :
 124:     scalarTypeII S Γ f c A B K K' α β =
 125:       ∑ J ∈ range (S.T ^ 2 + 1), ∑ P : Fin J → Fin S.H, ∑ χ : Fin S.Kc → Fin 3,
 126:         ∑ i ∈ range n, ∑ i' ∈ range n,
 127:           (physCell S δ N Γ f c A B K (2 ^ i) (2 ^ i') Nn M J P χ α β).T +
 128:       physUrem S δ N Γ f c A B K K' α β := by
 129:   set w : ℕ → ℝ := fun v => (α * β) v * resMask f c v with hw
 130:   -- Step A: move the `v`-sum outside
 131:   have hA : scalarTypeII S Γ f c A B K K' α β = ∑ v ∈ range K', w v *
 132:       (Γ * ∑ d ∈ Ico 1 K, if Nat.Coprime f d then S.ellX d * (Iz A B d v - Uz d v) else 0) := by
 133:     unfold scalarTypeII
 134:     rw [mul_sum]
 135:     have : ∀ d ∈ Ico 1 K, Γ * (if Nat.Coprime f d then S.ellX d *
 136:         ∑ v ∈ range K', (α * β) v * (resMask f c v * (Iz A B d v - Uz d v)) else 0) =
 137:         ∑ v ∈ range K', w v * (Γ * (if Nat.Coprime f d then
 138:           S.ellX d * (Iz A B d v - Uz d v) else 0)) := by
 139:       intro d _
```

Lines 180–220:

```text
 180:   refine sum_congr rfl (fun v _ => ?_)
 181:   simp only [physCoefCut, hw]
 182:   split_ifs <;> ring
 183: 
 184: /-- **Packet-level composed identity**: the scalar Type-II sources of all labelled packets
 185: `ξ ∈ Ξ`, each with its actual `Γ_ξ`, `f_ξ`, `c_ξ`, `A_ξ`, `B_ξ`, summed **once** over `Ξ`, equal
 186: the sum of the actual Ordering-B cells plus the `h_l U_r` parts.  The designated pair
 187: `(j(ξ), ℓ(ξ))` is part of the packet index; no further sum over designated coordinates occurs. -/
 188: theorem packet_typeII_eq_cells (Pd : PhysData) (hS : S.Good) (δ : ℝ)
 189:     (N : Packet Pd.k → ℝ) {K n : ℕ} (hKn : K ≤ 2 ^ n) (Nn M K' : Packet Pd.k → ℕ)
 190:     (α β : Packet Pd.k → ArithmeticFunction ℝ)
 191:     (hα : ∀ ξ m, α ξ m ≠ 0 → Nn ξ ≤ m ∧ m < 2 * Nn ξ)
 192:     (hβ : ∀ ξ m, β ξ m ≠ 0 → M ξ ≤ m ∧ m < 2 * M ξ) (hK' : ∀ ξ, 4 * Nn ξ * M ξ ≤ K' ξ) :
 193:     ∑ ξ ∈ Pd.XiAll, scalarTypeII S (Pd.Gamma ξ) (Pd.f ξ) (Pd.cRes ξ) (Pd.A ξ) (Pd.B ξ) K (K' ξ)
 194:         (α ξ) (β ξ) =
 195:       ∑ ξ ∈ Pd.XiAll,
 196:         ((∑ J ∈ range (S.T ^ 2 + 1), ∑ P : Fin J → Fin S.H, ∑ χ : Fin S.Kc → Fin 3,
 197:           ∑ i ∈ range n, ∑ i' ∈ range n,
 198:             (physCell S δ (N ξ) (Pd.Gamma ξ) (Pd.f ξ) (Pd.cRes ξ) (Pd.A ξ) (Pd.B ξ) K (2 ^ i)
 199:               (2 ^ i') (Nn ξ) (M ξ) J P χ (α ξ) (β ξ)).T) +
 200:           physUrem S δ (N ξ) (Pd.Gamma ξ) (Pd.f ξ) (Pd.cRes ξ) (Pd.A ξ) (Pd.B ξ) K (K' ξ)
 201:             (α ξ) (β ξ)) :=
 202:   sum_congr rfl (fun ξ _ => scalarTypeII_eq_cells hS δ (N ξ) _ _ _ _ _ hKn (α ξ) (β ξ)
 203:     (hα ξ) (hβ ξ) (hK' ξ))
 204: 
 205: /-- **Contract of every actual critical Type-II cell** (`δ = κ`, `N = N_n`). -/
 206: theorem physCell_contract {κ : ℝ} (h : CritRegime S κ) {Nn : ℕ} (hN : CritCell S κ Nn)
 207:     (Γ : ℝ) (f c A : ℕ) (B : ℤ) (K L R M J : ℕ) (P : Fin J → Fin S.H) (χ : Fin S.Kc → Fin 3)
 208:     (α β : ArithmeticFunction ℝ) :
 209:     let D := physCell S κ Nn Γ f c A B K L R Nn M J P χ α β
 210:     let col := S.atomColour κ Nn J P
 211:     let Q := (Nn : ℝ) * S.X ^ (-κ)
 212:     let Sb := cprod (S.boxVec J P) col 1 J
 213:     let Rb := cprod (S.boxVec J P) col 2 J
 214:     (∀ l r, |D.coef l r| ≤ |Γ| * S.atomWeight J P col) ∧
 215:       (∀ l r, D.coef l r ≠ 0 → S.BoxAdm J P ∧ Nat.Coprime l r ∧ Nat.Coprime f (l * r) ∧
 216:         l * r < K ∧ (l : ℝ) ≤ Q ∧ ∃ a₂ a₃ : ℕ, a₂ * a₃ = r ∧ (a₂ : ℝ) ≤ Sb ∧ (a₃ : ℝ) ≤ Rb) ∧
 217:       (S.BoxAdm J P →
 218:         (Nn : ℝ) ^ 2 * Rb ^ 2 * Sb ≤ S.X ^ (1 - 8 * (κ / 2000)) ∧
 219:         (Nn : ℝ) ^ ((71 : ℝ) / 50) * Rb * Sb ^ ((93 : ℝ) / 50) ≤ S.X ^ (1 - 16 * (κ / 2000)) ∧
 220:         (Nn : ℝ) ^ ((39 : ℝ) / 25) * Q ^ ((11 : ℝ) / 25) * Rb ^ 2 * Sb ^ 5 ≤
```

## `RequestProject/Erdos287/SourceChain/Physical/TypeII/RemainingProviders.lean`

SHA-256: `d56fc19e5a58336b84464943d57acdae3703a7013d84a6978f476409a4b192ea`

Lines 3–77:

```text
   3: /-!
   4: # Erdős #287 — remaining analytic providers for the actual Type-II source
   5: 
   6: **ERDŐS #287 REMAINS OPEN.  TAIL-287 IS NOT BANKED.  Nothing in this file is proved about
   7: primes: every `def … : Prop` below is an UNPROVED analytic input, stated in full.**
   8: 
   9: The source side is closed by `scalarTypeII_eq_cells` / `physCell_contract`.  What remains for
  10: the *critical* Type-II part of the actual source is:
  11: 
  12: * `PascadiCriticalCellProvider κ` — **Pascadi's beyond-half estimate** for the actual critical
  13:   cells.  The moduli `l r` reach `D_tot = X^{59/100} > X^{1/2}`, so ordinary BV/BDH does **not**
  14:   supply it.
  15: * `OrdinaryBVUremProvider κ` — the `h_l U_r` part: only the modulus `f l` with
  16:   `l ≤ N X^{-κ} ≤ X^{1/3}` carries a congruence, so this is an **ordinary** BV/BDH-range input
  17:   (level below `1/2`).
  18: * `SWSeq` — the Siegel–Walfisz condition on the smooth-variable sequence `α`, used as a
  19:   hypothesis inside `PascadiCriticalCellProvider` (as in every Bombieri–Vinogradov-type
  20:   bilinear estimate).
  21: 
  22: `scalarTypeII_bound_of_cells` is the kernel-proved composition: per-atom cell bounds plus a bound
  23: on `physUrem` give a bound on the scalar Type-II source, with the atom total variation
  24: `∑_{J ≤ T²} H^J 3^J` (independent of `X`).  `scalarTypeII_bound_of_providers` instantiates it
  25: with the two providers.
  26: -/
  27: 
  28: open Finset Real
  29: 
  30: set_option autoImplicit false
  31: 
  32: namespace Erdos287.Physical.TypeII
  33: 
  34: open Erdos287.Physical.Sieve Erdos287.Physical.Sieve.ScalarParams Erdos287.Physical.Factor
  35: 
  36: open Classical in
  37: /-- Siegel–Walfisz condition for a sequence supported on `[N, 2N)`, moduli `q ≤ (log N)^B`. -/
  38: def SWSeq (α : ArithmeticFunction ℝ) (Nn : ℕ) (Aexp B C : ℝ) : Prop :=
  39:   ∀ q a : ℕ, 0 < q → (q : ℝ) ≤ Real.log Nn ^ B → Nat.Coprime a q →
  40:     |∑ n ∈ range (2 * Nn), (if n ≡ a [MOD q] then α n else 0) -
  41:       (1 / (Nat.totient q : ℝ)) * ∑ n ∈ range (2 * Nn), (if Nat.Coprime n q then α n else 0)|
  42:       ≤ C * Nn / Real.log Nn ^ Aexp
  43: 
  44: /-- **(UNPROVED) Pascadi's beyond-half estimate, at the actual critical Type-II cells.**
  45: For every saving exponent `A` and every Siegel–Walfisz constant `C_SW` there are a
  46: Siegel–Walfisz strength `A'`, a modulus range `(log N)^B`, and `C, X₀` such that for every scalar parameter set in the
  47: small-`ε₀` regime of `κ`, every critical cell `N_n`, `N_n M ≤ X`, every packet modulus
  48: `f ≤ X^{κ/1000}` with `(c, f) = 1`, every sequence pair `α ∼ N_n`, `β ∼ M` with `|α| ≤ B_α`,
  49: `|β| ≤ B_β` and `α` Siegel–Walfisz, and every admissible sector `(J, P)` and colouring `χ`,
  50: the dyadically summed cells of the atom are bounded by
  51: `C B_α B_β |Γ| w_{J,P} X / (f (log X)^A)`. -/
  52: def PascadiCriticalCellProvider (κ : ℝ) : Prop :=
  53:   ∀ Aexp Csw : ℝ, ∃ A' B C X0 : ℝ, ∀ S : ScalarParams, CritRegime S κ → X0 ≤ S.X →
  54:     ∀ Nn M : ℕ, CritCell S κ Nn → (Nn : ℝ) * M ≤ S.X →
  55:     ∀ (Γ : ℝ) (f c A : ℕ) (Bres : ℤ) (K n : ℕ), K ≤ 2 ^ n → 0 < f → (f : ℝ) ≤ S.X ^ (κ / 1000) →
  56:     Nat.Coprime c f →
  57:     ∀ (α β : ArithmeticFunction ℝ) (Bα Bβ : ℝ), (∀ m, |α m| ≤ Bα) → (∀ m, |β m| ≤ Bβ) →
  58:     (∀ m, α m ≠ 0 → Nn ≤ m ∧ m < 2 * Nn) → (∀ m, β m ≠ 0 → M ≤ m ∧ m < 2 * M) →
  59:     SWSeq α Nn A' B (Csw * Bα) →
  60:     ∀ (J : ℕ) (P : Fin J → Fin S.H) (χ : Fin S.Kc → Fin 3), S.BoxAdm J P →
  61:       |∑ i ∈ range n, ∑ i' ∈ range n,
  62:           (physCell S κ Nn Γ f c A Bres K (2 ^ i) (2 ^ i') Nn M J P χ α β).T| ≤
  63:         C * Bα * Bβ * |Γ| * S.atomWeight J P (S.atomColour κ Nn J P) * S.X /
  64:           (f * Real.log S.X ^ Aexp)
  65: 
  66: /-- **(UNPROVED) Ordinary BV/BDH-range bound for the `h_l U_r` part** of the actual
  67: critical Type-II source (only `f l`, `l ≤ X^{1/3}`, carries a congruence). -/
  68: def OrdinaryBVUremProvider (κ : ℝ) : Prop :=
  69:   ∀ Aexp : ℝ, ∃ C X0 : ℝ, ∀ S : ScalarParams, CritRegime S κ → X0 ≤ S.X →
  70:     ∀ Nn M : ℕ, CritCell S κ Nn → (Nn : ℝ) * M ≤ S.X →
  71:     ∀ (Γ : ℝ) (f c A : ℕ) (Bres : ℤ) (K K' : ℕ), 0 < f → (f : ℝ) ≤ S.X ^ (κ / 1000) →
  72:     Nat.Coprime c f →
  73:     ∀ (α β : ArithmeticFunction ℝ) (Bα Bβ : ℝ), (∀ m, |α m| ≤ Bα) → (∀ m, |β m| ≤ Bβ) →
  74:     (∀ m, α m ≠ 0 → Nn ≤ m ∧ m < 2 * Nn) → (∀ m, β m ≠ 0 → M ≤ m ∧ m < 2 * M) →
  75:       |physUrem S κ Nn Γ f c A Bres K K' α β| ≤
  76:         C * Bα * Bβ * |Γ| * (∑ J ∈ range (S.T ^ 2 + 1), (S.H : ℝ) ^ J * 3 ^ J) * S.X /
  77:           (f * Real.log S.X ^ Aexp)
```

Lines 135–188:

```text
 135: 
 136: /-- **The actual critical scalar Type-II source under the two named providers.**
 137: For every `A` and `C_SW` there are `A', B, C, X₀` such that, in the small-`ε₀` regime and on critical cells,
 138: `|scalarTypeII| ≤ C B_α B_β |Γ| (∑_{J ≤ T²} H^J 3^J) X / (f (log X)^A)`. -/
 139: theorem scalarTypeII_bound_of_providers {κ : ℝ} (hP4 : PascadiCriticalCellProvider κ)
 140:     (hBV : OrdinaryBVUremProvider κ) (Aexp Csw : ℝ) :
 141:     ∃ A' B C X0 : ℝ, ∀ S : ScalarParams, CritRegime S κ → X0 ≤ S.X →
 142:     ∀ Nn M : ℕ, CritCell S κ Nn → (Nn : ℝ) * M ≤ S.X →
 143:     ∀ (Γ : ℝ) (f c A : ℕ) (Bres : ℤ) (K n K' : ℕ), K ≤ 2 ^ n → 4 * Nn * M ≤ K' → 0 < f →
 144:     (f : ℝ) ≤ S.X ^ (κ / 1000) → Nat.Coprime c f →
 145:     ∀ (α β : ArithmeticFunction ℝ) (Bα Bβ : ℝ), (∀ m, |α m| ≤ Bα) → (∀ m, |β m| ≤ Bβ) →
 146:     (∀ m, α m ≠ 0 → Nn ≤ m ∧ m < 2 * Nn) → (∀ m, β m ≠ 0 → M ≤ m ∧ m < 2 * M) →
 147:     SWSeq α Nn A' B (Csw * Bα) →
 148:       |scalarTypeII S Γ f c A Bres K K' α β| ≤
 149:         C * Bα * Bβ * |Γ| * (∑ J ∈ range (S.T ^ 2 + 1), (S.H : ℝ) ^ J * 3 ^ J) * S.X /
 150:           (f * Real.log S.X ^ Aexp) := by
 151:   obtain ⟨A', B, C1, X1, h1⟩ := hP4 Aexp Csw
 152:   obtain ⟨C2, X2, h2⟩ := hBV Aexp
 153:   refine ⟨A', B, |C1| + C2, max X1 X2, ?_⟩
 154:   intro S hreg hX Nn M hN hNM Γ f c A Bres K n K' hKn hK' hf0 hf hcf α β Bα Bβ hαb hβb hα hβ hsw
 155:   have hX1 : X1 ≤ S.X := le_trans (le_max_left _ _) hX
 156:   have hX2 : X2 ≤ S.X := le_trans (le_max_right _ _) hX
 157:   have hBα : 0 ≤ Bα := le_trans (abs_nonneg _) (hαb 0)
 158:   have hBβ : 0 ≤ Bβ := le_trans (abs_nonneg _) (hβb 0)
 159:   set E : ℝ := |C1| * Bα * Bβ * S.X / (f * Real.log S.X ^ Aexp) with hEdef
 160:   have hXpos : 0 < S.X := by linarith [hreg.good.X_gt]
 161:   have hlog : 0 ≤ Real.log S.X := Real.log_nonneg hreg.good.X_gt.le
 162:   have hden : 0 ≤ (f : ℝ) * Real.log S.X ^ Aexp :=
 163:     mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg hlog _)
 164:   have hE : 0 ≤ E := div_nonneg (by positivity) hden
 165:   have key := scalarTypeII_bound_of_cells hreg.good κ (Nn : ℝ) Γ f c A Bres hKn α β hα hβ hK'
 166:     hE (EU := C2 * Bα * Bβ * |Γ| * (∑ J ∈ range (S.T ^ 2 + 1), (S.H : ℝ) ^ J * 3 ^ J) * S.X /
 167:           (f * Real.log S.X ^ Aexp)) ?_ ?_
 168:   · refine key.trans (le_of_eq ?_)
 169:     simp only [hEdef]
 170:     ring
 171:   · intro J P χ hP
 172:     refine (h1 S hreg hX1 Nn M hN hNM Γ f c A Bres K n hKn hf0 hf hcf α β Bα Bβ hαb hβb hα hβ hsw
 173:       J P χ hP).trans ?_
 174:     simp only [hEdef]
 175:     have hw := atomWeight_nonneg P (S.atomColour κ Nn J P)
 176:     rw [mul_div_assoc, mul_div_assoc]
 177:     have hq : 0 ≤ S.X / (f * Real.log S.X ^ Aexp) := div_nonneg hXpos.le hden
 178:     have : C1 * Bα * Bβ * |Γ| * S.atomWeight J P (S.atomColour κ Nn J P) ≤
 179:         |Γ| * S.atomWeight J P (S.atomColour κ Nn J P) * (|C1| * Bα * Bβ) := by
 180:       have hc : C1 ≤ |C1| := le_abs_self C1
 181:       have : 0 ≤ Bα * Bβ * |Γ| * S.atomWeight J P (S.atomColour κ Nn J P) := by positivity
 182:       nlinarith
 183:     calc C1 * Bα * Bβ * |Γ| * S.atomWeight J P (S.atomColour κ Nn J P) *
 184:           (S.X / (f * Real.log S.X ^ Aexp))
 185:         ≤ |Γ| * S.atomWeight J P (S.atomColour κ Nn J P) * (|C1| * Bα * Bβ) *
 186:           (S.X / (f * Real.log S.X ^ Aexp)) := mul_le_mul_of_nonneg_right this hq
 187:       _ = _ := by ring
 188:   · exact h2 S hreg hX2 Nn M hN hNM Γ f c A Bres K K' hf0 hf hcf α β Bα Bβ hαb hβb hα hβ
```

## `RequestProject/Erdos287/SourceChain/Physical/Tail.lean`

SHA-256: `3125376a8574983234bad70df780c87674f12964c2bce5abb3b92838e578e79f`

Lines 29–40:

```text
  29: namespace Erdos287.Physical
  30: 
  31: open Erdos287 Erdos287.PostV71V87 Erdos287.PostV87V90R Erdos287.CurrentTail
  32:   Erdos287.SourceChain
  33: 
  34: /-- The one-sided seven-block framework, for an arbitrary remainder function `R`. -/
  35: structure OneSidedFrameworkFor (R target : ℕ → ℝ) : Prop where
  36:   errors : ∃ e₁ e₂ : ℕ → ℝ, (∀ ε > 0, ∃ X0 : ℕ, ∀ X ≥ X0, e₁ X ≤ ε ∧ e₂ X ≤ ε) ∧
  37:     ∀ X0 : ℕ, ∃ M0 : ℕ, ∀ W : ExactWord, 1 < W.a → M0 ≤ W.M →
  38:       ∃ X ≥ X0, ∃ (K : ℕ) (C : AffineContactCompiler 7 2 K) (F : FiniteWeights) (H : ℕ),
  39:         OneSidedSevenBlockDictionary F (blockCount C) (e₁ X) (e₂ X) (R X) (target X) ∧
  40:         ∀ t ∈ F.T, 0 < F.w t → WindowControl C W.a W.M H t
```

Lines 69–125:

```text
  69: /-- The physical data at scale `X`: fixed slopes/test function from `P₀`, scale `X`, and the
  70: actual presieve modulus `W = physW X`. -/
  71: noncomputable def physDataAt (P₀ : PhysData) (X : ℕ) : PhysData :=
  72:   { P₀ with W := physW X, X := X }
  73: 
  74: /-- The presieve hypotheses hold at the physical `W` for all large `X`. -/
  75: theorem physDataAt_wgood (P₀ : PhysData) (ha : ∀ i, 0 < P₀.a i)
  76:     (hinj : Function.Injective P₀.a) : ∃ X0 : ℕ, ∀ X ≥ X0, (physDataAt P₀ X).WGood := by
  77:   obtain ⟨Y0, hY0⟩ := wgood_eventually P₀ ha hinj
  78:   refine ⟨⌈Y0⌉₊, fun X hX => ?_⟩
  79:   have hX' : Y0 ≤ (X : ℝ) := (Nat.le_ceil Y0).trans (by exact_mod_cast hX)
  80:   have h := hY0 X hX'
  81:   exact ⟨h.a_pos, h.W_pos, h.slope, h.diff⟩
  82: 
  83: /-- A scale-indexed physical source: physical data and scalar sieve at each scale, with the
  84: normalisation `target X = 𝒩_X I(F)`. -/
  85: structure PhysicalFamily where
  86:   P : ℕ → PhysData
  87:   S : ℕ → ScalarSieve
  88:   target : ℕ → ℝ
  89: 
  90: namespace PhysicalFamily
  91: 
  92: variable (F : PhysicalFamily)
  93: 
  94: /-- The literal physical remainder `R_Σ^P(X)` of the family. -/
  95: noncomputable def R (X : ℕ) : ℝ := (F.P X).RSigmaP (F.S X)
  96: 
  97: /-- The relative part `R_rel(X)`. -/
  98: noncomputable def Rrel (X : ℕ) : ℝ := (F.P X).Rrel (F.S X)
  99: 
 100: /-- The base part `R_base(X)`. -/
 101: noncomputable def Rbase (X : ℕ) : ℝ := (F.P X).Rbase (F.S X)
 102: 
 103: /-- `R_rel = o(target)`, `R_base = o(target)` ⟹ `R_Σ^P = o(target)` (exact centering). -/
 104: theorem physical_littleO_of_rel_base
 105:     (hgood : ∃ X0 : ℕ, ∀ X ≥ X0, (F.P X).WGood ∧ (F.S X).Good (F.P X).W)
 106:     (hrel : IsLittleOTarget F.Rrel F.target) (hbase : IsLittleOTarget F.Rbase F.target) :
 107:     IsLittleOTarget F.R F.target := by
 108:   obtain ⟨X0, hX0⟩ := hgood
 109:   intro ε hε
 110:   obtain ⟨X1, hX1⟩ := hrel.add hbase ε hε
 111:   refine ⟨max X0 X1, fun X hX => ?_⟩
 112:   obtain ⟨hP, hS⟩ := hX0 X ((le_max_left _ _).trans hX)
 113:   have := hX1 X ((le_max_right _ _).trans hX)
 114:   unfold R
 115:   rw [PhysData.RSigmaP_eq_rel_add_base hP (F.S X) hS]
 116:   exact this
 117: 
 118: /-- **Conditional tail theorem with the literal physical remainder.**  Hypotheses: the
 119: one-sided seven-block framework for `R_Σ^P`, the presieve/support conditions for large `X`,
 120: and `R_rel = o(𝒩_X I)`, `R_base = o(𝒩_X I)`.  NOT unconditional. -/
 121: theorem Tail287_of_physical (Fw : OneSidedFrameworkFor F.R F.target)
 122:     (hgood : ∃ X0 : ℕ, ∀ X ≥ X0, (F.P X).WGood ∧ (F.S X).Good (F.P X).W)
 123:     (hrel : IsLittleOTarget F.Rrel F.target) (hbase : IsLittleOTarget F.Rbase F.target) :
 124:     Tail287Statement :=
 125:   tail_of_littleO_for Fw (F.physical_littleO_of_rel_base hgood hrel hbase)
```

## `RequestProject/Erdos287/SourceChain/W4Route.lean`

SHA-256: `1f35e0bc4a37811b221e63b12e5518a0a50280faa2e3061d42b9b36628077241`

Lines 39–60:

```text
  39: /-! ### Source → positive `W₄` (first Cauchy + multiplicity) -/
  40: 
  41: /-- **First Cauchy + representation multiplicity.** -/
  42: theorem source_to_W4 {α β : Type*} [DecidableEq β] (Ω : Finset α) (π : α → β) (a : α → ℂ)
  43:     (G : β → ℂ) (m : ℕ) (ha : ∀ ω ∈ Ω, ‖a ω‖ ≤ 1)
  44:     (hm : ∀ b, (Ω.filter (fun ω => π ω = b)).card ≤ m) :
  45:     ‖∑ ω ∈ Ω, a ω * G (π ω)‖ ^ 2 ≤ Ω.card * (m * ∑ b ∈ Ω.image π, ‖G b‖ ^ 2) := by
  46:   have h1 : ‖∑ ω ∈ Ω, a ω * G (π ω)‖ ≤ ∑ ω ∈ Ω, ‖G (π ω)‖ := by
  47:     refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun ω hω => ?_))
  48:     rw [norm_mul]
  49:     exact mul_le_of_le_one_left (norm_nonneg _) (ha ω hω)
  50:   have h2 : (∑ ω ∈ Ω, ‖G (π ω)‖) ^ 2 ≤ Ω.card * ∑ ω ∈ Ω, ‖G (π ω)‖ ^ 2 :=
  51:     sq_sum_le_card_mul_sum_sq
  52:   have h3 : ∑ ω ∈ Ω, ‖G (π ω)‖ ^ 2 ≤ m * ∑ b ∈ Ω.image π, ‖G b‖ ^ 2 := by
  53:     rw [Finset.sum_comp (fun b => ‖G b‖ ^ 2) π, Finset.mul_sum]
  54:     refine Finset.sum_le_sum (fun b _ => ?_)
  55:     rw [nsmul_eq_mul]
  56:     exact mul_le_mul_of_nonneg_right (by exact_mod_cast hm b) (sq_nonneg _)
  57:   calc ‖∑ ω ∈ Ω, a ω * G (π ω)‖ ^ 2 ≤ (∑ ω ∈ Ω, ‖G (π ω)‖) ^ 2 :=
  58:         pow_le_pow_left₀ (norm_nonneg _) h1 2
  59:     _ ≤ _ := h2
  60:     _ ≤ _ := mul_le_mul_of_nonneg_left h3 (Nat.cast_nonneg _)
```

Lines 77–93:

```text
  77: /-- **Fixed-`A` positive domination** `W_{A₀}(B₀,C₀,F₀) ≤ W₁(A₀B₀,C₀,F₀)`: an injective
  78: positive-stage map `ι` (e.g. `b ↦ A₀ b`) with `w ≤ w₁ ∘ ι`, `inner = inner₁ ∘ ι` and
  79: `ι(T) ⊆ T₁` gives domination, provided the target weights are non-negative.  It concerns the
  80: already-formed positive square only. -/
  81: theorem fixedA_domination {β γ : Type*} [DecidableEq γ] (T : Finset β) (T1 : Finset γ)
  82:     (ι : β → γ) (hinj : Set.InjOn ι T) (hsub : T.image ι ⊆ T1) (w : β → ℝ) (w1 : γ → ℝ)
  83:     (inner : β → ℂ) (inner1 : γ → ℂ) (hw : ∀ b ∈ T, w b ≤ w1 (ι b))
  84:     (hw1 : ∀ g ∈ T1, 0 ≤ w1 g) (hin : ∀ b ∈ T, inner b = inner1 (ι b)) :
  85:     W4 T w inner ≤ W4 T1 w1 inner1 := by
  86:   unfold W4
  87:   calc ∑ b ∈ T, w b * ‖inner b‖ ^ 2 ≤ ∑ b ∈ T, w1 (ι b) * ‖inner1 (ι b)‖ ^ 2 :=
  88:         Finset.sum_le_sum (fun b hb => by
  89:           rw [hin b hb]; exact mul_le_mul_of_nonneg_right (hw b hb) (sq_nonneg _))
  90:     _ = ∑ g ∈ T.image ι, w1 g * ‖inner1 g‖ ^ 2 := (Finset.sum_image (f := fun g => w1 g * ‖inner1 g‖ ^ 2) hinj).symm
  91:     _ ≤ ∑ g ∈ T1, w1 g * ‖inner1 g‖ ^ 2 :=
  92:         Finset.sum_le_sum_of_subset_of_nonneg hsub (fun g hg _ =>
  93:           mul_nonneg (hw1 g hg) (sq_nonneg _))
```

Lines 133–183:

```text
 133: /-! ### The audited Pascadi term and the three narrow `W₄` providers -/
 134: 
 135: /-- **Audited Pascadi term** `FC² + B₀CS² + FCHS`. -/
 136: def pascadiInner (F C B0 S H : ℝ) : ℝ := F * C ^ 2 + B0 * C * S ^ 2 + F * C * H * S
 137: 
 138: /-- The superseded transcription `FC² + B₀CS² + FHS` (kept only for the regression). -/
 139: def pascadiInnerOld (F C B0 S H : ℝ) : ℝ := F * C ^ 2 + B0 * C * S ^ 2 + F * H * S
 140: 
 141: /-- **Regression**: the old `FHS` term is a different function, so it cannot feed the chain. -/
 142: theorem regr_old_FHS : pascadiInner 1 2 0 1 1 ≠ pascadiInnerOld 1 2 0 1 1 := by
 143:   unfold pascadiInner pascadiInnerOld; norm_num
 144: 
 145: /-- For `C ≥ 1` (and non-negative data) the audited term dominates the old one: a bound proved
 146: with the old term is *weaker than claimed* and does not imply the audited bound. -/
 147: theorem pascadiInner_ge_old {F C B0 S H : ℝ} (hF : 0 ≤ F) (hC : 1 ≤ C) (hS : 0 ≤ S)
 148:     (hH : 0 ≤ H) : pascadiInnerOld F C B0 S H ≤ pascadiInner F C B0 S H := by
 149:   unfold pascadiInner pascadiInnerOld
 150:   have : F * H * S ≤ F * C * H * S := by
 151:     have h0 : 0 ≤ F * H * S := by positivity
 152:     nlinarith
 153:   linarith
 154: 
 155: /-- The spectral right-hand side with the audited term. -/
 156: noncomputable def specRHS (Λ T F C B0 S H : ℝ) : ℝ :=
 157:   Λ * T ^ ((7 : ℝ) / 64) * (1 + C * Real.sqrt F / (S ^ ((3 : ℝ) / 2) * H)) ^ ((7 : ℝ) / 32) *
 158:     (H * S ^ 2 * Real.sqrt F * Real.sqrt (pascadiInner F C B0 S H))
 159: 
 160: /-- **Narrow provider 1 (diagonal)**: `W_diag ≤ Λ · S H F C B₀`. -/
 161: def W4DiagEstimate (Wdiag Λ S H F C B0 : ℝ) : Prop := Wdiag ≤ Λ * (S * H * F * C * B0)
 162: 
 163: /-- **Narrow provider 2 (Ramanujan)**: `W_Ram ≤ Λ · S² H² F B₀`. -/
 164: def W4RamEstimate (Wram Λ S H F B0 : ℝ) : Prop := Wram ≤ Λ * (S ^ 2 * H ^ 2 * F * B0)
 165: 
 166: /-- **Narrow provider 3 (spectral)**, with the audited Pascadi term and the `T^{7/64}`
 167: exceptional loss. -/
 168: def W4SpecEstimate (Wspec Λ T F C B0 S H : ℝ) : Prop := Wspec ≤ specRHS Λ T F C B0 S H
 169: 
 170: /-- The three providers combine (no hidden fourth input beyond the structural split
 171: `𝒲₄ ≤ W_diag + W_Ram + W_spec`). -/
 172: theorem W4_bound_of_pieces {W Wd Wr Ws Λ T F C B0 S H : ℝ} (hsplit : W ≤ Wd + Wr + Ws)
 173:     (hd : W4DiagEstimate Wd Λ S H F C B0) (hr : W4RamEstimate Wr Λ S H F B0)
 174:     (hs : W4SpecEstimate Ws Λ T F C B0 S H) :
 175:     W ≤ Λ * (S * H * F * C * B0) + Λ * (S ^ 2 * H ^ 2 * F * B0) + specRHS Λ T F C B0 S H := by
 176:   unfold W4DiagEstimate W4RamEstimate W4SpecEstimate at *; linarith
 177: 
 178: /-! ### `T_H` propagation: `T^{7/64}` inside `𝒲₄` becomes `T^{7/128}` after the square root -/
 179: 
 180: theorem TH_sqrt_propagation {T W0 : ℝ} (hT : 0 ≤ T) :
 181:     Real.sqrt (T ^ ((7 : ℝ) / 64) * W0) = T ^ ((7 : ℝ) / 128) * Real.sqrt W0 := by
 182:   rw [Real.sqrt_mul (Real.rpow_nonneg hT _), Real.sqrt_eq_rpow, ← Real.rpow_mul hT]
 183:   norm_num
```

Lines 221–228:

```text
 221: /-- **Astra final packet exponent `391/256`** from the (weaker) kernel target `f^{263/128}`. -/
 222: theorem astra_packet_391 {M N Q f x K Fsh Bc C0 L ε : ℝ} (hM : 0 < M) (hN : 0 < N)
 223:     (hQ : 0 < Q) (hf : 0 < f) (hC0 : 0 ≤ C0) (hL : 0 ≤ L) (hx : x = M * N)
 224:     (hK : |K| ≤ C0 * f ^ ((263 : ℝ) / 128) * N ^ 2 / Q * x ^ (-ε)) (hF : Fsh = M / f * K)
 225:     (hB : Bc ≤ M * Q * L) :
 226:     Real.sqrt (Bc * |Fsh|) ≤ x / f * (f ^ ((391 : ℝ) / 256) * x ^ (-(ε / 2)) * Real.sqrt (C0 * L)) := by
 227:   have h := packet_exponent hM hN hQ hf hC0 hL hx hK hF hB
 228:   rwa [show ((263 : ℝ) / 128 + 1) / 2 = 391 / 256 by norm_num] at h
```

## `RequestProject/Erdos287/SourceChain/ActualAtomW4Comparison.lean`

SHA-256: `5a49ac2946e4289cf648fc62485b04a265bb515a9c5b1d68e385e76325c1b1d8`

Lines 90–99:

```text
  90: theorem sharpPowerSaving_of_atom {S : TailSourceFamily ι} (C : OrderingBCells S)
  91:     (Fs : FamilyScale S) {σ ε CK C0 : ℝ} (hC0 : 0 ≤ C0)
  92:     (hledger : 391 / 256 * σ < ε / 2)
  93:     (hatom : ∃ X1 : ℕ, ∀ X ≥ X1, ∀ ξ ∈ (S.T X).Xi,
  94:       ((S.T X).f ξ : ℝ) ≤ Fs.x X ^ σ ∧
  95:       AstraAtomBound (Fs.x X) ((S.T X).f ξ) (C.Bc X ξ) (C.piece X ξ .sharp) CK C0 ε) :
  96:     PowerSavingCell S C Fs .sharp := by
  97:   obtain ⟨X1, hX1⟩ := hatom
  98:   obtain ⟨X2, hX2⟩ := Fs.x_large 3
  99:   refine ⟨CK / 2, ε / 2 - 391 / 256 * σ, Real.sqrt C0, by linarith, Real.sqrt_nonneg _,
```

Lines 134–158:

```text
 134: /-- **Actual-atom estimate + reciprocal packet norm ⟹ clean-AA aggregate payment.** -/
 135: theorem sharpPaid_of_atom {S : TailSourceFamily ι} (C : OrderingBCells S) (Fs : FamilyScale S)
 136:     {CD σ ε CK C0 : ℝ} (hspec : SpectatorReciprocalNorm S Fs CD) (hC0 : 0 ≤ C0)
 137:     (hledger : 391 / 256 * σ < ε / 2)
 138:     (hatom : ∃ X1 : ℕ, ∀ X ≥ X1, ∀ ξ ∈ (S.T X).Xi,
 139:       ((S.T X).f ξ : ℝ) ≤ Fs.x X ^ σ ∧
 140:       AstraAtomBound (Fs.x X) ((S.T X).f ξ) (C.Bc X ξ) (C.piece X ξ .sharp) CK C0 ε) :
 141:     PiecePaid S C .sharp :=
 142:   piecePaid_of_powerSaving C Fs hspec .sharp (sharpPowerSaving_of_atom C Fs hC0 hledger hatom)
 143: 
 144: /-- **Conditional tail theorem with the Astra actual-atom estimate.**  NOT unconditional. -/
 145: theorem Tail287_of_AtomProviders (S : TailSourceFamily ι) (C : OrderingBCells S)
 146:     (Fs : FamilyScale S) {CD σ ε CK C0 : ℝ}
 147:     (Fw : SevenBlockTailFramework S) (hBase : BaseSWProvider S) (hCop : CoprimalityPaid S)
 148:     (hRed : OrderingBPoissonReduction S C) (hCent : CenteringPaid S C)
 149:     (hspec : SpectatorReciprocalNorm S Fs CD) (hC0 : 0 ≤ C0)
 150:     (hledger : 391 / 256 * σ < ε / 2)
 151:     (hatom : ∃ X1 : ℕ, ∀ X ≥ X1, ∀ ξ ∈ (S.T X).Xi,
 152:       ((S.T X).f ξ : ℝ) ≤ Fs.x X ^ σ ∧
 153:       AstraAtomBound (Fs.x X) ((S.T X).f ξ) (C.Bc X ξ) (C.piece X ξ .sharp) CK C0 ε)
 154:     (hOther : ∀ p, p ≠ CellPiece.sharp → PiecePaid S C p) : Tail287Statement := by
 155:   refine Tail287_of_MinimalAnalyticProviders S C Fw hBase hCop hRed hCent (fun p => ?_)
 156:   by_cases hp : p = CellPiece.sharp
 157:   · subst hp; exact sharpPaid_of_atom C Fs hspec hC0 hledger hatom
 158:   · exact hOther p hp
```

## `lean-toolchain`

SHA-256: `db7bb24b756d745bbde83fe92718b51bd3625dae3701ba0f598d0eedcd3f3028`

Lines 1–1:

```text
   1: leanprover/lean4:v4.28.0
```

## `lakefile.toml`

SHA-256: `b1481968ce2912f2b85288fc18aa05fb22750e4083f9e03f49f59a8814ba268a`

Lines 1–11:

```text
   1: name = "RequestProject"
   2: defaultTargets = ["RequestProject"]
   3: 
   4: [[require]]
   5: name = "mathlib"
   6: git = "https://github.com/leanprover-community/mathlib4.git"
   7: rev = "v4.28.0"
   8: 
   9: [[lean_lib]]
  10: name = "RequestProject"
  11: globs = ["RequestProject.+"]
```
