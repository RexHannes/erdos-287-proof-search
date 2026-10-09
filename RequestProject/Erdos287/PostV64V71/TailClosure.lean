import RequestProject.Erdos287.PostV64V71.ExceptionAccounting
import RequestProject.Erdos287.PostQSigma.TerminalBridge

/-!
# Erdős #287 — V71 tail closure: `DeterminantSupply287 ⇒` no counterexample above `2^1500`

**ERDŐS #287 REMAINS OPEN.**  This file proves *implications* only.

## Canonical height (discrete / analytic separation)

`Hcan M = ⌊(log M - 6 log log M) / log 2⌋₊`.  For `M ≥ 2^1500`, with `L = log M`,
`canonical_height_facts` proves (real analysis, fully in Lean):

* `1 ≤ Hcan M`;
* `Hcan M ≤ 3L/2`;
* `12 L⁶ < √M`.

## Named propositions (NOT proved, NOT assumed globally)

* `DeterminantSupply287` — **the current OPEN research owner**: for every `M ≥ 2^1500`,
  `D_Λ(M) > 13 M / (log M)³` (with `H = Hcan M`, `y = ⌊M/H⌋`).
* `FingerprintLogBound287` — the V68 explicit exceptional-prime log budget
  `log Ξ_H < 2 M / (log M)⁵` for `M ≥ 2^1500` (paper-level; it needs an explicit Chebyshev upper
  bound `ψ(H) ≲ 1.04 H` that is not available in Lean/Mathlib — Mathlib's `ψ(x) ≤ log 4 · x + …`
  is too weak by a hair).  It is an explicit **hypothesis** of the tail theorem.

## Proved implications

* `contamination_lt` — `8 H √M L² < M/L³` (so `D_Λ > 13M/L³ ⇒ D_θ > 12M/L³`);
* `loss_lt` — `B_E < 2M/L⁵ ⇒ 4 H L B_E < 12 M/L³`;
* `supply_implies_theta_supply` — `D_Λ > 13M/L³ ⇒ D_θ > 12M/L³`;
* `determinant_supply_excludes_source` — for a literal counterexample with `M ≥ 2^1500`:
  `D_Λ(M) > 13M/L³` and `log Ξ_H < 2M/L⁵` give a contradiction (some tuple survives deletion of
  all fingerprint-exception owners; both owners are good; `kq` and `tr` are adjacent mandatory
  omissions).  **No prime-distribution heuristic is used.**
* `determinant_supply_implies_no_tail` — `DeterminantSupply287 → FingerprintLogBound287 →
  NoCounterexampleAbove (2^1500)`;
* `finite_and_tail_imply_erdos287` — finite exclusion up to `U ≥ 2^1500 - 1` + tail ⇒ original
  ordered statement;
* `erdos287_of_determinant_supply` — the conditional global theorem;
* `erdos287_of_determinant_supply_repository_native` — uses only the proved `4·10⁹` bank and
  exposes the unresolved range `(4·10⁹, 2^1500)` as an explicit hypothesis.
-/

open scoped BigOperators

namespace Erdos287.PostV64V71

open Erdos287 Erdos287.PostQSigma

/-- The canonical V71 height `H = ⌊(log M - 6 log log M)/log 2⌋₊`. -/
noncomputable def Hcan (M : ℕ) : ℕ :=
  ⌊(Real.log M - 6 * Real.log (Real.log M)) / Real.log 2⌋₊

/-! ## Real-analysis facts for `M ≥ 2^1500` -/

theorem log_ge_of_large {M : ℕ} (hM : 2 ^ 1500 ≤ M) : 1039 < Real.log M := by
  have h2 : ((2 : ℝ) ^ 1500) ≤ (M : ℝ) := by exact_mod_cast hM
  have h3 : Real.log ((2 : ℝ) ^ 1500) ≤ Real.log M := Real.log_le_log (by positivity) h2
  rw [Real.log_pow] at h3
  have := Real.log_two_gt_d9
  push_cast at h3
  linarith

/-- `log L ≤ L/12` for `L ≥ 1039` (via `log s ≤ s - 1` at `s = √L`). -/
theorem log_le_div_twelve {L : ℝ} (hL : 1039 < L) : 6 * Real.log L ≤ L / 2 := by
  have hL0 : 0 < L := by linarith
  set s := Real.sqrt L with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 hL0
  have hss : s ^ 2 = L := Real.sq_sqrt hL0.le
  have hs24 : 24 ≤ s := by
    rw [hs, Real.le_sqrt (by norm_num) hL0.le]; linarith
  have hlog : Real.log L = 2 * Real.log s := by
    rw [← hss, Real.log_pow]; push_cast; ring
  have h1 : Real.log s ≤ s - 1 := Real.log_le_sub_one_of_pos hs0
  rw [hlog, ← hss]
  nlinarith

/-- `12 L⁶ < √M` for `M ≥ 2^1500`, `L = log M` (via `exp x ≥ x¹²/12!`). -/
theorem twelve_log_pow_lt_sqrt {M : ℕ} (hM : 2 ^ 1500 ≤ M) :
    12 * Real.log M ^ 6 < Real.sqrt M := by
  have hL := log_ge_of_large hM
  set L := Real.log M with hLdef
  have hM0 : (0 : ℝ) < M := by
    have : (0 : ℕ) < M := lt_of_lt_of_le (by positivity) hM
    exact_mod_cast this
  have hsq : Real.sqrt M = Real.exp (L / 2) := by
    have h1 : (M : ℝ) = Real.exp (L / 2) ^ 2 := by
      rw [← Real.exp_nat_mul, hLdef]; push_cast
      rw [show (2 : ℝ) * (Real.log M / 2) = Real.log M by ring, Real.exp_log hM0]
    rw [h1, Real.sqrt_sq (Real.exp_pos _).le]
  rw [hsq]
  have hexp := Real.pow_div_factorial_le_exp (x := L / 2) (by linarith) 12
  have hfact : (Nat.factorial 12 : ℝ) = 479001600 := by norm_num [Nat.factorial]
  rw [hfact] at hexp
  have hL6 : (1039 : ℝ) ^ 6 ≤ L ^ 6 := pow_le_pow_left₀ (by norm_num) hL.le 6
  have hL6pos : 0 < L ^ 6 := by positivity
  have key : 12 * L ^ 6 < (L / 2) ^ 12 / 479001600 := by
    rw [lt_div_iff₀ (by norm_num), div_pow, show L ^ 12 = L ^ 6 * L ^ 6 by ring]
    have : (12 : ℝ) * 479001600 * 2 ^ 12 < L ^ 6 := by nlinarith
    rw [lt_div_iff₀ (by norm_num)]
    nlinarith
  linarith

/-- **Canonical-height facts** for `M ≥ 2^1500`. -/
theorem canonical_height_facts {M : ℕ} (hM : 2 ^ 1500 ≤ M) :
    1 ≤ Hcan M ∧ (Hcan M : ℝ) ≤ 3 / 2 * Real.log M ∧
      12 * Real.log M ^ 6 < Real.sqrt M := by
  have hL := log_ge_of_large hM
  set L := Real.log M with hLdef
  have h6 := log_le_div_twelve hL
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  have hlogL : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
  have hval_lo : 1 ≤ (L - 6 * Real.log L) / Real.log 2 := by
    rw [le_div_iff₀ (by linarith)]; linarith
  refine ⟨?_, ?_, twelve_log_pow_lt_sqrt hM⟩
  · unfold Hcan
    rw [← hLdef]
    exact Nat.one_le_floor_iff _ |>.2 hval_lo
  · unfold Hcan
    rw [← hLdef]
    have hnn : 0 ≤ (L - 6 * Real.log L) / Real.log 2 := by linarith
    refine le_trans (Nat.floor_le hnn) ?_
    rw [div_le_iff₀ (by linarith)]
    nlinarith

/-! ## The two closure margins -/

/-- **Contamination margin**: `8 H √M L² < M / L³` when `H ≤ 3L/2`, `L > 0`, `12 L⁶ < √M`. -/
theorem contamination_lt {M H L : ℝ} (hM : 0 < M) (hL : 0 < L)
    (hH : H ≤ 3 / 2 * L) (hsq : 12 * L ^ 6 < Real.sqrt M) :
    8 * H * Real.sqrt M * L ^ 2 < M / L ^ 3 := by
  have hs0 : 0 < Real.sqrt M := Real.sqrt_pos.2 hM
  have hss : Real.sqrt M * Real.sqrt M = M := Real.mul_self_sqrt hM.le
  rw [lt_div_iff₀ (by positivity)]
  have h1 : 8 * H * Real.sqrt M * L ^ 2 * L ^ 3 ≤ 12 * L ^ 6 * Real.sqrt M := by
    have : 8 * H * L ^ 5 ≤ 12 * L ^ 6 := by
      have hL5 : 0 ≤ L ^ 5 := by positivity
      nlinarith
    nlinarith
  have h2 : 12 * L ^ 6 * Real.sqrt M < Real.sqrt M * Real.sqrt M :=
    mul_lt_mul_of_pos_right hsq hs0
  linarith

/-- **Loss margin**: `0 ≤ B < 2M/L⁵`, `H ≤ 3L/2` ⇒ `4 H L B < 12 M/L³`. -/
theorem loss_lt {M H L B : ℝ} (hL : 0 < L) (hH : H ≤ 3 / 2 * L) (hB0 : 0 ≤ B)
    (hB : B < 2 * M / L ^ 5) : 4 * H * L * B < 12 * M / L ^ 3 := by
  have h1 : 4 * H * L * B ≤ 6 * L ^ 2 * B := by
    nlinarith [mul_nonneg (mul_nonneg hL.le (by linarith : 0 ≤ 3 / 2 * L - H)) hB0]
  have h2 : 6 * L ^ 2 * B < 6 * L ^ 2 * (2 * M / L ^ 5) :=
    mul_lt_mul_of_pos_left hB (by positivity)
  have h3 : 6 * L ^ 2 * (2 * M / L ^ 5) = 12 * M / L ^ 3 := by
    field_simp
    ring
  linarith

/-! ## Named propositions -/

/-- **`DeterminantSupply287` — CURRENT OPEN RESEARCH OWNER (definition only; never proved or
assumed globally).**  For every `M ≥ 2^1500`, `D_Λ(M) > 13 M/(log M)³`, where `D_Λ` is the V71
von Mangoldt determinant count with the canonical height `H = Hcan M` and `y = ⌊M/H⌋`. -/
def DeterminantSupply287 : Prop :=
  ∀ M : ℕ, 2 ^ 1500 ≤ M → 13 * (M : ℝ) / Real.log M ^ 3 < DLambda M (Hcan M)

/-- **`FingerprintLogBound287` — explicit exceptional-prime log budget (PAPER-LEVEL / EXTERNAL;
Lean-uninhabited).**  `log Ξ_H < 2M/(log M)⁵` for every `M ≥ 2^1500`, `H = Hcan M`. -/
def FingerprintLogBound287 : Prop :=
  ∀ M : ℕ, 2 ^ 1500 ≤ M → Real.log (Xi (Hcan M)) < 2 * (M : ℝ) / Real.log M ^ 5

/-- No exact Erdős #287 counterexample has maximum `≥ B`. -/
def NoCounterexampleAbove (B : ℕ) : Prop :=
  ∀ A : Finset ℕ, ∀ h : Erdos287Counterexample A, B ≤ A.max' h.nonempty → False

/-! ## The closure chain -/

/-- `D_Λ > 13M/L³ ⇒ D_θ > 12M/L³` (for `M ≥ 2^1500`, `H = Hcan M`). -/
theorem supply_implies_theta_supply {M : ℕ} (hM : 2 ^ 1500 ≤ M)
    (hD : 13 * (M : ℝ) / Real.log M ^ 3 < DLambda M (Hcan M)) :
    12 * (M : ℝ) / Real.log M ^ 3 < Dtheta M (Hcan M) := by
  obtain ⟨hH1, hH, hsq⟩ := canonical_height_facts hM
  have hL := log_ge_of_large hM
  have hM1 : 1 ≤ M := le_trans (Nat.one_le_two_pow) hM
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM1
  have hcont := (mangoldt_prime_power_error M (Hcan M) hM1).2
  have hlt := contamination_lt hM0 (by linarith) hH hsq
  have h13 : 13 * (M : ℝ) / Real.log M ^ 3 = 12 * (M : ℝ) / Real.log M ^ 3 +
      (M : ℝ) / Real.log M ^ 3 := by ring
  linarith

/-- After deleting all tuples with an owner in `E_H`, the `θ*` mass is still positive. -/
theorem Dgg_pos_of_supply {M : ℕ} (hM : 2 ^ 1500 ≤ M)
    (hD : 13 * (M : ℝ) / Real.log M ^ 3 < DLambda M (Hcan M))
    (hXi : Real.log (Xi (Hcan M)) < 2 * (M : ℝ) / Real.log M ^ 5) :
    0 < Dgg M (Hcan M) (exceptionalPrimes M (Hcan M)) := by
  obtain ⟨hH1, hH, hsq⟩ := canonical_height_facts hM
  have hL := log_ge_of_large hM
  have hθ := supply_implies_theta_supply hM hD
  have hloss := (exception_weight_loss M (Hcan M) (exceptionalPrimes M (Hcan M))).2
  have hBE : BE M (Hcan M) < 2 * (M : ℝ) / Real.log M ^ 5 :=
    lt_of_le_of_lt (BE_le_log_Xi M (Hcan M)) hXi
  have hlt := loss_lt (by linarith) hH (BE_nonneg M (Hcan M)) hBE
  unfold BE at hlt
  linarith

/-- **Determinant supply excludes the source.**  For a literal counterexample (as a `Gap2CE`)
with `M ≥ 2^1500`, the inequalities `D_Λ(M) > 13M/L³` and `log Ξ_H < 2M/L⁵` are contradictory. -/
theorem determinant_supply_excludes_source (ce : Erdos287.Gap2CE) (hM : 2 ^ 1500 ≤ ce.M)
    (hD : 13 * (ce.M : ℝ) / Real.log ce.M ^ 3 < DLambda ce.M (Hcan ce.M))
    (hXi : Real.log (Xi (Hcan ce.M)) < 2 * (ce.M : ℝ) / Real.log ce.M ^ 5) : False := by
  have hpos := Dgg_pos_of_supply hM hD hXi
  obtain ⟨hH1, -, -⟩ := canonical_height_facts hM
  set H := Hcan ce.M
  set E := exceptionalPrimes ce.M H
  obtain ⟨x, hx, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hpos.ne'
  obtain ⟨hxbox, hqE, hrE⟩ := Finset.mem_filter.1 hx
  have hq : x.q.Prime := by
    by_contra h; exact hne (by rw [thetaStar_of_not_prime h, zero_mul])
  have hr : x.r.Prime := by
    by_contra h; exact hne (by rw [thetaStar_of_not_prime h, mul_zero])
  have m := mem_detBox.1 hxbox
  have hqXi : ¬ x.q ∣ Xi H := fun h => hqE (mem_exceptionalPrimes.2 ⟨m.2.1, hq, h⟩)
  have hrXi : ¬ x.r ∣ Xi H := fun h => hrE (mem_exceptionalPrimes.2 ⟨m.2.2.2.1, hr, h⟩)
  have hM4 : 4 ≤ ce.M :=
    le_trans (le_trans (show 4 ≤ 2 ^ 2 by norm_num) (Nat.pow_le_pow_right (by norm_num)
      (by norm_num))) hM
  exact Gap2CE.good_tuple_excludes ce hM4 (by omega) hxbox hq hr hqXi hrXi

/-- **Tail theorem (A).**  `DeterminantSupply287` and the explicit fingerprint log budget imply
that no exact counterexample has maximum `≥ 2^1500`. -/
theorem determinant_supply_implies_no_tail (hS : DeterminantSupply287)
    (hXi : FingerprintLogBound287) : NoCounterexampleAbove (2 ^ 1500) := by
  intro A h hM
  have hM' : 2 ^ 1500 ≤ h.toGap2CE.M := hM
  exact determinant_supply_excludes_source h.toGap2CE hM' (hS _ hM') (hXi _ hM')

/-! ## Terminal splices -/

/-- **Theorem B (conditional full splice).**  A finite exclusion up to `U` with
`2^1500 ≤ U + 1` (overlap condition) and the tail statement imply the original ordered-sequence
statement of Erdős #287. -/
theorem finite_and_tail_imply_erdos287 {U : ℕ} (hfin : FiniteExclusionUpTo U)
    (hU : 2 ^ 1500 ≤ U + 1) (htail : NoCounterexampleAbove (2 ^ 1500))
    (k : ℕ) (n : ℕ → ℕ) (hmono : ∀ i j, i < j → j < k → n i < n j)
    (hone : ∀ i, i < k → 1 < n i) (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / (n i) = 1) :
    ∃ i, i + 1 < k ∧ n i + 3 ≤ n (i + 1) := by
  refine erdos287_seq_of_no_counterexample (fun A hA => ?_) k n hmono hone hsum
  have := hfin A hA
  exact htail A hA (by omega)

/-- **Conditional global theorem.**  Finite exclusion through the overlap, `DeterminantSupply287`
(OPEN) and `FingerprintLogBound287` (paper-level) imply the original statement. -/
theorem erdos287_of_determinant_supply {U : ℕ} (hfin : FiniteExclusionUpTo U)
    (hU : 2 ^ 1500 ≤ U + 1) (hS : DeterminantSupply287) (hXi : FingerprintLogBound287)
    (k : ℕ) (n : ℕ → ℕ) (hmono : ∀ i j, i < j → j < k → n i < n j)
    (hone : ∀ i, i < k → 1 < n i) (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / (n i) = 1) :
    ∃ i, i + 1 < k ∧ n i + 3 ≤ n (i + 1) :=
  finite_and_tail_imply_erdos287 hfin hU (determinant_supply_implies_no_tail hS hXi)
    k n hmono hone hsum

/-- **Theorem C (repository-native; does NOT claim closure).**  Uses only the proved finite bank
`M ≤ 4·10⁹`.  The enormous unresolved range `4·10⁹ < M < 2^1500` is an explicit hypothesis
`hmid`, and the tail needs the OPEN `DeterminantSupply287` and `FingerprintLogBound287`. -/
theorem erdos287_of_determinant_supply_repository_native
    (hmid : ∀ A : Finset ℕ, ∀ h : Erdos287Counterexample A,
      4000000000 < A.max' h.nonempty → A.max' h.nonempty < 2 ^ 1500 → False)
    (hS : DeterminantSupply287) (hXi : FingerprintLogBound287) :
    ∀ A : Finset ℕ, ¬ Erdos287Counterexample A := by
  intro A hA
  have h1 := finiteExclusionUpTo_4e9 A hA
  by_cases hM : A.max' hA.nonempty < 2 ^ 1500
  · exact hmid A hA h1 hM
  · exact determinant_supply_implies_no_tail hS hXi A hA (by omega)

end Erdos287.PostV64V71
