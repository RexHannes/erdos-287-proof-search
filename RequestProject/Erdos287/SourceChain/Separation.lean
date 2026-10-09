import RequestProject.Erdos287.CurrentTail.ExponentLedger

/-!
# Erdős #287 — source chain: `h`-separation cost, cross-coprime ordering, ranges, `e`-errors

**ERDŐS #287 REMAINS OPEN.  TAIL-287 IS NOT BANKED.**  Source level: `MESSAGE_LEVEL_SOURCE`
(source pack §15, §18, §20; request §6, §11).

* `hsep_cost_subpower` — the separation-of-variables cost `exp((log log x)^5)` is `x^{o(1)}`:
  for every `η > 0` it is `≤ x^η` for all large `x` (kernel-proved; the separation lemma
  itself — Maynard II Lemma 6.9 / Maynard I Lemma 14.5 — stays an external analytic input).
* `hsep_membership` — exact source-membership arithmetic for the separation hypotheses:
  exponent inequalities `θ_Q + θ_R < 2/3` and `θ_Q + 2θ_R < θ_M + 1 - 2ε` give
  `QR < x^{2/3}` and `QR² < M x^{1-2ε}`.
* `subpower_absorbed_by_power` / `log_saving_not_absorbing` — the cross-coprime ordering:
  an `x^{o(1)}` partition count is absorbed by a fixed power saving, but **not** by a
  logarithmic one (explicit counter-model `(log x)² · (log x)^{-1} = log x → ∞`).  Hence all
  merely logarithmic errors must be paid *before* the sub-power partition.
* `Q1_absorb` — the small-prime factor absorbed in `Q₁ = b q₁`: exponents add.
* `eErrors`, `eErrors_absent_at_one` — the reduction specialises to `e = 1`; the `e`-errors
  (`e ≥ 2`) are an empty sum, proved `= 0` (not silently dropped).
* `PascadiRangeExport` — the three Pascadi kernel inequalities as an **explicit range
  hypothesis bundle** (their numerical constants are not in the supplied source); the second
  inequality's field takes the Proposition-5.2 bound `N ≤ x^{1/3+δ}` **as an argument**
  (referee repair R3), so it cannot be discharged from the other two alone.
-/

open scoped BigOperators
open Filter

namespace Erdos287.SourceChain

open Erdos287.CurrentTail

/-! ### `h`-separation cost -/

/-- **`exp((log log x)^5) = x^{o(1)}`.** -/
theorem hsep_cost_subpower {η : ℝ} (hη : 0 < η) :
    ∃ x0 : ℝ, ∀ x ≥ x0, Real.exp (Real.log (Real.log x) ^ 5) ≤ x ^ η := by
  have h := (Real.isLittleO_pow_log_id_atTop (n := 5)).bound hη
  obtain ⟨Y0, hY0⟩ := Filter.eventually_atTop.1 (h.and (Filter.eventually_ge_atTop (1 : ℝ)))
  refine ⟨Real.exp (max Y0 1), fun x hx => ?_⟩
  have hxpos : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have hlog : max Y0 1 ≤ Real.log x := by
    rw [← Real.log_exp (max Y0 1)]; exact Real.log_le_log (Real.exp_pos _) hx
  obtain ⟨hb, h1⟩ := hY0 (Real.log x) (le_trans (le_max_left _ _) hlog)
  have hlog0 : 0 ≤ Real.log x := by linarith
  simp only [id] at hb
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hlog0] at hb
  have hb' : Real.log (Real.log x) ^ 5 ≤ η * Real.log x := (le_abs_self _).trans hb
  rw [Real.rpow_def_of_pos hxpos]
  exact Real.exp_le_exp.2 (by linarith)

/-- **Separation-lemma membership arithmetic** (exponent form ⟹ size form). -/
theorem hsep_membership {x Q R M θQ θR θM ε : ℝ} (hx : 1 < x) (hR0 : 0 ≤ R)
    (hQ : Q ≤ x ^ θQ) (hR : R ≤ x ^ θR) (hM : x ^ θM ≤ M)
    (h1 : θQ + θR < 2 / 3) (h2 : θQ + 2 * θR < θM + 1 - 2 * ε) :
    Q * R < x ^ ((2 : ℝ) / 3) ∧ Q * R ^ 2 < M * x ^ (1 - 2 * ε) := by
  have hx0 : 0 < x := by linarith
  constructor
  · calc Q * R ≤ x ^ θQ * x ^ θR := mul_le_mul hQ hR hR0 (by positivity)
      _ = x ^ (θQ + θR) := (Real.rpow_add hx0 _ _).symm
      _ < x ^ ((2 : ℝ) / 3) := Real.rpow_lt_rpow_of_exponent_lt hx h1
  · calc Q * R ^ 2 ≤ x ^ θQ * (x ^ θR) ^ 2 :=
          mul_le_mul hQ (pow_le_pow_left₀ hR0 hR 2) (by positivity) (by positivity)
      _ = x ^ (θQ + 2 * θR) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le, ← Real.rpow_add hx0]; push_cast; ring_nf
      _ < x ^ (θM + (1 - 2 * ε)) := Real.rpow_lt_rpow_of_exponent_lt hx (by linarith)
      _ = x ^ θM * x ^ (1 - 2 * ε) := Real.rpow_add hx0 _ _
      _ ≤ M * x ^ (1 - 2 * ε) := mul_le_mul_of_nonneg_right hM (by positivity)

/-! ### Cross-coprime partition ordering -/

/-- A sub-power count (`≤ x^η` eventually, every `η > 0`) is absorbed by a fixed power
saving `x^{-κ}`: the product is `≤ x^{-κ/2}` eventually. -/
theorem subpower_absorbed_by_power {P : ℝ → ℝ}
    (hP : ∀ η : ℝ, 0 < η → ∃ x0 : ℝ, ∀ x ≥ x0, P x ≤ x ^ η) {κ : ℝ} (hκ : 0 < κ) :
    ∃ x0 : ℝ, ∀ x ≥ x0, P x * x ^ (-κ) ≤ x ^ (-κ / 2) := by
  obtain ⟨x0, hx0⟩ := hP (κ / 2) (by linarith)
  refine ⟨max x0 1, fun x hx => ?_⟩
  have hx1 : 0 < x := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) hx)
  calc P x * x ^ (-κ) ≤ x ^ (κ / 2) * x ^ (-κ) :=
        mul_le_mul_of_nonneg_right (hx0 x (le_trans (le_max_left _ _) hx)) (by positivity)
    _ = x ^ (-κ / 2) := by rw [← Real.rpow_add hx1]; ring_nf

/-- `(log x)²` is a sub-power count. -/
theorem logSq_subpower :
    ∀ η : ℝ, 0 < η → ∃ x0 : ℝ, ∀ x ≥ x0, Real.log x ^ (2 : ℝ) ≤ x ^ η := fun _ hη =>
  logCost_absorbed hη 2

/-- **Counter-model**: the sub-power count `(log x)²` times the logarithmic saving
`(log x)^{-1}` is `log x`, which is unbounded — log savings do not absorb the partition. -/
theorem log_saving_not_absorbing :
    ∀ C : ℝ, ∃ x : ℝ, 1 < x ∧ C < Real.log x ^ (2 : ℝ) * (Real.log x)⁻¹ := by
  intro C
  refine ⟨Real.exp (max C 0 + 1), by
    rw [← Real.exp_zero]; exact Real.exp_lt_exp.2 (by positivity), ?_⟩
  rw [Real.log_exp]
  have hpos : 0 < max C 0 + 1 := by positivity
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq, mul_assoc,
    mul_inv_cancel₀ hpos.ne', mul_one]
  linarith [le_max_left C 0]

/-! ### Small-prime absorption `Q₁ = b q₁` -/

theorem Q1_absorb {x b q1 θb θq : ℝ} (hx : 0 < x) (hq0 : 0 ≤ q1)
    (hb : b ≤ x ^ θb) (hq : q1 ≤ x ^ θq) : b * q1 ≤ x ^ (θb + θq) := by
  rw [Real.rpow_add hx]; exact mul_le_mul hb hq hq0 (by positivity)

/-! ### `e`-errors -/

/-- The `e`-error sum over `2 ≤ e ≤ e_max`. -/
def eErrors (E : ℕ → ℝ) (emax : ℕ) : ℝ := ∑ e ∈ Finset.Icc 2 emax, E e

/-- **At `e = 1` the `e`-errors are absent** (empty sum, proved). -/
theorem eErrors_absent_at_one (E : ℕ → ℝ) : eErrors E 1 = 0 := by
  unfold eErrors; rfl

/-! ### Pascadi range export (explicit hypothesis bundle; constants not supplied) -/

/-- The three Pascadi kernel range inequalities, as propositions in the exponents
`(θ_{Q₁}, θ_R, θ_S, θ_N, δ)`.  The second one is available **only from** the
Proposition-5.2 bound `θ_N ≤ 1/3 + δ` (referee repair R3). -/
structure PascadiRangeExport (θQ1 θR θS θN δ : ℝ) where
  ineq1 : Prop
  ineq2 : Prop
  ineq3 : Prop
  proof1 : ineq1
  proof2_of_prop52 : θN ≤ 1 / 3 + δ → ineq2
  proof3 : ineq3

/-- The second inequality is obtained exactly by feeding the Proposition-5.2 range. -/
theorem PascadiRangeExport.ineq2_holds {θQ1 θR θS θN δ : ℝ}
    (P : PascadiRangeExport θQ1 θR θS θN δ) (h52 : θN ≤ 1 / 3 + δ) : P.ineq2 :=
  P.proof2_of_prop52 h52

end Erdos287.SourceChain
