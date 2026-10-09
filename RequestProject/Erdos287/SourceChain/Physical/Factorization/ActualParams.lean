import RequestProject.Erdos287.SourceChain.Physical.TypeII.Constructed

/-!
# Erdős #287 — discharging the actual physical atom parameters

**ERDŐS #287 REMAINS OPEN.  TAIL-287 IS NOT BANKED.**

The scalar levels are those of `Scalar/Weights.lean`:
`D_low = D_int^{ε₀}`, `D_int = D_tot^{1/(1+ε₀+τ)}`, `D_tot = X^{59/100}`, `τ = ε₀⁹`, `ε₀ = 1/T`.

* `Dlow_eq_rpow_beta` — `D_low = X^β` with `β = 59 ε₀ / (100 (1 + ε₀ + ε₀⁹))` (proved, not
  defined that way).
* `CritRegime S κ` — the **small-`ε₀` regime** of `sources/physical_spec.md` §18 for the
  critical-range parameter `κ`: `0 < κ < 10⁻⁵`, `T ≥ 100/κ` (and the standing `T ≥ 2`, `X > 1`).
  This is **not** an arbitrary `ScalarParams.Good`.
* `Tchoice κ = ⌈100/κ⌉₊ + 2` and `critRegime_Tchoice` — a compatible fixed `T` exists for every
  `κ ∈ (0, 10⁻⁵)` and every `X > 1`.
* `beta_lt_kappa` — `β < κ/100` in the regime.
* `Dlow_sq_le` — `D_low² ≤ X^{κ/2}` in the regime (Pascadi `δ = κ`), **no hypothesis**.
* `CritCell S κ N` — the actual critical individual-variable range
  `X^{3κ} ≤ N ≤ X^{1/3+κ/2}`.
* `atomParams_of_crit` — every `AtomParams` field for `δ = κ`, in particular
  `X^{2δ} ≤ N / D_low` and `N ≤ X^{1/3+δ}`.
* `atom_factorization_actual` — `atom_factorization_clean` for the actual source with **both**
  former parameter hypotheses (`AtomParams S δ N` and `D_low² ≤ X^{δ/2}`) discharged.
-/

open Finset Real

set_option autoImplicit false

namespace Erdos287.Physical.Sieve.ScalarParams

open Erdos287.Physical.Factor

variable {S : ScalarParams}

/-- `β = 59 ε₀ / (100 (1 + ε₀ + ε₀⁹))`, the exponent of `D_low`. -/
noncomputable def beta (S : ScalarParams) : ℝ :=
  59 * S.eps0 / (100 * (1 + S.eps0 + S.eps0 ^ 9))

/-- **`D_low = X^β`**. -/
theorem Dlow_eq_rpow_beta (hS : S.Good) : S.Dlow = S.X ^ S.beta := by
  have hX : 0 ≤ S.X := by linarith [hS.X_gt]
  have he := expo_pos hS
  unfold Dlow Dint Dtot beta
  rw [← Real.rpow_mul hX, ← Real.rpow_mul hX]
  congr 1
  unfold tau
  field_simp

theorem beta_pos (hS : S.Good) : 0 < S.beta := by
  unfold beta
  have := eps0_pos hS
  positivity

theorem beta_le (hS : S.Good) : S.beta ≤ 59 / 100 * S.eps0 := by
  unfold beta
  have he := eps0_pos hS
  have h9 : 0 ≤ S.eps0 ^ 9 := by positivity
  rw [div_le_iff₀ (by positivity)]
  nlinarith

/-- **The small-`ε₀` regime** for the critical-range parameter `κ`. -/
structure CritRegime (S : ScalarParams) (κ : ℝ) : Prop where
  good : S.Good
  κ_pos : 0 < κ
  κ_small : κ < 1 / 100000
  T_large : 100 / κ ≤ (S.T : ℝ)

/-- A compatible fixed choice of `T` for `κ`. -/
noncomputable def Tchoice (κ : ℝ) : ℕ := ⌈100 / κ⌉₊ + 2

/-- **Existence of a compatible `T`**: for every `κ ∈ (0, 10⁻⁵)` and every `X > 1`, the
parameters `(X, Tchoice κ)` lie in the regime. -/
theorem critRegime_Tchoice {κ X : ℝ} (hκ : 0 < κ) (hκ' : κ < 1 / 100000) (hX : 1 < X) :
    CritRegime ⟨X, Tchoice κ⟩ κ := by
  refine ⟨⟨show 2 ≤ Tchoice κ by unfold Tchoice; omega, hX⟩, hκ, hκ', ?_⟩
  show 100 / κ ≤ ((⌈100 / κ⌉₊ + 2 : ℕ) : ℝ)
  push_cast
  linarith [Nat.le_ceil (100 / κ)]

theorem eps0_le_of_regime {κ : ℝ} (h : CritRegime S κ) : S.eps0 ≤ κ / 100 := by
  have hT := T_pos h.good
  have hκ := h.κ_pos
  unfold eps0
  rw [div_le_div_iff₀ hT (by norm_num)]
  have := h.T_large
  rw [div_le_iff₀ hκ] at this
  linarith

/-- **`β < κ/100`** in the small-`ε₀` regime. -/
theorem beta_lt_kappa {κ : ℝ} (h : CritRegime S κ) : S.beta < κ / 100 := by
  have h1 := beta_le h.good
  have h2 := eps0_le_of_regime h
  have := h.κ_pos
  nlinarith

/-- **`D_low² ≤ X^{κ/2}`** (no hypothesis beyond the regime). -/
theorem Dlow_sq_le {κ : ℝ} (h : CritRegime S κ) : S.Dlow ^ 2 ≤ S.X ^ (κ / 2) := by
  have hS := h.good
  have hX : 0 < S.X := by linarith [hS.X_gt]
  rw [Dlow_eq_rpow_beta hS, ← Real.rpow_natCast, ← Real.rpow_mul hX.le]
  apply Real.rpow_le_rpow_of_exponent_le hS.X_gt.le
  have := beta_lt_kappa h
  have := h.κ_pos
  push_cast
  linarith

/-- The actual critical individual-variable range `X^{3κ} ≤ N ≤ X^{1/3+κ/2}`. -/
structure CritCell (S : ScalarParams) (κ N : ℝ) : Prop where
  N_lo : S.X ^ (3 * κ) ≤ N
  N_hi : N ≤ S.X ^ (1 / 3 + κ / 2)

/-- `X^{2κ} ≤ N / D_low` on a critical cell. -/
theorem crit_N_lo {κ N : ℝ} (h : CritRegime S κ) (hN : CritCell S κ N) :
    S.X ^ (2 * κ) ≤ N / S.Dlow := by
  have hS := h.good
  have hX : 0 < S.X := by linarith [hS.X_gt]
  have hDl : 0 < S.Dlow := lt_of_lt_of_le one_pos (Dlow_ge_one hS)
  rw [le_div_iff₀ hDl, Dlow_eq_rpow_beta hS, ← Real.rpow_add hX]
  refine le_trans (Real.rpow_le_rpow_of_exponent_le hS.X_gt.le ?_) hN.N_lo
  have := beta_lt_kappa h
  have := h.κ_pos
  linarith

/-- `N ≤ X^{1/3+κ}` on a critical cell. -/
theorem crit_N_hi {κ N : ℝ} (h : CritRegime S κ) (hN : CritCell S κ N) :
    N ≤ S.X ^ (1 / 3 + κ) :=
  hN.N_hi.trans (Real.rpow_le_rpow_of_exponent_le h.good.X_gt.le (by linarith [h.κ_pos]))

/-- **All `AtomParams` inequalities for `δ = κ`, derived for actual critical cells.** -/
theorem atomParams_of_crit {κ N : ℝ} (h : CritRegime S κ) (hN : CritCell S κ N) :
    AtomParams S κ N :=
  ⟨h.good, h.κ_pos, h.κ_small, crit_N_lo h hN, crit_N_hi h hN⟩

/-- **Pascadi factorization of every actual atom, parameter hypotheses discharged.**
For `T` in the small-`ε₀` regime of `κ` and a critical cell `N`, every nonzero atom
`d = b ∏ q_i` factors as `d₁ d₂ d₃` satisfying Pascadi's system (5.3) with `δ/2 = κ/2`. -/
theorem atom_factorization_actual {κ N : ℝ} (h : CritRegime S κ) (hN : CritCell S κ N)
    {J : ℕ} {P : Fin J → Fin S.H} (hP : S.BoxAdm J P) {b : ℕ} (hb : S.kappa J b ≠ 0)
    {q : Fin J → ℕ} (hq : q ∈ S.tuples J P) :
    let c := S.atomColour κ N J P
    b * ∏ i, q i = (b * tupleFactor c 0 q) * tupleFactor c 1 q * tupleFactor c 2 q ∧
      Sys53 S.X (κ / 2) N (b * tupleFactor c 0 q : ℕ) (tupleFactor c 1 q) (tupleFactor c 2 q) :=
  atom_factorization_clean (atomParams_of_crit h hN) (Dlow_sq_le h) hP hb hq

end Erdos287.Physical.Sieve.ScalarParams
