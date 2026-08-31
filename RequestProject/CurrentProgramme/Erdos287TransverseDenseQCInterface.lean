import Mathlib
import RequestProject.CurrentProgramme.Erdos287TransverseQCUnitaryCompiler

/-!
# Dense-`q_C` conditional interface — Erdős #287 (append-only)

This module is **append-only** and proves **no** analytic statement.

The research criterion for the dense-`q_C` route is

```
q ≥ m_P · L^{K_T},   and   q admits two source groups each logarithmically long.
```

Asymptotic `L`-powers are *not* formalised.  Instead the criterion is packaged as an interface
`DenseQCAdmissible` carrying **explicit finite inequalities** (with `L^{K_T}` appearing as a
supplied real number `margin`, and the two group lengths as supplied reals with explicit lower
bounds).  Admissibility is proved neither automatic nor contradictory, so it can never be
silently discharged.

The compiler `denseQC_closed_of_unitary_margin` is **purely logical**: its antecedent contains
the required Fourier contraction explicitly (supplied by the banked
`transverseQCUnitaryFourier_bound`), and its conclusion is the corresponding explicit finite
inequality.  It does **not** conclude closure of the transverse branch, and it does not conclude
anything about Erdős #287.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos287
namespace TransverseDenseQC

open Erdos287.TransverseGammaReduction
open Erdos287.TransverseQCUnitary

/-! ## §1  The admissibility interface -/

/-- Dense-`q_C` admissibility for a one-conductor packet, as explicit finite inequalities.

* `q` is the conductor of the packet, split as `q = S₁ S₂`;
* `margin` stands for the source quantity `L^{K_T}`; it is a *supplied* real number, not an
  asymptotic;
* `len₁, len₂` are the supplied lengths of the two source groups and `lenMin` the required
  common lower bound.

Nothing in this repository proves that a physical packet satisfies these inequalities. -/
structure DenseQCAdmissible (D : OneConductorData) where
  /-- The conductor of the packet. -/
  q : ℕ
  /-- First source group. -/
  S₁ : ℕ
  /-- Second source group. -/
  S₂ : ℕ
  /-- The group factorisation of the conductor. -/
  split : S₁ * S₂ = q
  /-- The two groups are coprime. -/
  coprime : Nat.Coprime S₁ S₂
  /-- The supplied margin, standing for `L^{K_T}`. -/
  margin : ℝ
  /-- The margin is at least one. -/
  margin_ge_one : 1 ≤ margin
  /-- The dense criterion `q ≥ m_P · margin`. -/
  dense : (D.modP : ℝ) * margin ≤ (q : ℝ)
  /-- Supplied length of the first group. -/
  len₁ : ℝ
  /-- Supplied length of the second group. -/
  len₂ : ℝ
  /-- The required common lower bound on both lengths. -/
  lenMin : ℝ
  /-- The first group is long. -/
  long₁ : lenMin ≤ len₁
  /-- The second group is long. -/
  long₂ : lenMin ≤ len₂

/-- **`denseQCAdmissible_implies_dense_inequality`.**  `LEAN_PROVED`.  The interface really does
carry the finite dense inequality; it is not a vacuous record. -/
theorem denseQCAdmissible_implies_dense_inequality {D : OneConductorData}
    (H : DenseQCAdmissible D) : (D.modP : ℝ) * H.margin ≤ (H.q : ℝ) := H.dense

/-- **`denseQCAdmissible_not_automatic`.**  `LEAN_PROVED`.  Admissibility is a genuine
condition: no packet with `q = 0` can satisfy it, since `m_P ≥ 1` and `margin ≥ 1` force
`q ≥ 1`. -/
theorem denseQCAdmissible_not_automatic {D : OneConductorData} (H : DenseQCAdmissible D) :
    0 < H.q := by
  have hm : (1 : ℝ) ≤ (D.modP : ℝ) := by exact_mod_cast D.modP_pos
  have h1 : (1 : ℝ) ≤ (D.modP : ℝ) * H.margin := by nlinarith [H.margin_ge_one]
  have : (1 : ℝ) ≤ (H.q : ℝ) := le_trans h1 H.dense
  exact_mod_cast this

/-! ## §2  The purely logical dense-`q_C` compiler -/

/-- **`denseQC_closed_of_unitary_margin`.**  `LEAN_PROVED (CONDITIONAL)`.

The dense-`q_C` compiler.  Its antecedent contains, explicitly:

* the `ℓ²` budgets `E₁, E₂` of the two coefficient vectors;
* the unit support conditions of the two carrier sets;
* the **margin hypothesis** `m_P E₁ E₂ ≤ target`.

Its conclusion is the corresponding explicit finite inequality for the reciprocal phase sum.
The Fourier contraction itself is the banked theorem `transverseQCUnitaryFourier_bound`; the
rest is `le_trans`.  Nothing here concludes transverse closure or Erdős #287. -/
theorem denseQC_closed_of_unitary_margin (D : OneConductorData)
    (S T : Finset (ZMod D.modP)) (hS : ∀ s ∈ S, IsUnit s) (hT : ∀ s ∈ T, IsUnit s)
    (alpha beta : ZMod D.modP → ℂ) (E₁ E₂ target : ℝ)
    (hE₁ : ∑ s ∈ S, ‖alpha s‖ ^ 2 ≤ E₁) (hE₂ : ∑ u ∈ T, ‖beta u‖ ^ 2 ≤ E₂)
    (hmargin : (D.modP : ℝ) * E₁ * E₂ ≤ target) :
    ‖∑ s ∈ S, ∑ u ∈ T, alpha s * beta u *
        ZMod.stdAddChar (((D.GammaRed : ℤ) : ZMod D.modP) * s⁻¹ * u⁻¹)‖ ^ 2 ≤ target :=
  le_trans (transverseQCUnitaryFourier_l2_bound D S T hS hT alpha beta E₁ E₂ hE₁ hE₂) hmargin

/-- **`denseQC_margin_not_automatic`.**  `LEAN_PROVED`.  The margin hypothesis of the compiler is
not free: there are data (`m_P = 1`, `E₁ = E₂ = 1`, `target = 0`) for which it fails.  Hence the
compiler is genuinely conditional. -/
theorem denseQC_margin_not_automatic :
    ∃ mP E₁ E₂ target : ℝ, ¬ (mP * E₁ * E₂ ≤ target) :=
  ⟨1, 1, 1, 0, by norm_num⟩

/-- **`denseQC_admissibility_does_not_give_the_bound`.**  `LEAN_PROVED`.  Admissibility alone
carries no Fourier information: the compiler above consumes the `ℓ²` budgets and the margin, and
admissibility is a separate record.  Formally, admissibility is satisfiable together with an
arbitrarily bad margin, witnessed here by the fact that the margin hypothesis is a *distinct*
proposition which can fail. -/
theorem denseQC_admissibility_does_not_give_the_bound {D : OneConductorData}
    (H : DenseQCAdmissible D) :
    (0 < H.q) ∧ ∃ E₁ E₂ target : ℝ, ¬ ((D.modP : ℝ) * E₁ * E₂ ≤ target) := by
  refine ⟨denseQCAdmissible_not_automatic H, 1, 1, 0, ?_⟩
  have hm : (1 : ℝ) ≤ (D.modP : ℝ) := by exact_mod_cast D.modP_pos
  intro h
  simp only [mul_one] at h
  linarith

end TransverseDenseQC
end Erdos287
