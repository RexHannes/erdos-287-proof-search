import Mathlib.Tactic

/-!
# Erdős #287 — Research Bank V9 §3B: the affine contact identity

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

For `F_i(t) = a_i t + 1` with `gcd(a_i, a_j) = a_j − a_i = g` (`0 < a_i < a_j`), kernel-proved:

* `affine_contact_identity` — `(a_j/g) F_i(t) − (a_i/g) F_j(t) = 1`;
* `contact_locations` — the adjacent physical locations `z = (a_i/g) F_j(t)` and
  `z + 1 = (a_j/g) F_i(t)`, with the explicit forms `z = u w g t + u`, `z + 1 = u w g t + w`
  (`u = a_i/g`, `w = a_j/g = u + 1`);
* `contact_in_window_iff` — the rational localization `c M ≤ z` and `z + 1 ≤ M` in explicit
  polynomial form.
-/

namespace Erdos287
namespace ResearchBankV9
namespace AffineContact

/-- The affine form `F(t) = a t + 1`. -/
def F (a t : ℕ) : ℕ := a * t + 1

/-- The cofactor decomposition: `a_i = g u`, `a_j = g w` with `w = u + 1`. -/
theorem cofactors {ai aj : ℕ} (hij : ai < aj) (hg : Nat.gcd ai aj = aj - ai) :
    ai = (aj - ai) * (ai / (aj - ai)) ∧ aj = (aj - ai) * (aj / (aj - ai)) ∧
      aj / (aj - ai) = ai / (aj - ai) + 1 := by
  set g := aj - ai with hgdef
  have hg0 : 0 < g := by omega
  have hdi : g ∣ ai := hg ▸ Nat.gcd_dvd_left ai aj
  have hdj : g ∣ aj := hg ▸ Nat.gcd_dvd_right ai aj
  obtain ⟨u, hu⟩ := hdi
  obtain ⟨w, hw⟩ := hdj
  have hu' : ai / g = u := by rw [hu, Nat.mul_div_cancel_left _ hg0]
  have hw' : aj / g = w := by rw [hw, Nat.mul_div_cancel_left _ hg0]
  rw [hu', hw']
  refine ⟨hu, hw, ?_⟩
  have h : g * w = g * (u + 1) := by rw [mul_add, ← hu, ← hw]; omega
  exact Nat.eq_of_mul_eq_mul_left hg0 h

/-- **The affine contact identity** `(a_j/g) F_i(t) − (a_i/g) F_j(t) = 1` (in `ℤ`). -/
theorem affine_contact_identity {ai aj : ℕ} (hij : ai < aj) (hg : Nat.gcd ai aj = aj - ai)
    (t : ℕ) :
    ((aj / (aj - ai) : ℕ) : ℤ) * (F ai t : ℤ) - ((ai / (aj - ai) : ℕ) : ℤ) * (F aj t : ℤ) = 1 := by
  obtain ⟨h1, h2, h3⟩ := cofactors hij hg
  set g := aj - ai
  set u := ai / g
  set w := aj / g
  unfold F
  rw [h1, h2, h3] at *
  push_cast
  ring

/-- **The adjacent physical locations.** -/
theorem contact_locations {ai aj : ℕ} (hij : ai < aj) (hg : Nat.gcd ai aj = aj - ai) (t : ℕ) :
    (ai / (aj - ai)) * F aj t + 1 = (aj / (aj - ai)) * F ai t ∧
    (ai / (aj - ai)) * F aj t =
      (ai / (aj - ai)) * (aj / (aj - ai)) * (aj - ai) * t + ai / (aj - ai) ∧
    (aj / (aj - ai)) * F ai t =
      (ai / (aj - ai)) * (aj / (aj - ai)) * (aj - ai) * t + aj / (aj - ai) := by
  obtain ⟨h1, h2, h3⟩ := cofactors hij hg
  set g := aj - ai
  set u := ai / g
  set w := aj / g
  unfold F
  refine ⟨?_, ?_, ?_⟩
  · rw [h1, h2, h3] at *; ring
  · conv_lhs => rw [h2]
    ring
  · conv_lhs => rw [h1]
    ring

/-- **Rational localization of the contact** in explicit form: with `u = a_i/g`, `w = a_j/g`,
the contact `z = u F_j(t)` satisfies `c M ≤ z` and `z + 1 ≤ M` iff
`c M ≤ u w g t + u` and `u w g t + w ≤ M`. -/
theorem contact_in_window_iff {ai aj : ℕ} (hij : ai < aj) (hg : Nat.gcd ai aj = aj - ai)
    (t M : ℕ) (c : ℝ) :
    (c * M ≤ ((ai / (aj - ai)) * F aj t : ℕ) ∧ (ai / (aj - ai)) * F aj t + 1 ≤ M) ↔
      (c * M ≤ (((ai / (aj - ai)) * (aj / (aj - ai)) * (aj - ai) * t + ai / (aj - ai) : ℕ) : ℝ) ∧
        (ai / (aj - ai)) * (aj / (aj - ai)) * (aj - ai) * t + aj / (aj - ai) ≤ M) := by
  obtain ⟨h1, h2, h3⟩ := contact_locations hij hg t
  rw [h2, ← h3, ← h1, h2]

/-- A concrete instance: `a = (2, 3)`, `g = 1`, `t = 2`: `F₂ = 5`, `F₃ = 7`, `3·5 − 2·7 = 1`. -/
theorem contact_example : Nat.gcd 2 3 = 3 - 2 ∧ F 2 2 = 5 ∧ F 3 2 = 7 ∧ 3 * 5 - 2 * 7 = 1 := by
  decide

end AffineContact
end ResearchBankV9
end Erdos287
