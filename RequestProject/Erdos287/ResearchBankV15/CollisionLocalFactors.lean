import Mathlib.Tactic
import RequestProject.Erdos287.ResearchBankV9.AsraCRT

/-!
# Erdős #287 — Research Bank V15 §B6: collision-preserving local factors

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

For a prime `p` put `ν_p = #{t mod p : p ∣ ∏_i (a_i t + 1)}` (`nu`), computed in `ZMod p`, so
roots shared by several coordinates (collisions) are counted **once**.

* `nu_le_card` — `ν_p ≤ K`;
* `nu_good` — at a good prime (`p ∤ a_i`, the `a_i` distinct mod `p`) the roots `−a_i⁻¹` are
  distinct and `ν_p = K`;
* `localFactor p = (1 − ν_p/p)/(1 − 1/p)^K` — the exact singular factor retained at the
  Mellin/Fourier origin; `localFactor_good` — its value at a good prime;
* `collision_only_at_differences` — reusing the V9 collision-zero theorem: two coordinates can
  share a prime divisor at a common `t` only when `p ∣ a_j − a_i`.

**Firewall.**  These are local (single-prime) identities.  The global asymptotic moment is **not**
inferred from the origin value: it is a separate main-term provider (`Normalization`,
`ZerothMomentContract`, `FirstMomentContract`).
-/

namespace Erdos287
namespace ResearchBankV15
namespace CollisionLocalFactors

open Classical in
/-- `ν_p` = number of roots of `∏_i (a_i t + 1)` modulo `p`. -/
noncomputable def nu {K : ℕ} (a : Fin K → ℕ) (p : ℕ) [Fact p.Prime] : ℕ :=
  (Finset.univ.filter fun t : ZMod p => ∃ i, (a i : ZMod p) * t + 1 = 0).card

/-- The exact singular factor at the origin. -/
noncomputable def localFactor {K : ℕ} (a : Fin K → ℕ) (p : ℕ) [Fact p.Prime] : ℝ :=
  (1 - (nu a p : ℝ) / p) / (1 - 1 / (p : ℝ)) ^ K

/-- A good prime for the tuple. -/
def GoodPrime {K : ℕ} (a : Fin K → ℕ) (p : ℕ) : Prop :=
  p.Prime ∧ (∀ i, ¬ p ∣ a i) ∧ ∀ i j, i ≠ j → ¬ (p : ℤ) ∣ (a j : ℤ) - a i

theorem roots_subset {K : ℕ} (a : Fin K → ℕ) (p : ℕ) [Fact p.Prime] :
    (Finset.univ.filter fun t : ZMod p => ∃ i, (a i : ZMod p) * t + 1 = 0) ⊆
      Finset.univ.image fun i => -((a i : ZMod p))⁻¹ := by
  intro t ht
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
  obtain ⟨i, hi⟩ := ht
  have hai : (a i : ZMod p) ≠ 0 := by
    intro h0; rw [h0, zero_mul, zero_add] at hi; exact one_ne_zero hi
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  refine ⟨i, ?_⟩
  rw [inv_eq_of_mul_eq_one_right (show (a i : ZMod p) * (-t) = 1 by linear_combination -hi),
    neg_neg]

/-- **`ν_p ≤ K`.** -/
theorem nu_le_card {K : ℕ} (a : Fin K → ℕ) (p : ℕ) [Fact p.Prime] : nu a p ≤ K := by
  classical
  unfold nu
  calc _ ≤ (Finset.univ.image fun i => -((a i : ZMod p))⁻¹).card :=
        Finset.card_le_card (roots_subset a p)
    _ ≤ (Finset.univ : Finset (Fin K)).card := Finset.card_image_le
    _ = K := by simp

/-- **At a good prime `ν_p = K`.** -/
theorem nu_good {K : ℕ} (a : Fin K → ℕ) (p : ℕ) [hp : Fact p.Prime] (hg : GoodPrime a p) :
    nu a p = K := by
  classical
  obtain ⟨-, hdiv, hsep⟩ := hg
  have hne : ∀ i, (a i : ZMod p) ≠ 0 := fun i h =>
    hdiv i ((ZMod.natCast_eq_zero_iff _ _).1 h)
  have heq : (Finset.univ.filter fun t : ZMod p => ∃ i, (a i : ZMod p) * t + 1 = 0) =
      Finset.univ.image fun i => -((a i : ZMod p))⁻¹ := by
    apply Finset.Subset.antisymm (roots_subset a p)
    intro t ht
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at ht
    obtain ⟨i, rfl⟩ := ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨i, by rw [mul_neg, mul_inv_cancel₀ (hne i)]; ring⟩
  have hinj : Function.Injective fun i => -((a i : ZMod p))⁻¹ := by
    intro i j hij
    by_contra hne'
    simp only [neg_inj, inv_inj] at hij
    apply hsep i j hne'
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hij, sub_self]
  unfold nu
  rw [heq, Finset.card_image_of_injective _ hinj]
  simp

/-- **The local factor at a good prime.** -/
theorem localFactor_good {K : ℕ} (a : Fin K → ℕ) (p : ℕ) [Fact p.Prime] (hg : GoodPrime a p) :
    localFactor a p = (1 - (K : ℝ) / p) / (1 - 1 / (p : ℝ)) ^ K := by
  unfold localFactor; rw [nu_good a p hg]

/-- A prime dividing every slope has no roots: `ν_p = 0` and the factor is `(1 − 1/p)^{−K}`. -/
theorem nu_eq_zero_of_dvd_all {K : ℕ} (a : Fin K → ℕ) (p : ℕ) [Fact p.Prime]
    (h : ∀ i, p ∣ a i) : nu a p = 0 := by
  classical
  unfold nu
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro t - ⟨i, hi⟩
  rw [(ZMod.natCast_eq_zero_iff _ _).2 (h i), zero_mul, zero_add] at hi
  exact one_ne_zero hi

/-- **Collisions only at differences** (V9 collision-zero reused): if `p ∤ a_j − a_i`, no `t`
has `p ∣ a_i t + 1` and `p ∣ a_j t + 1`. -/
theorem collision_only_at_differences {p : ℕ} {ai aj : ℤ} (h : ¬ (p : ℤ) ∣ aj - ai)
    (T : Finset ℤ) :
    T.filter (fun t => (p : ℤ) ∣ ai * t + 1 ∧ (p : ℤ) ∣ aj * t + 1) = ∅ :=
  (ResearchBankV9.AsraCRT.collision_zero (ak := ai) (ck := 1) (al := aj) (cl := 1)
    (by rwa [mul_one, mul_one]) T (fun _ => 0)).1

end CollisionLocalFactors
end ResearchBankV15
end Erdos287
