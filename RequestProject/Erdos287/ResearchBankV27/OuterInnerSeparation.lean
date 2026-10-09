import Mathlib

/-!
# Erdős #287 — Research Bank V27 §5.3–5.4: outer / inner separation and the product cutoff

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

After `n₁ − n₂ = f d q` the OUTER variables are `o = (f, n₁, n₂, u₁, u₂, v₂)` and the INNER
variables are `(v₁, h)`.  Admissible decorations are `A(o)` (`|A| ≤ 1`) and `Ψ(v₁, h)`
(`|Ψ| ≤ 1`).

**LEAN BANK.**
* `InnerCoeff` — the type of inner decorations: functions of `(v₁, h)` ONLY;
* `decoration_firewall` — a decoration that depends on a final Kloosterman variable is NOT an
  inner decoration: there is `Φ(i, b)` with `Φ(i, b) ≠ Ψ(i)` for every candidate `Ψ`;
* `joint_dependence_allowed` — `Ψ` may depend JOINTLY on `(v₁, h)` (non-product example);
* **`product_cutoff_separation`** — exact discrete separation on a finite `v₁`-box:
  `1_{u₁ v₁ ≤ T₁} = Σ_{j ∈ V} 1_{u₁ j ≤ T₁} · 1_{v₁ = j}`;  the new phase `1_{v₁ = j}` is an
  INNER `v₁`-coefficient, the factor `1_{u₁ j ≤ T₁}` is OUTER;  `L¹` cost `#V`;
* `separated_inner_coeff_bounded` — `Ψ(v₁,h) · 1_{v₁ = j}` is again a one-bounded inner
  decoration.

**EXTERNAL PROVIDER.**
* `ProductCutoffFourierProvider` — the smooth (Fourier/Mellin) separation with `L¹` cost
  `≤ log^C x` (only needed if the `#V` cost of the exact discrete separation is too large).
-/

namespace Erdos287
namespace ResearchBankV27
namespace OuterInnerSeparation

/-- Inner decorations: functions of the inner variables `(v₁, h)` only. -/
abbrev InnerCoeff := ℤ × ℤ → ℂ

/-- One-boundedness of an inner decoration. -/
def OneBoundedInner (Ψ : InnerCoeff) : Prop := ∀ i, ‖Ψ i‖ ≤ 1

/-- **Typing firewall** (LEAN BANK): a decoration depending on a final Kloosterman variable
`b` cannot be written as an inner decoration. -/
theorem decoration_firewall :
    ∃ Φ : (ℤ × ℤ) × Bool → ℂ, ∀ Ψ : InnerCoeff, ∃ i b, Φ (i, b) ≠ Ψ i := by
  refine ⟨fun p => if p.2 then 1 else 0, fun Ψ => ?_⟩
  by_cases h : Ψ (0, 0) = 1
  · exact ⟨(0, 0), false, by simp [h]⟩
  · exact ⟨(0, 0), true, by simp; exact fun h' => h h'.symm⟩

/-- **Joint dependence on `(v₁, h)` is allowed** (LEAN BANK): `Ψ(v₁,h) = 1_{v₁ = h}` is a
one-bounded inner decoration that is not a product `a(v₁) b(h)`. -/
theorem joint_dependence_allowed :
    OneBoundedInner (fun i => if i.1 = i.2 then 1 else 0) ∧
      ¬ ∃ a b : ℤ → ℂ, ∀ v h, (if v = h then (1 : ℂ) else 0) = a v * b h := by
  refine ⟨fun i => by beta_reduce; split_ifs <;> simp, ?_⟩
  rintro ⟨a, b, hab⟩
  have h00 := hab 0 0
  have h11 := hab 1 1
  have h01 := hab 0 1
  have h10 := hab 1 0
  simp at h00 h11 h01 h10
  rcases h01 with h | h
  · rw [h, zero_mul] at h00; exact one_ne_zero h00
  · rw [h, mul_zero] at h11; exact one_ne_zero h11

/-- **Exact discrete separation of the product cutoff** (LEAN BANK). -/
theorem product_cutoff_separation (V : Finset ℤ) (u1 v1 T1 : ℤ) (hv : v1 ∈ V) :
    (if u1 * v1 ≤ T1 then (1 : ℂ) else 0) =
      ∑ j ∈ V, (if u1 * j ≤ T1 then (1 : ℂ) else 0) * (if v1 = j then 1 else 0) := by
  rw [Finset.sum_eq_single v1]
  · simp
  · intro j _ hj; rw [if_neg (Ne.symm hj), mul_zero]
  · intro h; exact absurd hv h

/-- The separated inner coefficient `Ψ_j(v₁,h) = Ψ(v₁,h) 1_{v₁ = j}` (inner only). -/
def separatedInner (Ψ : InnerCoeff) (j : ℤ) : InnerCoeff := fun i => Ψ i * if i.1 = j then 1 else 0

theorem separated_inner_coeff_bounded {Ψ : InnerCoeff} (hΨ : OneBoundedInner Ψ) (j : ℤ) :
    OneBoundedInner (separatedInner Ψ j) := by
  intro i; unfold separatedInner
  split_ifs
  · simpa using hΨ i
  · simp

/-- **Smooth product-cutoff separation** (EXTERNAL PROVIDER; never constructed): the cutoff is a
combination `Σ_t c_t a_t(u₁) b_t(v₁)` of one-bounded outer/inner factors with `Σ |c_t| ≤ L1`. -/
structure ProductCutoffFourierProvider (U V : Finset ℤ) (T1 L1 : ℝ) : Prop where
  sep : ∃ (ι : Type) (_ : Fintype ι) (c : ι → ℂ) (a b : ι → ℤ → ℂ),
    (∀ t u, ‖a t u‖ ≤ 1) ∧ (∀ t v, ‖b t v‖ ≤ 1) ∧ (∑ t, ‖c t‖ ≤ L1) ∧
    ∀ u ∈ U, ∀ v ∈ V, (if ((u * v : ℤ) : ℝ) ≤ T1 then (1 : ℂ) else 0) = ∑ t, c t * a t u * b t v

end OuterInnerSeparation
end ResearchBankV27
end Erdos287
