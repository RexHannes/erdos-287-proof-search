import RequestProject.Erdos287.CurrentTail.OrderingBSource

/-!
# Erdős #287 — current tail consolidation: the `E₁` (Maynard-type) interface

**ERDŐS #287 REMAINS OPEN.  TAIL-287 IS NOT BANKED.**

## Source side (kernel-proved)

* `convolution` — Dirichlet-type convolution `(β ⋆ γ)(k) = ∑_{m n = k} β_m γ_n` over finite
  supports;
* `coefficient_placement` — `∑_{m,n} β_m γ_n g(mn) = ∑_k (β ⋆ γ)(k) g(k)` (exact);
* `typeIIDiscrepancy` and `Delta_convolution` — the ordinary discrepancy of a convolution
  sequence *is* the Type-II discrepancy `∑_{m,n} β_m γ_n (1_{mn≡a(q)} - 1_{(mn,q)=1}/φ(q))`;
* `DeltaRel_convolution` — the Ordering-B relative discrepancy of a convolution is the Type-II
  discrepancy of the restricted convolution (the tiny base `f` stays inside the coefficient).

## Analytic side (isolated, never constructed)

* `E1Hypotheses` — **all** hypotheses of the Maynard-type estimate, each as a separate field:
  coefficient (divisor-power) bounds, the dyadic `N`-range, modulus range, coprimality,
  smoothness of the moduli, and a Siegel–Walfisz-type condition on `γ`;
* `MaynardE1Estimate θ σlo σhi δ B A` — the estimate itself: under `E1Hypotheses`,
  `∑_{q∈𝒬} |Δ^{II}(q, a)| ≤ C x (log x)^{-A}` for every `C > 0` and large `x`.
  Its conclusion speaks only about Type-II discrepancies: nothing about #287 or `R_Σ^P`.

What is **not** formalised (UNFORMALISED_SOURCE): the identification of the specific Ordering-B
`E₁` piece of `R_rel^main` with a sum of Type-II discrepancies satisfying `E1Hypotheses`
(the Maynard reduction / source dictionary).  It is recorded separately in
`RemainderRecombination.lean` as `OrderingBSourceDictionary`, never inside the provider.
-/

open scoped BigOperators
open Finset

namespace Erdos287.CurrentTail

/-- `(β ⋆ γ)(k) = ∑_{m ∈ 𝓜, n ∈ 𝓝, mn = k} β_m γ_n`. -/
noncomputable def convolution (Mset Nset : Finset ℕ) (β γ : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ p ∈ (Mset ×ˢ Nset).filter (fun p => p.1 * p.2 = k), β p.1 * γ p.2

/-- The product support `{mn}`. -/
def prodSupport (Mset Nset : Finset ℕ) : Finset ℕ := (Mset ×ˢ Nset).image (fun p => p.1 * p.2)

/-- **Coefficient placement.**  `∑_{m,n} β_m γ_n g(mn) = ∑_k (β ⋆ γ)(k) g(k)`. -/
theorem coefficient_placement (Mset Nset : Finset ℕ) (β γ : ℕ → ℝ) (g : ℕ → ℝ) :
    ∑ m ∈ Mset, ∑ n ∈ Nset, β m * γ n * g (m * n) =
      ∑ k ∈ prodSupport Mset Nset, convolution Mset Nset β γ k * g k := by
  rw [← Finset.sum_product' (f := fun m n => β m * γ n * g (m * n))]
  unfold prodSupport convolution
  rw [← Finset.sum_fiberwise_of_maps_to (s := Mset ×ˢ Nset)
    (t := (Mset ×ˢ Nset).image (fun p => p.1 * p.2)) (g := fun p => p.1 * p.2)
    (fun p hp => Finset.mem_image_of_mem _ hp)]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  rw [(Finset.mem_filter.1 hp).2]

/-- Type-II discrepancy. -/
noncomputable def typeIIDiscrepancy (Mset Nset : Finset ℕ) (β γ : ℕ → ℝ) (q a : ℕ) : ℝ :=
  ∑ m ∈ Mset, ∑ n ∈ Nset, β m * γ n *
    (ind (m * n ≡ a [MOD q]) - ind (Nat.Coprime (m * n) q) / (Nat.totient q : ℝ))

/-- The ordinary discrepancy of a convolution is its Type-II discrepancy. -/
theorem Delta_convolution (Mset Nset : Finset ℕ) (β γ : ℕ → ℝ) (q a : ℕ) :
    Delta (prodSupport Mset Nset) (convolution Mset Nset β γ) q a =
      typeIIDiscrepancy Mset Nset β γ q a := by
  unfold Delta typeIIDiscrepancy
  rw [coefficient_placement Mset Nset β γ
    (fun k => ind (k ≡ a [MOD q]) - ind (Nat.Coprime k q) / (Nat.totient q : ℝ))]

/-- **Ordering-B `E₁` source form.**  The relative discrepancy of a convolution equals the
Type-II discrepancy with the tiny-base restriction kept on the product `mn ≡ c (mod f)`. -/
theorem DeltaRel_convolution (Mset Nset : Finset ℕ) (β γ : ℕ → ℝ) (f c q a : ℕ) :
    DeltaRel (prodSupport Mset Nset) (convolution Mset Nset β γ) f c q a =
      ∑ m ∈ Mset, ∑ n ∈ Nset, β m * γ n * (ind (m * n ≡ c [MOD f]) *
        (ind (m * n ≡ a [MOD q]) - ind (Nat.Coprime (m * n) q) / (Nat.totient q : ℝ))) := by
  rw [DeltaRel_eq_sum]
  rw [coefficient_placement Mset Nset β γ (fun k => ind (k ≡ c [MOD f]) *
    (ind (k ≡ a [MOD q]) - ind (Nat.Coprime k q) / (Nat.totient q : ℝ)))]

/-- Siegel–Walfisz-type condition on `γ` at level `A₀`: for every modulus `q ≤ (log x)^{A₀}`
and class `a`, `|Δ_γ(q,a)| ≤ ‖γ‖₂ √N (log x)^{-A₀}`. -/
def SWCondition (x : ℝ) (Nset : Finset ℕ) (γ : ℕ → ℝ) (A0 : ℝ) : Prop :=
  ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.log x ^ A0 → ∀ a : ℕ,
    |Delta Nset γ q a| ≤ Real.sqrt (∑ n ∈ Nset, γ n ^ 2) * Real.sqrt Nset.card /
      Real.log x ^ A0

/-- **All hypotheses of the `E₁` estimate**, as separate fields. -/
structure E1Hypotheses (x : ℝ) (Mset Nset Qset : Finset ℕ) (β γ : ℕ → ℝ) (a : ℕ)
    (θ σlo σhi δ : ℝ) (B : ℕ) (A0 : ℝ) : Prop where
  coeff_beta : ∀ m ∈ Mset, |β m| ≤ (tau m : ℝ) ^ B
  coeff_gamma : ∀ n ∈ Nset, |γ n| ≤ (tau n : ℝ) ^ B
  N_range : ∀ n ∈ Nset, x ^ σlo ≤ n ∧ (n : ℝ) ≤ x ^ σhi
  MN_range : ∀ m ∈ Mset, ∀ n ∈ Nset, ((m * n : ℕ) : ℝ) ≤ x
  modulus_range : ∀ q ∈ Qset, 1 ≤ q ∧ (q : ℝ) ≤ x ^ θ
  coprime : ∀ q ∈ Qset, Nat.Coprime a q
  smooth : ∀ q ∈ Qset, ∀ p ∈ q.primeFactors, (p : ℝ) ≤ x ^ δ
  siegelWalfisz : SWCondition x Nset γ A0

/-- **Maynard-type `E₁` estimate (external analytic provider; never constructed).** -/
def MaynardE1Estimate (θ σlo σhi δ : ℝ) (B : ℕ) (A0 A : ℝ) : Prop :=
  ∀ C : ℝ, 0 < C → ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (Mset Nset Qset : Finset ℕ) (β γ : ℕ → ℝ) (a : ℕ),
    E1Hypotheses x Mset Nset Qset β γ a θ σlo σhi δ B A0 →
      ∑ q ∈ Qset, |typeIIDiscrepancy Mset Nset β γ q a| ≤ C * x / Real.log x ^ A

end Erdos287.CurrentTail
