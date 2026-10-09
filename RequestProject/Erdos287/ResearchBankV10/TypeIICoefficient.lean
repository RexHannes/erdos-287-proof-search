import Mathlib

/-!
# Erdős #287 — Research Bank V10 §H: the Type-II grouped coefficient

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

The exact index map of the restored Type-II estimate

  `u = C q₁ n₂ n₂'`,  `v = q₂`,  `w = a k (h n₂' − h' n₂)`,

and the grouped coefficient defined **only on `(u, v, w)`**.

* `CoeffVars` — the coefficient-side packet variables `C, q₁, q₂, n₂, n₂', a, k, h, h'`;
  `SpectralVars` — the later spectral variables `c, r₁`, which are a **different type**;
* `indexMap` and `grouped S φ : ℤ × ℤ × ℤ → ℂ` — the grouped coefficient is a fibre sum over the
  index map; its type contains neither `c` nor `r₁`;
* `grouped_factorization` — the construction factors through the triple: for every spectral
  kernel `F`, `∑_x φ(x) F(u(x), v(x), w(x); σ) = ∑_{(u,v,w)} G(u, v, w) F(u, v, w; σ)`;
* `u_coprime_v`, `exists_reciprocal` — the exact gcd / invertibility conditions: from the packet
  coprimality hypotheses `(C, q₂) = (q₁, q₂) = (n₂, q₂) = (n₂', q₂) = 1`, `gcd(u, v) = 1`, hence the
  reciprocal `ū (mod v)` needed for the reciprocal phase exists;
* `w_ne_zero_iff` — `w ≠ 0 ⟺ a ≠ 0 ∧ k ≠ 0 ∧ h n₂' ≠ h' n₂`.

The Kloosterman-sum estimate itself stays external (`ZhengKloostermanInput` in `Providers`).
-/

namespace Erdos287
namespace ResearchBankV10
namespace TypeIICoefficient

open Finset

/-- Coefficient-side packet variables. -/
structure CoeffVars where
  C : ℤ
  q₁ : ℤ
  q₂ : ℤ
  n₂ : ℤ
  n₂' : ℤ
  a : ℤ
  k : ℤ
  h : ℤ
  h' : ℤ
  deriving DecidableEq

/-- The later spectral variables — a different type, never an argument of the coefficient. -/
structure SpectralVars where
  c : ℤ
  r₁ : ℤ
  deriving DecidableEq

/-- The index map `(u, v, w)`. -/
def indexMap (x : CoeffVars) : ℤ × ℤ × ℤ :=
  (x.C * x.q₁ * x.n₂ * x.n₂', x.q₂, x.a * x.k * (x.h * x.n₂' - x.h' * x.n₂))

/-- The grouped coefficient type: functions of `(u, v, w)` only. -/
abbrev GroupedCoeff2 := ℤ × ℤ × ℤ → ℂ

/-- The grouped coefficient: fibre sum of the packet weight over the index map. -/
noncomputable def grouped (S : Finset CoeffVars) (φ : CoeffVars → ℂ) : GroupedCoeff2 :=
  fun t => ∑ x ∈ S.filter (fun x => indexMap x = t), φ x

/-- **Factorization through the triple.** -/
theorem grouped_factorization (S : Finset CoeffVars) (φ : CoeffVars → ℂ)
    (F : ℤ × ℤ × ℤ → SpectralVars → ℂ) (σ : SpectralVars) :
    ∑ x ∈ S, φ x * F (indexMap x) σ = ∑ t ∈ S.image indexMap, grouped S φ t * F t σ := by
  unfold grouped
  simp_rw [Finset.sum_mul]
  rw [← Finset.sum_fiberwise_of_maps_to (g := indexMap) (fun x hx => Finset.mem_image_of_mem _ hx)]
  refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun x hx => ?_
  rw [(Finset.mem_filter.1 hx).2]

/-- A cleaner restatement: the grouped coefficient only sees `(u, v, w)`: two packets with the same
triple contribute to the same grouped value. -/
theorem grouped_depends_only_on_triple (S : Finset CoeffVars) (φ : CoeffVars → ℂ)
    {x y : CoeffVars} (h : indexMap x = indexMap y) :
    grouped S φ (indexMap x) = grouped S φ (indexMap y) := by rw [h]

/-- **Coprimality of `u` and `v`** from the packet hypotheses. -/
theorem u_coprime_v (x : CoeffVars) (hC : IsCoprime x.C x.q₂) (h1 : IsCoprime x.q₁ x.q₂)
    (h2 : IsCoprime x.n₂ x.q₂) (h3 : IsCoprime x.n₂' x.q₂) :
    IsCoprime (indexMap x).1 (indexMap x).2.1 := by
  simp only [indexMap]
  exact ((hC.mul_left h1).mul_left h2).mul_left h3

/-- **The reciprocal `ū (mod v)` exists.** -/
theorem exists_reciprocal (x : CoeffVars) (hC : IsCoprime x.C x.q₂) (h1 : IsCoprime x.q₁ x.q₂)
    (h2 : IsCoprime x.n₂ x.q₂) (h3 : IsCoprime x.n₂' x.q₂) :
    ∃ ubar : ℤ, (indexMap x).1 * ubar ≡ 1 [ZMOD (indexMap x).2.1] := by
  obtain ⟨α, β, hαβ⟩ := u_coprime_v x hC h1 h2 h3
  refine ⟨α, ?_⟩
  rw [Int.modEq_iff_dvd]
  exact ⟨β, by linarith⟩

/-- `w ≠ 0 ⟺ a ≠ 0 ∧ k ≠ 0 ∧ h n₂' ≠ h' n₂`. -/
theorem w_ne_zero_iff (x : CoeffVars) :
    (indexMap x).2.2 ≠ 0 ↔ x.a ≠ 0 ∧ x.k ≠ 0 ∧ x.h * x.n₂' ≠ x.h' * x.n₂ := by
  simp only [indexMap, ne_eq, mul_eq_zero, not_or, sub_eq_zero, and_assoc]

/-- `w = 0 ⟺ h n₂' = h' n₂` when `a, k ≠ 0` (the primitive-ratio diagonal). -/
theorem w_eq_zero_iff {x : CoeffVars} (ha : x.a ≠ 0) (hk : x.k ≠ 0) :
    (indexMap x).2.2 = 0 ↔ x.h * x.n₂' = x.h' * x.n₂ := by
  have := w_ne_zero_iff x
  constructor
  · intro h; by_contra h'; exact (this.2 ⟨ha, hk, h'⟩) h
  · intro h; by_contra h'; exact (this.1 h').2.2 h

end TypeIICoefficient
end ResearchBankV10
end Erdos287
