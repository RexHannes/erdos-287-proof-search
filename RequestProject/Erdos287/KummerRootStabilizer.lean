import Mathlib

/-!
# Quadratic-Kummer backend, layer 2: the root-stabilizer algebra

The claim to be hostile-checked is:

> for a squarefree quadratic `F` and nonzero `n₁, n₂` (mod `p`), the product
> `F(n₁X)·F(n₂X)` can be a square polynomial only when multiplication by `n₂/n₁`
> preserves the unordered pair of roots of `F`; that stabilizer has at most two
> elements.

It is formalized here over an **arbitrary field** `K` — in particular over `ZMod p`
for an odd prime `p`, but also in characteristic `2` — and **without** passing to a
splitting field: the criterion is stated and proved on the coefficients, so the
irreducible case is covered with no assumption that the roots lie in `K`.

Conventions.  `quadPoly a b c = aX² + bX + c`, the discriminant is `b² − 4ac`, and the
scaling `F(nX)` is `(quadPoly a b c).comp (C n * X) = quadPoly (a n²) (b n) c`
(`quadPoly_comp_scale`).  The degenerate strata are excluded explicitly:

* `a ≠ 0` (genuine degree two),
* `b² − 4ac ≠ 0` (no repeated root — the repeated-root router is a *different* sector),
* `n₁ ≠ 0`, `n₂ ≠ 0`.

## Main results

* `quadPoly_squarefree` — nonzero discriminant ⟹ squarefree (any characteristic);
* `quadratic_scaling_square_criterion` — if `F(n₁X)·F(n₂X)` is a square then
  `n₂ = n₁` or `n₂ = −n₁`;
* `quadratic_scaling_square_criterion_of_b_ne_zero` — if moreover `b ≠ 0` then
  `n₂ = n₁`;
* `scalingSquareStabilizer_subset` / `scalingSquareStabilizer_ncard_le_two` — the
  stabilizer is contained in `{n₁, −n₁}` and so has at most two elements;
* `repeated_root_scaling_square` — a counterexample in the excluded repeated-root
  sector, showing the discriminant hypothesis is necessary.
-/

open Polynomial

namespace Erdos287
namespace Kummer

variable {K : Type*} [Field K]

/-- The quadratic `aX² + bX + c`. -/
noncomputable def quadPoly (a b c : K) : K[X] := C a * X ^ 2 + C b * X + C c

@[simp] theorem quadPoly_coeff_zero (a b c : K) : (quadPoly a b c).coeff 0 = c := by
  simp [quadPoly]

@[simp] theorem quadPoly_coeff_one (a b c : K) : (quadPoly a b c).coeff 1 = b := by
  simp [quadPoly]

@[simp] theorem quadPoly_coeff_two (a b c : K) : (quadPoly a b c).coeff 2 = a := by
  simp [quadPoly]

theorem quadPoly_natDegree {a : K} (b c : K) (ha : a ≠ 0) :
    (quadPoly a b c).natDegree = 2 := natDegree_quadratic ha

theorem quadPoly_ne_zero {a : K} (b c : K) (ha : a ≠ 0) : quadPoly a b c ≠ 0 := by
  intro h
  have := quadPoly_coeff_two a b c
  rw [h] at this
  exact ha this.symm

/-- Scaling the variable: `F(nX) = quadPoly (a n²) (b n) c`. -/
theorem quadPoly_comp_scale (a b c n : K) :
    (quadPoly a b c).comp (C n * X) = quadPoly (a * n ^ 2) (b * n) c := by
  simp only [quadPoly, add_comp, mul_comp, C_comp, X_comp, pow_comp, C_mul, C_pow]
  ring

/-- The Bézout identity `4a·F − (F')² = 4ac − b²`, valid in every characteristic. -/
theorem quadPoly_bezout (a b c : K) :
    C (4 * a) * quadPoly a b c - derivative (quadPoly a b c) * derivative (quadPoly a b c)
      = C (4 * a * c - b ^ 2) := by
  simp only [quadPoly, derivative_add, derivative_mul, derivative_C, derivative_X,
    derivative_X_pow, C_mul, C_sub, C_pow, map_ofNat, zero_mul, add_zero, zero_add,
    mul_one, Nat.cast_ofNat]
  ring

/-- Nonzero discriminant ⟹ separable. -/
theorem quadPoly_separable {a b c : K} (hdisc : b ^ 2 - 4 * a * c ≠ 0) :
    (quadPoly a b c).Separable := by
  have hE : 4 * a * c - b ^ 2 ≠ 0 := fun h => hdisc (by linear_combination -h)
  rw [separable_def]
  refine ⟨C (4 * a) * C (4 * a * c - b ^ 2)⁻¹,
    -(C (4 * a * c - b ^ 2)⁻¹ * derivative (quadPoly a b c)), ?_⟩
  have key := quadPoly_bezout a b c
  have : C (4 * a) * C (4 * a * c - b ^ 2)⁻¹ * quadPoly a b c
      + -(C (4 * a * c - b ^ 2)⁻¹ * derivative (quadPoly a b c))
        * derivative (quadPoly a b c)
      = C (4 * a * c - b ^ 2)⁻¹ *
        (C (4 * a) * quadPoly a b c
          - derivative (quadPoly a b c) * derivative (quadPoly a b c)) := by ring
  rw [this, key, ← C_mul, inv_mul_cancel₀ hE, C_1]

/-- Nonzero discriminant ⟹ squarefree. -/
theorem quadPoly_squarefree {a b c : K} (hdisc : b ^ 2 - 4 * a * c ≠ 0) :
    Squarefree (quadPoly a b c) := (quadPoly_separable hdisc).squarefree

/-- The scaled discriminant: `(bn)² − 4(an²)c = n²(b² − 4ac)`. -/
theorem scaled_disc {a b c n : K} (hn : n ≠ 0) (hdisc : b ^ 2 - 4 * a * c ≠ 0) :
    (b * n) ^ 2 - 4 * (a * n ^ 2) * c ≠ 0 := by
  intro h
  refine hdisc ?_
  have hn2 : n ^ 2 ≠ 0 := pow_ne_zero 2 hn
  field_simp at h ⊢
  rcases mul_eq_zero.1 (by linear_combination h : (b ^ 2 - 4 * a * c) * n ^ 2 = 0) with h1 | h1
  · exact h1
  · exact absurd h1 hn2

/-- **Core step.**  If `F(n₁X)·F(n₂X)` is a square, the two scaled quadratics differ by a
square constant factor. -/
theorem exists_const_of_scaling_square {a b c n₁ n₂ : K} {G : K[X]}
    (ha : a ≠ 0) (hdisc : b ^ 2 - 4 * a * c ≠ 0) (h1 : n₁ ≠ 0) (h2 : n₂ ≠ 0)
    (hsq : quadPoly (a * n₁ ^ 2) (b * n₁) c * quadPoly (a * n₂ ^ 2) (b * n₂) c = G ^ 2) :
    ∃ v : K, v ≠ 0 ∧ quadPoly (a * n₂ ^ 2) (b * n₂) c
      = quadPoly (a * n₁ ^ 2) (b * n₁) c * C v := by
  set A := quadPoly (a * n₁ ^ 2) (b * n₁) c with hA
  set B := quadPoly (a * n₂ ^ 2) (b * n₂) c with hB
  have ha1 : a * n₁ ^ 2 ≠ 0 := mul_ne_zero ha (pow_ne_zero 2 h1)
  have ha2 : a * n₂ ^ 2 ≠ 0 := mul_ne_zero ha (pow_ne_zero 2 h2)
  have hAsf : Squarefree A := quadPoly_squarefree (scaled_disc h1 hdisc)
  have hA0 : A ≠ 0 := quadPoly_ne_zero _ _ ha1
  have hB0 : B ≠ 0 := quadPoly_ne_zero _ _ ha2
  -- `A ∣ G²`, hence `A ∣ G`
  have hdvd2 : A ∣ G ^ 2 := ⟨B, hsq.symm⟩
  have hdvd : A ∣ G := (hAsf.dvd_pow_iff_dvd (by norm_num)).1 hdvd2
  obtain ⟨H, hH⟩ := hdvd
  have hBH : B = A * H ^ 2 := by
    have : A * B = A * (A * H ^ 2) := by rw [hsq, hH]; ring
    exact mul_left_cancel₀ hA0 this
  -- degrees force `H` to be a nonzero constant
  have hH0 : H ≠ 0 := by
    intro hh
    apply hB0
    rw [hBH, hh]
    ring
  have hdegB : B.natDegree = 2 := quadPoly_natDegree _ _ ha2
  have hdegA : A.natDegree = 2 := quadPoly_natDegree _ _ ha1
  have hdeg : B.natDegree = A.natDegree + 2 * H.natDegree := by
    rw [hBH, natDegree_mul hA0 (pow_ne_zero 2 hH0), natDegree_pow]
  have hHdeg : H.natDegree = 0 := by omega
  obtain ⟨u, hu⟩ := natDegree_eq_zero.1 hHdeg
  refine ⟨u ^ 2, ?_, ?_⟩
  · have : u ≠ 0 := by
      intro h
      rw [h] at hu
      simp at hu
      exact hH0 hu.symm
    exact pow_ne_zero 2 this
  · rw [hBH, ← hu, ← C_pow]

/-- **Root-stabilizer criterion (coefficient form).**  For a squarefree quadratic `F` and
nonzero `n₁, n₂`, if `F(n₁X)·F(n₂X)` is a square then `n₂ = ±n₁`. -/
theorem quadratic_scaling_square_criterion {a b c n₁ n₂ : K} {G : K[X]}
    (ha : a ≠ 0) (hdisc : b ^ 2 - 4 * a * c ≠ 0) (h1 : n₁ ≠ 0) (h2 : n₂ ≠ 0)
    (hsq : quadPoly (a * n₁ ^ 2) (b * n₁) c * quadPoly (a * n₂ ^ 2) (b * n₂) c = G ^ 2) :
    n₂ = n₁ ∨ n₂ = -n₁ := by
  obtain ⟨v, hv0, hv⟩ := exists_const_of_scaling_square ha hdisc h1 h2 hsq
  -- compare coefficients
  have e0 : c = c * v := by
    have := congrArg (fun p => Polynomial.coeff p 0) hv
    simpa [coeff_mul_C] using this
  have e1 : b * n₂ = b * n₁ * v := by
    have := congrArg (fun p => Polynomial.coeff p 1) hv
    simpa [coeff_mul_C] using this
  have e2 : a * n₂ ^ 2 = a * n₁ ^ 2 * v := by
    have := congrArg (fun p => Polynomial.coeff p 2) hv
    simpa [coeff_mul_C] using this
  by_cases hc : c = 0
  · -- `c = 0`: then `b ≠ 0` (else the discriminant vanishes) and `n₂ = n₁`
    have hb : b ≠ 0 := by
      intro hb0
      apply hdisc
      rw [hb0, hc]; ring
    have hv1 : n₂ = n₁ * v := by
      have hbz : b * (n₂ - n₁ * v) = 0 := by linear_combination e1
      rcases mul_eq_zero.1 hbz with h' | h'
      · exact absurd h' hb
      · linear_combination h'
    have key : a * n₁ * n₂ * (n₂ - n₁) = 0 := by
      linear_combination n₁ * e2 - a * n₁ ^ 2 * hv1
    have h4 : n₂ - n₁ = 0 := by
      rcases mul_eq_zero.1 key with h' | h'
      · exact absurd h' (mul_ne_zero (mul_ne_zero ha h1) h2)
      · exact h'
    left
    linear_combination h4
  · -- `c ≠ 0`: then `v = 1` and `n₂² = n₁²`
    have hv1 : v = 1 := by
      have hcv : c * (v - 1) = 0 := by linear_combination -e0
      rcases mul_eq_zero.1 hcv with h' | h'
      · exact absurd h' hc
      · linear_combination h'
    rw [hv1, mul_one] at e2
    have hfac : a * (n₂ - n₁) * (n₂ + n₁) = 0 := by linear_combination e2
    rcases mul_eq_zero.1 hfac with h' | h'
    · rcases mul_eq_zero.1 h' with h'' | h''
      · exact absurd h'' ha
      · left; linear_combination h''
    · right; linear_combination h'

/-- With `b ≠ 0` (a non-centred quadratic) the stabilizer collapses to the identity. -/
theorem quadratic_scaling_square_criterion_of_b_ne_zero {a b c n₁ n₂ : K} {G : K[X]}
    (ha : a ≠ 0) (hb : b ≠ 0) (hdisc : b ^ 2 - 4 * a * c ≠ 0) (h1 : n₁ ≠ 0) (h2 : n₂ ≠ 0)
    (hsq : quadPoly (a * n₁ ^ 2) (b * n₁) c * quadPoly (a * n₂ ^ 2) (b * n₂) c = G ^ 2) :
    n₂ = n₁ ∨ (n₂ = -n₁ ∧ (2 : K) = 0) := by
  rcases quadratic_scaling_square_criterion ha hdisc h1 h2 hsq with h | h
  · exact Or.inl h
  · obtain ⟨v, hv0, hv⟩ := exists_const_of_scaling_square ha hdisc h1 h2 hsq
    have e0 : c = c * v := by
      have := congrArg (fun p => Polynomial.coeff p 0) hv
      simpa [coeff_mul_C] using this
    have e1 : b * n₂ = b * n₁ * v := by
      have := congrArg (fun p => Polynomial.coeff p 1) hv
      simpa [coeff_mul_C] using this
    have e2 : a * n₂ ^ 2 = a * n₁ ^ 2 * v := by
      have := congrArg (fun p => Polynomial.coeff p 2) hv
      simpa [coeff_mul_C] using this
    -- from `n₂ = -n₁` and `n₂² = n₁²` we get `v = 1`, hence `b n₂ = b n₁`, hence `2n₁ = 0`
    have hv1 : v = 1 := by
      have hz : a * n₁ ^ 2 * (v - 1) = 0 := by
        have hsq2 : n₂ ^ 2 = n₁ ^ 2 := by rw [h]; ring
        rw [hsq2] at e2; linear_combination -e2
      rcases mul_eq_zero.1 hz with h' | h'
      · exact absurd h' (mul_ne_zero ha (pow_ne_zero 2 h1))
      · linear_combination h'
    rw [hv1, mul_one, h] at e1
    have hz2 : b * (2 * n₁) = 0 := by linear_combination -e1
    rcases mul_eq_zero.1 hz2 with h' | h'
    · exact absurd h' hb
    · rcases mul_eq_zero.1 h' with h'' | h''
      · exact Or.inr ⟨h, h''⟩
      · exact absurd h'' h1

/-- The scaling stabilizer of a squarefree quadratic, as a set. -/
def scalingSquareStabilizer (a b c n₁ : K) : Set K :=
  {n₂ : K | n₂ ≠ 0 ∧ ∃ G : K[X],
    quadPoly (a * n₁ ^ 2) (b * n₁) c * quadPoly (a * n₂ ^ 2) (b * n₂) c = G ^ 2}

/-- **Stabilizer containment.** -/
theorem scalingSquareStabilizer_subset {a b c n₁ : K}
    (ha : a ≠ 0) (hdisc : b ^ 2 - 4 * a * c ≠ 0) (h1 : n₁ ≠ 0) :
    scalingSquareStabilizer a b c n₁ ⊆ {n₁, -n₁} := by
  rintro n₂ ⟨h2, G, hG⟩
  rcases quadratic_scaling_square_criterion ha hdisc h1 h2 hG with h | h
  · exact Or.inl h
  · exact Or.inr h

/-- **Stabilizer cardinality: at most two.** -/
theorem scalingSquareStabilizer_ncard_le_two {a b c n₁ : K}
    (ha : a ≠ 0) (hdisc : b ^ 2 - 4 * a * c ≠ 0) (h1 : n₁ ≠ 0) :
    (scalingSquareStabilizer a b c n₁).ncard ≤ 2 := by
  have hsub := scalingSquareStabilizer_subset ha hdisc h1
  have hfin : ({n₁, -n₁} : Set K).Finite := (Set.finite_singleton _).insert _
  calc (scalingSquareStabilizer a b c n₁).ncard ≤ ({n₁, -n₁} : Set K).ncard :=
        Set.ncard_le_ncard hsub hfin
    _ ≤ 2 := by
        refine le_trans (Set.ncard_insert_le _ _) ?_
        simp

/-- The identity is always in the stabilizer, so the bound is not vacuous. -/
theorem mem_scalingSquareStabilizer_self {a b c n₁ : K} (h1 : n₁ ≠ 0) :
    n₁ ∈ scalingSquareStabilizer a b c n₁ :=
  ⟨h1, quadPoly (a * n₁ ^ 2) (b * n₁) c, (sq _).symm⟩

/-- **The discriminant hypothesis is necessary.**  In the excluded repeated-root sector
(`disc = 0`) the product is a square for *every* pair of nonzero scalings: with
`a = 1, b = 0, c = 0` one has `F = X²` and `F(n₁X)F(n₂X) = (n₁n₂X²)²`. -/
theorem repeated_root_scaling_square (n₁ n₂ : K) :
    quadPoly (1 * n₁ ^ 2) (0 * n₁) 0 * quadPoly (1 * n₂ ^ 2) (0 * n₂) 0
      = (C (n₁ * n₂) * X ^ 2) ^ 2 := by
  simp only [quadPoly, one_mul, zero_mul, map_zero, add_zero, C_mul, C_pow]
  ring

end Kummer
end Erdos287
