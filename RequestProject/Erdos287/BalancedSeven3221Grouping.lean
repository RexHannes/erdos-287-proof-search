import Mathlib
import RequestProject.Erdos287.FactorialEulerPolarization

/-!
# V17, Phase A — the exact labelled `1+2+2+2` regrouping of the seven-slot source

`BALANCED7-3221-GROUPING45`.

The V16 bank proves the factorial Euler polarization identity: for `Ω(m) = 7`,

`7^7 · [z_1 ⋯ z_7] F_z(m) = ∑_{t ∈ ordFact 7 m} ∏_i ω_i(t i)`,

the sum running over **ordered** prime 7-tuples with product `m`, repetitions included
(`Erdos287.FactorialEuler.factorialEulerPolarization_seven`).  The 3221 arrangement groups
the seven labelled slots as

`{0} ∪ {1,2} ∪ {3,4} ∪ {5,6}`,  `e = p₀`, `m = p₁p₂`, `n = p₃p₄`, `ℓ = p₅p₆`.

## What is proved here

* `block_card_sum`, `blocks_disjoint`, `blocks_cover` — the labelled partition of `Fin 7`
  into blocks of sizes `1+2+2+2 = 7`.
* `grouped_product_eq` — `e · m · n · ℓ = p₀p₁p₂p₃p₄p₅p₆` for every seven-tuple.
* **Multiplicity firewall.**  `grouping_not_injective` exhibits two *distinct* prime
  seven-tuples with the same `(e,m,n,ℓ)`, so the pair-product map is provably **not**
  injective; `alpha_not_one_bounded` exhibits a value of the pair coefficient `α` equal to
  `2` for unimodular `ω`, so `α, β, γ` are provably **not** 1-bounded.  Nothing downstream
  may assume either.
* `prod_apply_tuples` — the general exact expansion of an iterated Dirichlet convolution as
  a sum over ordered `k`-tuples with prescribed product.  This is the engine that keeps all
  convolution multiplicities exact.
* `sevenfold_regrouping` — the literal regrouping

  `∑_{t ∈ ordFact 7 m} ∏_i ω_i(t i) = ∑_{e·a·b·c = m} η(e) α(a) β(b) γ(c)`,

  with `α = g₁ * g₂`, `β = g₃ * g₄`, `γ = g₅ * g₆` the *exact* prime-restricted Dirichlet
  convolutions, i.e. with every convolution multiplicity retained.
* `alpha_apply_prime_pairs` — `α(a) = ∑_{p₁p₂ = a, both prime} ω₁(p₁) ω₂(p₂)`.
* `alpha_norm_le_card_divisors` — the honest divisor-majorant statement for the pair
  coefficients: `‖α(a)‖ ≤ τ(a)` for unimodular `ω`.  **No `X^{o(1)}` is defined anywhere.**

**Honesty statement.**  Everything in this file is a finite algebraic identity or a finite
counting bound.  No analytic estimate is proved, assumed, or implied.  Erdős #287 remains
OPEN.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset ArithmeticFunction
open scoped BigOperators

namespace Erdos287
namespace Grouping3221

/-! ## §4a. The labelled `1+2+2+2` partition of `Fin 7` -/

/-- The `e`-block `{0}`. -/
def blockE : Finset (Fin 7) := {0}

/-- The `m`-block `{1,2}`. -/
def blockM : Finset (Fin 7) := {1, 2}

/-- The `n`-block `{3,4}`. -/
def blockN : Finset (Fin 7) := {3, 4}

/-- The `ℓ`-block `{5,6}`. -/
def blockL : Finset (Fin 7) := {5, 6}

/-- `1 + 2 + 2 + 2 = 7`. -/
theorem block_card_sum :
    blockE.card + blockM.card + blockN.card + blockL.card = 7 := by decide

/-- The individual block cardinalities. -/
theorem block_cards :
    blockE.card = 1 ∧ blockM.card = 2 ∧ blockN.card = 2 ∧ blockL.card = 2 := by decide

/-- The four blocks are pairwise disjoint. -/
theorem blocks_disjoint :
    Disjoint blockE blockM ∧ Disjoint blockE blockN ∧ Disjoint blockE blockL ∧
      Disjoint blockM blockN ∧ Disjoint blockM blockL ∧ Disjoint blockN blockL := by decide

/-- The four blocks cover `Fin 7`. -/
theorem blocks_cover : blockE ∪ blockM ∪ blockN ∪ blockL = Finset.univ := by decide

/-! ## §4b. The grouped physical values -/

/-- `e = p₀`. -/
def gE (p : Fin 7 → ℕ) : ℕ := p 0

/-- `m = p₁ p₂`. -/
def gM (p : Fin 7 → ℕ) : ℕ := p 1 * p 2

/-- `n = p₃ p₄`. -/
def gN (p : Fin 7 → ℕ) : ℕ := p 3 * p 4

/-- `ℓ = p₅ p₆`. -/
def gL (p : Fin 7 → ℕ) : ℕ := p 5 * p 6

/-- **`e · m · n · ℓ = p₀ p₁ p₂ p₃ p₄ p₅ p₆`.** -/
theorem grouped_product_eq (p : Fin 7 → ℕ) :
    gE p * gM p * gN p * gL p = ∏ i, p i := by
  simp only [gE, gM, gN, gL, Fin.prod_univ_seven]
  ring

/-! ## §4c. Multiplicity firewall

The map `(p₀,…,p₆) ↦ (e,m,n,ℓ)` is **not** injective, and the pair coefficients are **not**
1-bounded.  Both facts are proved by explicit witnesses, so that no later step can quietly
assume the contrary. -/

/-- Witness one: `(2,2,3,3,3,3,3)`. -/
def wit₁ : Fin 7 → ℕ := ![2, 2, 3, 3, 3, 3, 3]

/-- Witness two: `(2,3,2,3,3,3,3)`. -/
def wit₂ : Fin 7 → ℕ := ![2, 3, 2, 3, 3, 3, 3]

/-- **Multiplicity firewall.**  Two distinct ordered prime seven-tuples with the *same*
grouped values `(e,m,n,ℓ)`: taking pair products destroys injectivity. -/
theorem grouping_not_injective :
    wit₁ ≠ wit₂ ∧ (∀ i, (wit₁ i).Prime) ∧ (∀ i, (wit₂ i).Prime) ∧
      gE wit₁ = gE wit₂ ∧ gM wit₁ = gM wit₂ ∧ gN wit₁ = gN wit₂ ∧ gL wit₁ = gL wit₂ := by
  refine ⟨?_, ?_, ?_, by decide, by decide, by decide, by decide⟩
  · intro h
    have := congrFun h 1
    simp [wit₁, wit₂] at this
  · decide
  · decide

/-! ## §4d. Ordered `k`-tuples with prescribed product, and iterated convolution -/

variable {K : Type*} [CommRing K]

/-- The finset of ordered `k`-tuples of naturals with product `m`. -/
def tuples (k m : ℕ) : Finset (Fin k → ℕ) :=
  (Fintype.piFinset (fun _ : Fin k => m.divisors)).filter (fun t => ∏ i, t i = m)

/-- For `m ≠ 0`, membership in `tuples k m` is exactly the product condition. -/
theorem mem_tuples {k m : ℕ} (hm : m ≠ 0) (t : Fin k → ℕ) :
    t ∈ tuples k m ↔ ∏ i, t i = m := by
  classical
  simp only [tuples, Finset.mem_filter, Fintype.mem_piFinset, Nat.mem_divisors]
  constructor
  · rintro ⟨-, h⟩; exact h
  · intro h
    exact ⟨fun i => ⟨h ▸ Finset.dvd_prod_of_mem t (Finset.mem_univ i), hm⟩, h⟩

/-- **Exact expansion of an iterated Dirichlet convolution.**  For `m ≠ 0`,

`(f₀ ⋆ ⋯ ⋆ f_{k-1})(m) = ∑_{t₀ ⋯ t_{k-1} = m} ∏_i f_i(t_i)`,

the sum being over *ordered* tuples, so all multiplicities are exact. -/
theorem prod_apply_tuples : ∀ (k : ℕ) (f : Fin k → ArithmeticFunction K) {m : ℕ}, m ≠ 0 →
    (∏ i, f i) m = ∑ t ∈ tuples k m, ∏ i, (f i) (t i) := by
  intro k
  induction k with
  | zero =>
      intro f m hm
      classical
      simp only [Finset.univ_eq_empty, Finset.prod_empty, ArithmeticFunction.one_apply, tuples]
      by_cases h : m = 1
      · subst h; simp
      · rw [if_neg h, Finset.sum_eq_zero]
        intro t ht
        simp only [Finset.mem_filter] at ht
        exact absurd ht.2.symm h
  | succ k ih =>
      intro f m hm
      classical
      rw [Fin.prod_univ_succ, ArithmeticFunction.mul_apply]
      have step : ∀ x ∈ m.divisorsAntidiagonal,
          (f 0) x.1 * (∏ i : Fin k, f i.succ) x.2
            = ∑ s ∈ tuples k x.2, (f 0) x.1 * ∏ i : Fin k, (f i.succ) (s i) := by
        intro x hx
        rw [Nat.mem_divisorsAntidiagonal] at hx
        have hne : x.1 * x.2 ≠ 0 := by rw [hx.1]; exact hm
        rw [ih (fun i => f i.succ) (right_ne_zero_of_mul hne), Finset.mul_sum]
      rw [Finset.sum_congr rfl step, Finset.sum_sigma']
      refine Finset.sum_nbij' (i := fun x => Fin.cons x.1.1 x.2)
          (j := fun t => ⟨(t 0, ∏ i : Fin k, t i.succ), Fin.tail t⟩) ?_ ?_ ?_ ?_ ?_
      · rintro ⟨⟨d, e⟩, s⟩ hmem
        simp only [Finset.mem_sigma, Nat.mem_divisorsAntidiagonal] at hmem
        obtain ⟨⟨hde, -⟩, hs⟩ := hmem
        have hne : d * e ≠ 0 := by rw [hde]; exact hm
        have he : e ≠ 0 := right_ne_zero_of_mul hne
        rw [mem_tuples hm, Fin.prod_univ_succ]
        simp only [Fin.cons_zero, Fin.cons_succ]
        rw [(mem_tuples he s).mp hs, hde]
      · intro t ht
        rw [mem_tuples hm] at ht
        have hrest : (∏ i : Fin k, t i.succ) ≠ 0 := by
          rintro h
          rw [Fin.prod_univ_succ, h, mul_zero] at ht; exact hm ht.symm
        simp only [Finset.mem_sigma, Nat.mem_divisorsAntidiagonal]
        refine ⟨⟨?_, hm⟩, ?_⟩
        · rw [← Fin.prod_univ_succ]; exact ht
        · rw [mem_tuples hrest]; rfl
      · rintro ⟨⟨d, e⟩, s⟩ hmem
        simp only [Finset.mem_sigma, Nat.mem_divisorsAntidiagonal] at hmem
        obtain ⟨⟨hde, -⟩, hs⟩ := hmem
        have hne : d * e ≠ 0 := by rw [hde]; exact hm
        have hprod : (∏ i : Fin k, s i) = e := (mem_tuples (right_ne_zero_of_mul hne) s).mp hs
        simp [hprod]
      · intro t ht
        simp
      · rintro ⟨⟨d, e⟩, s⟩ hmem
        simp [Fin.prod_univ_succ]

/-! ## §4e. Prime-restricted coefficients and the pair convolutions -/

/-- The prime-restricted arithmetic function attached to a weight `w : ℕ → K`. -/
def primeRestrict (w : ℕ → K) : ArithmeticFunction K :=
  ⟨fun n => if n.Prime then w n else 0, by simp [Nat.not_prime_zero]⟩

@[simp] theorem primeRestrict_apply (w : ℕ → K) (n : ℕ) :
    (primeRestrict w) n = if n.Prime then w n else 0 := rfl

variable (om : ℕ → Fin 7 → K)

/-- The seven prime-restricted slot functions `g_i`. -/
def slot (i : Fin 7) : ArithmeticFunction K := primeRestrict (fun p => om p i)

/-- `η = g₀` — the single-prime block. -/
def eta : ArithmeticFunction K := slot om 0

/-- `α = g₁ ⋆ g₂` — the `m`-block pair coefficient, with exact multiplicities. -/
def alpha : ArithmeticFunction K := slot om 1 * slot om 2

/-- `β = g₃ ⋆ g₄` — the `n`-block pair coefficient. -/
def beta : ArithmeticFunction K := slot om 3 * slot om 4

/-- `γ = g₅ ⋆ g₆` — the `ℓ`-block pair coefficient. -/
def gamma : ArithmeticFunction K := slot om 5 * slot om 6

/-- `α(a) = ∑_{p₁p₂ = a, both prime} ω₁(p₁) ω₂(p₂)`. -/
theorem alpha_apply_prime_pairs (a : ℕ) :
    (alpha om) a
      = ∑ x ∈ a.divisorsAntidiagonal with (x.1.Prime ∧ x.2.Prime), om x.1 1 * om x.2 2 := by
  classical
  rw [alpha, ArithmeticFunction.mul_apply, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  by_cases h1 : x.1.Prime <;> by_cases h2 : x.2.Prime <;> simp [slot, h1, h2]

/-- Likewise for `β`. -/
theorem beta_apply_prime_pairs (a : ℕ) :
    (beta om) a
      = ∑ x ∈ a.divisorsAntidiagonal with (x.1.Prime ∧ x.2.Prime), om x.1 3 * om x.2 4 := by
  classical
  rw [beta, ArithmeticFunction.mul_apply, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  by_cases h1 : x.1.Prime <;> by_cases h2 : x.2.Prime <;> simp [slot, h1, h2]

/-- Likewise for `γ`. -/
theorem gamma_apply_prime_pairs (a : ℕ) :
    (gamma om) a
      = ∑ x ∈ a.divisorsAntidiagonal with (x.1.Prime ∧ x.2.Prime), om x.1 5 * om x.2 6 := by
  classical
  rw [gamma, ArithmeticFunction.mul_apply, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  by_cases h1 : x.1.Prime <;> by_cases h2 : x.2.Prime <;> simp [slot, h1, h2]

/-! ## §4f. The regrouping identity -/

/-- The seven-slot labelled sum, expanded over unrestricted ordered seven-tuples: the
prime restriction lives in the coefficients. -/
theorem sevenfold_tuples_eq_ordFact {m : ℕ} (hm : m ≠ 0) :
    ∑ t ∈ tuples 7 m, ∏ i, (slot om i) (t i)
      = ∑ t ∈ Erdos287.FactorialEuler.ordFact 7 m, ∏ i, om (t i) i := by
  classical
  rw [← Finset.sum_subset
      (s₁ := Erdos287.FactorialEuler.ordFact 7 m) (s₂ := tuples 7 m)
      (f := fun t => ∏ i, (slot om i) (t i))]
  · refine Finset.sum_congr rfl (fun t ht => ?_)
    rw [Erdos287.FactorialEuler.mem_ordFact_iff hm] at ht
    exact Finset.prod_congr rfl (fun i _ => by simp [slot, ht.1 i])
  · intro t ht
    rw [Erdos287.FactorialEuler.mem_ordFact_iff hm] at ht
    rw [mem_tuples hm]
    exact ht.2
  · intro t ht htn
    rw [mem_tuples hm] at ht
    rw [Erdos287.FactorialEuler.mem_ordFact_iff hm] at htn
    push_neg at htn
    obtain ⟨i, hi⟩ := not_forall.mp (fun h => htn h ht)
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    simp [slot, hi]

/-- **The exact `1+2+2+2` regrouping.**  For `m ≠ 0`,

`∑_{t ∈ ordFact 7 m} ∏_i ω_i(t i) = ∑_{e·a·b·c = m} η(e) α(a) β(b) γ(c)`,

with `α, β, γ` the exact prime-restricted pair convolutions: every convolution multiplicity
is retained, and no injectivity of `(p₀,…,p₆) ↦ (e,m,n,ℓ)` is used (indeed
`grouping_not_injective` shows there is none). -/
theorem sevenfold_regrouping {m : ℕ} (hm : m ≠ 0) :
    ∑ t ∈ Erdos287.FactorialEuler.ordFact 7 m, ∏ i, om (t i) i
      = ∑ u ∈ tuples 4 m,
          (eta om) (u 0) * (alpha om) (u 1) * (beta om) (u 2) * (gamma om) (u 3) := by
  classical
  have h7 : (∏ i, slot om i) m = ∑ t ∈ tuples 7 m, ∏ i, (slot om i) (t i) :=
    prod_apply_tuples 7 _ hm
  have h4 : (∏ j, ![eta om, alpha om, beta om, gamma om] j) m
      = ∑ u ∈ tuples 4 m, ∏ j, (![eta om, alpha om, beta om, gamma om] j) (u j) :=
    prod_apply_tuples 4 _ hm
  have hring : (∏ i, slot om i) = (∏ j, ![eta om, alpha om, beta om, gamma om] j) := by
    simp only [Fin.prod_univ_seven, Fin.prod_univ_four, eta, alpha, beta, gamma,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.tail_cons]
    ring
  calc ∑ t ∈ Erdos287.FactorialEuler.ordFact 7 m, ∏ i, om (t i) i
      = ∑ t ∈ tuples 7 m, ∏ i, (slot om i) (t i) := (sevenfold_tuples_eq_ordFact om hm).symm
    _ = (∏ i, slot om i) m := h7.symm
    _ = (∏ j, ![eta om, alpha om, beta om, gamma om] j) m := by rw [hring]
    _ = ∑ u ∈ tuples 4 m, ∏ j, (![eta om, alpha om, beta om, gamma om] j) (u j) := h4
    _ = ∑ u ∈ tuples 4 m,
          (eta om) (u 0) * (alpha om) (u 1) * (beta om) (u 2) * (gamma om) (u 3) := by
        refine Finset.sum_congr rfl (fun u _ => ?_)
        simp [Fin.prod_univ_four]

/-- Every term of the regrouped sum satisfies the physical constraint `e · a · b · c = m`. -/
theorem tuples_four_product {m : ℕ} (hm : m ≠ 0) {u : Fin 4 → ℕ} (hu : u ∈ tuples 4 m) :
    u 0 * u 1 * u 2 * u 3 = m := by
  have := (mem_tuples hm u).mp hu
  rwa [Fin.prod_univ_four] at this

/-! ## §4g. Divisor-majorant bound for the pair coefficients

The correct statement is a **divisor** bound, not a 1-bound.  `alpha_not_one_bounded`
below shows the 1-bound is false. -/

/-- The number of ordered pairs of naturals with product `a` is `τ(a)`. -/
theorem card_divisorsAntidiagonal (a : ℕ) :
    a.divisorsAntidiagonal.card = a.divisors.card := by
  rw [← Nat.map_div_right_divisors]
  simp

/-- **Divisor majorant for the pair coefficients.**  If the prime weights are unimodular
then `‖α(a)‖ ≤ τ(a)`; the same proof gives `β` and `γ`. -/
theorem alpha_norm_le_card_divisors (om : ℕ → Fin 7 → ℂ)
    (hb : ∀ p i, ‖om p i‖ ≤ 1) (a : ℕ) :
    ‖(alpha om) a‖ ≤ (a.divisors.card : ℝ) := by
  classical
  rw [alpha, ArithmeticFunction.mul_apply]
  calc ‖∑ x ∈ a.divisorsAntidiagonal, (slot om 1) x.1 * (slot om 2) x.2‖
      ≤ ∑ x ∈ a.divisorsAntidiagonal, ‖(slot om 1) x.1 * (slot om 2) x.2‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _x ∈ a.divisorsAntidiagonal, (1 : ℝ) := by
        refine Finset.sum_le_sum (fun x _ => ?_)
        rw [norm_mul]
        have h1 : ‖(slot om 1) x.1‖ ≤ 1 := by
          by_cases h : x.1.Prime <;> simp [slot, h, hb]
        have h2 : ‖(slot om 2) x.2‖ ≤ 1 := by
          by_cases h : x.2.Prime <;> simp [slot, h, hb]
        exact mul_le_one₀ h1 (norm_nonneg _) h2
    _ = (a.divisors.card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one, card_divisorsAntidiagonal]

/-- **The pair coefficients are not 1-bounded.**  With all weights equal to `1`, the value
of `α` at `6 = 2·3 = 3·2` is `2`.  Hence no step may treat `α, β, γ` as unimodular. -/
theorem alpha_not_one_bounded :
    (alpha (fun _ _ => (1 : ℂ))) 6 = 2 := by
  classical
  rw [alpha_apply_prime_pairs,
    show (Nat.divisorsAntidiagonal 6) = {(1, 6), (2, 3), (3, 2), (6, 1)} from by decide]
  norm_num [Finset.filter_insert, Finset.sum_insert, Nat.prime_two, Nat.prime_three]

end Grouping3221
end Erdos287
