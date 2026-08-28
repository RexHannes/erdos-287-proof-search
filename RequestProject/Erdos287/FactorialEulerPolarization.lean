import Mathlib
import RequestProject.Erdos287.BalancedSevenPolarization

/-!
# V16, Part 2 — the factorial (divided-power) Euler polarization identity

Working entry point for the new controlling finite/algebraic input of the V16 audit.

For a field `K` of characteristic zero (so that `e!` is invertible; `ℂ` is the intended
instance) and a matrix of prime weights `om p i = ω_i(p)` we set

* `linForm  N om p  = ∑_i ω_i(p) · z_i`,
* `divPowerFactor N om p e = (e !)⁻¹ · (∑_i ω_i(p) z_i)^e`,
* `Fdiv N om m = ∏_{p ∣ m} divPowerFactor N om p (v_p(m))`,

i.e. exactly the multiplicative extension of `F_z(p^e) = a_z(p)^e / e!` with the `1/N`
normalisation of `a_z` factored out (it is restored in the `N = 7` statement below).

The main theorem `factorialEulerPolarization` says: if `Ω(m) = N` then

`[z_1 ⋯ z_N] Fdiv N om m = ∑_{(p_1,…,p_N) ordered, p_1⋯p_N = m} ∏_i ω_i(p_i)`,

the sum running over the finset `ordFact N m` of **ordered** factorisations of `m` into `N`
primes, *including* the ones with repeated primes; `mem_ordFact_iff` certifies that
`ordFact N m` is literally the set of such tuples.  The factorials `∏_p v_p(m)!` cancel
exactly the number of permutations of equal prime occurrences: this is `fiber_card_eq`,
which rests on Mathlib's `DomMulAct.stabilizer_card'`.

`factorialEulerPolarization_seven` is the requested `N = 7` form with the genuine
normalisation `a_z(p) = (1/7) ∑_i z_i ω_i(p)`, giving the factor `7^7`.

Status: `OMEGA7-FACTORIAL-EULER-POLARIZATION45 : PROVED_ALGEBRAIC`.

**Honesty statement.**  This is a finite coefficient-extraction identity for polynomials.
No analytic convergence, no Euler product, no exponent of distribution, no class-`C`
theorem and no distribution estimate is proved or assumed here.  Erdős #287 remains OPEN.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MvPolynomial Finset
open scoped BigOperators

namespace Erdos287
namespace FactorialEuler

open Erdos287.BalancedSeven

variable {K : Type*} [Field K] [CharZero K]

/-! ## The polarized local data -/

/-- The linear form `L_p(z) = ∑_i ω_i(p) z_i`. -/
noncomputable def linForm (N : ℕ) (om : ℕ → Fin N → K) (p : ℕ) : MvPolynomial (Fin N) K :=
  ∑ i, C (om p i) * X i

/-- The divided-power local factor `L_p^e / e !`, i.e. `F_z(p^e)` before normalisation. -/
noncomputable def divPowerFactor (N : ℕ) (om : ℕ → Fin N → K) (p e : ℕ) :
    MvPolynomial (Fin N) K :=
  C ((e.factorial : K)⁻¹) * (linForm N om p) ^ e

/-- The multiplicative extension `F_z(m) = ∏_p F_z(p^{v_p(m)})`. -/
noncomputable def Fdiv (N : ℕ) (om : ℕ → Fin N → K) (m : ℕ) : MvPolynomial (Fin N) K :=
  ∏ p ∈ m.primeFactors, divPowerFactor N om p (m.factorization p)

omit [CharZero K] in
@[simp] theorem Fdiv_one (N : ℕ) (om : ℕ → Fin N → K) : Fdiv N om 1 = 1 := by
  simp [Fdiv]

omit [CharZero K] in
/-- On a prime power the extension really is the divided power `a^e / e !`. -/
theorem Fdiv_primePow (N : ℕ) (om : ℕ → Fin N → K) {p e : ℕ} (hp : p.Prime) (he : e ≠ 0) :
    Fdiv N om (p ^ e) = divPowerFactor N om p e := by
  have h1 : (p ^ e).primeFactors = {p} := by
    rw [Nat.primeFactors_pow p he, hp.primeFactors]
  have h2 : (p ^ e).factorization p = e := by
    rw [Nat.Prime.factorization_pow hp]
    simp
  rw [Fdiv, h1, Finset.prod_singleton, h2]

/-! ## Ordered factorisations into `N` primes -/

/-- The finset of **ordered** `N`-tuples of primes with product `m` (repetitions allowed). -/
def ordFact (N m : ℕ) : Finset (Fin N → ℕ) :=
  (Fintype.piFinset fun _ => m.primeFactors).filter (fun f => ∏ i, f i = m)

/-- `ordFact N m` is literally the set of ordered prime `N`-tuples with product `m`. -/
theorem mem_ordFact_iff {N m : ℕ} (hm : m ≠ 0) (f : Fin N → ℕ) :
    f ∈ ordFact N m ↔ (∀ i, (f i).Prime) ∧ ∏ i, f i = m := by
  classical
  simp only [ordFact, Finset.mem_filter, Fintype.mem_piFinset, Nat.mem_primeFactors]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun i => (h1 i).1, h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨fun i => ⟨h1 i, ?_, hm⟩, h2⟩
    exact h2 ▸ Finset.dvd_prod_of_mem f (Finset.mem_univ i)

/-! ## Counting occurrences of a prime in an ordered factorisation -/

/-- In an ordered prime factorisation of `m`, the prime `v` occurs exactly `v_p(m)` times. -/
theorem count_eq_factorization {N m : ℕ} (q : Fin N → ℕ) (hq : ∀ i, (q i).Prime)
    (hm : ∏ i, q i = m) (v : ℕ) :
    (univ.filter fun i => q i = v).card = m.factorization v := by
  classical
  have h0 : ∀ i ∈ (univ : Finset (Fin N)), q i ≠ 0 := fun i _ => (hq i).ne_zero
  have := Nat.factorization_prod (S := (univ : Finset (Fin N))) (g := q) h0
  rw [hm] at this
  rw [this]
  have hsum : (∑ i : Fin N, (q i).factorization) v = ∑ i : Fin N, ((q i).factorization) v := by
    simp
  rw [hsum]
  have : ∀ i : Fin N, ((q i).factorization) v = if q i = v then 1 else 0 := by
    intro i
    rw [(hq i).factorization]
    simp [Finsupp.single_apply, eq_comm]
  simp [this, Finset.sum_boole]

/-! ## Two ordered factorisations differ by a permutation -/

/-- If two tuples have the same fibre cardinalities then they differ by a permutation. -/
theorem exists_perm_comp {N : ℕ} (p q : Fin N → ℕ)
    (h : ∀ v, (univ.filter fun i => p i = v).card = (univ.filter fun i => q i = v).card) :
    ∃ σ : Equiv.Perm (Fin N), q ∘ σ = p := by
  classical
  have hcard : ∀ v : ℕ, Fintype.card {i : Fin N // p i = v} = Fintype.card {i // q i = v} := by
    intro v
    rw [Fintype.card_subtype, Fintype.card_subtype]
    exact h v
  have e : ∀ v : ℕ, {i : Fin N // p i = v} ≃ {i : Fin N // q i = v} :=
    fun v => (Fintype.card_eq.mp (hcard v)).some
  refine ⟨((Equiv.sigmaFiberEquiv p).symm.trans (Equiv.sigmaCongrRight e)).trans
    (Equiv.sigmaFiberEquiv q), ?_⟩
  funext i
  exact ((e (p i)) ⟨i, rfl⟩).2

/-! ## The orbit of a listing is the set of ordered factorisations -/

/-- The image of the permutation action on a fixed listing is exactly `ordFact N m`. -/
theorem image_perm_eq_ordFact {N m : ℕ} (q : Fin N → ℕ) (hq : ∀ i, (q i).Prime)
    (hm : ∏ i, q i = m) :
    Finset.image (fun σ : Equiv.Perm (Fin N) => q ∘ (σ : Fin N → Fin N)) univ
      = ordFact N m := by
  classical
  have hm0 : m ≠ 0 := by
    rw [← hm]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => (hq i).ne_zero
  ext f
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  rw [mem_ordFact_iff hm0]
  constructor
  · rintro ⟨σ, rfl⟩
    refine ⟨fun i => hq _, ?_⟩
    rw [← hm]
    exact Equiv.prod_comp σ q
  · rintro ⟨hf1, hf2⟩
    obtain ⟨σ, hσ⟩ := exists_perm_comp f q (fun v => by
      rw [count_eq_factorization f hf1 hf2 v, count_eq_factorization q hq hm v])
    exact ⟨σ, hσ⟩

/-! ## The fibres all have cardinality `∏_p v_p(m)!` -/

/-- Every nonempty fibre of `σ ↦ q ∘ σ` has cardinality `∏_v (#q⁻¹(v))!`. -/
theorem fiber_card_eq {N : ℕ} (q : Fin N → ℕ) (f : Fin N → ℕ)
    (hf : ∃ σ0 : Equiv.Perm (Fin N), q ∘ (σ0 : Fin N → Fin N) = f) :
    (univ.filter fun σ : Equiv.Perm (Fin N) => q ∘ (σ : Fin N → Fin N) = f).card
      = ∏ v ∈ univ.image q, ((univ.filter fun i => q i = v).card).factorial := by
  classical
  obtain ⟨σ0, hσ0⟩ := hf
  have hbij : (univ.filter fun σ : Equiv.Perm (Fin N) => q ∘ (σ : Fin N → Fin N) = f)
      = (univ.filter fun τ : Equiv.Perm (Fin N) => q ∘ (τ : Fin N → Fin N) = q).image
          (fun τ => τ * σ0) := by
    ext σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hσ
      refine ⟨σ * σ0⁻¹, ?_, by group⟩
      funext j
      have : q (σ (σ0⁻¹ j)) = f (σ0⁻¹ j) := congrFun hσ (σ0⁻¹ j)
      have h2 : f (σ0⁻¹ j) = q (σ0 (σ0⁻¹ j)) := (congrFun hσ0 (σ0⁻¹ j)).symm
      simpa using this.trans (h2.trans (by simp))
    · rintro ⟨τ, hτ, rfl⟩
      funext i
      have : q (τ (σ0 i)) = q (σ0 i) := congrFun hτ (σ0 i)
      simpa [← hσ0] using this
  rw [hbij, Finset.card_image_of_injective _ (mul_left_injective σ0)]
  have hsub : (univ.filter fun τ : Equiv.Perm (Fin N) => q ∘ (τ : Fin N → Fin N) = q).card
      = Fintype.card {g : Equiv.Perm (Fin N) // q ∘ (g : Fin N → Fin N) = q} := by
    rw [Fintype.card_subtype]
  rw [hsub, DomMulAct.stabilizer_card' q]
  exact Finset.prod_congr rfl fun v _ => by rw [Fintype.card_subtype]

/-! ## The main identity -/

/-- **Core form.**  For an explicit listing `q` of the primes of `m` with multiplicity. -/
theorem factorialEulerPolarization_of_listing {N : ℕ} (om : ℕ → Fin N → K) {m : ℕ}
    (q : Fin N → ℕ) (hq : ∀ i, (q i).Prime) (hm : ∏ i, q i = m) :
    coeff (balancedMonomial N) (Fdiv N om m)
      = ∑ f ∈ ordFact N m, ∏ i, om (f i) i := by
  classical
  have hm0 : m ≠ 0 := by
    rw [← hm]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => (hq i).ne_zero
  -- image of the listing is the set of primes of `m`
  have himg : univ.image q = m.primeFactors := by
    ext v
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Nat.mem_primeFactors]
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨hq i, hm ▸ Finset.dvd_prod_of_mem q (Finset.mem_univ i), hm0⟩
    · rintro ⟨hv, hdvd, -⟩
      have hpos : 0 < m.factorization v := hv.factorization_pos_of_dvd hm0 hdvd
      rw [← count_eq_factorization q hq hm v, Finset.card_pos] at hpos
      obtain ⟨i, hi⟩ := hpos
      exact ⟨i, (Finset.mem_filter.mp hi).2⟩
  -- the product of the linear forms over the listing
  have hprod : ∏ i, linForm N om (q i)
      = ∏ p ∈ m.primeFactors, (linForm N om p) ^ (m.factorization p) := by
    rw [Finset.prod_comp (linForm N om) q, himg]
    exact Finset.prod_congr rfl fun v hv => by
      rw [count_eq_factorization q hq hm v]
  -- the scalar denominator
  set D : K := ∏ p ∈ m.primeFactors, ((m.factorization p).factorial : K) with hD
  have hDne : D ≠ 0 := by
    rw [hD]
    refine Finset.prod_ne_zero_iff.mpr fun p _ => ?_
    exact Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hCprod : ∏ p ∈ m.primeFactors, (C (((m.factorization p).factorial : K)⁻¹) :
      MvPolynomial (Fin N) K) = C D⁻¹ := by
    rw [← map_prod, Finset.prod_inv_distrib, hD]
  have hFdiv : Fdiv N om m = C D⁻¹ * ∏ i, linForm N om (q i) := by
    rw [hprod, Fdiv]
    simp only [divPowerFactor]
    rw [Finset.prod_mul_distrib, hCprod]
  -- the coefficient of the product of linear forms is the permanent-type sum
  have hlab : ∏ i, linForm N om (q i) = labelledPolynomial N (fun i j => om (q j) i) := rfl
  rw [hFdiv, coeff_C_mul, hlab, coeff_balanced_eq_perm_sum]
  -- reindex the permutation sum so that the slot index is the free one
  have step1 : ∀ σ : Equiv.Perm (Fin N),
      ∏ j, om (q j) (σ j) = ∏ i, om (q (σ⁻¹ i)) i := by
    intro σ
    rw [← Equiv.prod_comp σ (fun i => om (q (σ⁻¹ i)) i)]
    exact Finset.prod_congr rfl fun j _ => by simp
  have step2 : ∑ σ : Equiv.Perm (Fin N), ∏ i, om (q (σ⁻¹ i)) i
      = ∑ σ : Equiv.Perm (Fin N), ∏ i, om (q (σ i)) i :=
    Fintype.sum_equiv (Equiv.inv (Equiv.Perm (Fin N))) _ _ (fun _ => rfl)
  rw [Finset.sum_congr rfl (fun σ _ => step1 σ), step2]
  -- group the permutations according to the ordered factorisation they produce
  have hcomp := Finset.sum_comp (s := (univ : Finset (Equiv.Perm (Fin N))))
    (fun f : Fin N → ℕ => ∏ i, om (f i) i) (fun σ : Equiv.Perm (Fin N) => q ∘ (σ : Fin N → Fin N))
  rw [show (∑ σ : Equiv.Perm (Fin N), ∏ i, om (q (σ i)) i)
      = ∑ σ ∈ (univ : Finset (Equiv.Perm (Fin N))),
          (fun f : Fin N → ℕ => ∏ i, om (f i) i) (q ∘ (σ : Fin N → Fin N)) from rfl, hcomp,
    image_perm_eq_ordFact q hq hm]
  -- every fibre has the same cardinality `∏_p v_p(m)!`
  have hDnat : ∀ f ∈ ordFact N m,
      (univ.filter fun σ : Equiv.Perm (Fin N) => q ∘ (σ : Fin N → Fin N) = f).card
        = ∏ p ∈ m.primeFactors, ((m.factorization p).factorial) := by
    intro f hf
    have hex : ∃ σ0 : Equiv.Perm (Fin N), q ∘ (σ0 : Fin N → Fin N) = f := by
      have : f ∈ Finset.image (fun σ : Equiv.Perm (Fin N) => q ∘ (σ : Fin N → Fin N)) univ := by
        rw [image_perm_eq_ordFact q hq hm]; exact hf
      simpa only [Finset.mem_image, Finset.mem_univ, true_and] using this
    rw [fiber_card_eq q f hex, himg]
    exact Finset.prod_congr rfl fun v _ => by rw [count_eq_factorization q hq hm v]
  rw [Finset.sum_congr rfl (fun f hf => by rw [hDnat f hf])]
  simp only [nsmul_eq_mul, Nat.cast_prod]
  rw [← Finset.mul_sum, ← mul_assoc, ← hD, inv_mul_cancel₀ hDne, one_mul]

/-! ## The identity in terms of `Ω(m) = N` -/

/-- A nonzero `m` with `Ω(m) = N` admits an ordered listing of its `N` prime occurrences. -/
theorem exists_prime_listing {m N : ℕ} (hm : m ≠ 0) (hΩ : m.primeFactorsList.length = N) :
    ∃ q : Fin N → ℕ, (∀ i, (q i).Prime) ∧ ∏ i, q i = m := by
  subst hΩ
  refine ⟨fun i => m.primeFactorsList.get i,
    fun i => Nat.prime_of_mem_primeFactorsList (List.get_mem _ _), ?_⟩
  rw [← List.prod_ofFn, List.ofFn_get]
  exact Nat.prod_primeFactorsList hm

/-- **`factorialEulerPolarization`** — `PROVED_ALGEBRAIC`.

The finite coefficient-extraction identity, unnormalised form: for `Ω(m) = N`,
`[z_1 ⋯ z_N] ∏_p (L_p^{v_p(m)} / v_p(m)!)` is the sum of `∏_i ω_i(p_i)` over **ordered**
`N`-tuples of primes with product `m`, repeated primes included. -/
theorem factorialEulerPolarization {N : ℕ} (om : ℕ → Fin N → K) {m : ℕ} (hm : m ≠ 0)
    (hΩ : ArithmeticFunction.cardFactors m = N) :
    coeff (balancedMonomial N) (Fdiv N om m) = ∑ f ∈ ordFact N m, ∏ i, om (f i) i := by
  rw [ArithmeticFunction.cardFactors_apply] at hΩ
  obtain ⟨q, hq, hqm⟩ := exists_prime_listing hm hΩ
  exact factorialEulerPolarization_of_listing om q hq hqm

/-! ## The normalised seven-slot form -/

/-- `a_z(p) = (1/7) ∑_i z_i ω_i(p)`, the actual polarized prime datum. -/
noncomputable def azForm (om : ℕ → Fin 7 → K) (p : ℕ) : MvPolynomial (Fin 7) K :=
  C (1 / 7 : K) * linForm 7 om p

/-- `F_z(m) = ∏_p a_z(p)^{v_p(m)} / v_p(m)!`, the factorial Euler polarization. -/
noncomputable def Fz7 (om : ℕ → Fin 7 → K) (m : ℕ) : MvPolynomial (Fin 7) K :=
  ∏ p ∈ m.primeFactors,
    C (((m.factorization p).factorial : K)⁻¹) * (azForm om p) ^ (m.factorization p)

omit [CharZero K] in
/-- On prime powers, `F_z(p^e) = a_z(p)^e / e !` exactly. -/
theorem Fz7_primePow (om : ℕ → Fin 7 → K) {p e : ℕ} (hp : p.Prime) (he : e ≠ 0) :
    Fz7 om (p ^ e) = C ((e.factorial : K)⁻¹) * (azForm om p) ^ e := by
  have h1 : (p ^ e).primeFactors = {p} := by
    rw [Nat.primeFactors_pow p he, hp.primeFactors]
  have h2 : (p ^ e).factorization p = e := by
    rw [Nat.Prime.factorization_pow hp]; simp
  rw [Fz7, h1, Finset.prod_singleton, h2]

omit [CharZero K] in
/-- The normalisation is a rescaling of the prime weights. -/
theorem Fz7_eq_Fdiv (om : ℕ → Fin 7 → K) (m : ℕ) :
    Fz7 om m = Fdiv 7 (fun p i => (1 / 7 : K) * om p i) m := by
  have hlin : ∀ p : ℕ, azForm om p = linForm 7 (fun p i => (1 / 7 : K) * om p i) p := by
    intro p
    rw [azForm, linForm, linForm, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [← mul_assoc, ← map_mul]
  simp only [Fz7, Fdiv, divPowerFactor, hlin]

/-- **`factorialEulerPolarization_seven`** — `PROVED_ALGEBRAIC`.

With the genuine normalisation `a_z(p) = (1/7) ∑_i z_i ω_i(p)` and `F_z(p^e) = a_z(p)^e/e!`
extended multiplicatively, for every `m` with `Ω(m) = 7`:

`7^7 · [z_1 ⋯ z_7] F_z(m) = ∑_{p_1 ⋯ p_7 = m, ordered} ∏_{i=1}^{7} ω_i(p_i)`,

the sum running over all ordered prime 7-tuples with product `m`, repeated primes included
(`mem_ordFact_iff`); the factorials `∏_p v_p(m)!` cancel exactly the permutations of equal
prime occurrences (`fiber_card_eq`). -/
theorem factorialEulerPolarization_seven (om : ℕ → Fin 7 → K) {m : ℕ} (hm : m ≠ 0)
    (hΩ : ArithmeticFunction.cardFactors m = 7) :
    (7 : K) ^ 7 * coeff balancedSevenMonomial (Fz7 om m)
      = ∑ f ∈ ordFact 7 m, ∏ i, om (f i) i := by
  have h7 : (7 : K) ≠ 0 := by
    exact_mod_cast (by norm_num : (7 : ℕ) ≠ 0)
  rw [Fz7_eq_Fdiv, balancedSevenMonomial, factorialEulerPolarization _ hm hΩ]
  have hterm : ∀ f : Fin 7 → ℕ,
      (∏ i, (1 / 7 : K) * om (f i) i) = (1 / 7 : K) ^ 7 * ∏ i, om (f i) i := by
    intro f
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [Finset.sum_congr rfl (fun f _ => hterm f), ← Finset.mul_sum, ← mul_assoc]
  rw [show (7 : K) ^ 7 * (1 / 7 : K) ^ 7 = 1 by
    rw [← mul_pow]; field_simp]
  rw [one_mul]

/-- The complex specialisation actually used by the polarized seven-box encoding. -/
theorem factorialEulerPolarization_seven_complex (om : ℕ → Fin 7 → ℂ) {m : ℕ} (hm : m ≠ 0)
    (hΩ : ArithmeticFunction.cardFactors m = 7) :
    (7 : ℂ) ^ 7 * coeff balancedSevenMonomial (Fz7 om m)
      = ∑ f ∈ ordFact 7 m, ∏ i, om (f i) i :=
  factorialEulerPolarization_seven om hm hΩ

/-! ## Non-vacuity of the seven-slot statement -/

/-- `Ω(128) = 7`. -/
theorem cardFactors_128 : ArithmeticFunction.cardFactors 128 = 7 := by
  rw [ArithmeticFunction.cardFactors_apply, show (128 : ℕ) = 2 ^ 7 by norm_num,
    Nat.Prime.primeFactorsList_pow Nat.prime_two]
  simp

/-- The constant tuple `(2,…,2)` is an ordered factorisation of `128 = 2^7`; in particular
`ordFact 7 128` is nonempty, so the seven-slot identity is not vacuous, and this is the
extreme repeated-prime case (all seven primes equal). -/
theorem const_two_mem_ordFact_128 : (fun _ => 2) ∈ ordFact 7 128 := by
  rw [mem_ordFact_iff (by norm_num)]
  exact ⟨fun _ => Nat.prime_two, by norm_num⟩

/-- The seven-slot identity, instantiated at the fully repeated prime power `128 = 2^7`. -/
theorem factorialEulerPolarization_seven_128 (om : ℕ → Fin 7 → ℂ) :
    (7 : ℂ) ^ 7 * coeff balancedSevenMonomial (Fz7 om 128)
      = ∑ f ∈ ordFact 7 128, ∏ i, om (f i) i :=
  factorialEulerPolarization_seven_complex om (by norm_num) cardFactors_128

end FactorialEuler
end Erdos287
