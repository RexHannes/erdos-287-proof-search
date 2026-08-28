import Mathlib

/-!
# V15, Part 8 — the squarefree labelled polarization identity

The algebra beneath the balanced-seven polarization, formalised exactly and finitely with
`MvPolynomial` (no Haar integration, no analysis).

For `n` labelled weights `ω_i` evaluated at `n` labelled points, i.e. a matrix
`om : Fin n → Fin n → R` with `om i j = ω_i(p_j)`, set

`labelledPolynomial n om = ∏_{j} (∑_{i} ω_i(p_j) · z_i) ∈ MvPolynomial (Fin n) R`.

The main theorem `coeff_balanced_eq_perm_sum` states that the fully multilinear
coefficient, i.e. the coefficient at the squarefree monomial `z_1 z_2 ⋯ z_n`
(`balancedMonomial n`), is exactly the permanent-type sum

`∑_{σ ∈ S_n} ∏_{j} ω_{σ(j)}(p_j)`,

with **multiplicity one** for each permutation: the sum runs over `Equiv.Perm (Fin n)`
with no repetition and no extra factor.  It is proved over an arbitrary commutative
semiring, and specialised to `n = 7` (`coeff_balancedSeven_eq_perm_sum`) and to `ℂ`.

The analytic normalisation `a_z(p) = (1/7) ∑_i z_i ω_i(p)` is kept **separate**: it is the
scalar theorem `coeff_balanced_scaled` (`c^n` comes out in front), specialised as
`coeff_balancedSeven_scaled_seventh`, together with the arithmetic fact
`sevenPow_seven : 7^7 = 823543`.  The normalisation is never mixed into the combinatorial
permutation identity.

Status: `BALANCED7-SQUAREFREE-POLARIZATION45 : PROVED_ALGEBRAIC`.

**Honesty statement.**  This is polynomial coefficient extraction and nothing else.  It
does not close the balanced-seven case of anything: no analytic smallness, no character
sum, no exponent of distribution is proved or assumed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MvPolynomial Finset
open scoped BigOperators

namespace Erdos287
namespace BalancedSeven

/-! ## The squarefree ("balanced") monomial -/

/-- The fully multilinear monomial `z_1 z_2 ⋯ z_n`, as an exponent vector. -/
noncomputable def balancedMonomial (n : ℕ) : Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun _ => 1)

@[simp] theorem balancedMonomial_apply (n : ℕ) (i : Fin n) : balancedMonomial n i = 1 := rfl

/-- The `n = 7` case, the monomial `z_1 ⋯ z_7`. -/
noncomputable def balancedSevenMonomial : Fin 7 →₀ ℕ := balancedMonomial 7

/-! ## Two elementary lemmas -/

/-- A finite product of monomials is the monomial of the sum of the exponent vectors. -/
theorem prod_monomial {R : Type*} [CommSemiring R] {ι : Type*} {σ : Type*} (s : Finset ι)
    (d : ι → (σ →₀ ℕ)) (c : ι → R) :
    ∏ i ∈ s, monomial (d i) (c i) = monomial (∑ i ∈ s, d i) (∏ i ∈ s, c i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, ih, Finset.sum_insert ha, Finset.prod_insert ha, monomial_mul]

/-- The exponent vector attached to a labelling `g` counts the fibres of `g`. -/
theorem degreeVector_apply (n : ℕ) (g : Fin n → Fin n) (i : Fin n) :
    (∑ j : Fin n, Finsupp.single (g j) (1 : ℕ)) i
      = (univ.filter (fun j => g j = i)).card := by
  classical
  rw [Finset.sum_apply']
  simp [Finsupp.single_apply, Finset.sum_boole]

/-- A labelling contributes to the squarefree monomial **iff** it is a permutation. -/
theorem degreeVector_eq_balanced_iff (n : ℕ) (g : Fin n → Fin n) :
    (∑ j : Fin n, Finsupp.single (g j) (1 : ℕ)) = balancedMonomial n
      ↔ Function.Bijective g := by
  classical
  constructor
  · intro h
    have hc : ∀ i, (univ.filter (fun j => g j = i)).card = 1 := by
      intro i
      rw [← degreeVector_apply, h, balancedMonomial_apply]
    have hsurj : Function.Surjective g := by
      intro i
      have hne : (univ.filter (fun j => g j = i)).Nonempty := by
        rw [← Finset.card_pos, hc i]; norm_num
      obtain ⟨j, hj⟩ := hne
      exact ⟨j, (Finset.mem_filter.mp hj).2⟩
    exact Finite.surjective_iff_bijective.mp hsurj
  · intro hb
    ext i
    rw [degreeVector_apply, balancedMonomial_apply]
    obtain ⟨j0, hj0⟩ := hb.2 i
    rw [Finset.card_eq_one]
    refine ⟨j0, ?_⟩
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hj; exact hb.1 (hj.trans hj0.symm)
    · rintro rfl; exact hj0

/-! ## The labelled polynomial and its multilinear coefficient -/

/-- `∏_{j} (∑_{i} ω_i(p_j) · z_i)`. -/
noncomputable def labelledPolynomial {R : Type*} [CommSemiring R] (n : ℕ)
    (om : Fin n → Fin n → R) : MvPolynomial (Fin n) R :=
  ∏ j : Fin n, ∑ i : Fin n, C (om i j) * X i

/-- **`coeff_balanced_eq_perm_sum`** — `PROVED_ALGEBRAIC`.

The coefficient of `z_1 ⋯ z_n` in `∏_j (∑_i ω_i(p_j) z_i)` is `∑_{σ ∈ S_n} ∏_j ω_{σ(j)}(p_j)`,
each permutation occurring exactly once. -/
theorem coeff_balanced_eq_perm_sum {R : Type*} [CommSemiring R] (n : ℕ)
    (om : Fin n → Fin n → R) :
    coeff (balancedMonomial n) (labelledPolynomial n om)
      = ∑ σ : Equiv.Perm (Fin n), ∏ j : Fin n, om (σ j) j := by
  classical
  rw [labelledPolynomial, Finset.prod_univ_sum, MvPolynomial.coeff_sum]
  have step : ∀ g ∈ Fintype.piFinset (fun _ : Fin n => (univ : Finset (Fin n))),
      coeff (balancedMonomial n) (∏ j : Fin n, C (om (g j) j) * X (g j))
        = if Function.Bijective g then ∏ j : Fin n, om (g j) j else 0 := by
    intro g _
    have h1 : (∏ j : Fin n, C (om (g j) j) * X (g j))
        = monomial (∑ j : Fin n, Finsupp.single (g j) 1) (∏ j : Fin n, om (g j) j) := by
      rw [← prod_monomial]
      exact Finset.prod_congr rfl fun j _ => C_mul_X_eq_monomial
    rw [h1, coeff_monomial]
    by_cases hb : Function.Bijective g
    · rw [if_pos ((degreeVector_eq_balanced_iff n g).2 hb), if_pos hb]
    · rw [if_neg (fun h => hb ((degreeVector_eq_balanced_iff n g).1 h)), if_neg hb]
  rw [Finset.sum_congr rfl step, Fintype.piFinset_univ, ← Finset.sum_filter]
  refine (Finset.sum_nbij (fun σ : Equiv.Perm (Fin n) => (σ : Fin n → Fin n)) ?_ ?_ ?_ ?_).symm
  · intro σ _
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, σ.bijective⟩
  · intro σ _ τ _ h
    exact Equiv.coe_fn_injective h
  · intro g hg
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hg
    exact ⟨Equiv.ofBijective g hg, Finset.mem_coe.mpr (Finset.mem_univ _), rfl⟩
  · intro σ _
    rfl

/-- **`coeff_balancedSeven_eq_perm_sum`** — the `n = 7` case. -/
theorem coeff_balancedSeven_eq_perm_sum {R : Type*} [CommSemiring R] (om : Fin 7 → Fin 7 → R) :
    coeff balancedSevenMonomial (labelledPolynomial 7 om)
      = ∑ σ : Equiv.Perm (Fin 7), ∏ j : Fin 7, om (σ j) j :=
  coeff_balanced_eq_perm_sum 7 om

/-- The complex specialisation. -/
theorem coeff_balancedSeven_eq_perm_sum_complex (om : Fin 7 → Fin 7 → ℂ) :
    coeff balancedSevenMonomial (labelledPolynomial 7 om)
      = ∑ σ : Equiv.Perm (Fin 7), ∏ j : Fin 7, om (σ j) j :=
  coeff_balancedSeven_eq_perm_sum om

/-- There really are `7! = 5040` terms, each with multiplicity one. -/
theorem card_perm_seven : Fintype.card (Equiv.Perm (Fin 7)) = 5040 := by
  simp [Fintype.card_perm, Nat.factorial]

/-! ## The normalisation scalar, kept separate -/

/-- **`coeff_balanced_scaled`** — scaling every weight by `c` multiplies the multilinear
coefficient by `c^n`.  This is the *only* place the analytic normalisation enters. -/
theorem coeff_balanced_scaled {R : Type*} [CommSemiring R] (n : ℕ) (c : R)
    (om : Fin n → Fin n → R) :
    coeff (balancedMonomial n) (labelledPolynomial n (fun i j => c * om i j))
      = c ^ n * ∑ σ : Equiv.Perm (Fin n), ∏ j : Fin n, om (σ j) j := by
  rw [coeff_balanced_eq_perm_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- `7^7 = 823543` (the normalisation denominator, checked). -/
theorem sevenPow_seven : (7 : ℕ) ^ 7 = 823543 := by norm_num

/-- **`coeff_balancedSeven_scaled_seventh`** — the analytic normalisation
`a_z(p) = (1/7) ∑_i z_i ω_i(p)` contributes exactly the factor `7^{-7} = 1/823543`. -/
theorem coeff_balancedSeven_scaled_seventh (om : Fin 7 → Fin 7 → ℂ) :
    coeff balancedSevenMonomial (labelledPolynomial 7 (fun i j => (1 / 7 : ℂ) * om i j))
      = (1 / 823543 : ℂ) * ∑ σ : Equiv.Perm (Fin 7), ∏ j : Fin 7, om (σ j) j := by
  rw [balancedSevenMonomial, coeff_balanced_scaled 7 (1 / 7 : ℂ) om]
  norm_num

end BalancedSeven
end Erdos287
