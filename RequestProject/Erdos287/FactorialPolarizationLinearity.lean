import Mathlib
import RequestProject.Erdos287.FactorialEulerPolarization

/-!
# V16, Part 4 — expected-term linearity of the factorial polarization

The polarized family `z ↦ F_z` is, for each argument `n`, a polynomial in `z`; its
*coefficient data* is the family `d ↦ (n ↦ [z^d] F_z(n))`.  Any **linear** operator `E` on
the coefficient space acts on that data, and the normalised balanced extraction
`7^7 · [z_1 ⋯ z_7]` commutes with it.  That is the whole content of this file:

* `factorialPolarization_commutes_linearMap` — the abstract module-level statement;
* `factorialPolarization_commutes_arith` — its instance for operators on arithmetic
  functions `ℕ → K`, using the coefficientwise extension `arithExtend`;
* `weightedProjection` and `factorialPolarization_commutes_weightedProjection` — the
  multiplication-by-a-weight instance, which abstractly and **conditionally** covers a
  principal-character projection, a finite low-conductor character projection, and an
  exceptional-character linear term.  Which weight is the "physical" one is *not* decided
  here.

Status: `POLARIZED-EXPECTED-TERM-LINEARITY45 : PROVED_ALGEBRAIC`.

**Honesty statement.**  Nothing here claims that the physical comparison sequence equals the
expected term: `M_fac = M_phys` is **not** proved, and the corresponding interface
(`AFFINE287-MULOG-COMPARISON-LOWCOND-MATCH45`) stays uninhabited.  Linearity of `E` is a
hypothesis, never a conclusion.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MvPolynomial

namespace Erdos287
namespace FactorialEuler

open Erdos287.BalancedSeven

variable {K : Type*} [Field K]
variable {A B : Type*} [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B]

/-- The coefficient data of a polarized family in `n` variables with values in a module. -/
abbrev CoeffFamily (n : ℕ) (A : Type*) := (Fin n →₀ ℕ) → A

/-- Extraction of the fully multilinear ("balanced") coefficient. -/
noncomputable def balancedExtract (n : ℕ) (Phi : CoeffFamily n A) : A := Phi (balancedMonomial n)

omit [AddCommGroup A] in
@[simp] theorem balancedExtract_apply (n : ℕ) (Phi : CoeffFamily n A) :
    balancedExtract n Phi = Phi (balancedMonomial n) := rfl

/-- **`factorialPolarization_commutes_linearMap`** — `PROVED_ALGEBRAIC`.

For any `K`-linear operator `E` on the coefficient space, extracting the balanced
coefficient after applying `E` coefficientwise, and scaling by `c` (in the application
`c = 7^7`), is the same as applying `E` to the scaled extracted coefficient. -/
theorem factorialPolarization_commutes_linearMap (n : ℕ) (E : A →ₗ[K] B)
    (Phi : CoeffFamily n A) (c : K) :
    c • balancedExtract n (fun d => E (Phi d)) = E (c • balancedExtract n Phi) := by
  simp only [balancedExtract_apply, map_smul]

/-- The `n = 7`, `c = 7^7` form actually used by the polarized seven-box encoding. -/
theorem factorialPolarization_commutes_linearMap_seven (E : A →ₗ[K] B)
    (Phi : CoeffFamily 7 A) :
    (7 : K) ^ 7 • balancedExtract 7 (fun d => E (Phi d))
      = E ((7 : K) ^ 7 • balancedExtract 7 Phi) :=
  factorialPolarization_commutes_linearMap 7 E Phi _

/-! ## Instance: operators on arithmetic functions -/

/-- The coefficientwise extension of an operator on arithmetic functions to a polarized
family of polynomial-valued arithmetic functions. -/
noncomputable def arithExtend (E : (ℕ → K) →ₗ[K] (ℕ → K))
    (F : ℕ → MvPolynomial (Fin 7) K) : CoeffFamily 7 (ℕ → K) :=
  fun d => E (fun m => coeff d (F m))

/-- **`factorialPolarization_commutes_arith`** — the arithmetic-function instance.

`7^7 · [z_1 ⋯ z_7] E(F_z) = E(7^7 · [z_1 ⋯ z_7] F_z)` for every linear `E`. -/
theorem factorialPolarization_commutes_arith (E : (ℕ → K) →ₗ[K] (ℕ → K))
    (F : ℕ → MvPolynomial (Fin 7) K) :
    (7 : K) ^ 7 • balancedExtract 7 (arithExtend E F)
      = E ((7 : K) ^ 7 • fun m => coeff balancedSevenMonomial (F m)) := by
  rw [balancedExtract_apply, arithExtend, map_smul]
  rfl

/-! ## Instance: multiplication by a weight (character projections) -/

/-- Multiplication by a fixed weight `w`, as a `K`-linear operator on arithmetic functions.
Taking `w` to be the principal character, a low-conductor character, or the weight of an
exceptional-character linear term gives the three projections of interest; **which weight is
the physical one is not decided here.** -/
def weightedProjection (w : ℕ → K) : (ℕ → K) →ₗ[K] (ℕ → K) where
  toFun g := fun m => w m * g m
  map_add' g h := by funext m; simp [mul_add]
  map_smul' c g := by funext m; simp [mul_left_comm]

@[simp] theorem weightedProjection_apply (w g : ℕ → K) (m : ℕ) :
    weightedProjection w g m = w m * g m := rfl

/-- The weighted-projection instance of the linearity lemma. -/
theorem factorialPolarization_commutes_weightedProjection (w : ℕ → K)
    (F : ℕ → MvPolynomial (Fin 7) K) :
    (7 : K) ^ 7 • balancedExtract 7 (arithExtend (weightedProjection w) F)
      = weightedProjection w ((7 : K) ^ 7 • fun m => coeff balancedSevenMonomial (F m)) :=
  factorialPolarization_commutes_arith (weightedProjection w) F

end FactorialEuler
end Erdos287
