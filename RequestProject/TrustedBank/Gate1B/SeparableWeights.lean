import Mathlib
import RequestProject.TrustedBank.Gate1B.MobiusCollapse

/-!
# Gate 1B — separable weights, SOURCE-MMD on a clean cell, and the missing source fields

Three things are banked here.

1. **SOURCE-MMD on a clean cell** (`sourceMMD_clean_cell`): the `(d,p)`-indexed centered
   expression equals the `q = d·p` Möbius-modulus expression, *only* under the exact
   hypotheses proved in `MobiusCollapse.lean` (squarefree `q`, product-separable
   weights).

2. **Nonseparable weight interface** (`SeparableWeightDecomposition`): a finite mode
   index with a `D`-side factor, a `P`-side factor, a reconstruction identity and an
   `L¹`/nuclear mode cost.  If a two-variable weight `W(d,p)` admits such a
   decomposition with cost `C`, then the clean reduction is inherited with at most the
   factor `C` (`mmd_cost_bound`).  **No claim** is made that the actual source weight
   admits such a decomposition.

3. **`SourceMMDRequirements`**: the record of source fields that would have to be
   supplied before the clean reduction could be run on the actual source.  It is a bare
   structure of `Prop`s; **no theorem in this project instantiates it**.

Gate 1B remains **OPEN**.
-/

open scoped BigOperators
open ArithmeticFunction
open scoped ArithmeticFunction.Moebius

namespace TrustedBank
namespace Gate1B

/-! ## 1. SOURCE-MMD on a clean squarefree cell -/

/-- The clean cell: the set of factorizations `q = d·p` with `p` a prime divisor of `q`
lying in the `P`-box and cofactor `d = q/p` in the `D`-box, presented as pairs. -/
def cleanCell (Pbox Dbox : Finset ℕ) (q : ℕ) : Finset (ℕ × ℕ) :=
  (q.primeFactors.filter (fun p => p ∈ Pbox ∧ q / p ∈ Dbox)).image (fun p => (q / p, p))

/-- Every pair in the clean cell really is a factorization `d·p = q` with `p` prime. -/
theorem mem_cleanCell {Pbox Dbox : Finset ℕ} {q : ℕ} {x : ℕ × ℕ}
    (hx : x ∈ cleanCell Pbox Dbox q) :
    x.2.Prime ∧ x.1 * x.2 = q ∧ x.1 = q / x.2 := by
  simp only [cleanCell, Finset.mem_image, Finset.mem_filter] at hx
  obtain ⟨p, ⟨hpf, _⟩, rfl⟩ := hx
  have hprime : p.Prime := (Nat.mem_primeFactors.mp hpf).1
  have hpq : p ∣ q := (Nat.mem_primeFactors.mp hpf).2.1
  exact ⟨hprime, Nat.div_mul_cancel hpq, rfl⟩

/-- **SOURCE-MMD, clean cell.**  For a squarefree modulus `q` and *product-separable*
weights, the `(d,p)`-indexed centered expression equals the Möbius-modulus expression
`-μ(q)·LambdaSharp(q)`. -/
theorem sourceMMD_clean_cell {q : ℕ} (hq : Squarefree q)
    (Pbox Dbox : Finset ℕ) (logW PW DW : ℕ → ℚ) :
    ∑ x ∈ cleanCell Pbox Dbox q,
        ((μ x.1 : ℤ) : ℚ) * logW x.2 * DW x.1 * PW x.2
      = -((μ q : ℤ) : ℚ) * LambdaSharp Pbox Dbox logW PW DW q := by
  have hinj : Set.InjOn (fun p => (q / p, p))
      (q.primeFactors.filter (fun p => p ∈ Pbox ∧ q / p ∈ Dbox)) := by
    intro a _ b _ hab
    exact (Prod.mk.injEq .. ▸ hab).2
  rw [cleanCell, Finset.sum_image (fun a ha b hb h => hinj ha hb h)]
  exact mmd_clean_collapse hq Pbox Dbox logW PW DW

/-! ## 2. Nonseparable weights: an explicit decomposition record -/

/-- A finite separable decomposition of a two-variable weight `W(d,p)`: a finite mode
index, a `D`-side factor, a `P`-side factor, the reconstruction identity, and the
`L¹`/nuclear mode cost (here the number of modes). -/
structure SeparableWeightDecomposition (W : ℕ → ℕ → ℚ) where
  /-- The finite index set of separable modes. -/
  modes : Finset ℕ
  /-- The `D`-side factor of each mode. -/
  Dfac : ℕ → ℕ → ℚ
  /-- The `P`-side factor of each mode. -/
  Pfac : ℕ → ℕ → ℚ
  /-- Reconstruction of the weight from its modes. -/
  recon : ∀ d p, W d p = ∑ i ∈ modes, Dfac i d * Pfac i p

namespace SeparableWeightDecomposition

variable {W : ℕ → ℕ → ℚ}

/-- The `L¹`/nuclear cost of the decomposition: the number of separable modes. -/
def cost (dec : SeparableWeightDecomposition W) : ℕ := dec.modes.card

/-- **Mode expansion.**  Any weighted sum against `W` splits as a sum of the
corresponding separable (clean) sums, one per mode. -/
theorem sum_expand (dec : SeparableWeightDecomposition W) (T : Finset (ℕ × ℕ))
    (f : ℕ × ℕ → ℚ) :
    ∑ x ∈ T, f x * W x.1 x.2
      = ∑ i ∈ dec.modes, ∑ x ∈ T, f x * (dec.Dfac i x.1 * dec.Pfac i x.2) := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [dec.recon x.1 x.2, Finset.mul_sum]

/-- **Cost inheritance.**  If every clean (single-mode) sum is bounded by `B`, then the
nonseparable sum is bounded by `cost · B`. -/
theorem mmd_cost_bound (dec : SeparableWeightDecomposition W) (T : Finset (ℕ × ℕ))
    (f : ℕ × ℕ → ℚ) (B : ℚ)
    (hB : ∀ i ∈ dec.modes, |∑ x ∈ T, f x * (dec.Dfac i x.1 * dec.Pfac i x.2)| ≤ B) :
    |∑ x ∈ T, f x * W x.1 x.2| ≤ (dec.cost : ℚ) * B := by
  rw [dec.sum_expand T f]
  calc |∑ i ∈ dec.modes, ∑ x ∈ T, f x * (dec.Dfac i x.1 * dec.Pfac i x.2)|
      ≤ ∑ i ∈ dec.modes, |∑ x ∈ T, f x * (dec.Dfac i x.1 * dec.Pfac i x.2)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ dec.modes, B := Finset.sum_le_sum hB
    _ = (dec.cost : ℚ) * B := by rw [Finset.sum_const, cost, nsmul_eq_mul]

end SeparableWeightDecomposition

/-- A product weight is separable with one mode, hence cost `1`. -/
def productDecomposition (D P : ℕ → ℚ) :
    SeparableWeightDecomposition (fun d p => D d * P p) where
  modes := {0}
  Dfac := fun _ d => D d
  Pfac := fun _ p => P p
  recon := by intro d p; simp

@[simp] theorem productDecomposition_cost (D P : ℕ → ℚ) :
    (productDecomposition D P).cost = 1 := rfl

/-! ## 3. The source fields that are still required -/

/-- The record of source fields that must be verified before the clean MMD reduction
can be applied to the actual source weight.  **No theorem in this project supplies an
inhabitant of this structure**; it is a specification, not an assumption. -/
structure SourceMMDRequirements where
  /-- The gcd routing of the `(d,p)` decomposition is respected by the source. -/
  gcdRouting : Prop
  /-- The repeated-prime sector (`p ∣ d`) is separated off. -/
  repeatedPrimeSector : Prop
  /-- The dyadic boundary terms are controlled. -/
  dyadicBoundary : Prop
  /-- The actual smooth weight admits a finite separable decomposition. -/
  smoothWeightDecomposition : Prop
  /-- The unary `B_D` / `B_P` routing is available. -/
  unaryRouting : Prop
  /-- The source normalization matches the one used in the clean cell. -/
  sourceNormalization : Prop

/-- The conjunction of all required source fields. -/
def SourceMMDRequirements.all (R : SourceMMDRequirements) : Prop :=
  R.gcdRouting ∧ R.repeatedPrimeSector ∧ R.dyadicBoundary ∧
    R.smoothWeightDecomposition ∧ R.unaryRouting ∧ R.sourceNormalization

end Gate1B
end TrustedBank
