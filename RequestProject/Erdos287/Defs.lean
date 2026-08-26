import Mathlib

/-!
# Erdős Problem #287 — elementary structural package (definitions)

This file sets up the basic definitions used throughout the package:

* the top `p`-adic layer of a finite set `A` of positive integers whose reciprocals sum to `1`;
* a kernel-reducing computation of the reduced numerator of `∑_{s∈S} 1/s`
  together with the "largest numerator" quantity `C`.

All of the "structural" theorems live in the sibling files.
-/

open scoped BigOperators

namespace Erdos287

/-! ## Top `p`-adic layer -/

/-- The maximal `p`-adic valuation attained over a finite set `A`. -/
def topExp (A : Finset ℕ) (p : ℕ) : ℕ := A.sup (fun a => Nat.factorization a p)

/-- The top `p`-adic layer: the elements of `A` whose `p`-adic valuation is maximal. -/
def topLayer (A : Finset ℕ) (p : ℕ) : Finset ℕ :=
  A.filter (fun a => Nat.factorization a p = topExp A p)

lemma mem_topLayer {A : Finset ℕ} {p a : ℕ} :
    a ∈ topLayer A p ↔ a ∈ A ∧ Nat.factorization a p = topExp A p := by
  simp [topLayer]

lemma topLayer_subset (A : Finset ℕ) (p : ℕ) : topLayer A p ⊆ A := by
  intro a ha; exact (mem_topLayer.1 ha).1

/-! ## Computable reduced-numerator machinery

We compute the reduced numerator of `∑_{s∈S} 1/s` with a kernel-reducing fold
so that the values of `C` can be certified with `decide` (never `native_decide`).
-/

/-- One step of reduced-fraction addition on `(numerator, denominator)` pairs. -/
def addF (x y : ℤ × ℕ) : ℤ × ℕ :=
  let n := x.1 * (y.2 : ℤ) + y.1 * (x.2 : ℤ)
  let d := x.2 * y.2
  let g := Nat.gcd n.natAbs d
  (n / (g : ℤ), d / g)

/-- The reduced `(numerator, denominator)` pair of `∑_{s∈l} 1/s` for a list `l`. -/
def sumP (l : List ℕ) : ℤ × ℕ :=
  l.foldr (fun s acc => addF acc (1, s)) (0, 1)

/-- The reduced numerator of `∑_{s∈l} 1/s`. -/
def numOf (l : List ℕ) : ℤ := (sumP l).1

/-- The reduced denominator of `∑_{s∈l} 1/s`. -/
def denOf (l : List ℕ) : ℕ := (sumP l).2

/-- The largest reduced numerator of `∑_{s∈S} 1/s` over nonempty subsets
`S ⊆ {1,…,j}`, computed over the sublists of `[1,…,j]`. -/
def C (j : ℕ) : ℤ :=
  ((((List.range j).map (· + 1)).sublists.filter (fun l => l ≠ [])).map numOf).foldr max 0

end Erdos287
