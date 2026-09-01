import Mathlib

/-!
# The exact K0-SP2 source object (finite / source level only)

`K0-SP2 SOURCE OBJECT : KERNEL-PROVED (finite identities only)`

This module is **append-only**.  Nothing earlier is edited.

It fixes, once and for all, the *finite* data underlying the K0-SP2 source

```
S_X = { n : X/2 < n ≤ X, P⁺(n) ≤ n^σ* },

M_γ(n) = ∑_{e ∣ n, e ≤ n^γ*} μ(e),

Source = ∑_{s = ±1} ∑_{n ∈ S_X} W(n/X) · D_s(n) · M_γ(n).
```

**Design decisions, and why they are honest.**

* The two exponents `σ*`, `γ*` are carried as *rational* exponents `snum/sden`,
  `gnum/gden` and the two inequalities are written in the equivalent
  **integer-power** form `P⁺(n)^sden ≤ n^snum`, `e^gden ≤ n^gnum`.  No real
  exponentiation is needed, the predicates are decidable, and the sets are
  genuine `Finset`s.
* The analytic coefficients `W` (smooth weight) and `D_s` (the two-sign
  Dirichlet-type coefficient) are kept as **explicit parameters** of type
  `ℕ → ℂ`.  Nothing analytic about them is assumed or proved here.
* Everything proved below is a finite identity: support identities, the
  two-sign expansion, and additivity of the source over a partition of `S_X`.
  **No analytic estimate is stated, assumed, or inhabited.**
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open Finset ArithmeticFunction

namespace Erdos287
namespace K0SP2Source

/-! ## §1.  The greatest prime factor `P⁺` -/

/-- **`greatestPrimeFactor n = P⁺(n)`**, with the conventions `P⁺(0) = P⁺(1) = 0`. -/
def greatestPrimeFactor (n : ℕ) : ℕ := n.primeFactors.sup _root_.id

@[simp] theorem greatestPrimeFactor_one : greatestPrimeFactor 1 = 0 := by
  simp [greatestPrimeFactor]

@[simp] theorem greatestPrimeFactor_zero : greatestPrimeFactor 0 = 0 := by
  simp [greatestPrimeFactor]

/-- Every prime factor of `n` is at most `P⁺(n)`. -/
theorem le_greatestPrimeFactor {n p : ℕ} (hp : p ∈ n.primeFactors) :
    p ≤ greatestPrimeFactor n :=
  Finset.le_sup (f := _root_.id) hp

/-- For a prime `p`, `P⁺(p) = p`. -/
theorem greatestPrimeFactor_prime {p : ℕ} (hp : p.Prime) : greatestPrimeFactor p = p := by
  simp [greatestPrimeFactor, hp.primeFactors]

/-! ## §2.  The smoothness parameters and the source set `S_X` -/

/-- **`K0SP2Params`** — the finite parameter package of the K0-SP2 source.
`σ* = snum/sden` is the smoothness exponent and `γ* = gnum/gden` the Möbius
truncation exponent. -/
structure K0SP2Params where
  /-- The dyadic scale `X`. -/
  X : ℕ
  /-- Numerator of the smoothness exponent `σ*`. -/
  snum : ℕ
  /-- Denominator of the smoothness exponent `σ*` (positive). -/
  sden : ℕ
  /-- Numerator of the Möbius truncation exponent `γ*`. -/
  gnum : ℕ
  /-- Denominator of the Möbius truncation exponent `γ*` (positive). -/
  gden : ℕ
  /-- `σ*` has a positive denominator. -/
  sden_pos : 0 < sden
  /-- `γ*` has a positive denominator. -/
  gden_pos : 0 < gden

namespace K0SP2Params

variable (P : K0SP2Params)

/-- The `σ*`-smoothness predicate, in integer-power form: `P⁺(n)^sden ≤ n^snum`. -/
def IsSmooth (n : ℕ) : Prop := greatestPrimeFactor n ^ P.sden ≤ n ^ P.snum

instance (n : ℕ) : Decidable (P.IsSmooth n) := by
  unfold IsSmooth; infer_instance

/-- **`S_X`** — the audited source set:
`{ n : X/2 < n ≤ X, P⁺(n) ≤ n^{σ*} }`. -/
def sourceSet : Finset ℕ :=
  (Finset.Ioc (P.X / 2) P.X).filter (fun n => P.IsSmooth n)

@[simp] theorem mem_sourceSet {n : ℕ} :
    n ∈ P.sourceSet ↔ (P.X / 2 < n ∧ n ≤ P.X) ∧ P.IsSmooth n := by
  simp [sourceSet, Finset.mem_filter, Finset.mem_Ioc, and_assoc]

/-- Every source row is positive. -/
theorem sourceSet_pos {n : ℕ} (h : n ∈ P.sourceSet) : 0 < n := by
  rw [mem_sourceSet] at h; omega

/-- Every source row lies in the dyadic window `(X/2, X]`. -/
theorem sourceSet_window {n : ℕ} (h : n ∈ P.sourceSet) : P.X / 2 < n ∧ n ≤ P.X := by
  rw [mem_sourceSet] at h; exact h.1

/-- The source set is contained in the dyadic window. -/
theorem sourceSet_subset : P.sourceSet ⊆ Finset.Ioc (P.X / 2) P.X :=
  Finset.filter_subset _ _

/-- **`M_γ`** — the truncated Möbius coefficient
`M_γ(n) = ∑_{e ∣ n, e^{gden} ≤ n^{gnum}} μ(e)`. -/
def MgammaCoeff (n : ℕ) : ℤ :=
  ∑ e ∈ n.divisors.filter (fun e => e ^ P.gden ≤ n ^ P.gnum), (moebius e : ℤ)

/-- `M_γ(0) = 0`: the empty divisor set. -/
@[simp] theorem MgammaCoeff_zero : P.MgammaCoeff 0 = 0 := by
  simp [MgammaCoeff]

end K0SP2Params

/-! ## §3.  The two-sign source expression -/

/-- **The formal two-sign K0-SP2 source.**

```
Source = ∑_{s = ±1} ∑_{n ∈ S_X} W(n) · D_s(n) · M_γ(n).
```

`W` is the (rescaled) smooth weight `n ↦ W(n/X)` and `D : Bool → ℕ → ℂ` the
two-sign coefficient, `s = true` standing for `+1` and `s = false` for `-1`.
Both are **parameters**: no analytic property of them is used. -/
noncomputable def sourceExpr (P : K0SP2Params) (W : ℕ → ℂ) (D : Bool → ℕ → ℂ) : ℂ :=
  ∑ s : Bool, ∑ n ∈ P.sourceSet, W n * D s n * (P.MgammaCoeff n : ℂ)

/-- The sector of the source carried by a subset `T ⊆ S_X`. -/
noncomputable def sectorExpr (P : K0SP2Params) (W : ℕ → ℂ) (D : Bool → ℕ → ℂ)
    (T : Finset ℕ) : ℂ :=
  ∑ s : Bool, ∑ n ∈ T, W n * D s n * (P.MgammaCoeff n : ℂ)

@[simp] theorem sectorExpr_sourceSet (P : K0SP2Params) (W : ℕ → ℂ) (D : Bool → ℕ → ℂ) :
    sectorExpr P W D P.sourceSet = sourceExpr P W D := rfl

/-- **Two-sign expansion.**  The source is literally the sum of its `+` and `−` halves. -/
theorem sourceExpr_two_sign (P : K0SP2Params) (W : ℕ → ℂ) (D : Bool → ℕ → ℂ) :
    sourceExpr P W D
      = (∑ n ∈ P.sourceSet, W n * D true n * (P.MgammaCoeff n : ℂ))
        + ∑ n ∈ P.sourceSet, W n * D false n * (P.MgammaCoeff n : ℂ) := by
  simp [sourceExpr, add_comm]

/-- **Sector additivity.**  If `T` is the disjoint union of `T₁` and `T₂`, the sector
expression splits.  This is the only reassembly rule used downstream. -/
theorem sectorExpr_union (P : K0SP2Params) (W : ℕ → ℂ) (D : Bool → ℕ → ℂ)
    {T₁ T₂ : Finset ℕ} (h : Disjoint T₁ T₂) :
    sectorExpr P W D (T₁ ∪ T₂) = sectorExpr P W D T₁ + sectorExpr P W D T₂ := by
  unfold sectorExpr
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun s _ => Finset.sum_union h

/-- The empty sector carries nothing. -/
@[simp] theorem sectorExpr_empty (P : K0SP2Params) (W : ℕ → ℂ) (D : Bool → ℕ → ℂ) :
    sectorExpr P W D ∅ = 0 := by simp [sectorExpr]

/-- **Exhaustive four-sector reassembly (abstract form).**  If `S_X` is the union of four
pairwise disjoint sectors then the source is exactly the sum of the four sector values.
This is the identity that §2 of the partition module instantiates. -/
theorem sourceExpr_four_sectors (P : K0SP2Params) (W : ℕ → ℂ) (D : Bool → ℕ → ℂ)
    {A B C R : Finset ℕ}
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hAR : Disjoint A R)
    (hBC : Disjoint B C) (hBR : Disjoint B R) (hCR : Disjoint C R)
    (hunion : A ∪ B ∪ C ∪ R = P.sourceSet) :
    sourceExpr P W D
      = sectorExpr P W D A + sectorExpr P W D B + sectorExpr P W D C
        + sectorExpr P W D R := by
  have h1 : Disjoint (A ∪ B) C := Finset.disjoint_union_left.2 ⟨hAC, hBC⟩
  have h2 : Disjoint (A ∪ B ∪ C) R :=
    Finset.disjoint_union_left.2 ⟨Finset.disjoint_union_left.2 ⟨hAR, hBR⟩, hCR⟩
  have h0 : sourceExpr P W D = sectorExpr P W D (A ∪ B ∪ C ∪ R) := by
    rw [hunion]; rfl
  rw [h0, sectorExpr_union P W D h2, sectorExpr_union P W D h1,
    sectorExpr_union P W D hAB]

end K0SP2Source
end Erdos287
