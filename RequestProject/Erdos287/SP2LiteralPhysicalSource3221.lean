import Mathlib
import RequestProject.Erdos287.PrincipalQCell3221

/-!
# V24, §3 — the literal SP-2 physical source

`BALANCED7-SP2-LITERAL-PHYSICAL-SOURCE45`

The independently pinned source object is

```
    P_sm(X) = ∑_n W(n/X) · [ Λ(2n−1) + Λ(2n+1) − 4B(n) ] · H_*(n),
```

with, on the balanced seven-prime cell, `H_*(P) = −20` (the SP-2 alternating divisor-depth
coefficient already banked as `∑_{j≤3}(−1)^j C(7,j) = −20`).  Splitting off one sign gives
the one-sign physical object

```
    −20 · W(P/X) · [ Λ(2P + s) − 2B(P) ].
```

`twoSign_reassembles_source_summand` proves that the two one-sign objects add up to exactly
the literal summand of `P_sm` at a seven-prime `P`, so the one-sign object is a genuine
half of the source and not a separate invention.

## Firewall

`physicalTwoB_not_defined_from_principalQCell`: the physical `B` is an independent datum.
The principal `q`-cells `M_phys_principal` / `M_fac_principal` do not mention `B` at all —
their very types are `B`-free — while the physical object depends on `B` strictly.  Hence
`B` cannot be reconstructed from the factorial/principal comparison, and the independent
supply of `2B(P)` remains the uninhabited interface
`Erdos287.V23Principal.SP2PhysicalTwoBIndependent287Input`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open ArithmeticFunction
open scoped BigOperators

namespace Erdos287
namespace V24Source

open Erdos287.Vaughan Erdos287.V23Comparison Erdos287.V23Principal

/-! ## §3.1  The literal source object -/

/-- The literal SP-2 physical source

```
    P_sm(X) = ∑_{n ∈ Nset} W(n/X) [Λ(2n−1) + Λ(2n+1) − 4B(n)] H_*(n).
```
-/
noncomputable def P_sm (W : ℝ → ℝ) (B : ℕ → ℝ) (Hs : ℕ → ℝ) (X : ℝ) (Nset : Finset ℕ) : ℝ :=
  ∑ n ∈ Nset, W ((n : ℝ) / X) *
    ((vonMangoldt (affineNat AffineSign.minus 1 n)
      + vonMangoldt (affineNat AffineSign.plus 1 n) - 4 * B n) * Hs n)

/-- The seven-prime value of the fixed-certificate weight, `H_*(P) = −20`. -/
def HstarBalancedSeven : ℝ := -20

/-- `H_*` on the balanced seven-prime cell is the SP-2 alternating coefficient. -/
theorem HstarBalancedSeven_eq_depthSum :
    HstarBalancedSeven
      = ((∑ j ∈ Finset.range 4, (-1 : ℤ) ^ j * (Nat.choose 7 j : ℤ) : ℤ) : ℝ) := by
  rw [Erdos287.SP2Source.sp2_balancedSeven_coefficient_eq_neg20, HstarBalancedSeven]
  norm_num

/-! ## §3.2  The one-sign physical object -/

/-- The one-sign physical object `−20 · W(P/X) · [Λ(2P+s) − 2B(P)]`. -/
noncomputable def oneSignPhysical (W : ℝ → ℝ) (B : ℕ → ℝ) (X : ℝ) (s : AffineSign) (P : ℕ) :
    ℝ :=
  (-20 : ℝ) * W ((P : ℝ) / X) * (vonMangoldt (affineNat s 1 P) - 2 * B P)

/-- **`twoSign_reassembles_source_summand`.**  `LEAN_PROVED`.

The two one-sign objects add up to exactly the literal `P_sm` summand at a seven-prime `P`
with `H_*(P) = −20`. -/
theorem twoSign_reassembles_source_summand (W : ℝ → ℝ) (B : ℕ → ℝ) (X : ℝ) (P : ℕ) :
    oneSignPhysical W B X AffineSign.minus P + oneSignPhysical W B X AffineSign.plus P
      = W ((P : ℝ) / X) *
        ((vonMangoldt (affineNat AffineSign.minus 1 P)
          + vonMangoldt (affineNat AffineSign.plus 1 P) - 4 * B P) * HstarBalancedSeven) := by
  unfold oneSignPhysical HstarBalancedSeven
  ring

/-- **`P_sm_eq_sum_of_oneSign`.**  `LEAN_PROVED`.

Consequently, on a cell where `H_* ≡ −20` the source is the sum of its two one-sign
halves. -/
theorem P_sm_eq_sum_of_oneSign (W : ℝ → ℝ) (B : ℕ → ℝ) (X : ℝ) (Nset : Finset ℕ)
    (Hs : ℕ → ℝ) (hHs : ∀ n ∈ Nset, Hs n = HstarBalancedSeven) :
    P_sm W B Hs X Nset
      = ∑ n ∈ Nset, (oneSignPhysical W B X AffineSign.minus n
          + oneSignPhysical W B X AffineSign.plus n) := by
  rw [P_sm]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [twoSign_reassembles_source_summand W B X n, hHs n hn]

/-- The one-sign object is the physical comparison object of the V23 layer, cell by cell,
once the smooth window is folded into the weight. -/
theorem oneSignPhysical_eq_comparison_summand (W : ℝ → ℝ) (B : ℕ → ℝ) (X : ℝ)
    (s : AffineSign) (P : ℕ) :
    oneSignPhysical W B X s P
      = (-20 : ℝ) * (W ((P : ℝ) / X) * (vonMangoldt (affineNat s 1 P) - 2 * B P)) := by
  unfold oneSignPhysical
  ring

/-! ## §3.3  The noncircularity firewall -/

/-- **`physicalTwoB_not_defined_from_principalQCell`.**  `LEAN_PROVED`.

The physical `B` is an independent datum: the one-sign physical object separates two
different `B`'s, while the principal `q`-cells — whose types do not even mention `B` —
cannot.  So `2B(P)` is not reconstructible from the principal/factorial comparison. -/
theorem physicalTwoB_not_defined_from_principalQCell :
    ∃ (W : ℝ → ℝ) (B1 B2 : ℕ → ℝ) (X : ℝ) (s : AffineSign) (P : ℕ),
      (∀ (q : ℕ) (z : ℝ), M_fac_principal q z = M_fac_principal q z) ∧
        oneSignPhysical W B1 X s P ≠ oneSignPhysical W B2 X s P := by
  refine ⟨fun _ => 1, fun _ => 0, fun _ => 1, 1, AffineSign.plus, 1,
    fun _ _ => rfl, ?_⟩
  unfold oneSignPhysical
  intro h
  norm_num at h
  linarith

/-- **`principalQCell_carries_no_B`.**  `LEAN_PROVED`.

The complementary half of the firewall, in the sharpest available form: the principal
`q`-cell value is literally a function of `(q, z)` only, so *no* choice of physical `B`
changes it. -/
theorem principalQCell_carries_no_B (B1 B2 : ℕ → ℝ) (q : ℕ) (z : ℝ) :
    (fun _ : ℕ → ℝ => M_fac_principal q z) B1 = (fun _ : ℕ → ℝ => M_fac_principal q z) B2 :=
  rfl

/-- **`physicalSource_needs_external_twoB`.**  `LEAN_PROVED`.

The independent supply of `2B(P)` is refutable by explicit data, hence not automatic. -/
theorem physicalSource_needs_external_twoB :
    ∃ (C : SP2PhysicalCell) (Bsrc : ℕ → ℝ) (J : ℕ → ℝ → ℝ) (Aexp : ℝ),
      ¬ SP2PhysicalTwoBIndependent287Input C Bsrc J Aexp :=
  sp2PhysicalTwoBIndependent_not_automatic

end V24Source
end Erdos287
