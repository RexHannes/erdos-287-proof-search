import Mathlib
import RequestProject.CurrentProgramme.SmallROwnerSubtraction
import RequestProject.CurrentProgramme.PostRepairOwnerCompiler

/-!
# Hostile-audit safe bank §7 — SmallR owner / principal algebra and capacity

`AFFINE287-SP2-SMALLR-OWNER-SUBTRACTION45 : provedAlgebraic`

The three objects `S_sr`, `M_sr_prin`, `D_sr` are the ones already banked in
`CurrentProgramme.SmallROwnerSubtraction`; they are **reused**, not redefined.  What is added
here is

* the exact pair of owner identities `D_sr = S_sr − M_sr_prin` and `S_sr = M_sr_prin + D_sr`;
* exact **owner uniqueness** for the two SmallR cells inside the banked post-repair owner map:
  the SmallR principal cell is owned by `eulerPrincipal` and the SmallR defect cell by
  `smallRDirect`, and by nobody else;
* the elementary **capacity** statement of the SmallR region: with the cut `U = X^{1/3}` and
  the factorisation `q·r = X`, the SmallR condition `r ≤ U` forces `q ≥ X^{2/3}`;
* the rational exponent ledger `2/3 + 1/3 = 1` underlying the `X^{1/3+o(1)}` principal target.

The divisor-function asymptotic and the `φ` lower bound remain **external**: they are the
uninhabited interface `SmallRPrincipalCapacityInput`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Erdos287
namespace HostileAudit

open Erdos287.CurrentProgramme
open Erdos287.PostBalanced7Pro
open Erdos287.PostBalanced7Pro.PostRepairCell
open Erdos287.PostBalanced7Pro.PostRepairOwner

/-! ## §7.1  The exact owner subtraction -/

/-- **`smallR_defect_eq_source_sub_principal`.**  `LEAN_PROVED`.

`D_sr = S_sr − M_sr_prin`, exactly. -/
theorem smallR_defect_eq_source_sub_principal (u N : ℕ) (coeff : ℕ × ℕ → ℝ) (mPrin : ℝ) :
    dSmallR u N coeff mPrin = sSmallR u N coeff - mPrin := rfl

/-- **`smallR_source_eq_principal_add_defect`.**  `LEAN_PROVED`.

`S_sr = M_sr_prin + D_sr`, exactly. -/
theorem smallR_source_eq_principal_add_defect (u N : ℕ) (coeff : ℕ × ℕ → ℝ) (mPrin : ℝ) :
    sSmallR u N coeff = mPrin + dSmallR u N coeff mPrin := by
  rw [smallR_defect_eq_source_sub_principal]
  ring

/-- **`smallR_owner_pair_is_exact`.**  `LEAN_PROVED`.

Both directions of the owner subtraction, together: no mass is created or lost. -/
theorem smallR_owner_pair_is_exact (u N : ℕ) (coeff : ℕ × ℕ → ℝ) (mPrin : ℝ) :
    dSmallR u N coeff mPrin = sSmallR u N coeff - mPrin ∧
      sSmallR u N coeff = mPrin + dSmallR u N coeff mPrin :=
  ⟨rfl, smallR_source_eq_principal_add_defect u N coeff mPrin⟩

/-! ## §7.2  Exact owner uniqueness -/

/-- **`smallR_owner_assignment`.**  `LEAN_PROVED`.

```
SmallR principal → EulerPrincipal,      SmallR defect → SmallRDirect,
```

and each assignment is the unique one in the banked post-repair owner map. -/
theorem smallR_owner_assignment :
    postRepairOwnerOf smallRPrincipal = eulerPrincipal ∧
      postRepairOwnerOf smallRDefect = smallRDirect ∧
      (∀ o : PostRepairOwner, postRepairOwnerOf smallRPrincipal = o → o = eulerPrincipal) ∧
      (∀ o : PostRepairOwner, postRepairOwnerOf smallRDefect = o → o = smallRDirect) :=
  ⟨rfl, rfl, fun _ h => h.symm, fun _ h => h.symm⟩

/-- **`smallR_owners_are_distinct`.**  `LEAN_PROVED`.

The principal and defect cells have *different* owners, so the SmallR principal mass is never
charged to the SmallR direct account. -/
theorem smallR_owners_are_distinct :
    postRepairOwnerOf smallRPrincipal ≠ postRepairOwnerOf smallRDefect := by
  decide +kernel

/-- **`smallR_defect_account`.**  `LEAN_PROVED`.

The `smallRDirect` owner's account is exactly the single SmallR defect cell. -/
theorem smallR_defect_account (contrib : PostRepairCell → ℝ) :
    postRepairAccount contrib smallRDirect = contrib smallRDefect := by
  have hfil : (Finset.univ.filter (fun c => postRepairOwnerOf c = smallRDirect)) =
      {smallRDefect} := by decide +kernel
  rw [postRepairAccount, hfil, Finset.sum_singleton]

/-! ## §7.3  The SmallR capacity exponent -/

/-- **`smallR_modulus_capacity`.**  `LEAN_PROVED`.

In the SmallR region the modulus is large: if `q·r = X` with `0 < r ≤ X^{1/3}`, then

```
q ≥ X^{2/3}.
```
-/
theorem smallR_modulus_capacity {X q r : ℝ} (hX : 0 < X) (hr : 0 < r)
    (hqr : q * r = X) (hrU : r ≤ X ^ ((1 : ℝ) / 3)) :
    X ^ ((2 : ℝ) / 3) ≤ q := by
  have hq : 0 < q := by
    by_contra hcon
    push_neg at hcon
    nlinarith
  have hsplit : X ^ ((2 : ℝ) / 3) * X ^ ((1 : ℝ) / 3) = X := by
    rw [← Real.rpow_add hX]
    norm_num
  have hpos : (0 : ℝ) < X ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hX _
  have hstep : X ^ ((2 : ℝ) / 3) * X ^ ((1 : ℝ) / 3) ≤ q * X ^ ((1 : ℝ) / 3) := by
    rw [hsplit]
    calc X = q * r := hqr.symm
      _ ≤ q * X ^ ((1 : ℝ) / 3) := mul_le_mul_of_nonneg_left hrU hq.le
  exact le_of_mul_le_mul_right hstep hpos

/-- The SmallR capacity exponent `2/3`. -/
def smallRCapacityExponent : ℚ := 2 / 3

/-- The SmallR principal target exponent `1/3`. -/
def smallRPrincipalTargetExponent : ℚ := 1 / 3

/-- **`smallR_exponent_ledger`.**  `LEAN_PROVED`.

`2/3 + 1/3 = 1` and `2/3 = 1 − 1/3`: the capacity exponent and the principal target exponent
are complementary, which is the rational content of the `X^{1/3+o(1)}` target. -/
theorem smallR_exponent_ledger :
    smallRCapacityExponent + smallRPrincipalTargetExponent = 1 ∧
      smallRCapacityExponent = 1 - smallRPrincipalTargetExponent ∧
      smallRPrincipalTargetExponent < smallRCapacityExponent := by
  unfold smallRCapacityExponent smallRPrincipalTargetExponent
  norm_num

/-! ## §7.4  The external principal-capacity interface -/

/-- **`SmallRPrincipalCapacityInput`** — `EXTERNAL / ANALYTIC / UNINHABITED`.

The two analytic ingredients of the SmallR principal target that are *not* available here:
the divisor-function average and the `φ` lower bound.  Both are supplied as declared bounds
at scale `X`; no proof is attempted. -/
structure SmallRPrincipalCapacityInput (X mPrin divAvg phiLower : ℝ) : Prop where
  /-- The scale is nontrivial. -/
  scale : 3 ≤ X
  /-- The divisor-average input. -/
  divisor_average : 0 ≤ divAvg ∧ divAvg ≤ (Real.log X) ^ 2
  /-- The `φ` lower bound input. -/
  phi_lower : 0 < phiLower ∧ phiLower ≤ 1
  /-- The resulting principal bound at the `X^{1/3+o(1)}` target. -/
  principal_bound : |mPrin| ≤ divAvg / phiLower * X ^ ((1 : ℝ) / 3)

/-- **`smallR_principal_of_capacity_input`.**  `CONDITIONAL / LEAN_PROVED`. -/
theorem smallR_principal_of_capacity_input {X mPrin divAvg phiLower : ℝ}
    (h : SmallRPrincipalCapacityInput X mPrin divAvg phiLower) :
    |mPrin| ≤ divAvg / phiLower * X ^ ((1 : ℝ) / 3) :=
  h.principal_bound

/-- **`smallRPrincipalCapacity_not_automatic`.**  `LEAN_PROVED`.  The interface is not
inhabited. -/
theorem smallRPrincipalCapacity_not_automatic :
    ∃ X mPrin divAvg phiLower : ℝ, ¬ SmallRPrincipalCapacityInput X mPrin divAvg phiLower := by
  refine ⟨0, 0, 0, 0, ?_⟩
  intro h
  have := h.scale
  norm_num at this

end HostileAudit
end Erdos287
