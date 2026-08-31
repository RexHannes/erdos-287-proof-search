import Mathlib
import RequestProject.CurrentProgramme.PostAuditFullQCompiler
import RequestProject.CurrentProgramme.SmallPrimePrefix

/-!
# CurrentProgramme (post-Balanced7 pass) §10 — the post-repair owner map and compiler

The pass-1 owner map of `OwnerMap.lean` is **not modified**.  What is added here is the
*refined* owner map that the repair route requires:

* the hard defect is no longer routed to the `3221` provider but to the **short-`t` sieve**
  provider (`hardShortT`), which is where the `δ = 1/21` physical-range ledger lives;
* the SmallQ defect is split into its low-conductor and high-conductor children, both owned
  by `smallQ34LS`;
* the `Ω(d) ≥ 3` small-prime-prefix residual gets its **own** owner
  (`threeSmallPrimePrefix`), so it can never be absorbed silently into another account.

Banked: exhaustiveness, unique ownership, pairwise disjointness of accounts, the exact
no-double-spending identity, and a purely logical compiler to the pass-1 conclusion
`BalancedSevenAsymptoticConclusion`.  The antecedent bundle is **not** inhabited.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Erdos287
namespace PostBalanced7Pro

open Erdos287.CurrentProgramme

/-! ## §10.1  The refined owner and cell types -/

/-- The post-repair owner type.  `hardShortT` replaces the pass-1 `hard3221` owner and
`threeSmallPrimePrefix` is new. -/
inductive PostRepairOwner
  | eulerPrincipal
  | smallQ34LS
  | smallRDirect
  | hardShortT
  | threeSmallPrimePrefix
  | zeroRouted
  deriving DecidableEq, Fintype, Repr

/-- The post-repair cell type. -/
inductive PostRepairCell
  | smallQPrincipal
  | smallQDefectLowConductor
  | smallQDefectHighConductor
  | smallRPrincipal
  | smallRDefect
  | hardPrincipal
  | hardDefect
  | threePrefixResidual
  | evenNonunit
  deriving DecidableEq, Fintype, Repr

open PostRepairCell PostRepairOwner

/-- The mandated post-repair owner map. -/
def postRepairOwnerOf : PostRepairCell → PostRepairOwner
  | smallQPrincipal => eulerPrincipal
  | smallQDefectLowConductor => smallQ34LS
  | smallQDefectHighConductor => smallQ34LS
  | smallRPrincipal => eulerPrincipal
  | smallRDefect => smallRDirect
  | hardPrincipal => eulerPrincipal
  | hardDefect => hardShortT
  | threePrefixResidual => threeSmallPrimePrefix
  | evenNonunit => zeroRouted

/-- **`postRepairOwnerMap_is_the_mandated_one`.**  `LEAN_PROVED`. -/
theorem postRepairOwnerMap_is_the_mandated_one :
    postRepairOwnerOf smallQPrincipal = eulerPrincipal ∧
      postRepairOwnerOf smallQDefectLowConductor = smallQ34LS ∧
      postRepairOwnerOf smallQDefectHighConductor = smallQ34LS ∧
      postRepairOwnerOf smallRPrincipal = eulerPrincipal ∧
      postRepairOwnerOf smallRDefect = smallRDirect ∧
      postRepairOwnerOf hardPrincipal = eulerPrincipal ∧
      postRepairOwnerOf hardDefect = hardShortT ∧
      postRepairOwnerOf threePrefixResidual = threeSmallPrimePrefix ∧
      postRepairOwnerOf evenNonunit = zeroRouted :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **`postRepairOwner_exists_unique`.**  `LEAN_PROVED`.  Every cell has exactly one owner. -/
theorem postRepairOwner_exists_unique (c : PostRepairCell) :
    ∃! o : PostRepairOwner, postRepairOwnerOf c = o :=
  ⟨postRepairOwnerOf c, rfl, fun _ h => h.symm⟩

/-- **`postRepairOwner_is_a_refinement`.**  `LEAN_PROVED`.

The post-repair owner map is a genuine refinement of the pass-1 one: it has one more owner
(the `Ω(d) ≥ 3` prefix account) and two more cells. -/
theorem postRepairOwner_is_a_refinement :
    Fintype.card PostRepairOwner = 6 ∧ Fintype.card Balanced7Owner = 5 ∧
      Fintype.card PostRepairCell = 9 ∧ Fintype.card Balanced7Cell = 7 := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-! ## §10.2  Accounts, disjointness and no double spending -/

/-- The account of a post-repair owner. -/
def postRepairAccount (contrib : PostRepairCell → ℝ) (o : PostRepairOwner) : ℝ :=
  ∑ c ∈ Finset.univ.filter (fun c => postRepairOwnerOf c = o), contrib c

/-- **`postRepair_no_double_spending`.**  `LEAN_PROVED`.

The owners' accounts sum to the total contribution: every cell is spent exactly once. -/
theorem postRepair_no_double_spending (contrib : PostRepairCell → ℝ) :
    ∑ o : PostRepairOwner, postRepairAccount contrib o = ∑ c : PostRepairCell, contrib c :=
  Finset.sum_fiberwise_of_maps_to (fun c _ => Finset.mem_univ (postRepairOwnerOf c)) contrib

/-- **`postRepair_accounts_disjoint`.**  `LEAN_PROVED`. -/
theorem postRepair_accounts_disjoint {o1 o2 : PostRepairOwner} (h : o1 ≠ o2) :
    Disjoint (Finset.univ.filter (fun c => postRepairOwnerOf c = o1))
      (Finset.univ.filter (fun c => postRepairOwnerOf c = o2)) := by
  refine Finset.disjoint_filter.2 ?_
  intro c _ h1 h2
  exact h (h1 ▸ h2.symm ▸ rfl)

/-- **`postRepair_smallQ_account`.**  `LEAN_PROVED`.

The SmallQ `3+4` owner's account is exactly the two conductor children — the conductor split
of §5 is spent once. -/
theorem postRepair_smallQ_account (contrib : PostRepairCell → ℝ) :
    postRepairAccount contrib smallQ34LS =
      contrib smallQDefectLowConductor + contrib smallQDefectHighConductor := by
  have hfil : (Finset.univ.filter (fun c => postRepairOwnerOf c = smallQ34LS)) =
      {smallQDefectLowConductor, smallQDefectHighConductor} := by decide +kernel
  rw [postRepairAccount, hfil, Finset.sum_insert (by decide), Finset.sum_singleton]

/-- **`postRepair_threePrefix_account`.**  `LEAN_PROVED`.

The `Ω(d) ≥ 3` residual owns exactly one cell: it is never absorbed into another account. -/
theorem postRepair_threePrefix_account (contrib : PostRepairCell → ℝ) :
    postRepairAccount contrib threeSmallPrimePrefix = contrib threePrefixResidual := by
  have hfil : (Finset.univ.filter (fun c => postRepairOwnerOf c = threeSmallPrimePrefix)) =
      {threePrefixResidual} := by decide +kernel
  rw [postRepairAccount, hfil, Finset.sum_singleton]

/-! ## §10.3  The conditional compiler -/

/-- **`BalancedSevenPostRepairInputs`** — the post-repair antecedent bundle.  `UNINHABITED`.

The four external children are the `3+4` conductor-split source, the short-`t` sieve source,
the `Ω(d) ≥ 3` small-prime-prefix Type-II source, and the full Euler principal identity. -/
structure BalancedSevenPostRepairInputs
    (S : ℝ → ℝ) (cellVal : PostRepairCell → ℝ → ℝ)
    (conductorSplitSource shortTSource threePrefixSource eulerPrincipalInput : Prop) : Prop where
  /-- The conductor-split `3+4` large-sieve source is supplied. -/
  conductor_split : conductorSplitSource
  /-- The short-`t` sieve source (physical range, `δ = 1/21`) is supplied. -/
  short_t : shortTSource
  /-- The `Ω(d) ≥ 3` small-prime-prefix Type-II source is supplied. -/
  three_prefix : threePrefixSource
  /-- The full Euler principal identity is supplied. -/
  euler_principal : eulerPrincipalInput
  /-- Exact reassembly of the physical sum from the owners' accounts. -/
  owner_reassembly :
    ∀ X : ℝ, S X = ∑ o : PostRepairOwner, postRepairAccount (fun c => cellVal c X) o
  /-- Each cell is supplied by its owner with an `o(X / log X)` saving. -/
  cell_savings : ∀ c : PostRepairCell, ∀ eps : ℝ, 0 < eps →
    ∃ X0 : ℝ, ∀ X : ℝ, X0 ≤ X → |cellVal c X| ≤ eps * X / Real.log X

/-- **`balancedSeven_postRepair_compiler`.**  `LEAN_PROVED` (purely logical implication).

The post-repair bundle implies the Balanced7 asymptotic conclusion of pass 1.  This is a
conditional compiler: no antecedent is available. -/
theorem balancedSeven_postRepair_compiler
    {S : ℝ → ℝ} {cellVal : PostRepairCell → ℝ → ℝ}
    {conductorSplitSource shortTSource threePrefixSource eulerPrincipalInput : Prop}
    (h : BalancedSevenPostRepairInputs S cellVal conductorSplitSource shortTSource
      threePrefixSource eulerPrincipalInput) :
    BalancedSevenAsymptoticConclusion S := by
  intro eps heps
  choose X0 hX0 using fun c : PostRepairCell => h.cell_savings c (eps / 9) (by positivity)
  refine ⟨Finset.univ.sup' ⟨smallQPrincipal, Finset.mem_univ _⟩ X0, ?_⟩
  intro X hX
  have hXc : ∀ c : PostRepairCell, X0 c ≤ X := fun c =>
    le_trans (Finset.le_sup' X0 (Finset.mem_univ c)) hX
  calc |S X| = |∑ c : PostRepairCell, cellVal c X| := by
        rw [h.owner_reassembly X, postRepair_no_double_spending]
    _ ≤ ∑ c : PostRepairCell, |cellVal c X| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _c : PostRepairCell, eps / 9 * X / Real.log X :=
        Finset.sum_le_sum fun c _ => hX0 c X (hXc c)
    _ = eps * X / Real.log X := by
        rw [Finset.sum_const, Finset.card_univ]
        have hcard : (Fintype.card PostRepairCell : ℝ) = 9 := by
          norm_num [show Fintype.card PostRepairCell = 9 from by decide +kernel]
        rw [nsmul_eq_mul, hcard]
        ring

/-- **`postRepairInputs_not_inhabited_here`.**  `LEAN_PROVED`. -/
theorem postRepairInputs_not_inhabited_here :
    ∃ (S : ℝ → ℝ) (cellVal : PostRepairCell → ℝ → ℝ) (a b c d : Prop),
      ¬ BalancedSevenPostRepairInputs S cellVal a b c d := by
  refine ⟨fun _ => 0, fun _ _ => 0, False, True, True, True, ?_⟩
  intro h
  exact h.conductor_split

/-- **`postRepair_compiler_does_not_prove_balancedSeven`.**  `LEAN_PROVED`.

Balanced7 remains open: the compiler is conditional and its antecedent is not available. -/
theorem postRepair_compiler_does_not_prove_balancedSeven :
    (∃ (S : ℝ → ℝ) (cellVal : PostRepairCell → ℝ → ℝ) (a b c d : Prop),
      ¬ BalancedSevenPostRepairInputs S cellVal a b c d) ∧
      ∀ (S : ℝ → ℝ) (cellVal : PostRepairCell → ℝ → ℝ) (a b c d : Prop),
        BalancedSevenPostRepairInputs S cellVal a b c d →
          BalancedSevenAsymptoticConclusion S :=
  ⟨postRepairInputs_not_inhabited_here, fun _ _ _ _ _ _ h => balancedSeven_postRepair_compiler h⟩

end PostBalanced7Pro
end Erdos287
