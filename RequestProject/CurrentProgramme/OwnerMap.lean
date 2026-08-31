import Mathlib
import RequestProject.CurrentProgramme.ShortTShiuSockets

/-!
# CurrentProgramme §12 — the exact owner map and the no-double-spending compiler

`ALL-Q-NO-DOUBLE-SPENDING45` — `conditionalCompiler`.

The finite owner type and the mandated source map

```
    SmallQ principal → EulerPrincipal      SmallQ defect → SmallQ34LS
    SmallR principal → EulerPrincipal      SmallR defect → SmallRDirect
    Hard   principal → EulerPrincipal      Hard   defect → Hard3221
    Even / nonunit   → ZeroRouted
```

Banked: the map is total and single-valued (`owner_exists_unique`), every owner's account is
the sum over exactly its own cells, and the accounts reassemble the total *exactly*
(`no_double_spending`).  Nothing is claimed about the analytic providers themselves.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Erdos287
namespace CurrentProgramme

/-! ## §12.1  Cells and owners -/

/-- The finite owner type. -/
inductive Balanced7Owner
  | eulerPrincipal
  | smallQ34LS
  | smallRDirect
  | hard3221
  | zeroRouted
  deriving DecidableEq, Fintype, Repr

/-- The finite cell type of the full-`q` decomposition. -/
inductive Balanced7Cell
  | smallQPrincipal
  | smallQDefect
  | smallRPrincipal
  | smallRDefect
  | hardPrincipal
  | hardDefect
  | evenNonunit
  deriving DecidableEq, Fintype, Repr

open Balanced7Cell Balanced7Owner

/-- The mandated owner map. -/
def ownerOf : Balanced7Cell → Balanced7Owner
  | smallQPrincipal => eulerPrincipal
  | smallQDefect => smallQ34LS
  | smallRPrincipal => eulerPrincipal
  | smallRDefect => smallRDirect
  | hardPrincipal => eulerPrincipal
  | hardDefect => hard3221
  | evenNonunit => zeroRouted

/-- **`ownerMap_is_the_mandated_one`.**  `LEAN_PROVED`. -/
theorem ownerMap_is_the_mandated_one :
    ownerOf smallQPrincipal = eulerPrincipal ∧ ownerOf smallQDefect = smallQ34LS ∧
      ownerOf smallRPrincipal = eulerPrincipal ∧ ownerOf smallRDefect = smallRDirect ∧
      ownerOf hardPrincipal = eulerPrincipal ∧ ownerOf hardDefect = hard3221 ∧
      ownerOf evenNonunit = zeroRouted := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **`owner_exists_unique`.**  `LEAN_PROVED`.  Every cell has exactly one owner. -/
theorem owner_exists_unique (c : Balanced7Cell) : ∃! o : Balanced7Owner, ownerOf c = o :=
  ⟨ownerOf c, rfl, fun _ h => h.symm⟩

/-- **`owner_map_not_injective`.**  `LEAN_PROVED`.

Three distinct cells are owned by the Euler principal owner — the map is deliberately not
injective, which is why the reassembly below has to be proved rather than assumed. -/
theorem owner_map_not_injective :
    ownerOf smallQPrincipal = ownerOf smallRPrincipal ∧
      ownerOf smallRPrincipal = ownerOf hardPrincipal ∧
      smallQPrincipal ≠ smallRPrincipal := by
  refine ⟨rfl, rfl, by decide⟩

/-! ## §12.2  Accounts and the no-double-spending compiler -/

/-- The account of an owner: the sum of exactly the cells it owns. -/
def ownerAccount (contrib : Balanced7Cell → ℝ) (o : Balanced7Owner) : ℝ :=
  ∑ c ∈ Finset.univ.filter (fun c => ownerOf c = o), contrib c

/-- **`no_double_spending`.**  `LEAN_PROVED`.

The owners' accounts sum to the total contribution: every cell is spent exactly once. -/
theorem no_double_spending (contrib : Balanced7Cell → ℝ) :
    ∑ o : Balanced7Owner, ownerAccount contrib o = ∑ c : Balanced7Cell, contrib c :=
  Finset.sum_fiberwise_of_maps_to (fun c _ => Finset.mem_univ (ownerOf c)) contrib

/-- **`owner_cells_pairwise_disjoint`.**  `LEAN_PROVED`.

Distinct owners own disjoint sets of cells. -/
theorem owner_cells_pairwise_disjoint {o1 o2 : Balanced7Owner} (h : o1 ≠ o2) :
    Disjoint (Finset.univ.filter (fun c => ownerOf c = o1))
      (Finset.univ.filter (fun c => ownerOf c = o2)) := by
  refine Finset.disjoint_filter.2 ?_
  intro c _ h1 h2
  exact h (h1 ▸ h2.symm ▸ rfl)

/-- **`owner_cells_cover`.**  `LEAN_PROVED`.  Every cell belongs to its owner's account. -/
theorem owner_cells_cover (c : Balanced7Cell) :
    c ∈ Finset.univ.filter (fun c' => ownerOf c' = ownerOf c) := by
  simp

/-- **`euler_principal_account`.**  `LEAN_PROVED`.

The Euler principal owner's account is exactly the three principal cells — the full-`q`
principal identity is owned once, not three times. -/
theorem euler_principal_account (contrib : Balanced7Cell → ℝ) :
    ownerAccount contrib eulerPrincipal =
      contrib smallQPrincipal + contrib smallRPrincipal + contrib hardPrincipal := by
  have hfil : (Finset.univ.filter (fun c => ownerOf c = eulerPrincipal)) =
      {smallQPrincipal, smallRPrincipal, hardPrincipal} := by decide +kernel
  rw [ownerAccount, hfil, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

/-- **`zero_routed_account`.**  `LEAN_PROVED`.

The even / nonunit cell is routed to `ZeroRouted`, and if its contribution vanishes the
account is zero. -/
theorem zero_routed_account (contrib : Balanced7Cell → ℝ) (h : contrib evenNonunit = 0) :
    ownerAccount contrib zeroRouted = 0 := by
  unfold ownerAccount
  rw [show (Finset.univ.filter (fun c => ownerOf c = zeroRouted)) = {evenNonunit} from by
    decide +kernel]
  simpa using h

end CurrentProgramme
end Erdos287
