import Mathlib
import RequestProject.CurrentProgramme.ExactQRPartition
import RequestProject.CurrentProgramme.PostRepairOwnerCompiler

/-!
# Hostile-audit safe bank §12 — full-`q` exact reassembly

`ALL-Q-NO-DOUBLE-SPENDING45` / `ALL-Q-PROVIDER-REASSEMBLY45`.

The exact, literal partition of the full `q`-range at the cut `U`:

```
SmallQ : q ≤ U,        SmallR : q > U and r ≤ U,        Hard : q > U and r > U,
```

with **literal boundary ownership** (`q = U` belongs to SmallQ; `r = U` with `q > U` belongs
to SmallR).  The cover/disjointness statements are reused from the banked
`CurrentProgramme.ExactQRPartition`; this module adds the principal/defect refinement, the
Euler-principal reassembly and the two routing lemmas.

Banked here:

* `RegionSource = RegionPrincipal + RegionDefect` for each region, exactly;
* `region_principals_sum_eq_full` — `SmallQPrincipal + SmallRPrincipal + HardPrincipal =
  FullEulerPrincipal`, and `no_region_owns_the_full_principal`: **no region owns `2B(P)`
  independently**;
* `fullQ_no_double_spending` — the fiberwise owner identity for the six cells;
* routing: `even_q_is_impossible` (because `2P + s` is odd) and `q_coprime_twoP`
  (from `q ∣ 2P + s` with `s = ±1`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Erdos287
namespace HostileAudit

open Erdos287.CurrentProgramme

/-! ## §12.1  The literal boundary ownership -/

/-- **`fullQ_exact_cover`.**  `LEAN_PROVED` (reused). -/
theorem fullQ_exact_cover (U : ℕ) (x : ℕ × ℕ) :
    IsSmallQ U x ∨ IsSmallR U x ∨ IsHard U x :=
  qr_exact_cover U x

/-- **`fullQ_pairwise_disjoint`.**  `LEAN_PROVED` (reused). -/
theorem fullQ_pairwise_disjoint (U : ℕ) (x : ℕ × ℕ) :
    ¬ (IsSmallQ U x ∧ IsSmallR U x) ∧ ¬ (IsSmallQ U x ∧ IsHard U x) ∧
      ¬ (IsSmallR U x ∧ IsHard U x) :=
  qr_exact_pairwise_disjoint U x

/-- **`boundary_q_eq_U_is_smallQ`.**  `LEAN_PROVED`.

Literal boundary ownership: the modulus `q = U` is owned by SmallQ, and by nobody else. -/
theorem boundary_q_eq_U_is_smallQ (U r : ℕ) :
    IsSmallQ U (U, r) ∧ ¬ IsSmallR U (U, r) ∧ ¬ IsHard U (U, r) := by
  refine ⟨le_refl U, ?_, ?_⟩
  · rintro ⟨h, -⟩
    exact absurd h (lt_irrefl U)
  · rintro ⟨h, -⟩
    exact absurd h (lt_irrefl U)

/-- **`boundary_r_eq_U_is_smallR`.**  `LEAN_PROVED`.

Literal boundary ownership: with `q > U`, the cofactor `r = U` is owned by SmallR. -/
theorem boundary_r_eq_U_is_smallR {U q : ℕ} (hq : U < q) :
    IsSmallR U (q, U) ∧ ¬ IsSmallQ U (q, U) ∧ ¬ IsHard U (q, U) := by
  refine ⟨⟨hq, le_refl U⟩, ?_, ?_⟩
  · intro h
    exact absurd (lt_of_lt_of_le hq h) (lt_irrefl U)
  · rintro ⟨-, h⟩
    exact absurd h (lt_irrefl U)

/-! ## §12.2  Regions, cells and the principal/defect split -/

/-- The three regions of the full `q`-range. -/
inductive FullQRegion
  | smallQ
  | smallR
  | hard
  deriving DecidableEq, Fintype, Repr

/-- The six cells: each region has a principal and a defect part. -/
inductive FullQCell
  | smallQPrincipal
  | smallQDefect
  | smallRPrincipal
  | smallRDefect
  | hardPrincipal
  | hardDefect
  deriving DecidableEq, Fintype, Repr

open FullQRegion FullQCell

/-- The principal cell of a region. -/
def principalCell : FullQRegion → FullQCell
  | smallQ => smallQPrincipal
  | smallR => smallRPrincipal
  | hard => hardPrincipal

/-- The defect cell of a region. -/
def defectCell : FullQRegion → FullQCell
  | smallQ => smallQDefect
  | smallR => smallRDefect
  | hard => hardDefect

/-- The region source: principal plus defect. -/
def regionSource (val : FullQCell → ℝ) (R : FullQRegion) : ℝ :=
  val (principalCell R) + val (defectCell R)

/-- **`region_source_split`.**  `LEAN_PROVED`.

`RegionSource = RegionPrincipal + RegionDefect`, exactly, for each of the three regions. -/
theorem region_source_split (val : FullQCell → ℝ) (R : FullQRegion) :
    regionSource val R = val (principalCell R) + val (defectCell R) := rfl

/-- **`region_defect_is_the_subtraction`.**  `LEAN_PROVED`. -/
theorem region_defect_is_the_subtraction (val : FullQCell → ℝ) (R : FullQRegion) :
    val (defectCell R) = regionSource val R - val (principalCell R) := by
  rw [region_source_split]; ring

/-- The full Euler principal: the sum of the three region principals. -/
def fullEulerPrincipal (val : FullQCell → ℝ) : ℝ :=
  val smallQPrincipal + val smallRPrincipal + val hardPrincipal

/-- **`region_principals_sum_eq_full`.**  `LEAN_PROVED`.

```
SmallQPrincipal + SmallRPrincipal + HardPrincipal = FullEulerPrincipal.
```
-/
theorem region_principals_sum_eq_full (val : FullQCell → ℝ) :
    ∑ R : FullQRegion, val (principalCell R) = fullEulerPrincipal val := by
  unfold fullEulerPrincipal
  rw [show (Finset.univ : Finset FullQRegion) = {smallQ, smallR, hard} from rfl,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  show val smallQPrincipal + (val smallRPrincipal + val hardPrincipal)
      = val smallQPrincipal + val smallRPrincipal + val hardPrincipal
  ring

/-- **`no_region_owns_the_full_principal`.**  `LEAN_PROVED`.

No region owns `2B(P)` independently: with each region principal equal to `1` the full Euler
principal is `3`, so no single region principal equals it. -/
theorem no_region_owns_the_full_principal :
    ∃ val : FullQCell → ℝ, ∀ R : FullQRegion,
      val (principalCell R) ≠ fullEulerPrincipal val := by
  refine ⟨fun _ => 1, ?_⟩
  intro R
  unfold fullEulerPrincipal
  cases R <;> · show (1 : ℝ) ≠ 1 + 1 + 1
                norm_num

/-! ## §12.3  Owners and no double spending -/

/-- The full-`q` owner of each cell.  The three principals are owned by the single Euler
principal account; each defect has its own provider. -/
def fullQOwnerOf : FullQCell → Erdos287.PostBalanced7Pro.PostRepairOwner
  | smallQPrincipal => Erdos287.PostBalanced7Pro.PostRepairOwner.eulerPrincipal
  | smallRPrincipal => Erdos287.PostBalanced7Pro.PostRepairOwner.eulerPrincipal
  | hardPrincipal => Erdos287.PostBalanced7Pro.PostRepairOwner.eulerPrincipal
  | smallQDefect => Erdos287.PostBalanced7Pro.PostRepairOwner.smallQ34LS
  | smallRDefect => Erdos287.PostBalanced7Pro.PostRepairOwner.smallRDirect
  | hardDefect => Erdos287.PostBalanced7Pro.PostRepairOwner.hardShortT

/-- The account of a full-`q` owner. -/
def fullQAccount (val : FullQCell → ℝ) (o : Erdos287.PostBalanced7Pro.PostRepairOwner) : ℝ :=
  ∑ c ∈ Finset.univ.filter (fun c => fullQOwnerOf c = o), val c

/-- **`fullQ_owner_exists_unique`.**  `LEAN_PROVED`. -/
theorem fullQ_owner_exists_unique (c : FullQCell) :
    ∃! o : Erdos287.PostBalanced7Pro.PostRepairOwner, fullQOwnerOf c = o :=
  ⟨fullQOwnerOf c, rfl, fun _ h => h.symm⟩

/-- **`fullQ_no_double_spending`.**  `LEAN_PROVED`.

The owners' accounts reassemble the total: every cell is spent exactly once. -/
theorem fullQ_no_double_spending (val : FullQCell → ℝ) :
    ∑ o : Erdos287.PostBalanced7Pro.PostRepairOwner, fullQAccount val o
      = ∑ c : FullQCell, val c :=
  Finset.sum_fiberwise_of_maps_to (fun c _ => Finset.mem_univ (fullQOwnerOf c)) val

/-- **`fullQ_euler_account_is_the_three_principals`.**  `LEAN_PROVED`.

The Euler principal account is *exactly* the three region principals — the full principal,
owned once. -/
theorem fullQ_euler_account_is_the_three_principals (val : FullQCell → ℝ) :
    fullQAccount val Erdos287.PostBalanced7Pro.PostRepairOwner.eulerPrincipal
      = fullEulerPrincipal val := by
  have hfil : (Finset.univ.filter
      (fun c => fullQOwnerOf c = Erdos287.PostBalanced7Pro.PostRepairOwner.eulerPrincipal))
      = {smallQPrincipal, smallRPrincipal, hardPrincipal} := by decide +kernel
  rw [fullQAccount, hfil]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  unfold fullEulerPrincipal
  ring

/-! ## §12.4  Routing: even and non-unit moduli -/

/-- **`even_q_is_impossible`.**  `LEAN_PROVED`.

`2P + s` is odd for `s = ±1`, so no even modulus can divide it: the even-`q` cell is empty,
not merely negligible. -/
theorem even_q_is_impossible {q P s : ℤ} (hs : s = 1 ∨ s = -1) (hdvd : q ∣ 2 * P + s) :
    ¬ (2 ∣ q) := by
  intro h2
  obtain ⟨k, hk⟩ : (2 : ℤ) ∣ 2 * P + s := dvd_trans h2 hdvd
  rcases hs with rfl | rfl <;> omega

/-- **`q_coprime_twoP`.**  `LEAN_PROVED`.

From `q ∣ 2P + s` with `s = ±1` the modulus is coprime to `2P`: the non-unit cell is routed
out. -/
theorem q_coprime_twoP {q P s : ℤ} (hs : s = 1 ∨ s = -1) (hdvd : q ∣ 2 * P + s) :
    IsCoprime q (2 * P) := by
  obtain ⟨k, hk⟩ := hdvd
  rcases hs with rfl | rfl
  · exact ⟨k, -1, by linarith [hk]⟩
  · exact ⟨-k, 1, by linarith [hk]⟩

/-- **`routing_is_exhaustive`.**  `LEAN_PROVED`.

Both routed cells are genuinely empty under the physical hypothesis `q ∣ 2P + s`, `s = ±1`:
`q` is odd and coprime to `2P`. -/
theorem routing_is_exhaustive {q P s : ℤ} (hs : s = 1 ∨ s = -1) (hdvd : q ∣ 2 * P + s) :
    ¬ (2 ∣ q) ∧ IsCoprime q (2 * P) :=
  ⟨even_q_is_impossible hs hdvd, q_coprime_twoP hs hdvd⟩

end HostileAudit
end Erdos287
