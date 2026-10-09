import Mathlib

/-!
# Erdős #287 effectivity — conductor / complement architecture and the owner ledger (§63)

```
COMPLEMENT SLAB k < 15015, Ω(k) ≤ 3      : KERNEL-PROVED (exact support description)
ω(k) ≤ Ω(k) ON THE SLAB                  : KERNEL-PROVED
OWNER SOURCE VARIABLES PAIRWISE DISJOINT : KERNEL-PROVED
SUBTRACTION / UPDATE LAW                 : KERNEL-PROVED
DISJOINTNESS ⇒ NO NUMERICAL BOUND        : KERNEL-PROVED FIREWALL
```

After all already-banked source removals the live complement is described by the finite slab

    k < 15015    and    Ω(k) ≤ 3,

`15015 = 3·5·7·11·13` being the first odd modulus with five prime factors.  The slab is a
`Finset` and `mem_complementSlab` is its exact membership description; no numerical
whole-slab bound is kernel-promoted anywhere in this file.

The owner ledger records **who** pays for each removed source.  Each owner is attached to a
*declared source variable*; `owner_sources_pairwise_disjoint` proves the attachment is
injective, i.e. no double charge is possible at the level of source variables.  The update
law `ledgerUpdate` shows subtraction/replacement preserves the parent total exactly, and
`disjointness_gives_no_bound` records that disjointness alone implies **no** numerical
inequality.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open Finset

namespace Erdos287
namespace Effectivity

/-! ## §63.1  The complement slab -/

/-- `Ω(k)`, the number of prime factors of `k` with multiplicity. -/
def bigOmega (k : ℕ) : ℕ := ArithmeticFunction.cardFactors k

/-- The live complement slab: `k < 15015` with `Ω(k) ≤ 3`. -/
def complementSlab : Finset ℕ := (Finset.Icc 1 15014).filter (fun k => bigOmega k ≤ 3)

/-- **`mem_complementSlab`.**  `KERNEL-PROVED`.  Exact membership description. -/
theorem mem_complementSlab {k : ℕ} :
    k ∈ complementSlab ↔ (1 ≤ k ∧ k < 15015 ∧ bigOmega k ≤ 3) := by
  simp only [complementSlab, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, by omega, h3⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, by omega⟩, h3⟩

/-- **`omega_le_bigOmega_on_slab`.**  `KERNEL-PROVED`.  On the slab the number of *distinct*
prime factors is also at most three. -/
theorem omega_le_bigOmega_on_slab {k : ℕ} (hk : k ∈ complementSlab) :
    k.primeFactors.card ≤ 3 := by
  rw [mem_complementSlab] at hk
  have h : k.primeFactors.card ≤ bigOmega k := by
    rw [bigOmega, ArithmeticFunction.cardFactors_apply, ← Nat.toFinset_factors k]
    exact List.toFinset_card_le _
  omega

/-- **`slab_excludes_15015`.**  `KERNEL-PROVED`.  `15015 = 3·5·7·11·13` is outside the slab. -/
theorem slab_excludes_15015 : (15015 : ℕ) ∉ complementSlab := by
  rw [mem_complementSlab]
  rintro ⟨-, h, -⟩
  omega

/-- **`slab_contains_core`.**  `KERNEL-PROVED`.  The `k = 1` core lies in the slab. -/
theorem slab_contains_core : (1 : ℕ) ∈ complementSlab := by
  rw [mem_complementSlab]
  refine ⟨le_refl 1, by norm_num, ?_⟩
  rw [bigOmega, ArithmeticFunction.cardFactors_one]
  omega

/-! ## §63.2  The owner ledger -/

/-- The current owners of removed source. -/
inductive Owner
  | internalProjectorTail   -- `d > 30000`
  | sourceEGt5000           -- `e > 5000`
  | atomTOne                -- `t = 1`
  | p8BoundaryReplacement   -- P8 boundary
  | rankThreeOwners         -- rank-three closed `k`-owners
  | kOneCore                -- `k = 1` core
  deriving DecidableEq, Repr

/-- The declared source variables. -/
inductive SourceVar
  | dTail | eSource | tAtom | p8Boundary | rankThree | kCore
  deriving DecidableEq, Repr

/-- The declared source variable of each owner. -/
def ownerSource : Owner → SourceVar
  | .internalProjectorTail => .dTail
  | .sourceEGt5000 => .eSource
  | .atomTOne => .tAtom
  | .p8BoundaryReplacement => .p8Boundary
  | .rankThreeOwners => .rankThree
  | .kOneCore => .kCore

/-- **`owner_sources_pairwise_disjoint`.**  `KERNEL-PROVED`.  Distinct owners are attached to
distinct source variables: no owner can be charged twice at its declared source. -/
theorem owner_sources_pairwise_disjoint :
    Function.Injective ownerSource := by
  intro a b hab
  cases a <;> cases b <;> simp_all [ownerSource]

/-- A ledger assigns a charge to each owner. -/
abbrev Ledger := Owner → ℚ

/-- The total charge of a ledger. -/
def ledgerTotal (L : Ledger) : ℚ :=
  L .internalProjectorTail + L .sourceEGt5000 + L .atomTOne + L .p8BoundaryReplacement
    + L .rankThreeOwners + L .kOneCore

/-- Replace the charge of one owner. -/
def ledgerUpdate (L : Ledger) (o : Owner) (v : ℚ) : Ledger :=
  fun p => if p = o then v else L p

/-- **`ledgerUpdate_total`.**  `KERNEL-PROVED`.  The subtraction/update law: replacing one
owner's charge changes the total exactly by the declared difference, leaving every other
owner's contribution — and hence the parent source — untouched. -/
theorem ledgerUpdate_total (L : Ledger) (o : Owner) (v : ℚ) :
    ledgerTotal (ledgerUpdate L o v) = ledgerTotal L - L o + v := by
  cases o <;> simp [ledgerTotal, ledgerUpdate] <;> ring

/-- **`ledgerUpdate_preserves_others`.**  `KERNEL-PROVED`.  An update touches no other
owner. -/
theorem ledgerUpdate_preserves_others (L : Ledger) (o p : Owner) (v : ℚ) (h : p ≠ o) :
    ledgerUpdate L o v p = L p := by
  simp [ledgerUpdate, h]

/-- **`disjointness_gives_no_bound`.**  `KERNEL-PROVED` firewall.  Owner disjointness is a
bookkeeping statement only: for *every* proposed numerical bound there is a ledger, with the
same disjoint owner structure, exceeding it.  No numerical inequality may be inferred from
disjointness. -/
theorem disjointness_gives_no_bound (b : ℚ) :
    ∃ L : Ledger, Function.Injective ownerSource ∧ b < ledgerTotal L := by
  refine ⟨fun _ => |b| + 1, owner_sources_pairwise_disjoint, ?_⟩
  have h : |b| + 1 > 0 := by positivity
  have hb : b ≤ |b| := le_abs_self b
  simp only [ledgerTotal]
  linarith

end Effectivity
end Erdos287
