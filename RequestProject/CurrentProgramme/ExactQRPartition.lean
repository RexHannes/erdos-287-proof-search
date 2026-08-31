import Mathlib
import RequestProject.Erdos287.FullQStructuralPartition3221
import RequestProject.CurrentProgramme.EulerUniformityFirewall

/-!
# CurrentProgramme §4 — the exact `q`/`r` structural partition

`BALANCED7-QPACKET-STRUCTURAL-PARTITION45` — `PASS` (finite, kernel-checked).

For a positive cutoff `U` and a factorisation `q · r = N` the three sectors are the *exact*
predicates

```
    SmallQ :  q ≤ U
    SmallR :  q > U  and  r ≤ U
    Hard   :  q > U  and  r > U
```

Banked here: cover, pairwise disjointness, unique sharp ownership (as an `∃!` statement on
the factorisation set), agreement with the V24 `sectorOf` classifier, exact reassembly of an
arbitrary summand, and the sharpness facts

* the hard cell is empty unless `U^2 < N`;
* the SmallR cell is empty when `U^2 ≥ N` is *not* what is used — the exact criterion is
  recorded instead.

The hard smooth-dyadic partition of unity stays in the separate V24 layer; it is *not*
merged into this exact partition.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Erdos287
namespace CurrentProgramme

open Erdos287.V24FullQ

/-! ## §4.1  The exact predicates -/

/-- `SmallQ` : `q ≤ U`. -/
def IsSmallQ (U : ℕ) (x : ℕ × ℕ) : Prop := x.1 ≤ U

/-- `SmallR` : `q > U` and `r ≤ U`. -/
def IsSmallR (U : ℕ) (x : ℕ × ℕ) : Prop := U < x.1 ∧ x.2 ≤ U

/-- `Hard` : `q > U` and `r > U`. -/
def IsHard (U : ℕ) (x : ℕ × ℕ) : Prop := U < x.1 ∧ U < x.2

/-- **`qr_exact_cover`.**  `LEAN_PROVED`.  Every factorisation lies in one of the sectors. -/
theorem qr_exact_cover (U : ℕ) (x : ℕ × ℕ) : IsSmallQ U x ∨ IsSmallR U x ∨ IsHard U x := by
  unfold IsSmallQ IsSmallR IsHard
  by_cases h1 : x.1 ≤ U
  · exact Or.inl h1
  · by_cases h2 : x.2 ≤ U
    · exact Or.inr (Or.inl ⟨Nat.lt_of_not_le h1, h2⟩)
    · exact Or.inr (Or.inr ⟨Nat.lt_of_not_le h1, Nat.lt_of_not_le h2⟩)

/-- **`qr_exact_pairwise_disjoint`.**  `LEAN_PROVED`.  The three predicates are pairwise
mutually exclusive. -/
theorem qr_exact_pairwise_disjoint (U : ℕ) (x : ℕ × ℕ) :
    ¬ (IsSmallQ U x ∧ IsSmallR U x) ∧ ¬ (IsSmallQ U x ∧ IsHard U x) ∧
      ¬ (IsSmallR U x ∧ IsHard U x) := by
  unfold IsSmallQ IsSmallR IsHard
  refine ⟨?_, ?_, ?_⟩ <;> rintro ⟨h1, h2⟩ <;> omega

/-- **`qr_exact_unique_sector`.**  `LEAN_PROVED`.

Sharp ownership at the level of the predicates: exactly one of the three holds. -/
theorem qr_exact_unique_sector (U : ℕ) (x : ℕ × ℕ) :
    (IsSmallQ U x ∧ ¬ IsSmallR U x ∧ ¬ IsHard U x) ∨
      (¬ IsSmallQ U x ∧ IsSmallR U x ∧ ¬ IsHard U x) ∨
      (¬ IsSmallQ U x ∧ ¬ IsSmallR U x ∧ IsHard U x) := by
  unfold IsSmallQ IsSmallR IsHard
  by_cases h1 : x.1 ≤ U
  · exact Or.inl ⟨h1, by omega, by omega⟩
  · by_cases h2 : x.2 ≤ U
    · exact Or.inr (Or.inl ⟨h1, ⟨by omega, h2⟩, by omega⟩)
    · exact Or.inr (Or.inr ⟨h1, by omega, ⟨by omega, by omega⟩⟩)

/-! ## §4.2  Agreement with the V24 classifier -/

theorem sectorOf_eq_smallQ_iff (U : ℕ) (x : ℕ × ℕ) :
    sectorOf U x = QSector.smallQ ↔ IsSmallQ U x := by
  unfold sectorOf IsSmallQ
  by_cases h1 : x.1 ≤ U <;> by_cases h2 : x.2 ≤ U <;> simp [h1, h2]

theorem sectorOf_eq_smallR_iff (U : ℕ) (x : ℕ × ℕ) :
    sectorOf U x = QSector.smallR ↔ IsSmallR U x := by
  unfold sectorOf IsSmallR
  by_cases h1 : x.1 ≤ U <;> by_cases h2 : x.2 ≤ U <;> (simp [h1, h2]; try omega)

theorem sectorOf_eq_hard_iff (U : ℕ) (x : ℕ × ℕ) :
    sectorOf U x = QSector.hard ↔ IsHard U x := by
  unfold sectorOf IsHard
  by_cases h1 : x.1 ≤ U <;> by_cases h2 : x.2 ≤ U <;> (simp [h1, h2]; try omega)

/-! ## §4.3  Unique sharp ownership on the factorisation set -/

/-- **`qr_unique_sharp_ownership`.**  `LEAN_PROVED`.

Every factorisation `q · r = N` belongs to exactly one sector cell. -/
theorem qr_unique_sharp_ownership (U N : ℕ) {x : ℕ × ℕ}
    (hx : x ∈ Nat.divisorsAntidiagonal N) :
    ∃! S : QSector, x ∈ sectorCell U N S := by
  refine ⟨sectorOf U x, ?_, ?_⟩
  · exact mem_sectorCell.2 ⟨hx, rfl⟩
  · intro S hS
    exact (mem_sectorCell.1 hS).2.symm

/-- **`qr_cells_cover_factorisations`.**  `LEAN_PROVED`. -/
theorem qr_cells_cover_factorisations (U N : ℕ) :
    sectorCell U N QSector.smallQ ∪ sectorCell U N QSector.smallR ∪
      sectorCell U N QSector.hard = Nat.divisorsAntidiagonal N :=
  balancedSeven_qr_threeWay_cover U N

/-- **`qr_cells_pairwise_disjoint`.**  `LEAN_PROVED`. -/
theorem qr_cells_pairwise_disjoint (U N : ℕ) {S T : QSector} (hST : S ≠ T) :
    Disjoint (sectorCell U N S) (sectorCell U N T) :=
  balancedSeven_qr_threeWay_disjoint U N hST

/-- **`qr_exact_reassembly`.**  `LEAN_PROVED`.

Any summand over the factorisation set reassembles exactly from the three cells. -/
theorem qr_exact_reassembly (U N : ℕ) (f : ℕ × ℕ → ℝ) :
    ∑ x ∈ Nat.divisorsAntidiagonal N, f x =
      (∑ x ∈ sectorCell U N QSector.smallQ, f x) +
        (∑ x ∈ sectorCell U N QSector.smallR, f x) +
        (∑ x ∈ sectorCell U N QSector.hard, f x) :=
  sum_threeWay_sector U N f

/-- **`qr_cardinality_reassembly`.**  `LEAN_PROVED`.  The same statement for counts. -/
theorem qr_cardinality_reassembly (U N : ℕ) :
    (Nat.divisorsAntidiagonal N).card =
      (sectorCell U N QSector.smallQ).card + (sectorCell U N QSector.smallR).card +
        (sectorCell U N QSector.hard).card := by
  have h := qr_exact_reassembly U N (fun _ => (1 : ℝ))
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at h
  exact_mod_cast h

/-! ## §4.4  Sharpness of the cutoff -/

/-- **`hard_cell_forces_U_sq_lt_N`.**  `LEAN_PROVED`.

The hard cell is empty unless `U² < N`: a hard factorisation has `q > U` and `r > U`. -/
theorem hard_cell_forces_U_sq_lt_N {U N : ℕ} {x : ℕ × ℕ}
    (hx : x ∈ sectorCell U N QSector.hard) : U * U < N := by
  obtain ⟨hmem, hsec⟩ := mem_sectorCell.1 hx
  obtain ⟨h1, h2⟩ := (sectorOf_eq_hard_iff U x).1 hsec
  obtain ⟨hprod, _⟩ := Nat.mem_divisorsAntidiagonal.1 hmem
  calc U * U < x.1 * x.2 := by
        exact Nat.mul_lt_mul_of_lt_of_lt h1 h2
    _ = N := hprod

/-- **`hard_cell_empty_of_N_le_U_sq`.**  `LEAN_PROVED`. -/
theorem hard_cell_empty_of_N_le_U_sq {U N : ℕ} (h : N ≤ U * U) :
    sectorCell U N QSector.hard = ∅ := by
  refine Finset.eq_empty_of_forall_notMem ?_
  intro x hx
  exact absurd (hard_cell_forces_U_sq_lt_N hx) (by omega)

/-- **`smallQ_smallR_are_not_interchangeable`.**  `LEAN_PROVED`.

The `q ↔ r` switch is not a symmetry of the exact partition: the pair `(1, 4)` is SmallQ for
`U = 1` while its transpose `(4, 1)` is SmallR. -/
theorem smallQ_smallR_are_not_interchangeable :
    IsSmallQ 1 (1, 4) ∧ IsSmallR 1 (4, 1) ∧ ¬ IsSmallQ 1 (4, 1) := by
  refine ⟨by norm_num [IsSmallQ], ⟨by norm_num [IsSmallR], by norm_num [IsSmallR]⟩, ?_⟩
  · simp [IsSmallQ]

end CurrentProgramme
end Erdos287
