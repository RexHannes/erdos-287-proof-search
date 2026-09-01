import RequestProject.CurrentProgramme.Erdos287K0SP2SourceObject

/-!
# The exhaustive four-way K0-SP2 source partition

`K0-SP2 FOUR-CLASS PARTITION : KERNEL-PROVED (finite combinatorics)`

This module is **append-only**.

The audited source set `S_X` of `Erdos287K0SP2SourceObject` is cut into four
sectors:

```
A  repeated Balanced7          (seven-prime rows carrying a repetition);
B  other large prime power     (a prime power p^v ≥ L with v ≥ 2, not in A);
C  distinct Balanced7          (squarefree seven-prime rows, not in A ∪ B);
R  regular complement          (everything else, by exact set difference).
```

The owners are applied in this **fixed priority order**, and `R` is defined by
`R = S_X \ (A ∪ B ∪ C)`, so exhaustiveness is a finite-set theorem and no row
can have two owners.

`k0SP2_fourClass_partition_exact` bundles: pairwise disjointness, the union
identity, and the "no row has two owners" statement.

**Firewall.**  Nothing analytic is claimed here.  The statements that the `A`
and `B` sectors are *fixed-power negligible*, and that `C` is owned by the
banked full-`q` physical theorem, are **paper/external analytic inputs**; they
are not encoded as theorems in this module.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open Finset

namespace Erdos287
namespace K0SP2Source

/-! ## §1.  The four owner predicates -/

/-- **Balanced7 shape**: exactly seven distinct prime divisors. -/
def Balanced7Shape (n : ℕ) : Prop := n.primeFactors.card = 7

instance (n : ℕ) : Decidable (Balanced7Shape n) := by unfold Balanced7Shape; infer_instance

/-- **Repeated Balanced7**: a Balanced7 row whose seven-prime vector carries a
repetition, i.e. the row is not squarefree. -/
def RepeatedBalanced7 (n : ℕ) : Prop := Balanced7Shape n ∧ ¬ Squarefree n

instance (n : ℕ) : Decidable (RepeatedBalanced7 n) := by
  unfold RepeatedBalanced7; infer_instance

/-- **Large prime power row at cutoff `L`**: some prime `p ∣ n` occurs to an exponent
`v ≥ 2` with `p^v ≥ L`. -/
def LargePrimePowerRow (L n : ℕ) : Prop :=
  ∃ p ∈ n.primeFactors, 2 ≤ n.factorization p ∧ L ≤ p ^ (n.factorization p)

instance (L n : ℕ) : Decidable (LargePrimePowerRow L n) := by
  unfold LargePrimePowerRow; infer_instance

/-- **Distinct (direct) Balanced7**: a squarefree Balanced7 row. -/
def DistinctBalanced7 (n : ℕ) : Prop := Balanced7Shape n ∧ Squarefree n

instance (n : ℕ) : Decidable (DistinctBalanced7 n) := by
  unfold DistinctBalanced7; infer_instance

/-- Repeated and distinct Balanced7 are mutually exclusive already at the level of
predicates (squarefree versus not squarefree). -/
theorem repeated_distinct_exclusive (n : ℕ) :
    ¬ (RepeatedBalanced7 n ∧ DistinctBalanced7 n) := by
  rintro ⟨⟨-, h1⟩, ⟨-, h2⟩⟩
  exact h1 h2

/-! ## §2.  The four sectors, with a fixed owner priority -/

namespace K0SP2Params

variable (P : K0SP2Params) (L : ℕ)

/-- Sector `A` — repeated Balanced7 rows. -/
def classRepeatedB7 : Finset ℕ := P.sourceSet.filter (fun n => RepeatedBalanced7 n)

/-- Sector `B` — other large prime-power rows (priority: after `A`). -/
def classLargePP : Finset ℕ :=
  P.sourceSet.filter (fun n => ¬ RepeatedBalanced7 n ∧ LargePrimePowerRow L n)

/-- Sector `C` — direct, distinct Balanced7 rows (priority: after `A` and `B`). -/
def classDistinctB7 : Finset ℕ :=
  P.sourceSet.filter
    (fun n => ¬ RepeatedBalanced7 n ∧ ¬ LargePrimePowerRow L n ∧ DistinctBalanced7 n)

/-- Sector `R` — the **regular complement**, by exact set difference. -/
def classRegular : Finset ℕ :=
  P.sourceSet \ (P.classRepeatedB7 ∪ P.classLargePP L ∪ P.classDistinctB7 L)

@[simp] theorem mem_classRepeatedB7 {n : ℕ} :
    n ∈ P.classRepeatedB7 ↔ n ∈ P.sourceSet ∧ RepeatedBalanced7 n := by
  simp [classRepeatedB7]

@[simp] theorem mem_classLargePP {n : ℕ} :
    n ∈ P.classLargePP L ↔
      n ∈ P.sourceSet ∧ ¬ RepeatedBalanced7 n ∧ LargePrimePowerRow L n := by
  simp [classLargePP, and_assoc]

@[simp] theorem mem_classDistinctB7 {n : ℕ} :
    n ∈ P.classDistinctB7 L ↔
      n ∈ P.sourceSet ∧ ¬ RepeatedBalanced7 n ∧ ¬ LargePrimePowerRow L n ∧
        DistinctBalanced7 n := by
  simp [classDistinctB7, and_assoc]

@[simp] theorem mem_classRegular {n : ℕ} :
    n ∈ P.classRegular L ↔
      n ∈ P.sourceSet ∧ ¬ RepeatedBalanced7 n ∧ ¬ LargePrimePowerRow L n ∧
        ¬ DistinctBalanced7 n := by
  simp only [classRegular, Finset.mem_sdiff, Finset.mem_union, mem_classRepeatedB7,
    mem_classLargePP, mem_classDistinctB7]
  constructor
  · rintro ⟨hs, hno⟩
    have h1 : ¬ RepeatedBalanced7 n := fun h => hno (Or.inl (Or.inl ⟨hs, h⟩))
    have h2 : ¬ LargePrimePowerRow L n := fun h => hno (Or.inl (Or.inr ⟨hs, h1, h⟩))
    exact ⟨hs, h1, h2, fun h => hno (Or.inr ⟨hs, h1, h2, h⟩)⟩
  · rintro ⟨hs, h1, h2, h3⟩
    refine ⟨hs, ?_⟩
    rintro (((⟨-, h⟩) | ⟨-, -, h⟩) | ⟨-, -, -, h⟩)
    · exact h1 h
    · exact h2 h
    · exact h3 h

/-! ## §3.  Exhaustive disjoint partition -/

theorem disjoint_A_B : Disjoint P.classRepeatedB7 (P.classLargePP L) := by
  rw [Finset.disjoint_left]
  intro n hA hB
  rw [mem_classRepeatedB7] at hA
  rw [mem_classLargePP] at hB
  exact hB.2.1 hA.2

theorem disjoint_A_C : Disjoint P.classRepeatedB7 (P.classDistinctB7 L) := by
  rw [Finset.disjoint_left]
  intro n hA hC
  rw [mem_classRepeatedB7] at hA
  rw [mem_classDistinctB7] at hC
  exact hC.2.1 hA.2

theorem disjoint_A_R : Disjoint P.classRepeatedB7 (P.classRegular L) := by
  rw [Finset.disjoint_left]
  intro n hA hR
  rw [mem_classRepeatedB7] at hA
  rw [mem_classRegular] at hR
  exact hR.2.1 hA.2

theorem disjoint_B_C : Disjoint (P.classLargePP L) (P.classDistinctB7 L) := by
  rw [Finset.disjoint_left]
  intro n hB hC
  rw [mem_classLargePP] at hB
  rw [mem_classDistinctB7] at hC
  exact hC.2.2.1 hB.2.2

theorem disjoint_B_R : Disjoint (P.classLargePP L) (P.classRegular L) := by
  rw [Finset.disjoint_left]
  intro n hB hR
  rw [mem_classLargePP] at hB
  rw [mem_classRegular] at hR
  exact hR.2.2.1 hB.2.2

theorem disjoint_C_R : Disjoint (P.classDistinctB7 L) (P.classRegular L) := by
  rw [Finset.disjoint_left]
  intro n hC hR
  rw [mem_classDistinctB7] at hC
  rw [mem_classRegular] at hR
  exact hR.2.2.2 hC.2.2.2

/-- The four sectors exhaust the audited source. -/
theorem fourClass_union :
    P.classRepeatedB7 ∪ P.classLargePP L ∪ P.classDistinctB7 L ∪ P.classRegular L
      = P.sourceSet := by
  ext n
  simp only [Finset.mem_union, mem_classRepeatedB7, mem_classLargePP, mem_classDistinctB7,
    mem_classRegular]
  constructor
  · rintro ((((⟨h, -⟩) | ⟨h, -⟩) | ⟨h, -⟩) | ⟨h, -⟩) <;> exact h
  · intro hs
    by_cases h1 : RepeatedBalanced7 n
    · exact Or.inl (Or.inl (Or.inl ⟨hs, h1⟩))
    by_cases h2 : LargePrimePowerRow L n
    · exact Or.inl (Or.inl (Or.inr ⟨hs, h1, h2⟩))
    by_cases h3 : DistinctBalanced7 n
    · exact Or.inl (Or.inr ⟨hs, h1, h2, h3⟩)
    · exact Or.inr ⟨hs, h1, h2, h3⟩

/-- No source row has two owners. -/
theorem no_row_two_owners {n : ℕ} :
    ¬ ((n ∈ P.classRepeatedB7 ∧ n ∈ P.classLargePP L) ∨
       (n ∈ P.classRepeatedB7 ∧ n ∈ P.classDistinctB7 L) ∨
       (n ∈ P.classRepeatedB7 ∧ n ∈ P.classRegular L) ∨
       (n ∈ P.classLargePP L ∧ n ∈ P.classDistinctB7 L) ∨
       (n ∈ P.classLargePP L ∧ n ∈ P.classRegular L) ∨
       (n ∈ P.classDistinctB7 L ∧ n ∈ P.classRegular L)) := by
  rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩)
  · exact (Finset.disjoint_left.1 (P.disjoint_A_B L)) h1 h2
  · exact (Finset.disjoint_left.1 (P.disjoint_A_C L)) h1 h2
  · exact (Finset.disjoint_left.1 (P.disjoint_A_R L)) h1 h2
  · exact (Finset.disjoint_left.1 (P.disjoint_B_C L)) h1 h2
  · exact (Finset.disjoint_left.1 (P.disjoint_B_R L)) h1 h2
  · exact (Finset.disjoint_left.1 (P.disjoint_C_R L)) h1 h2

end K0SP2Params

/-! ## §4.  The bundled partition theorem -/

/-- **`k0SP2_fourClass_partition_exact`.**  `KERNEL-PROVED`.

The four K0-SP2 owner sectors are pairwise disjoint, exhaust the audited source
set, and no source row belongs to two owners. -/
theorem k0SP2_fourClass_partition_exact (P : K0SP2Params) (L : ℕ) :
    Disjoint P.classRepeatedB7 (P.classLargePP L) ∧
    Disjoint P.classRepeatedB7 (P.classDistinctB7 L) ∧
    Disjoint P.classRepeatedB7 (P.classRegular L) ∧
    Disjoint (P.classLargePP L) (P.classDistinctB7 L) ∧
    Disjoint (P.classLargePP L) (P.classRegular L) ∧
    Disjoint (P.classDistinctB7 L) (P.classRegular L) ∧
    (P.classRepeatedB7 ∪ P.classLargePP L ∪ P.classDistinctB7 L ∪ P.classRegular L
      = P.sourceSet) ∧
    (∀ n : ℕ,
      ¬ ((n ∈ P.classRepeatedB7 ∧ n ∈ P.classLargePP L) ∨
         (n ∈ P.classRepeatedB7 ∧ n ∈ P.classDistinctB7 L) ∨
         (n ∈ P.classRepeatedB7 ∧ n ∈ P.classRegular L) ∨
         (n ∈ P.classLargePP L ∧ n ∈ P.classDistinctB7 L) ∨
         (n ∈ P.classLargePP L ∧ n ∈ P.classRegular L) ∨
         (n ∈ P.classDistinctB7 L ∧ n ∈ P.classRegular L))) :=
  ⟨P.disjoint_A_B L, P.disjoint_A_C L, P.disjoint_A_R L, P.disjoint_B_C L,
    P.disjoint_B_R L, P.disjoint_C_R L, P.fourClass_union L,
    fun _ => P.no_row_two_owners L⟩

/-- **`k0SP2_source_four_sector_reassembly`.**  `KERNEL-PROVED`.

The exact source value is the sum of the four owner sectors — an identity, before any
triangle inequality. -/
theorem k0SP2_source_four_sector_reassembly (P : K0SP2Params) (L : ℕ)
    (W : ℕ → ℂ) (D : Bool → ℕ → ℂ) :
    sourceExpr P W D
      = sectorExpr P W D P.classRepeatedB7 + sectorExpr P W D (P.classLargePP L)
        + sectorExpr P W D (P.classDistinctB7 L) + sectorExpr P W D (P.classRegular L) :=
  sourceExpr_four_sectors P W D (P.disjoint_A_B L) (P.disjoint_A_C L) (P.disjoint_A_R L)
    (P.disjoint_B_C L) (P.disjoint_B_R L) (P.disjoint_C_R L) (P.fourClass_union L)

end K0SP2Source
end Erdos287
