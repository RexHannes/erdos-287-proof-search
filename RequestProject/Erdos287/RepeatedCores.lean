import Mathlib
import RequestProject.Erdos287.BernoulliKernel

/-!
# Erdős #287 — repeated-core partition and the no-double-counting ledger

```
CORE TAGS (abstract)                : DEFINED   (CoreTag)
LATTICE / NO-LATTICE SPLIT          : KERNEL-PROVED
TAG PARTITION (sf / p² / p³)        : KERNEL-PROVED
LEDGER DISJOINTNESS                 : KERNEL-PROVED (repeated_core_ledger_disjoint)
LEDGER EXHAUSTIVENESS (no double count) : KERNEL-PROVED (repeated_core_ledger_total)
```

The classification of the repeated cores as `r = 1`, `r = p²`, `r = p³` is **not** reproved
here: the three classes are carried abstractly as the three constructors of `CoreTag`.
What *is* proved is the bookkeeping the floor ledger consumes:

* every row is either lattice-bearing or no-lattice, exclusively;
* the global no-lattice charge, the repeated lattice charge and the squarefree lattice
  charge are indexed by **pairwise disjoint** row sets whose union is the whole row set;
* hence the total charge is their sum — no row is counted twice, and none is dropped.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open Finset

namespace Erdos287
namespace RepeatedCores

/-- The three repeated-core tags, carried abstractly. -/
inductive CoreTag where
  | squarefreeCore : CoreTag
  | p2Core : CoreTag
  | p3Core : CoreTag
  deriving DecidableEq, Repr

open BernoulliKernel

variable {ι : Type*}

/-- A row is *lattice-bearing* when the no-lattice condition `k > (9/10)X/z` fails. -/
def latticeBearing (X : ℝ) (z k : ι → ℝ) (i : ι) : Prop := latticeExists X (z i) (k i)

theorem latticeBearing_iff_not_noLattice (X : ℝ) (z k : ι → ℝ) (i : ι) :
    latticeBearing X z k i ↔ ¬ noLattice X (z i) (k i) := Iff.rfl

/-- Exclusivity: a row is never simultaneously lattice-bearing and no-lattice. -/
theorem not_latticeBearing_and_noLattice (X : ℝ) (z k : ι → ℝ) (i : ι) :
    ¬ (latticeBearing X z k i ∧ noLattice X (z i) (k i)) := fun h => h.1 h.2

/-- Exhaustiveness: every row is lattice-bearing or no-lattice. -/
theorem latticeBearing_or_noLattice (X : ℝ) (z k : ι → ℝ) (i : ι) :
    latticeBearing X z k i ∨ noLattice X (z i) (k i) :=
  (noLattice_or_latticeExists X (z i) (k i)).symm

open scoped Classical in
/-- Rows charged to the **global no-lattice** consumer. -/
noncomputable def globalNoLatticeRows (rows : Finset ι) (X : ℝ) (z k : ι → ℝ) : Finset ι :=
  rows.filter (fun i => ¬ latticeBearing X z k i)

open scoped Classical in
/-- Rows charged to the **repeated lattice** consumer (`p²` and `p³` cores only). -/
noncomputable def repeatedLatticeRows (rows : Finset ι) (tag : ι → CoreTag) (X : ℝ)
    (z k : ι → ℝ) : Finset ι :=
  rows.filter (fun i => tag i ≠ CoreTag.squarefreeCore ∧ latticeBearing X z k i)

open scoped Classical in
/-- Rows charged to the **squarefree lattice** consumer (the open medium-`k` node). -/
noncomputable def squarefreeLatticeRows (rows : Finset ι) (tag : ι → CoreTag) (X : ℝ)
    (z k : ι → ℝ) : Finset ι :=
  rows.filter (fun i => tag i = CoreTag.squarefreeCore ∧ latticeBearing X z k i)

open scoped Classical in
/-- The `p²` part of the repeated lattice charge. -/
noncomputable def p2LatticeRows (rows : Finset ι) (tag : ι → CoreTag) (X : ℝ)
    (z k : ι → ℝ) : Finset ι :=
  rows.filter (fun i => tag i = CoreTag.p2Core ∧ latticeBearing X z k i)

open scoped Classical in
/-- The `p³` part of the repeated lattice charge. -/
noncomputable def p3LatticeRows (rows : Finset ι) (tag : ι → CoreTag) (X : ℝ)
    (z k : ι → ℝ) : Finset ι :=
  rows.filter (fun i => tag i = CoreTag.p3Core ∧ latticeBearing X z k i)

/-- **`repeated_core_ledger_disjoint`.** `KERNEL-PROVED`.  The three ledger row sets are
pairwise disjoint: a repeated no-lattice row is charged **only** to the global no-lattice
consumer, and a repeated lattice-bearing row **only** to the repeated-lattice consumer. -/
theorem repeated_core_ledger_disjoint (rows : Finset ι) (tag : ι → CoreTag) (X : ℝ)
    (z k : ι → ℝ) :
    Disjoint (globalNoLatticeRows rows X z k) (repeatedLatticeRows rows tag X z k) ∧
    Disjoint (globalNoLatticeRows rows X z k) (squarefreeLatticeRows rows tag X z k) ∧
    Disjoint (repeatedLatticeRows rows tag X z k) (squarefreeLatticeRows rows tag X z k) := by
  classical
  refine ⟨?_, ?_, ?_⟩ <;>
    rw [Finset.disjoint_left] <;>
    intro i hi hj <;>
    simp only [globalNoLatticeRows, repeatedLatticeRows, squarefreeLatticeRows,
      Finset.mem_filter] at hi hj
  · exact hi.2 hj.2.2
  · exact hi.2 hj.2.2
  · exact hi.2.1 hj.2.1

/-- **`repeated_core_p2_p3_disjoint`.** `KERNEL-PROVED`.  The repeated lattice charge splits
disjointly into its `p²` and `p³` parts. -/
theorem repeated_core_p2_p3_disjoint (rows : Finset ι) (tag : ι → CoreTag) (X : ℝ)
    (z k : ι → ℝ) :
    Disjoint (p2LatticeRows rows tag X z k) (p3LatticeRows rows tag X z k) := by
  classical
  rw [Finset.disjoint_left]
  intro i hi hj
  simp only [p2LatticeRows, p3LatticeRows, Finset.mem_filter] at hi hj
  rw [hi.2.1] at hj
  exact CoreTag.noConfusion hj.2.1

theorem p2LatticeRows_union_p3LatticeRows [DecidableEq ι] (rows : Finset ι)
    (tag : ι → CoreTag) (X : ℝ) (z k : ι → ℝ) :
    p2LatticeRows rows tag X z k ∪ p3LatticeRows rows tag X z k
      = repeatedLatticeRows rows tag X z k := by
  classical
  ext i
  simp only [p2LatticeRows, p3LatticeRows, repeatedLatticeRows, Finset.mem_union,
    Finset.mem_filter]
  constructor
  · rintro (⟨hi, ht, hl⟩ | ⟨hi, ht, hl⟩)
    · exact ⟨hi, by rw [ht]; exact fun h => CoreTag.noConfusion h, hl⟩
    · exact ⟨hi, by rw [ht]; exact fun h => CoreTag.noConfusion h, hl⟩
  · rintro ⟨hi, ht, hl⟩
    cases htag : tag i with
    | squarefreeCore => exact absurd htag ht
    | p2Core => exact Or.inl ⟨hi, rfl, hl⟩
    | p3Core => exact Or.inr ⟨hi, rfl, hl⟩

/-- **`repeated_core_ledger_total`.** `KERNEL-PROVED`.  **No double counting**: the total
charge over all rows is exactly the sum of the three ledger charges. -/
theorem repeated_core_ledger_total (rows : Finset ι) (tag : ι → CoreTag) (X : ℝ)
    (z k : ι → ℝ) (charge : ι → ℝ) :
    ∑ i ∈ rows, charge i
      = (∑ i ∈ globalNoLatticeRows rows X z k, charge i)
        + (∑ i ∈ repeatedLatticeRows rows tag X z k, charge i)
        + (∑ i ∈ squarefreeLatticeRows rows tag X z k, charge i) := by
  classical
  have hsplit :
      ∑ i ∈ rows, charge i
        = (∑ i ∈ rows.filter (fun i => ¬ latticeBearing X z k i), charge i)
          + ∑ i ∈ rows.filter (fun i => latticeBearing X z k i), charge i := by
    rw [add_comm]
    exact (Finset.sum_filter_add_sum_filter_not rows (fun i => latticeBearing X z k i) charge).symm
  have hlat :
      ∑ i ∈ rows.filter (fun i => latticeBearing X z k i), charge i
        = (∑ i ∈ repeatedLatticeRows rows tag X z k, charge i)
          + ∑ i ∈ squarefreeLatticeRows rows tag X z k, charge i := by
    have h := (Finset.sum_filter_add_sum_filter_not
      (rows.filter (fun i => latticeBearing X z k i))
      (fun i => tag i ≠ CoreTag.squarefreeCore) charge).symm
    rw [h]
    congr 1
    · apply Finset.sum_congr _ (fun _ _ => rfl)
      ext i
      simp only [repeatedLatticeRows, Finset.mem_filter]
      tauto
    · apply Finset.sum_congr _ (fun _ _ => rfl)
      ext i
      simp only [squarefreeLatticeRows, Finset.mem_filter, not_not]
      tauto
  rw [hsplit, hlat, globalNoLatticeRows, add_assoc]

/-- **`repeated_noLattice_only_global`.** `KERNEL-PROVED`.  A repeated (`p²` or `p³`) row in
the no-lattice region contributes to the global no-lattice charge and to **neither** of the
lattice charges. -/
theorem repeated_noLattice_only_global (rows : Finset ι) (tag : ι → CoreTag) (X : ℝ)
    (z k : ι → ℝ) {i : ι} (hi : i ∈ rows) (hnl : noLattice X (z i) (k i)) :
    i ∈ globalNoLatticeRows rows X z k ∧
      i ∉ repeatedLatticeRows rows tag X z k ∧
      i ∉ squarefreeLatticeRows rows tag X z k := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · simp only [globalNoLatticeRows, Finset.mem_filter]
    exact ⟨hi, fun h => h hnl⟩
  · intro hmem
    simp only [repeatedLatticeRows, Finset.mem_filter] at hmem
    exact hmem.2.2 hnl
  · intro hmem
    simp only [squarefreeLatticeRows, Finset.mem_filter] at hmem
    exact hmem.2.2 hnl

end RepeatedCores
end Erdos287
