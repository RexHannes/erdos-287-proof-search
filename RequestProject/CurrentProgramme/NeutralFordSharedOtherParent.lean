import RequestProject.CurrentProgramme.Run1BConditionalCompiler

/-!
# The project-neutral shared Ford other-parent layer (§10) and the two adapters (§11)

```
neutral other-parent source object                     : DEFINED
ultra-near-half covariance input                       : OPEN EXTERNAL (uninhabited here)
two source subclasses (cross-block / same-block)       : KERNEL-PROVED exhaustive
shared OTHER conclusion from ultra + RUN1B landing     : CONDITIONAL KERNEL-PROVED
TwinOtherParentAdapter / Erdos287HardUAdapter          : mutually independent, KERNEL-PROVED
Erdos287HardUSharedFordAdapterInput (source equality)  : UNINHABITED, name-agreement firewall
```

This namespace is **project-neutral**: it names neither downstream programme's conclusion, and
neither adapter may import the other's downstream object.  Nothing here claims the twin-prime
conjecture or Erdős #287, and the ultra-near-half covariance statement is an open external
input, never proved.

This module is **append-only**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace SharedFord

open Run1B.Source Run1B.Compiler

/-! ## §10.1  The neutral other-parent source object -/

/-- A project-neutral other-parent source: two coefficient sequences on a finite support,
plus a purely descriptive label. -/
structure OtherParentSource where
  /-- The main parameter. -/
  X : ℕ
  /-- The finite support. -/
  support : Finset ℕ
  /-- The first coefficient sequence. -/
  first : ℕ → ℂ
  /-- The second coefficient sequence. -/
  second : ℕ → ℂ
  /-- A descriptive label.  Carries no mathematical content. -/
  label : String

/-- The covariance functional of an other-parent source. -/
noncomputable def covariance (src : OtherParentSource) : ℂ :=
  ∑ n ∈ src.support, src.first n * (starRingEnd ℂ) (src.second n)

/-- The two source subclasses of the ultra-near-half residual. -/
inductive UltraSourceSubclass
  /-- A. cross-block prime pair. -/
  | crossBlockPrimePair
  /-- B. selected-`E`-cut same-block prime pair. -/
  | sameBlockPrimePair
  deriving DecidableEq, Fintype, Repr

/-- **`ultraSourceSubclass_exhaustive`.**  `KERNEL-PROVED`.  Exactly two subclasses. -/
theorem ultraSourceSubclass_exhaustive (c : UltraSourceSubclass) :
    c = UltraSourceSubclass.crossBlockPrimePair ∨ c = UltraSourceSubclass.sameBlockPrimePair := by
  cases c <;> simp

/-- **`ultraSourceSubclass_card`.**  `KERNEL-PROVED`. -/
theorem ultraSourceSubclass_card : (Finset.univ : Finset UltraSourceSubclass).card = 2 := by
  decide

/-! ## §10.2  The open external ultra-near-half covariance input -/

/-- **`UltraNearHalfCovarianceInput`** — `OPEN EXTERNAL`.

The literal ultra-near-half covariance bound for a neutral other-parent source.  It is not
proved anywhere in this repository and is not an axiom: it is an explicit hypothesis. -/
structure UltraNearHalfCovarianceInput (src : OtherParentSource) (bound : ℝ) : Prop where
  /-- The covariance bound. -/
  covarianceBound : ‖covariance src‖ ≤ bound

/-- **`ultraInput_is_a_genuine_constraint`.**  `KERNEL-PROVED` counterguard: the open input is
not a `True`-like proposition. -/
theorem ultraInput_is_a_genuine_constraint (src : OtherParentSource) :
    ¬ UltraNearHalfCovarianceInput src (-1) := by
  intro h
  exact absurd h.covarianceBound
    (not_le.mpr (lt_of_lt_of_le (by norm_num : (-1 : ℝ) < 0) (norm_nonneg _)))

/-! ## §10.3  The shared other-parent conclusion, conditional on ultra + RUN1B -/

/-- The shared other-parent conclusion: the joint bound for the covariance together with the
RUN1B `d·w'` landing of the same configuration. -/
def SharedOtherParentConclusion (src : OtherParentSource) (s : DwpSource)
    (bound b l : ℝ) : Prop :=
  ‖covariance src + s.dwpSum‖ ≤ bound + (b + l)

/-- **`sharedOtherParent_conditional`.**  `CONDITIONAL KERNEL-PROVED`.

```
ultra-near-half covariance (OPEN EXTERNAL)  +  RUN1B conclusion (conditional)
      →  shared other-parent conclusion.
```

Both antecedents remain visible; nothing is claimed unconditionally. -/
theorem sharedOtherParent_conditional {ι : Type} (src : OtherParentSource)
    (sources : ι → DwpSource) (i : ι) (bound b l : ℝ)
    (ultra : UltraNearHalfCovarianceInput src bound)
    (run1b : Run1BConclusion sources b l) :
    SharedOtherParentConclusion src (sources i) bound b l := by
  refine le_trans (norm_add_le _ _) ?_
  have h1 := ultra.covarianceBound
  have h2 := run1b i
  linarith

/-! ## §11  The two mutually independent adapters -/

/-- **A. `TwinOtherParentAdapter`.**  Consumes only the neutral shared theorem; parametric in
the downstream twin-side conclusion, which is never inhabited here. -/
def TwinOtherParentAdapter (twinConclusion : Prop) (src : OtherParentSource) (s : DwpSource)
    (bound b l : ℝ) : Prop :=
  SharedOtherParentConclusion src s bound b l → twinConclusion

/-- **B. `Erdos287HardUAdapter`.**  Consumes only the neutral shared theorem; parametric in
the downstream #287-side conclusion, which is never inhabited here. -/
def Erdos287HardUAdapter (erdosConclusion : Prop) (src : OtherParentSource) (s : DwpSource)
    (bound b l : ℝ) : Prop :=
  SharedOtherParentConclusion src s bound b l → erdosConclusion

/-- **`adapters_are_independent`.**  `KERNEL-PROVED`.  Each adapter is exactly the implication
from the neutral shared theorem to its own downstream conclusion, uniformly in the other
project's conclusion: neither adapter can consume the other's downstream object. -/
theorem adapters_are_independent (src : OtherParentSource) (s : DwpSource) (bound b l : ℝ) :
    (∀ twinConclusion : Prop,
        TwinOtherParentAdapter twinConclusion src s bound b l
          ↔ (SharedOtherParentConclusion src s bound b l → twinConclusion)) ∧
      (∀ erdosConclusion : Prop,
        Erdos287HardUAdapter erdosConclusion src s bound b l
          ↔ (SharedOtherParentConclusion src s bound b l → erdosConclusion)) :=
  ⟨fun _ => Iff.rfl, fun _ => Iff.rfl⟩

/-- **`adapters_do_not_inhabit_each_other`.**  `KERNEL-PROVED`.  Holding one adapter at a
false downstream conclusion does not inhabit the other's downstream conclusion. -/
theorem adapters_do_not_inhabit_each_other (src : OtherParentSource) (s : DwpSource)
    (bound b l : ℝ) (twinConclusion : Prop) :
    TwinOtherParentAdapter twinConclusion src s bound b l →
      ¬ (Erdos287HardUAdapter False src s bound b l ∧
          SharedOtherParentConclusion src s bound b l) := by
  rintro _ ⟨hE, hS⟩
  exact hE hS

/-! ## §8 (of the #287 frontier)  The hard-`U` shared-Ford adapter input -/

/-- **`Erdos287HardUSharedFordAdapterInput`** — the adapter obligation is **source equality
only**: the hard `U`-lane generated packets must literally be the neutral shared Ford
other-parent source.  It is not inhabited here. -/
structure Erdos287HardUSharedFordAdapterInput (hardU neutral : OtherParentSource) : Prop where
  /-- Literal equality of source objects. -/
  source_equality : hardU = neutral

/-- **`hardU_adapter_transport`.**  `CONDITIONAL KERNEL-PROVED`.  With the source-equality
obligation discharged, the neutral shared conclusion transports to the hard-`U` source. -/
theorem hardU_adapter_transport {hardU neutral : OtherParentSource} {s : DwpSource}
    {bound b l : ℝ} (adapter : Erdos287HardUSharedFordAdapterInput hardU neutral)
    (h : SharedOtherParentConclusion neutral s bound b l) :
    SharedOtherParentConclusion hardU s bound b l := by
  rw [adapter.source_equality]
  exact h

/-- **`hardU_adapter_not_from_name_agreement`.**  `KERNEL-PROVED` firewall.

Agreement of the descriptive labels does **not** discharge the adapter obligation: two
sources may carry the same label and still differ.  Hence the adapter may never be inhabited
from theorem-name agreement. -/
theorem hardU_adapter_not_from_name_agreement :
    ∃ hardU neutral : OtherParentSource,
      hardU.label = neutral.label ∧ ¬ Erdos287HardUSharedFordAdapterInput hardU neutral := by
  refine ⟨⟨1, ∅, fun _ => 0, fun _ => 0, "ford722"⟩,
    ⟨2, ∅, fun _ => 0, fun _ => 0, "ford722"⟩, rfl, ?_⟩
  intro h
  have := congrArg OtherParentSource.X h.source_equality
  simp at this

/-- **`hardU_adapter_uninhabited_in_general`.**  `KERNEL-PROVED`.  The obligation is a genuine
constraint: it does not hold for arbitrary pairs of sources. -/
theorem hardU_adapter_uninhabited_in_general :
    ¬ ∀ hardU neutral : OtherParentSource, Erdos287HardUSharedFordAdapterInput hardU neutral := by
  intro h
  have hEq := (h ⟨1, ∅, fun _ => 0, fun _ => 0, "a"⟩ ⟨2, ∅, fun _ => 0, fun _ => 0, "a"⟩).source_equality
  have := congrArg OtherParentSource.X hEq
  simp at this

end SharedFord
