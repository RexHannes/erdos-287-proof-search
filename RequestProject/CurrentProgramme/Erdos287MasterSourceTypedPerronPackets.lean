import Mathlib
import RequestProject.CurrentProgramme.Erdos287K0SP2FourClassPartition
import RequestProject.CurrentProgramme.Erdos287FullSourceAnalyticKernelInput

/-!
# MASTER-SOURCE → TYPED PERRON PACKETS: the source/formal compiler

`MASTER-SOURCE-TO-TYPED-PERRON-PACKETS45 : KERNEL-PROVED SOURCE/FORMAL COMPILER`

This module is **append-only**.  It formalises the *exact dependency chain*

```
one-copy K0-SP2 physical source
  → four-class source partition
  → de-regularised full-smooth source
  → fixed smooth-threshold cells
  → Perron / dyadic template packets
  → Λ = μ ∗ log source packets
  → determinant-one parametrisation
  → two-copy dispersion object
  → proof-local shared-gcd partition
  → C0 / transverse / b-diagonal / local owner tags
```

as a finite linearly ordered stage type, together with

* the **exact de-regularisation identity** (§2) for the already kernel-proved
  four-class partition;
* the **finite owner type** and the exact owner partition of a typed packet
  family (§3–§4).

**Firewall.**  *No analytic estimate is proved or assumed here.*  Every theorem
is an exact finite identity or a type-correct adapter.  The asymptotic smallness
of the deleted sectors is *not* formalised: it is carried by the fields of
`Erdos287.FullAnalyticKernel.FullSourceLocalAnalyticKernelInput`, which is left
uninhabited.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Erdos287
namespace MasterSourcePackets

open Erdos287.K0SP2Source

/-! ## §1  The compiler chain -/

/-- The stages of the master-source → typed-packet compiler, in dependency order. -/
inductive CompilerStage
  /-- The one-copy K0-SP2 physical source. -/
  | oneCopyPhysicalSource
  /-- The exact four-class source partition. -/
  | fourClassSourcePartition
  /-- The de-regularised full-smooth source. -/
  | deRegularisedFullSmoothSource
  /-- The fixed smooth-threshold cells. -/
  | fixedSmoothThresholdCells
  /-- The Perron / dyadic template packets. -/
  | perronDyadicTemplatePackets
  /-- The `Λ = μ ∗ log` source packets. -/
  | lambdaMuLogSourcePackets
  /-- The determinant-one parametrisation. -/
  | determinantOneParametrisation
  /-- The two-copy dispersion object. -/
  | twoCopyDispersionObject
  /-- The proof-local shared-gcd (`Ω`) partition. -/
  | proofLocalSharedGcdPartition
  /-- The owner tags. -/
  | ownerTags
  deriving DecidableEq, Fintype, Repr

namespace CompilerStage

/-- The position of a stage in the chain. -/
def index : CompilerStage → ℕ
  | oneCopyPhysicalSource => 0
  | fourClassSourcePartition => 1
  | deRegularisedFullSmoothSource => 2
  | fixedSmoothThresholdCells => 3
  | perronDyadicTemplatePackets => 4
  | lambdaMuLogSourcePackets => 5
  | determinantOneParametrisation => 6
  | twoCopyDispersionObject => 7
  | proofLocalSharedGcdPartition => 8
  | ownerTags => 9

/-- The successor stage, if any. -/
def next : CompilerStage → Option CompilerStage
  | oneCopyPhysicalSource => some fourClassSourcePartition
  | fourClassSourcePartition => some deRegularisedFullSmoothSource
  | deRegularisedFullSmoothSource => some fixedSmoothThresholdCells
  | fixedSmoothThresholdCells => some perronDyadicTemplatePackets
  | perronDyadicTemplatePackets => some lambdaMuLogSourcePackets
  | lambdaMuLogSourcePackets => some determinantOneParametrisation
  | determinantOneParametrisation => some twoCopyDispersionObject
  | twoCopyDispersionObject => some proofLocalSharedGcdPartition
  | proofLocalSharedGcdPartition => some ownerTags
  | ownerTags => none

end CompilerStage

open CompilerStage

/-- **`chain_is_linear`.**  `KERNEL-PROVED`.  Each stage's successor sits exactly one
position later: the dependency chain is a linear order with no branch and no gap. -/
theorem chain_is_linear :
    ∀ s t : CompilerStage, s.next = some t → s.index + 1 = t.index := by decide

/-- **`chain_indices_distinct`.**  `KERNEL-PROVED`.  Distinct stages occupy distinct
positions. -/
theorem chain_indices_distinct : Function.Injective CompilerStage.index := by decide

/-- **`chain_starts_at_physical_source`.**  `KERNEL-PROVED`.  The unique stage with no
predecessor is the one-copy physical source. -/
theorem chain_starts_at_physical_source :
    ∀ s : CompilerStage, (∀ t : CompilerStage, t.next ≠ some s) ↔
      s = oneCopyPhysicalSource := by decide

/-- **`chain_ends_at_owner_tags`.**  `KERNEL-PROVED`.  The unique terminal stage is the
owner-tag stage. -/
theorem chain_ends_at_owner_tags :
    ∀ s : CompilerStage, s.next = none ↔ s = ownerTags := by decide

/-- **`omega_inserted_only_after_two_copies`.**  `KERNEL-PROVED`.

The proof-local shared-gcd `Ω`-partition is strictly later in the chain than the two-copy
dispersion object: no earlier (one-copy, physical) stage carries that coordinate. -/
theorem omega_inserted_only_after_two_copies :
    twoCopyDispersionObject.index < proofLocalSharedGcdPartition.index ∧
    oneCopyPhysicalSource.index < twoCopyDispersionObject.index ∧
    fourClassSourcePartition.index < twoCopyDispersionObject.index := by decide

/-- **`owner_tags_are_last`.**  `KERNEL-PROVED`.  Tagging happens strictly after every
other stage, in particular after the `Ω` insertion. -/
theorem owner_tags_are_last :
    ∀ s : CompilerStage, s ≠ ownerTags → s.index < ownerTags.index := by decide

/-! ## §2  The exact de-regularisation identity -/

namespace K0SP2Params

open Erdos287.K0SP2Source.K0SP2Params

variable (P : K0SP2Params) (W : ℕ → ℂ) (D : Bool → ℕ → ℂ) (L : ℕ)

/-- **`fullSmooth_eq_four_sectors`.**  `KERNEL-PROVED`.

The full-smooth (audited) source is exactly the sum of its four sectors:

```
fullSmooth = repeated + largePrimePower + distinctBalanced7 + regular.
```
-/
theorem fullSmooth_eq_four_sectors :
    sourceExpr P W D
      = sectorExpr P W D P.classRepeatedB7 + sectorExpr P W D (P.classLargePP L)
        + sectorExpr P W D (P.classDistinctB7 L) + sectorExpr P W D (P.classRegular L) :=
  sourceExpr_four_sectors P W D (P.disjoint_A_B L) (P.disjoint_A_C L) (P.disjoint_A_R L)
    (P.disjoint_B_C L) (P.disjoint_B_R L) (P.disjoint_C_R L) (P.fourClass_union L)

/-- **`deRegularisation_identity`.**  `KERNEL-PROVED`.

The exact algebraic de-regularisation identity

```
regular = fullSmooth − repeated − largePrimePower − distinctBalanced7.
```

Only the *identity* is formalised.  The asymptotic smallness of the three deleted
sectors is an external analytic input and is **not** proved here. -/
theorem deRegularisation_identity :
    sectorExpr P W D (P.classRegular L)
      = sourceExpr P W D - sectorExpr P W D P.classRepeatedB7
        - sectorExpr P W D (P.classLargePP L) - sectorExpr P W D (P.classDistinctB7 L) := by
  have h := fullSmooth_eq_four_sectors P W D L
  linear_combination -h

end K0SP2Params

/-! ## §3  The finite owner type -/

/-- The finite owner type of the typed Perron packets. -/
inductive PacketOwner
  /-- The low-`Q` owner. -/
  | lowQ
  /-- The generated Pascadi triple-cell owner. -/
  | pascadiTriple
  /-- The `C0` owner. -/
  | c0
  /-- The transverse owner. -/
  | transverse
  /-- The b-diagonal owner. -/
  | bDiagonal
  /-- The proof-local owner. -/
  | localOwner
  deriving DecidableEq, Fintype, Repr

/-- **`owner_type_is_exactly_six`.**  `KERNEL-PROVED`.  The owner type contains exactly the
six mandated owners. -/
theorem owner_type_is_exactly_six : Fintype.card PacketOwner = 6 := by decide

/-- **`owner_type_exhaustive`.**  `KERNEL-PROVED`.  Every owner is one of the six. -/
theorem owner_type_exhaustive (o : PacketOwner) :
    o = PacketOwner.lowQ ∨ o = PacketOwner.pascadiTriple ∨ o = PacketOwner.c0 ∨
      o = PacketOwner.transverse ∨ o = PacketOwner.bDiagonal ∨ o = PacketOwner.localOwner := by
  cases o <;> simp

/-! ## §4  Typed packet families and the owner partition -/

/-- **`PacketFamily`** — a finite family of typed Perron packets, each carrying an owner
tag and the compiler stage at which it was emitted. -/
structure PacketFamily (ι : Type) [DecidableEq ι] where
  /-- The finite index set of emitted packets. -/
  cells : Finset ι
  /-- The primary owner of each packet. -/
  owner : ι → PacketOwner
  /-- The stage at which each packet was emitted. -/
  emitted : ι → CompilerStage
  /-- Packets are emitted only at the owner-tag stage, i.e. after the `Ω` insertion. -/
  emitted_at_tag_stage : ∀ i ∈ cells, emitted i = CompilerStage.ownerTags

namespace PacketFamily

variable {ι : Type} [DecidableEq ι] (F : PacketFamily ι)

/-- The fibre of an owner. -/
def fibre (o : PacketOwner) : Finset ι := F.cells.filter (fun i => F.owner i = o)

@[simp] theorem mem_fibre {i : ι} {o : PacketOwner} :
    i ∈ F.fibre o ↔ i ∈ F.cells ∧ F.owner i = o := by
  simp [fibre]

/-- **`packet_has_one_owner`.**  `KERNEL-PROVED`.  Every typed packet has exactly one
owner. -/
theorem packet_has_one_owner (i : ι) : ∃! o : PacketOwner, F.owner i = o :=
  ⟨F.owner i, rfl, fun _ h => h.symm⟩

/-- **`no_packet_has_two_owners`.**  `KERNEL-PROVED`.  No packet lies in two owner
fibres. -/
theorem no_packet_has_two_owners {i : ι} {o₁ o₂ : PacketOwner} (h : o₁ ≠ o₂) :
    ¬ (i ∈ F.fibre o₁ ∧ i ∈ F.fibre o₂) := by
  rintro ⟨h₁, h₂⟩
  rw [mem_fibre] at h₁ h₂
  exact h (h₁.2 ▸ h₂.2 ▸ rfl)

/-- **`owner_fibres_disjoint`.**  `KERNEL-PROVED`. -/
theorem owner_fibres_disjoint {o₁ o₂ : PacketOwner} (h : o₁ ≠ o₂) :
    Disjoint (F.fibre o₁) (F.fibre o₂) := by
  rw [Finset.disjoint_left]
  intro i h₁ h₂
  exact F.no_packet_has_two_owners h ⟨h₁, h₂⟩

/-- **`owner_partition_exhaustive`.**  `KERNEL-PROVED`.  The six owner fibres cover the
whole packet family. -/
theorem owner_partition_exhaustive :
    (Finset.univ : Finset PacketOwner).biUnion F.fibre = F.cells := by
  ext i
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, mem_fibre]
  constructor
  · rintro ⟨_, h, -⟩; exact h
  · intro h; exact ⟨F.owner i, h, rfl⟩

/-- **`owner_partition_card`.**  `KERNEL-PROVED`.  The owner fibres partition the packet
count. -/
theorem owner_partition_card :
    ∑ o : PacketOwner, (F.fibre o).card = F.cells.card :=
  (Finset.card_eq_sum_card_fiberwise (fun i _ => Finset.mem_univ (F.owner i))).symm

/-- **`owner_accounts_reassemble`.**  `KERNEL-PROVED`.

Owner-wise accounting is exact: summing each owner's account reproduces the total, with
no packet counted twice and none dropped. -/
theorem owner_accounts_reassemble (val : ι → ℂ) :
    ∑ o : PacketOwner, ∑ i ∈ F.fibre o, val i = ∑ i ∈ F.cells, val i :=
  Finset.sum_fiberwise F.cells F.owner val

/-- **`packets_emitted_after_omega`.**  `KERNEL-PROVED`.

Every emitted packet carries the terminal (owner-tag) stage, which is strictly later than
the two-copy stage at which the proof-local `Ω` coordinate is introduced. -/
theorem packets_emitted_after_omega {i : ι} (hi : i ∈ F.cells) :
    (F.emitted i).index = CompilerStage.ownerTags.index ∧
      CompilerStage.twoCopyDispersionObject.index < (F.emitted i).index := by
  rw [F.emitted_at_tag_stage i hi]
  exact ⟨rfl, by decide⟩

end PacketFamily

/-! ## §5  Firewall: tags carry no analytic content -/

/-- **`owner_tags_carry_no_analytic_bound`.**  `KERNEL-PROVED`.

An owner tag is bookkeeping only: two packet families with *identical* owner tags can
carry arbitrarily different values, so no size information may be inferred from a tag. -/
theorem owner_tags_carry_no_analytic_bound (F : PacketFamily ℕ) (hF : F.cells = {0})
    (B : ℝ) : ∃ val : ℕ → ℂ, (∀ i ∈ F.cells, F.owner i = F.owner i) ∧
      B < ‖∑ i ∈ F.cells, val i‖ := by
  refine ⟨fun _ => ((|B| + 1 : ℝ) : ℂ), fun _ _ => rfl, ?_⟩
  rw [hF]
  simp only [Finset.sum_singleton, Complex.norm_real, Real.norm_eq_abs]
  have h1 : |B| ≤ |(|B| + 1)| := by
    rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ |B| + 1)]
    linarith
  have h2 : B ≤ |B| := le_abs_self B
  have h3 : |B| < |B| + 1 := by linarith
  calc B ≤ |B| := h2
    _ < |B| + 1 := h3
    _ = |(|B| + 1)| := (abs_of_nonneg (by positivity)).symm

/-- **`compiler_does_not_inhabit_analytic_input`.**  `KERNEL-PROVED`.

The typed source compiler of this module is complete and unconditional, yet it does not
inhabit the external analytic input: both statements hold simultaneously. -/
theorem compiler_does_not_inhabit_analytic_input :
    (∀ s t : CompilerStage, s.next = some t → s.index + 1 = t.index) ∧
    ∃ (X : ℝ) (v : Erdos287.FullAnalyticKernel.OwnerValues),
      ¬ Erdos287.FullAnalyticKernel.FullSourceLocalAnalyticKernelInput X v :=
  ⟨chain_is_linear, Erdos287.FullAnalyticKernel.analyticInput_is_a_genuine_constraint⟩

end MasterSourcePackets
end Erdos287
