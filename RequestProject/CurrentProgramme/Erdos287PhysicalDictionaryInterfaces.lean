import RequestProject.CurrentProgramme.Erdos287BDiagonalDeltaQAbstract
import RequestProject.CurrentProgramme.Erdos287ProofOmegaPartition

/-!
# Erdős #287 — physical source-realisation bridge interfaces (all uninhabited)

This module defines the **missing bridges** between the abstract kernels that are already
kernel-proved and the physical Erdős #287 source.  None of them is constructed here; each
one requires, as a field, the master physical source realisation that this repository does
not have.  No axiom is used: they are ordinary structures, left uninhabited.

* `Owner` — the owner labels used by the source census;
* `BDiagonalDeltaQPhysicalDictionary` — realisation of the physical b-diagonal coefficient
  as the abstract `A_t / B_t` family, including the Archimedean source factors, `U_e(Δ)`,
  the local harmonic profile, the Perron labels, the `A0`/`C0` dependence, the gcd mask and
  the dyadic/source factors;
* `bDiagonalPhysical_compiler` — the physical compiler, **conditional** on the dictionary
  plus explicit energy/range inputs;
* `C0SourceRealisationBridge`, `TransverseSourceRealisationBridge` — the two remaining
  source-realisation bridge types, each recording packet selection, the exact coefficient
  identity, the owner theorem and unique ownership.

Verdict recorded in the kernel below: the abstract `Δ × q` kernel is proved, the physical
b-diagonal dictionary is **OPEN**.  The b-diagonal face is *not* physically closed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Erdos287
namespace PhysicalDictionary

/-- Owner labels of the source census. -/
inductive Owner
  | c0
  | transverse
  | bDiagonal
  | archimedean
  | errorTerm
  deriving DecidableEq, Fintype, Repr

/-! ## §1  The physical b-diagonal `Δ × q_a` dictionary -/

/-- **`BDiagonalDeltaQPhysicalDictionary`.**  The physical realisation demanded by the
b-diagonal pivot: the physical coefficient must be *exhibited* as the abstract `A_t / B_t`
family of `BDiagonalDeltaQ`, with every physical factor named, and the physical source must
equal the resulting `Δ × q` double sum.

**Left uninhabited.**  Its first field is the master physical source realisation, which is
not constructed anywhere in this repository. -/
structure BDiagonalDeltaQPhysicalDictionary (n : ℕ) [NeZero n]
    (spec : MasterSource.SourceSpec) where
  /-- The missing master physical source realisation. -/
  source : MasterSource.MasterPhysicalSourceRealisation spec
  /-- The finite `t`-range of the pivot. -/
  tRange : Finset ℕ
  /-- The physical `Δ`-range. -/
  deltaRange : Finset (ZMod n)
  /-- The physical `q_a`-range. -/
  qRange : Finset (ZMod n)
  /-- `Δ`-range consists of units. -/
  deltaRange_unit : ∀ d ∈ deltaRange, IsUnit d
  /-- `q_a`-range consists of units. -/
  qRange_unit : ∀ q ∈ qRange, IsUnit q
  /-- The physical twist `u_t`. -/
  twist : ℕ → ZMod n
  /-- The twist is a unit for every `t` in range. -/
  twist_unit : ∀ t ∈ tRange, IsUnit (twist t)
  /-- The abstract `Δ`-side coefficient family. -/
  A : ℕ → ZMod n → ℂ
  /-- The abstract `q`-side coefficient family. -/
  B : ℕ → ZMod n → ℂ
  /-- Archimedean source factors. -/
  archimedean : ℕ → ℂ
  /-- The physical `U_e(Δ)` factor. -/
  Ue : ZMod n → ℂ
  /-- The local harmonic profile. -/
  localHarmonicProfile : ℕ → ℂ
  /-- The Perron labels. -/
  perronLabel : ℕ → ℤ
  /-- The `A0`/`C0` dependence. -/
  a0c0Dependence : ℕ → ℂ
  /-- The gcd mask. -/
  gcdMask : ℕ → ℕ
  /-- The dyadic/source factors. -/
  dyadicFactor : ℕ → ℝ
  /-- **Exact physical coefficient identity** on the `Δ`-side. -/
  A_identity : ∀ t ∈ tRange, ∀ d ∈ deltaRange,
    A t d = archimedean t * Ue d * localHarmonicProfile t * a0c0Dependence t *
      (gcdMask t : ℂ) * (dyadicFactor t : ℂ)
  /-- The gcd mask is a genuine (positive) mask. -/
  gcdMask_pos : ∀ t ∈ tRange, 0 < gcdMask t
  /-- **Exact physical source identity**: the parent expression is the `Δ × q` double sum. -/
  source_identity :
    spec.parent = ∑ t ∈ tRange, ∑ d ∈ deltaRange, ∑ q ∈ qRange,
      A t d * B t q * ZMod.stdAddChar (d * twist t * q⁻¹)

/-- **`bDiagonalPhysical_compiler`.**  `LEAN_PROVED` *conditionally*: given the (missing)
physical dictionary together with explicit energy inputs, the physical source obeys the
abstract `Δ × q` bound.  The dictionary hypothesis is never discharged. -/
theorem bDiagonalPhysical_compiler {n : ℕ} [NeZero n] {spec : MasterSource.SourceSpec}
    (Dict : BDiagonalDeltaQPhysicalDictionary n spec) (EA EB : ℝ)
    (hEA : ∑ t ∈ Dict.tRange, ∑ d ∈ Dict.deltaRange, ‖Dict.A t d‖ ^ 2 ≤ EA)
    (hEB : ∑ t ∈ Dict.tRange, ∑ q ∈ Dict.qRange, ‖Dict.B t q‖ ^ 2 ≤ EB)
    (hEA0 : 0 ≤ EA) :
    ‖spec.parent‖ ^ 2 ≤ (n : ℝ) * EA * EB := by
  have hbase := BDiagonalDeltaQ.deltaQ_cauchy_over_t Dict.tRange Dict.twist Dict.twist_unit
    Dict.deltaRange Dict.qRange Dict.deltaRange_unit Dict.qRange_unit Dict.A Dict.B
  rw [Dict.source_identity]
  refine hbase.trans ?_
  have hEB0 : (0 : ℝ) ≤ ∑ t ∈ Dict.tRange, ∑ q ∈ Dict.qRange, ‖Dict.B t q‖ ^ 2 :=
    Finset.sum_nonneg fun t _ => Finset.sum_nonneg fun q _ => by positivity
  calc (n : ℝ) * (∑ t ∈ Dict.tRange, ∑ d ∈ Dict.deltaRange, ‖Dict.A t d‖ ^ 2) *
        (∑ t ∈ Dict.tRange, ∑ q ∈ Dict.qRange, ‖Dict.B t q‖ ^ 2)
      ≤ (n : ℝ) * EA * (∑ t ∈ Dict.tRange, ∑ q ∈ Dict.qRange, ‖Dict.B t q‖ ^ 2) := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hEA (by positivity)) hEB0
    _ ≤ (n : ℝ) * EA * EB := mul_le_mul_of_nonneg_left hEB (by positivity)

/-- **`bDiagonalPhysicalDictionary_open`.**  The physical b-diagonal dictionary is not
constructed: for the countermodel spec of the master-source bank its type is empty, because
it requires the master physical source realisation. -/
theorem bDiagonalPhysicalDictionary_open (n : ℕ) [NeZero n] :
    ¬ Nonempty (BDiagonalDeltaQPhysicalDictionary n MasterSource.vanishingWeightSpec) := by
  rintro ⟨Dict⟩
  exact MasterSource.no_realisation_vanishingWeightSpec ⟨Dict.source⟩

/-- **`abstractDeltaQKernel_does_not_close_bDiagonal`.**  The abstract kernel is proved and
the physical dictionary is still open: owning the abstract `Δ × q` bound for every unit
twist does not produce a physical dictionary. -/
theorem abstractDeltaQKernel_does_not_close_bDiagonal (n : ℕ) [NeZero n]
    (D Q : Finset (ZMod n)) (hD : ∀ d ∈ D, IsUnit d) (hQ : ∀ q ∈ Q, IsUnit q)
    (A B : ZMod n → ℂ) {u : ZMod n} (hu : IsUnit u) :
    ‖∑ d ∈ D, ∑ q ∈ Q, A d * B q * ZMod.stdAddChar (d * u * q⁻¹)‖ ^ 2
        ≤ (n : ℝ) * (∑ d ∈ D, ‖A d‖ ^ 2) * (∑ q ∈ Q, ‖B q‖ ^ 2) ∧
      ¬ Nonempty (BDiagonalDeltaQPhysicalDictionary n MasterSource.vanishingWeightSpec) :=
  ⟨BDiagonalDeltaQ.deltaQ_unitaryFourier_bound hu D Q hD hQ A B,
    bDiagonalPhysicalDictionary_open n⟩

/-! ## §2  The remaining source-realisation bridges

These types do **not** reconstruct any mathematics.  Each records only what a
source-realisation bridge has to supply for an eventual master-source census: the packet
selection, the exact coefficient identity, the owner theorem, and unique ownership. -/

/-- **`C0SourceRealisationBridge`.**  Left uninhabited. -/
structure C0SourceRealisationBridge (spec : MasterSource.SourceSpec) where
  /-- The missing master physical source realisation. -/
  source : MasterSource.MasterPhysicalSourceRealisation spec
  /-- The selected source packets owned by the `C0` face. -/
  packetSelection : Finset ℕ
  /-- The selection is non-empty. -/
  packetSelection_nonempty : packetSelection.Nonempty
  /-- The coefficient exhibited for each selected packet. -/
  coefficient : ℕ → ℂ
  /-- **Exact coefficient identity** with the physical weights. -/
  coefficient_identity : ∀ p ∈ packetSelection, coefficient p = spec.requiredWeight p
  /-- The owner label of this bridge. -/
  owner : Owner
  /-- The owner theorem: this bridge owns the `C0` face. -/
  owner_eq : owner = Owner.c0
  /-- The census-wide ownership function. -/
  ownerOf : ℕ → Owner
  /-- Unique ownership: every selected packet is owned by this bridge and, `ownerOf` being
  a function, by no other. -/
  unique_ownership : ∀ p ∈ packetSelection, ownerOf p = owner

/-- **`TransverseSourceRealisationBridge`.**  Left uninhabited. -/
structure TransverseSourceRealisationBridge (spec : MasterSource.SourceSpec) where
  /-- The missing master physical source realisation. -/
  source : MasterSource.MasterPhysicalSourceRealisation spec
  /-- The selected source packets owned by the transverse face. -/
  packetSelection : Finset ℕ
  /-- The selection is non-empty. -/
  packetSelection_nonempty : packetSelection.Nonempty
  /-- The coefficient exhibited for each selected packet. -/
  coefficient : ℕ → ℂ
  /-- **Exact coefficient identity** with the physical weights. -/
  coefficient_identity : ∀ p ∈ packetSelection, coefficient p = spec.requiredWeight p
  /-- The owner label of this bridge. -/
  owner : Owner
  /-- The owner theorem: this bridge owns the transverse face. -/
  owner_eq : owner = Owner.transverse
  /-- The census-wide ownership function. -/
  ownerOf : ℕ → Owner
  /-- Unique ownership: every selected packet is owned by this bridge and, `ownerOf` being
  a function, by no other. -/
  unique_ownership : ∀ p ∈ packetSelection, ownerOf p = owner

/-- Unique ownership really is unique: a selected `C0` packet is owned by no other face. -/
theorem c0Bridge_owner_unique {spec : MasterSource.SourceSpec}
    (Br : C0SourceRealisationBridge spec) {p : ℕ} (hp : p ∈ Br.packetSelection)
    (o : Owner) (ho : o ≠ Owner.c0) : Br.ownerOf p ≠ o := by
  rw [Br.unique_ownership p hp, Br.owner_eq]
  exact fun h => ho h.symm

/-- The `C0` bridge is not constructed. -/
theorem c0SourceRealisationBridge_open :
    ¬ Nonempty (C0SourceRealisationBridge MasterSource.vanishingWeightSpec) := by
  rintro ⟨Br⟩
  exact MasterSource.no_realisation_vanishingWeightSpec ⟨Br.source⟩

/-- The transverse bridge is not constructed. -/
theorem transverseSourceRealisationBridge_open :
    ¬ Nonempty (TransverseSourceRealisationBridge MasterSource.vanishingWeightSpec) := by
  rintro ⟨Br⟩
  exact MasterSource.no_realisation_vanishingWeightSpec ⟨Br.source⟩

/-- Owner labels are pairwise distinct: the census faces are genuinely different owners. -/
theorem owner_labels_distinct :
    Owner.c0 ≠ Owner.transverse ∧ Owner.c0 ≠ Owner.bDiagonal ∧
      Owner.transverse ≠ Owner.bDiagonal := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

end PhysicalDictionary
end Erdos287
