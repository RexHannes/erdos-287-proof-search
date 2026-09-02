import RequestProject.CurrentProgramme.Erdos287SharedOtherConductorAndSocket

/-!
# The 287A / shared-other45 Type-I socket, the two independent adapters, and the
conditional FCL compiler

```
Tot CENSUS RECONSTRUCTION (finite/source portion)  : KERNEL-PROVED
E_T = o(X / log X)  (Type-I estimate)              : PAPER-CLOSED EXTERNAL / UNINHABITED
SharedOtherParentInput → E_L bound                 : KERNEL-PROVED CONDITIONAL
TwinOtherParentAdapter                             : parametric, never inhabited here
Erdos287HardUAdapter                               : KERNEL-PROVED CONDITIONAL
ASYMPTOTIC FCL FROM THE SHARED SOURCE              : KERNEL-PROVED CONDITIONAL
ERDOS287                                           : OPEN
```

This module is **append-only**.  No external analytic statement is proved; each is carried
as an explicit hypothesis with a counterguard showing that it is a genuine constraint.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Erdos287
namespace SharedOtherCompiler

open Erdos287.SharedOtherRaw
open Erdos287.SharedOtherParent
open Erdos287.PhysicalSupport
open Erdos287.FourErrorTransference

/-! ## §1  The finite/source portion of the Lemma-7.21 `Tot` reconstruction -/

/-- The `Tot` sub-census of a census of dependent raw packets. -/
def totCensus {X : ℕ} [DecidableEq (RawPacket X)] (S : Finset (RawPacket X)) :
    Finset (RawPacket X) := S.filter (fun p => p.isLeft)

/-- The `U` sub-census of a census of dependent raw packets. -/
def uCensus {X : ℕ} [DecidableEq (RawPacket X)] (S : Finset (RawPacket X)) :
    Finset (RawPacket X) := S.filter (fun p => ¬ p.isLeft)

/-- **`raw_census_union`.**  `KERNEL-PROVED`. -/
theorem raw_census_union {X : ℕ} [DecidableEq (RawPacket X)] (S : Finset (RawPacket X)) :
    totCensus S ∪ uCensus S = S :=
  Finset.filter_union_filter_not_eq _ _

/-- **`raw_census_disjoint`.**  `KERNEL-PROVED`. -/
theorem raw_census_disjoint {X : ℕ} [DecidableEq (RawPacket X)] (S : Finset (RawPacket X)) :
    Disjoint (totCensus S) (uCensus S) :=
  Finset.disjoint_filter_filter_not _ _ _

/-- **`raw_census_card`.**  `KERNEL-PROVED`. -/
theorem raw_census_card {X : ℕ} [DecidableEq (RawPacket X)] (S : Finset (RawPacket X)) :
    (totCensus S).card + (uCensus S).card = S.card := by
  rw [← Finset.card_union_of_disjoint (raw_census_disjoint S), raw_census_union S]

/-- **`tot_reconstruction_finite`.**  `KERNEL-PROVED`.

The finite/source portion of the Lemma-7.21 reconstruction: any additive quantity over the
dependent census splits exactly into its `Tot` and `U` parts. -/
theorem tot_reconstruction_finite {X : ℕ} [DecidableEq (RawPacket X)]
    (S : Finset (RawPacket X)) (val : RawPacket X → ℂ) :
    ∑ p ∈ S, val p = (∑ p ∈ totCensus S, val p) + ∑ p ∈ uCensus S, val p := by
  rw [← Finset.sum_union (raw_census_disjoint S), raw_census_union S]

/-- **`totCensus_carries_no_U_datum`.**  `KERNEL-PROVED`.  The `Tot` census consists of
`Tot` data only. -/
theorem totCensus_carries_no_U_datum {X : ℕ} [DecidableEq (RawPacket X)]
    {S : Finset (RawPacket X)} {p : RawPacket X} (hp : p ∈ totCensus S) :
    ∃ t : RawDataTot X, p = RawPacket.tot t := by
  have h : p.isLeft = true := (Finset.mem_filter.1 hp).2
  cases p with
  | inl t => exact ⟨t, rfl⟩
  | inr q => simp at h

/-! ## §2  The Type-I estimate socket: `E_T = o(X / log X)` -/

/-- **`IsLittleOXOverLogX`** — the literal `o(X / log X)` representation. -/
def IsLittleOXOverLogX (ET : ℝ → ℝ) : Prop :=
  ∀ delta : ℝ, 0 < delta → ∃ X0 : ℝ, ∀ X : ℝ, X0 ≤ X → Real.exp 1 ≤ X →
    ET X ≤ delta * (X / Real.log X)

/-- **`TypeIEstimatePaperInput`** — `PAPER-CLOSED EXTERNAL / UNINHABITED`.

The external Type-I estimate.  Its mathematical conclusion is exactly `E_T = o(X/log X)`,
pinned to the physical total channel by `channel_pin`.  `E_T` closure is **never** encoded
as a theorem without this input. -/
structure TypeIEstimatePaperInput (Cc : ℝ)
    (dw : ℝ → PhysicalSupportData × PhysicalWeightData) (ET : ℝ → ℝ) where
  /-- `ET` is the physical total-channel deficit at each scale. -/
  channel_pin : ∀ X : ℝ,
    ET X = Cc * Bmass (dw X).1 (dw X).2 - totalCorr (dw X).1 (dw X).2
  /-- The Type-I conclusion `E_T = o(X/log X)`. -/
  littleO : IsLittleOXOverLogX ET

/-- **`E_T_bound_of_typeI`.**  `KERNEL-PROVED CONDITIONAL`.

The only route to an `E_T` bound in this development: it consumes the external Type-I
estimate. -/
theorem E_T_bound_of_typeI {Cc : ℝ} {dw : ℝ → PhysicalSupportData × PhysicalWeightData}
    {ET : ℝ → ℝ} (I : TypeIEstimatePaperInput Cc dw ET) {delta : ℝ} (hd : 0 < delta) :
    ∃ X0 : ℝ, ∀ X : ℝ, X0 ≤ X → Real.exp 1 ≤ X →
      Cc * Bmass (dw X).1 (dw X).2 - totalCorr (dw X).1 (dw X).2
        ≤ delta * (X / Real.log X) := by
  obtain ⟨X0, hX0⟩ := I.littleO delta hd
  exact ⟨X0, fun X hX he => (I.channel_pin X) ▸ hX0 X hX he⟩

/-- **`littleO_is_a_genuine_constraint`.**  `KERNEL-PROVED`.

The `o(X/log X)` conclusion is not automatic: the identity function fails it, so the Type-I
input carries real mathematical content. -/
theorem littleO_is_a_genuine_constraint : ¬ IsLittleOXOverLogX (fun X => X) := by
  intro h
  obtain ⟨X0, hX0⟩ := h (1 / 2) (by norm_num)
  set X : ℝ := max X0 (Real.exp 2) with hXdef
  have hX2 : Real.exp 2 ≤ X := le_max_right _ _
  have hXpos : 0 < X := lt_of_lt_of_le (Real.exp_pos 2) hX2
  have hlog : (2 : ℝ) ≤ Real.log X := by
    have := Real.log_le_log (Real.exp_pos 2) hX2
    rwa [Real.log_exp] at this
  have he : Real.exp 1 ≤ X :=
    le_trans (Real.exp_le_exp.2 (by norm_num)) hX2
  have hmain := hX0 X (le_max_left _ _) he
  have hlogpos : (0 : ℝ) < Real.log X := lt_of_lt_of_le (by norm_num) hlog
  have hdiv : X / Real.log X ≤ X / 2 := by
    gcongr
  simp only at hmain
  linarith

/-! ## §3  The shared source input and the `E_L` compiler -/

/-- **`SharedOtherParentInput`** — the shared source object of the two projects.

It bundles the (uninhabited) Ford-7.22 generated-uniformity socket with the pin identifying
the physical leakage `L_X` with the generated covariance sum. -/
structure SharedOtherParentInput (d : PhysicalSupportData) (w : PhysicalWeightData)
    {X : ℕ} (p : RawDataU X) (eta : ℕ → ℝ) (chi : ℕ → ℤ → ℝ) (S T : Finset ℕ)
    (kernel : ℕ → ℕ → ℤ → ℝ) (tau : ℤ) (bound : ℝ) where
  /-- The shared Ford-7.22 covariance socket. -/
  ford : Ford722OtherParentGeneratedUniformityInput p eta chi S T kernel tau bound
  /-- The compilation pin: the physical leakage is the generated covariance sum. -/
  leakage_pin : E_L_exact d w
    = ∑ a ∈ S, ∑ b ∈ T, A_eta p eta chi a tau * B_eta p eta chi b tau * kernel a b tau

/-- **`E_L_bound_of_sharedOtherParent`.**  `KERNEL-PROVED CONDITIONAL`.

`SharedOtherParentInput ⟹ E_L bound`.  The leakage error is bounded by the *generated*
covariance bound; it is **not** inferred from `E_T` by monotonicity. -/
theorem E_L_bound_of_sharedOtherParent {d : PhysicalSupportData} {w : PhysicalWeightData}
    {X : ℕ} {p : RawDataU X} {eta : ℕ → ℝ} {chi : ℕ → ℤ → ℝ} {S T : Finset ℕ}
    {kernel : ℕ → ℕ → ℤ → ℝ} {tau : ℤ} {bound : ℝ}
    (I : SharedOtherParentInput d w p eta chi S T kernel tau bound) :
    E_L_exact d w ≤ bound := by
  rw [I.leakage_pin]
  exact le_trans (le_abs_self _) I.ford.generated_uniformity

/-- **`sharedOtherParentInput_is_a_genuine_constraint`.**  `KERNEL-PROVED`. -/
theorem sharedOtherParentInput_is_a_genuine_constraint
    (d : PhysicalSupportData) (w : PhysicalWeightData) :
    IsEmpty (SharedOtherParentInput d w sampleU (fun _ => 1) (fun _ _ => 1) ∅ ∅
      (fun _ _ _ => 1) 0 (-1)) := by
  constructor
  intro I
  exact (ford722_socket_is_a_genuine_constraint).false I.ford

/-! ## §4  The two independent adapters -/

/-- **A.  `TwinOtherParentAdapter`** — the twin-prime-side adapter.

It is *parametric* in the downstream conclusion of that project: this module never names,
imports or proves it. -/
def TwinOtherParentAdapter (twinConclusion : Prop) (d : PhysicalSupportData)
    (w : PhysicalWeightData) {X : ℕ} (p : RawDataU X) (eta : ℕ → ℝ) (chi : ℕ → ℤ → ℝ)
    (S T : Finset ℕ) (kernel : ℕ → ℕ → ℤ → ℝ) (tau : ℤ) (bound : ℝ) : Prop :=
  SharedOtherParentInput d w p eta chi S T kernel tau bound → twinConclusion

/-- **B.  `Erdos287HardUAdapter`** — the Erdős #287 hard-`U` adapter.

Its conclusion is the `E_L` bound of this project alone. -/
def Erdos287HardUAdapter (d : PhysicalSupportData) (w : PhysicalWeightData) {X : ℕ}
    (p : RawDataU X) (eta : ℕ → ℝ) (chi : ℕ → ℤ → ℝ) (S T : Finset ℕ)
    (kernel : ℕ → ℕ → ℤ → ℝ) (tau : ℤ) (bound : ℝ) : Prop :=
  SharedOtherParentInput d w p eta chi S T kernel tau bound → E_L_exact d w ≤ bound

/-- **`erdos287HardUAdapter_holds`.**  `KERNEL-PROVED CONDITIONAL`.

Adapter **B** is discharged from the shared input alone. -/
theorem erdos287HardUAdapter_holds (d : PhysicalSupportData) (w : PhysicalWeightData)
    {X : ℕ} (p : RawDataU X) (eta : ℕ → ℝ) (chi : ℕ → ℤ → ℝ) (S T : Finset ℕ)
    (kernel : ℕ → ℕ → ℤ → ℝ) (tau : ℤ) (bound : ℝ) :
    Erdos287HardUAdapter d w p eta chi S T kernel tau bound :=
  fun I => E_L_bound_of_sharedOtherParent I

/-- **`adapters_are_independent`.**  `KERNEL-PROVED`.

Adapter **B** holds *uniformly in* the downstream conclusion of the other project: the
twin-side statement is not a hypothesis of the #287 side, and adapter **A** stays parametric
so the #287 conclusion is not a hypothesis of the twin side. -/
theorem adapters_are_independent (d : PhysicalSupportData) (w : PhysicalWeightData)
    {X : ℕ} (p : RawDataU X) (eta : ℕ → ℝ) (chi : ℕ → ℤ → ℝ) (S T : Finset ℕ)
    (kernel : ℕ → ℕ → ℤ → ℝ) (tau : ℤ) (bound : ℝ) :
    (∀ _twinConclusion : Prop, Erdos287HardUAdapter d w p eta chi S T kernel tau bound) ∧
    (∀ twinConclusion : Prop,
      TwinOtherParentAdapter twinConclusion d w p eta chi S T kernel tau bound
        ↔ (SharedOtherParentInput d w p eta chi S T kernel tau bound → twinConclusion)) :=
  ⟨fun _ => erdos287HardUAdapter_holds d w p eta chi S T kernel tau bound,
    fun _ => Iff.rfl⟩

/-- **`twin_adapter_is_not_inhabited_here`.**  `KERNEL-PROVED`.

Adapter **A** is *not* discharged in this repository: for a false downstream conclusion it
is refutable as soon as the shared input is inhabited, so no proof of it can be manufactured
from the #287 side. -/
theorem twin_adapter_is_not_inhabited_here (d : PhysicalSupportData)
    (w : PhysicalWeightData) {X : ℕ} (p : RawDataU X) (eta : ℕ → ℝ) (chi : ℕ → ℤ → ℝ)
    (S T : Finset ℕ) (kernel : ℕ → ℕ → ℤ → ℝ) (tau : ℤ) (bound : ℝ)
    (hInhab : SharedOtherParentInput d w p eta chi S T kernel tau bound) :
    ¬ TwinOtherParentAdapter False d w p eta chi S T kernel tau bound :=
  fun h => h hInhab

/-! ## §5  The conditional asymptotic FCL from the shared source -/

/-- **`asymptoticFCL_of_shared_other_parent`.**  `KERNEL-PROVED CONDITIONAL`.

```
    shared other-parent source (E_L)
      + paper-closed Type-I estimate (E_T)
      + paper-closed N2 λ-collar (E_2)
      + paper-closed Bsrc/N1 comparison (E_M)
      + positive margin
        ⟹ AsymptoticFixedCertificatePositiveMass .
```

Every external mathematical result appears in the antecedents; none is discharged. -/
theorem asymptoticFCL_of_shared_other_parent
    {d : PhysicalSupportData} {w : PhysicalWeightData}
    {X : ℕ} {p : RawDataU X} {eta : ℕ → ℝ} {chi : ℕ → ℤ → ℝ} {S T : Finset ℕ}
    {kernel : ℕ → ℕ → ℤ → ℝ} {tau : ℤ} {ELbound Cc marginEps ET : ℝ}
    (hKernel : ∀ n ∈ d.PX, w.HX n = 1)
    (shared : SharedOtherParentInput d w p eta chi S T kernel tau ELbound)
    (hT : Cc * Bmass d w - totalCorr d w ≤ ET)
    (n2 : Erdos287.TwoLaneMaster.N2LambdaCollarPaperInput d w marginEps)
    (bsrc : Erdos287.TwoLaneMaster.BsrcN1ComparisonPaperInput d w (fun n => w.Bsrc n)
      marginEps)
    (hmargin : Erdos287.FCLBridge.PositiveMarginSupply Cc)
    (hbudget : ET + ELbound + (marginEps / 8) * Bmass d w + (marginEps / 8) * Bmass d w
      ≤ (1 + Cc) / 6 * Bmass d w) :
    Erdos287.TwoLaneMaster.AsymptoticFixedCertificatePositiveMass d w := by
  have hdom : ChannelDomination d w
      ⟨Cc, ET, ELbound, (marginEps / 8) * Bmass d w, (marginEps / 8) * Bmass d w⟩ :=
    { kernel_on_P := hKernel
      total_channel := hT
      main_channel := bsrc.E_M_small
      collar_channel := n2.collar
      leakage_channel := E_L_bound_of_sharedOtherParent shared }
  exact transference_with_supplied_margin hmargin hdom bsrc.Bmass_pos hbudget

/-- **`asymptoticFCL_keeps_every_shared_source_input`.**  `KERNEL-PROVED`.

None of the four external inputs may be dropped: each is refutable at explicit data. -/
theorem asymptoticFCL_keeps_every_shared_source_input :
    (∃ (d : PhysicalSupportData) (w : PhysicalWeightData),
      IsEmpty (SharedOtherParentInput d w sampleU (fun _ => 1) (fun _ _ => 1) ∅ ∅
        (fun _ _ _ => 1) 0 (-1))) ∧
    (¬ IsLittleOXOverLogX (fun X : ℝ => X)) ∧
    (∃ (d : PhysicalSupportData) (w : PhysicalWeightData) (m : ℝ),
      IsEmpty (Erdos287.TwoLaneMaster.N2LambdaCollarPaperInput d w m)) ∧
    (∃ (d : PhysicalSupportData) (w : PhysicalWeightData) (pB : ℕ → ℝ) (m : ℝ),
      IsEmpty (Erdos287.TwoLaneMaster.BsrcN1ComparisonPaperInput d w pB m)) ∧
    (∃ Cc : ℝ, ¬ Erdos287.FCLBridge.PositiveMarginSupply Cc) :=
  ⟨⟨⟨∅, fun _ => SupportClass.P⟩, ⟨1, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0⟩,
      sharedOtherParentInput_is_a_genuine_constraint _ _⟩,
    littleO_is_a_genuine_constraint,
    Erdos287.TwoLaneMaster.n2_paper_input_is_a_genuine_constraint,
    Erdos287.TwoLaneMaster.bsrc_paper_input_is_a_genuine_constraint,
    Erdos287.FourErrorTransference.positiveMarginSupply_still_uninhabited⟩

end SharedOtherCompiler
end Erdos287
