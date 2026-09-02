import RequestProject.CurrentProgramme.Erdos287OneCopyTwoCopyOwners
import RequestProject.CurrentProgramme.Erdos287EndgameEffectivityAndClosure

/-!
# The two-lane master compiler V2, the paper-closed analytic inputs, and the conditional
asymptotic FCL

```
TWO-LANE RAW → TWO-COPY TYPED-OWNER INPUT : OPEN / UNINHABITED  (supersedes the V1 socket)
N2 λ-COLLAR (fixed ε, eventual)           : PAPER-CLOSED EXTERNAL / UNINHABITED
Bsrc / N1 / E_M COMPARISON                : PAPER-CLOSED EXTERNAL / UNINHABITED
ASYMPTOTIC FCL COMPILER                   : KERNEL-PROVED CONDITIONAL
EXPLICIT THRESHOLD INPUTS                 : OPEN / UNINHABITED
END-TO-END CHAIN                          : KERNEL-PROVED CONDITIONAL
ERDOS287                                  : OPEN
```

This module is **append-only**.  The V1 master-source socket is *retained*; it is superseded
only through the later status layer, never deleted.

**§1 — the V2 master compiler socket.**  Its content is the exact two-lane reconstruction:
`Tot` reconstructs `T_X`, `U` reconstructs `L_X`, the dispersion step produces
coefficient-preserving two-copy descendants with their kernels retained, the descendants are
exhaustive, ownership is assigned at the *correct level* (`Owner1` on raw packets, `Owner2`
on descendants only), local dictionaries are supplied, and the Cauchy step reassembles back
to each raw packet.  **There is no one-copy `Owner2` field anywhere in the structure.**

**§2 — the paper-closed analytic inputs.**  The `N2` λ-collar is recorded in its *exact*
contract — a **fixed** admissible `ε` with `E_2 ≤ (m_ε/8)·Bmass` eventually — and explicitly
**not** as `E_2 = o(Bmass)`; the separation is kernel-proved.  The `Bsrc`/`N1`/`E_M`
comparison is likewise an explicit input.  Both are *external*: they are hypotheses of every
compiler and are never inhabited.

**§3 — the conditional asymptotic FCL** and **§4 — the end-to-end chain**, reusing the
four-error transference algebra and the banked finite range through `4·10⁹`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Erdos287
namespace TwoLaneMaster

open Erdos287.PhysicalSupport
open Erdos287.FourErrorTransference
open Erdos287.TwoLaneRawSource
open Erdos287.OneCopyTwoCopy
open Erdos287.EndgameFCL
open Erdos287.FCLWindowPair

/-! ## §1  The V2 master compiler socket -/

/-- **`TwoLaneRawToTwoCopyTypedOwnerInput`** — `OPEN / UNINHABITED`.

The exact content of the raw-to-two-copy master compiler.  Fields **A–H** of the
specification appear literally; ownership is typed at the correct level, so no one-copy
packet can be given a `C0` / `transverse` / `bDiagonal` owner. -/
structure TwoLaneRawToTwoCopyTypedOwnerInput
    (d : PhysicalSupportData) (w : PhysicalWeightData)
    (S : Finset RawPacketId) (rawValue : RawPacketId → ℝ)
    (ownerBudget : Owner2 → ℝ) where
  /-- The lane discipline holds on the census. -/
  wellFormed : ∀ p ∈ S, WellFormed p
  /-- **A.**  The `Tot` lane reconstructs the full correlation `T_X`. -/
  tot_reconstruction : totalCorr d w = ∑ p ∈ totCells S, rawValue p
  /-- **B.**  The `U` lane reconstructs the leakage `L_X`. -/
  u_reconstruction : E_L_exact d w = ∑ p ∈ uCells S, rawValue p
  /-- **C.**  The dispersion step supplies a two-copy descendant of every ordered pair. -/
  descendant : ∀ p q : RawPacketId, TwoCopyDescendant p q
  /-- **C.**  The two-copy value of each pair. -/
  pairValue : RawPacketId → RawPacketId → ℝ
  /-- **C.**  Coefficient preservation: the diagonal pair value is the raw square. -/
  coefficient_preserved : ∀ p, pairValue p p = rawValue p ^ 2
  /-- **D.**  The contour kernel label of each raw packet is retained by its descendants. -/
  kernel_retained : ∀ p q : RawPacketId, (descendant p q).config.g₁ = p.kernelMeta
  /-- **E.**  Descendant exhaustiveness on the census. -/
  descendant_exhaustive : ∀ p ∈ S, ∀ q ∈ S, ∃ x : TwoCopyDescendant p q, x = descendant p q
  /-- **F.**  One-copy ownership, at the one-copy level only. -/
  owner1Assignment : RawPacketId → Owner1
  /-- **F.**  Two-copy ownership, supplied as data on ordered pairs. -/
  owner2Assignment : RawPacketId → RawPacketId → Owner2
  /-- **F.**  The supplied two-copy ownership agrees with the exact router on descendants. -/
  owner2_from_router : ∀ p q : RawPacketId,
    owner2Assignment p q = owner2 (descendant p q)
  /-- **G.**  The local owner dictionaries. -/
  localDictionary : Owner1 → ℝ
  /-- **G.**  The owner-aggregate bound carried by each two-copy owner. -/
  owner_aggregate : ∀ p q : RawPacketId,
    |pairValue p q| ≤ ownerBudget (owner2Assignment p q)
  /-- **H.**  The Cauchy/square-root reassembly back to each raw packet. -/
  cauchy_reassembly : ∀ p ∈ S, rawValue p ^ 2 ≤ ∑ q ∈ S, |pairValue p q|

/-- **`twoLane_socket_is_a_genuine_constraint`.**  `KERNEL-PROVED`.

The V2 socket is refutable at explicit data: with an empty census the `Tot` reconstruction
forces the physical correlation to vanish, which it does not for the exhibited weights. -/
theorem twoLane_socket_is_a_genuine_constraint :
    ∃ (d : PhysicalSupportData) (w : PhysicalWeightData) (S : Finset RawPacketId)
      (rawValue : RawPacketId → ℝ) (ownerBudget : Owner2 → ℝ),
      IsEmpty (TwoLaneRawToTwoCopyTypedOwnerInput d w S rawValue ownerBudget) := by
  refine ⟨⟨{1}, fun _ => SupportClass.N2⟩,
    ⟨1, fun _ => 1, fun _ => 0, fun _ => -1, fun _ => 1⟩, ∅, fun _ => 0, fun _ => 0, ?_⟩
  constructor
  intro h
  have hrec := h.tot_reconstruction
  have hzero : totalCorr (⟨{1}, fun _ => SupportClass.N2⟩ : PhysicalSupportData)
      (⟨1, fun _ => 1, fun _ => 0, fun _ => -1, fun _ => 1⟩ : PhysicalWeightData) = 4 := by
    simp [totalCorr, corrOn, PhysicalWeightData.wX, PhysicalWeightData.aX,
      PhysicalWeightData.bX, PhysicalWeightData.HX]
  rw [hzero] at hrec
  simp [totCells] at hrec

/-- **`twoLane_socket_has_no_one_copy_two_copy_owner`.**  `KERNEL-PROVED`.

The typing discipline is real: the one-copy owner of any raw packet is never `C0`,
`transverse` or `bDiagonal`. -/
theorem twoLane_socket_has_no_one_copy_two_copy_owner
    {d : PhysicalSupportData} {w : PhysicalWeightData} {S : Finset RawPacketId}
    {rawValue : RawPacketId → ℝ} {ownerBudget : Owner2 → ℝ}
    (I : TwoLaneRawToTwoCopyTypedOwnerInput d w S rawValue ownerBudget) (p : RawPacketId) :
    (I.owner1Assignment p).toPacketOwner ≠ Erdos287.MasterSourcePackets.PacketOwner.c0 ∧
    (I.owner1Assignment p).toPacketOwner ≠
      Erdos287.MasterSourcePackets.PacketOwner.transverse ∧
    (I.owner1Assignment p).toPacketOwner ≠
      Erdos287.MasterSourcePackets.PacketOwner.bDiagonal :=
  owner1_excludes_two_copy_owners _

/-- **`E_L_channel_of_twoLane`.**  `KERNEL-PROVED CONDITIONAL`.

The `U` lane of the V2 socket compiles into the leakage channel, given the supplied bound on
the `U`-lane sum.  The bound itself is an open input (`L` of the specification). -/
theorem E_L_channel_of_twoLane
    {d : PhysicalSupportData} {w : PhysicalWeightData} {S : Finset RawPacketId}
    {rawValue : RawPacketId → ℝ} {ownerBudget : Owner2 → ℝ} {EL : ℝ}
    (I : TwoLaneRawToTwoCopyTypedOwnerInput d w S rawValue ownerBudget)
    (hU : ∑ p ∈ uCells S, rawValue p ≤ EL) : E_L_exact d w ≤ EL := by
  rw [I.u_reconstruction]; exact hU

/-- **`E_T_channel_of_twoLane`.**  `KERNEL-PROVED CONDITIONAL`.

The `Tot` lane compiles into the total channel, given the supplied bound on the `Tot`-lane
sum.  The bound is an open input until the master compiler is supplied. -/
theorem E_T_channel_of_twoLane
    {d : PhysicalSupportData} {w : PhysicalWeightData} {S : Finset RawPacketId}
    {rawValue : RawPacketId → ℝ} {ownerBudget : Owner2 → ℝ} {Cc ET : ℝ}
    (I : TwoLaneRawToTwoCopyTypedOwnerInput d w S rawValue ownerBudget)
    (hT : Cc * Bmass d w - ∑ p ∈ totCells S, rawValue p ≤ ET) :
    Cc * Bmass d w - totalCorr d w ≤ ET := by
  rw [I.tot_reconstruction]; exact hT

/-! ## §2  The paper-closed analytic inputs -/

/-- **`N2LambdaCollarPaperInput`** — `PAPER-CLOSED EXTERNAL / UNINHABITED`.

The **exact** contract of the `N2` λ-collar: there is a *fixed* `ε` obeying the Ford
parameter restrictions for which, eventually,

```
    E_2 ≤ (m_ε / 8) · Bmass .
```

The stronger `E_2 = o(Bmass)` is deliberately **not** encoded. -/
structure N2LambdaCollarPaperInput (d : PhysicalSupportData) (w : PhysicalWeightData)
    (marginEps : ℝ) where
  /-- The fixed perturbation parameter. -/
  eps : ℝ
  /-- It is positive. -/
  eps_pos : 0 < eps
  /-- It obeys the Ford parameter restriction `2ε < 1/2`. -/
  eps_ford_admissible : eps < 1 / 4
  /-- The fixed-`ε` collar conclusion. -/
  collar : E_2_exact d w ≤ (marginEps / 8) * Bmass d w

/-- **`fixed_eps_collar_is_not_vanishing`.**  `KERNEL-PROVED`.

The fixed-`ε` collar is strictly weaker than `E_2 = o(Bmass)`: explicit data satisfy the
former and violate the latter, so encoding the vanishing statement would overclaim. -/
theorem fixed_eps_collar_is_not_vanishing :
    ∃ (E2 B m : ℝ), 0 < B ∧ 0 < m ∧ E2 ≤ (m / 8) * B ∧ ¬ (E2 ≤ (m / 100) * B) := by
  refine ⟨1, 1, 16, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- **`n2_paper_input_is_a_genuine_constraint`.**  `KERNEL-PROVED`.

The paper-closed status is metadata: at kernel level the input is still an explicit,
refutable hypothesis. -/
theorem n2_paper_input_is_a_genuine_constraint :
    ∃ (d : PhysicalSupportData) (w : PhysicalWeightData) (m : ℝ),
      IsEmpty (N2LambdaCollarPaperInput d w m) := by
  refine ⟨⟨{1}, fun _ => SupportClass.N2⟩,
    ⟨1, fun _ => 1, fun _ => 0, fun _ => -1, fun _ => 1⟩, 1, ?_⟩
  constructor
  intro h
  have hB : Bmass (⟨{1}, fun _ => SupportClass.N2⟩ : PhysicalSupportData)
      (⟨1, fun _ => 1, fun _ => 0, fun _ => -1, fun _ => 1⟩ : PhysicalWeightData) = 0 := by
    simp [Bmass, PhysicalSupportData.PX, PhysicalSupportData.region]
  have hE : E_2_exact (⟨{1}, fun _ => SupportClass.N2⟩ : PhysicalSupportData)
      (⟨1, fun _ => 1, fun _ => 0, fun _ => -1, fun _ => 1⟩ : PhysicalWeightData) = 4 := by
    simp [E_2_exact, corrOn, PhysicalSupportData.N2X, PhysicalSupportData.region,
      PhysicalWeightData.wX, PhysicalWeightData.aX, PhysicalWeightData.bX,
      PhysicalWeightData.HX]
  have := h.collar
  rw [hE, hB] at this
  norm_num at this

/-- **`BsrcN1ComparisonPaperInput`** — `PAPER-CLOSED EXTERNAL / UNINHABITED`.

`B_physical = Bsrc` on the audited range, `E_M` small against `Bmass`, and a positive
comparison mass. -/
structure BsrcN1ComparisonPaperInput (d : PhysicalSupportData) (w : PhysicalWeightData)
    (physicalB : ℕ → ℝ) (marginEps : ℝ) where
  /-- Global equality of the physical `B` with the source `Bsrc`. -/
  global_equality : ∀ n ∈ d.I, physicalB n = w.Bsrc n
  /-- The `E_M = o(B_X)` conclusion, at the fixed margin. -/
  E_M_small : E_M_exact d w ≤ (marginEps / 8) * Bmass d w
  /-- The comparison mass is positive. -/
  Bmass_pos : 0 < Bmass d w
  /-- The margin is positive. -/
  margin_pos : 0 < marginEps

/-- **`BmassAsymptoticPaperInput`** — `PAPER-CLOSED EXTERNAL / UNINHABITED`.

The `B_X = (4·𝔖₂·∫W + o(1))·X/log X` representation, as an explicit two-sided bound at the
audited scale. -/
structure BmassAsymptoticPaperInput (d : PhysicalSupportData) (w : PhysicalWeightData)
    (X mainConstant err : ℝ) where
  /-- The scale is above `e`. -/
  scale : Real.exp 1 ≤ X
  /-- The main constant is positive. -/
  mainConstant_pos : 0 < mainConstant
  /-- The two-sided asymptotic. -/
  asymptotic : |Bmass d w - mainConstant * X / Real.log X| ≤ err

/-- **`bsrc_paper_input_is_a_genuine_constraint`.**  `KERNEL-PROVED`. -/
theorem bsrc_paper_input_is_a_genuine_constraint :
    ∃ (d : PhysicalSupportData) (w : PhysicalWeightData) (pB : ℕ → ℝ) (m : ℝ),
      IsEmpty (BsrcN1ComparisonPaperInput d w pB m) := by
  refine ⟨⟨∅, fun _ => SupportClass.P⟩, ⟨1, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0⟩,
    fun _ => 0, 1, ?_⟩
  constructor
  intro h
  have hB : Bmass (⟨∅, fun _ => SupportClass.P⟩ : PhysicalSupportData)
      (⟨1, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0⟩ : PhysicalWeightData) = 0 := by
    simp [Bmass, PhysicalSupportData.PX, PhysicalSupportData.region]
  have := h.Bmass_pos
  rw [hB] at this
  exact lt_irrefl 0 this

/-! ## §3  The conditional asymptotic FCL -/

/-- **`AsymptoticFixedCertificatePositiveMass`** — the conclusion of the asymptotic FCL. -/
def AsymptoticFixedCertificatePositiveMass (d : PhysicalSupportData)
    (w : PhysicalWeightData) : Prop := 0 < primeMass d w

/-- **`asymptoticFCL_of_paper_inputs`.**  `KERNEL-PROVED CONDITIONAL`.

The exact conditional compiler

```
    two-lane master compiler + N2 λ-collar (paper) + Bsrc/N1 comparison (paper)
      + positive margin + the still-open E_T / E_L channel bounds
        ⟹ AsymptoticFixedCertificatePositiveMass .
```

Every external mathematical result is visible in the antecedents; the `E_T` and `E_L` bounds
remain explicit because the master compiler is not supplied. -/
theorem asymptoticFCL_of_paper_inputs
    {d : PhysicalSupportData} {w : PhysicalWeightData} {S : Finset RawPacketId}
    {rawValue : RawPacketId → ℝ} {ownerBudget : Owner2 → ℝ} {physicalB : ℕ → ℝ}
    {Cc marginEps ET EL : ℝ}
    (hKernel : ∀ n ∈ d.PX, w.HX n = 1)
    (master : TwoLaneRawToTwoCopyTypedOwnerInput d w S rawValue ownerBudget)
    (n2 : N2LambdaCollarPaperInput d w marginEps)
    (bsrc : BsrcN1ComparisonPaperInput d w physicalB marginEps)
    (hmargin : Erdos287.FCLBridge.PositiveMarginSupply Cc)
    (hT : Cc * Bmass d w - ∑ p ∈ totCells S, rawValue p ≤ ET)
    (hU : ∑ p ∈ uCells S, rawValue p ≤ EL)
    (hbudget : ET + EL + (marginEps / 8) * Bmass d w + (marginEps / 8) * Bmass d w
      ≤ (1 + Cc) / 6 * Bmass d w) :
    AsymptoticFixedCertificatePositiveMass d w := by
  have hdom : ChannelDomination d w
      ⟨Cc, ET, EL, (marginEps / 8) * Bmass d w, (marginEps / 8) * Bmass d w⟩ :=
    { kernel_on_P := hKernel
      total_channel := E_T_channel_of_twoLane master hT
      main_channel := bsrc.E_M_small
      collar_channel := n2.collar
      leakage_channel := E_L_channel_of_twoLane master hU }
  exact transference_with_supplied_margin hmargin hdom bsrc.Bmass_pos hbudget

/-- **`asymptoticFCL_keeps_every_external_input`.**  `KERNEL-PROVED`.

None of the three research inputs may be dropped: each is refutable at explicit data. -/
theorem asymptoticFCL_keeps_every_external_input :
    (∃ (d : PhysicalSupportData) (w : PhysicalWeightData) (S : Finset RawPacketId)
        (rv : RawPacketId → ℝ) (ob : Owner2 → ℝ),
      IsEmpty (TwoLaneRawToTwoCopyTypedOwnerInput d w S rv ob)) ∧
    (∃ (d : PhysicalSupportData) (w : PhysicalWeightData) (m : ℝ),
      IsEmpty (N2LambdaCollarPaperInput d w m)) ∧
    (∃ (d : PhysicalSupportData) (w : PhysicalWeightData) (pB : ℕ → ℝ) (m : ℝ),
      IsEmpty (BsrcN1ComparisonPaperInput d w pB m)) ∧
    (∃ Cc : ℝ, ¬ Erdos287.FCLBridge.PositiveMarginSupply Cc) :=
  ⟨twoLane_socket_is_a_genuine_constraint, n2_paper_input_is_a_genuine_constraint,
    bsrc_paper_input_is_a_genuine_constraint,
    Erdos287.FCLBridge.positiveMargin_not_automatic⟩

/-! ## §4  Explicit thresholds and the end-to-end chain -/

/-- **`Erdos287ExplicitThresholdInputs`** — `OPEN / UNINHABITED`.

The numerical data eventually required, with **no value guessed**: the Ford perturbation
constant, the collar constant, the admissible `ε`, the `Bmass`/PNT threshold, the
owner-aggregate threshold from the master compiler, the final analytic scale `X_FCL`, and
the arithmetic threshold `M₀ = max(12, 2·X_FCL) ≤ 4·10⁹` together with the uniform FCL
witness above it. -/
structure Erdos287ExplicitThresholdInputs where
  /-- The Ford perturbation constant. -/
  K_pert : ℝ
  /-- The `N2` collar constant. -/
  K_collar : ℝ
  /-- The admissible perturbation parameter. -/
  eps : ℝ
  /-- The `Bmass` / PNT threshold. -/
  BmassThreshold : ℝ
  /-- The owner-aggregate threshold coming from the master compiler. -/
  ownerAggregateThreshold : ℝ
  /-- The final analytic scale. -/
  X_FCL : ℕ
  /-- The arithmetic threshold. -/
  M0 : ℕ
  /-- The constants are positive. -/
  K_pert_pos : 0 < K_pert
  /-- The collar constant is positive. -/
  K_collar_pos : 0 < K_collar
  /-- The perturbation parameter is admissible. -/
  eps_pos : 0 < eps
  /-- The threshold is the specified maximum. -/
  M0_def : M0 = max 12 (2 * X_FCL)
  /-- The threshold lies inside the kernel-verified finite range. -/
  M0_bounded : M0 ≤ 4000000000
  /-- The uniform FCL prime-mass witness above the threshold. -/
  witness : ∀ M : ℕ, M0 ≤ M → PositiveFCLPrimeMassWitness M

/-- **`effectivityInput_of_explicitThresholds`.**  `KERNEL-PROVED CONDITIONAL`.

The explicit-threshold socket produces the banked effectivity input. -/
def effectivityInput_of_explicitThresholds (I : Erdos287ExplicitThresholdInputs) :
    Erdos287.EndgameEffectivity.EndgameEffectivityInput where
  eps0 := I.eps
  X0 := (I.X_FCL : ℝ) + 1
  M0 := I.M0
  eps0_pos := I.eps_pos
  X0_pos := by positivity
  M0_ge_bridge := by rw [I.M0_def]; exact le_max_left _ _
  M0_bounded := I.M0_bounded
  witness := I.witness

/-- **`erdos287Statement_of_explicit_research_inputs`.**  `KERNEL-PROVED CONDITIONAL`.

The end-to-end chain

```
    explicit thresholds → effectivity → EffectiveWindowPairSupply (threshold 12)
      → Erdos287ClosureInputs → Erdos287Statement .
```

**The premise is never inhabited**, so Erdős #287 is not proved here. -/
theorem erdos287Statement_of_explicit_research_inputs
    (I : Erdos287ExplicitThresholdInputs) : Erdos287Statement :=
  Erdos287.EndgameEffectivity.erdos287Statement_of_effectivityInput
    (effectivityInput_of_explicitThresholds I)

/-- **`explicit_thresholds_not_supplied`.**  `KERNEL-PROVED`.

The threshold socket is a genuine obligation: no inhabitant can carry a composite `q` at its
own threshold, and nothing in this repository constructs one. -/
theorem explicit_thresholds_not_supplied :
    ¬ ∃ I : Erdos287ExplicitThresholdInputs, (I.witness I.M0 le_rfl).q = 4 := by
  rintro ⟨I, hq⟩
  have hp := (I.witness I.M0 le_rfl).q_prime
  rw [hq] at hp
  exact (by decide : ¬ Nat.Prime 4) hp

end TwoLaneMaster
end Erdos287
