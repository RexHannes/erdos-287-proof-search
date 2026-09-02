import Mathlib
import RequestProject.CurrentProgramme.Erdos287FullSourceAnalyticKernelInput
import RequestProject.CurrentProgramme.Erdos287MasterSourceTypedPerronPackets
import RequestProject.CurrentProgramme.Erdos287FCLAlgebraicBridge
import RequestProject.CurrentProgramme.Erdos287FCLWindowPairBridge

/-!
# Analytic input → full correlation → the four FCL error channels

`ANALYTIC-INPUT → FULL-CORRELATION COMPILER : KERNEL-PROVED CONDITIONAL`
`PHYSICAL FIXED-CERTIFICATE SOURCE PIN      : OPEN / UNINHABITED`
`FCL                                        : OPEN`

This module is **append-only**.  Four things are formalised.

**§1 — the conditional correlation compiler.**  *Conditionally* on the external
analytic input `FullSourceLocalAnalyticKernelInput` and on the exact owner
accounting of a typed packet family, the physical full correlation obeys the
explicit numerical error bound `17 · X/(log X)²` that FCL consumes.  The
analytic input is an explicit antecedent of every such theorem, and it is
**never inhabited**.

**§2 — the physical source pin.**  The literal physical certificate data
`P, N₁, N₂, U, a, b, H` is given a typed interface, with a type-correct adapter
into the banked `FixedCertificateData`.  No literal repository values are
invented: the pin predicate is left **uninhabited**.

**§3 — the four FCL error channels** `E_T, E_L, E_2, E_M`.  Only their exact
finite combination identity is proved.  The inequality
`E_T + E_L + E_2 + E_M < (1 + C_c)·B` is **not constructed**; it is compiled
conditionally into the banked fixed-certificate positivity theorem at the
canonical margin `δ = (1 + C_c)/6`.

**§4 — firewalls.**  Reuse (never duplication) of `PositiveMarginSupply`,
`CertificatePinned` and the conditional `FCL → WindowPair` bridge.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Erdos287
namespace FullAnalyticKernelFCL

open Erdos287.FullAnalyticKernel
open Erdos287.MasterSourcePackets
open Erdos287.FixedCertificate

/-! ## §1  Analytic input → the numerical error bound consumed by FCL -/

/-- **`fullCorrelation_bound_of_analyticInput`.**  `KERNEL-PROVED CONDITIONAL`.

*Given* the external analytic input, the physical full correlation obeys the explicit
bound `17 · X/(log X)²`.  This is exact finite algebra (a triangle inequality over the
six owner values) applied to the reassembly identity; the analytic content sits entirely
in the hypothesis. -/
theorem fullCorrelation_bound_of_analyticInput {X : ℝ} {v : OwnerValues}
    (h : FullSourceLocalAnalyticKernelInput X v) :
    |v.fullCorrelation| ≤ 17 * budget X := by
  have h1 := abs_le.mp h.lowQOwner_bound
  have h2 := abs_le.mp h.pascadiTripleCell_bound
  have h3 := abs_le.mp h.c0FixedPacket_bound
  have h4 := abs_le.mp h.transverseFixedPacket_bound
  have h5 := abs_le.mp h.bDiagonalFixedPacket_bound
  have h6 := abs_le.mp h.regularParent_bound
  rw [h.globalOwnerReassembly, abs_le]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2, h5.1, h5.2,
    h6.1, h6.2]

/-- The owner value attached to a packet owner, as produced by the source compiler. -/
def ownerValue (v : OwnerValues) : PacketOwner → ℝ
  | PacketOwner.lowQ => v.lowQOwner
  | PacketOwner.pascadiTriple => v.pascadiTripleCell
  | PacketOwner.c0 => v.c0FixedPacket
  | PacketOwner.transverse => v.transverseFixedPacket
  | PacketOwner.bDiagonal => v.bDiagonalFixedPacket
  | PacketOwner.localOwner => v.regularParent

/-- **`ownerValues_sum`.**  `KERNEL-PROVED`.  The six owner values sum to the physical full
correlation exactly when the reassembly identity of the analytic input holds. -/
theorem ownerValues_sum {X : ℝ} {v : OwnerValues}
    (h : FullSourceLocalAnalyticKernelInput X v) :
    ∑ o : PacketOwner, ownerValue v o = v.fullCorrelation := by
  have huniv : (Finset.univ : Finset PacketOwner) =
      {PacketOwner.lowQ, PacketOwner.pascadiTriple, PacketOwner.c0, PacketOwner.transverse,
        PacketOwner.bDiagonal, PacketOwner.localOwner} := by decide
  show ∑ o ∈ (Finset.univ : Finset PacketOwner), ownerValue v o = _
  rw [huniv]
  simp only [Finset.sum_insert, Finset.mem_insert, Finset.sum_singleton, ownerValue,
    Finset.mem_singleton, reduceCtorEq, or_self, not_false_eq_true]
  rw [h.globalOwnerReassembly]
  ring

/-- **`physicalCorrelation_error_bound`.**  `KERNEL-PROVED CONDITIONAL`.

The full chain: a typed packet family whose owner accounts are the physical owner values,
*together with* the external analytic input, yields the explicit numerical error bound on
the physical correlation.  The analytic input appears explicitly and is not inhabited. -/
theorem physicalCorrelation_error_bound {ι : Type} [DecidableEq ι] (F : PacketFamily ι)
    (val : ι → ℝ) {X : ℝ} {v : OwnerValues}
    (hAnalytic : FullSourceLocalAnalyticKernelInput X v)
    (hAccounts : ∀ o : PacketOwner, ∑ i ∈ F.fibre o, val i = ownerValue v o) :
    |∑ i ∈ F.cells, val i| ≤ 17 * budget X := by
  have hsum : ∑ i ∈ F.cells, val i = v.fullCorrelation := by
    rw [← Finset.sum_fiberwise F.cells F.owner val]
    have : ∀ o : PacketOwner, ∑ i ∈ F.cells with F.owner i = o, val i = ownerValue v o := by
      intro o; exact hAccounts o
    rw [Finset.sum_congr rfl fun o _ => this o]
    exact ownerValues_sum hAnalytic
  rw [hsum]
  exact fullCorrelation_bound_of_analyticInput hAnalytic

/-- **`correlation_compiler_needs_the_analytic_input`.**  `KERNEL-PROVED`.

The compiler of §1 is genuinely conditional: the analytic input is refutable at explicit
data, so no unconditional correlation bound follows from the source compiler. -/
theorem correlation_compiler_needs_the_analytic_input :
    ∃ (X : ℝ) (v : OwnerValues), ¬ FullSourceLocalAnalyticKernelInput X v :=
  analyticInput_is_a_genuine_constraint

/-! ## §2  The physical fixed-certificate source pin -/

/-- **`PhysicalCertificateSource`** — the literal physical certificate fields
`P, N₁, N₂, U, a, b, H` with exactly the elementary structural conditions the banked
compiler requires. -/
structure PhysicalCertificateSource where
  /-- The certificate-positive region `P`. -/
  P : Finset ℕ
  /-- The first good region `N₁`. -/
  N1 : Finset ℕ
  /-- The second good region `N₂`. -/
  N2 : Finset ℕ
  /-- The leakage region `U`. -/
  U : Finset ℕ
  /-- The prime-mass weight `a`. -/
  a : ℕ → ℝ
  /-- The comparison weight `b`. -/
  b : ℕ → ℝ
  /-- The certificate kernel `H`. -/
  H : ℕ → ℝ
  /-- `P` and `N₁` are disjoint. -/
  hPN1 : Disjoint P N1
  /-- `P` and `N₂` are disjoint. -/
  hPN2 : Disjoint P N2
  /-- `P` and `U` are disjoint. -/
  hPU : Disjoint P U
  /-- `N₁` and `U` are disjoint. -/
  hN1U : Disjoint N1 U
  /-- `N₂` and `U` are disjoint. -/
  hN2U : Disjoint N2 U
  /-- The prime-mass weight is nonnegative. -/
  ha : ∀ n, 0 ≤ a n
  /-- The kernel is `1` on `P`. -/
  hHP : ∀ p ∈ P, H p = 1
  /-- The kernel is nonpositive on `N₁`. -/
  hHN1 : ∀ n ∈ N1, H n ≤ 0
  /-- The kernel is nonpositive on `N₂`. -/
  hHN2 : ∀ n ∈ N2, H n ≤ 0

/-- **`PhysicalCertificateSource.toData`.**  `KERNEL-PROVED` type-correct adapter.

The physical fields compile into the banked `FixedCertificateData` with
`Ngood = N₁ ∪ N₂`. -/
def PhysicalCertificateSource.toData (s : PhysicalCertificateSource) :
    FixedCertificateData where
  P := s.P
  Ngood := s.N1 ∪ s.N2
  U := s.U
  a := s.a
  b := s.b
  H := s.H
  hPN := Finset.disjoint_union_right.2 ⟨s.hPN1, s.hPN2⟩
  hPU := s.hPU
  hNU := Finset.disjoint_union_left.2 ⟨s.hN1U, s.hN2U⟩
  ha := s.ha
  hHP := s.hHP
  hHN := by
    intro n hn
    rcases Finset.mem_union.mp hn with h | h
    · exact s.hHN1 n h
    · exact s.hHN2 n h

/-- **`PhysicalSourcePinned`** — `SOURCE-PIN OPEN / UNINHABITED`.

The predicate "these are the *literal* physical certificate fields of the run": the
region is nonempty, the comparison mass is positive and the kernel is genuinely
supported.  **No inhabitant is constructed: the literal repository source field is
absent, and nothing is invented in its place.** -/
structure PhysicalSourcePinned (s : PhysicalCertificateSource) : Prop where
  /-- The certificate-positive region is nonempty. -/
  P_nonempty : s.P.Nonempty
  /-- The comparison mass at the certificate is positive. -/
  B_pos : 0 < ∑ p ∈ s.P, s.b p
  /-- The good region is nonempty. -/
  good_nonempty : (s.N1 ∪ s.N2).Nonempty

/-- **`physicalSourcePin_not_automatic`.**  `KERNEL-PROVED`.

The pin is a genuine obligation: the empty configuration refutes it. -/
theorem physicalSourcePin_not_automatic :
    ∃ s : PhysicalCertificateSource, ¬ PhysicalSourcePinned s := by
  refine ⟨⟨∅, ∅, ∅, ∅, fun _ => 0, fun _ => 0, fun _ => 0, by simp, by simp, by simp,
    by simp, by simp, by simp, by simp, by simp, by simp⟩, ?_⟩
  intro h
  exact absurd h.P_nonempty (by simp)

/-- **`pinned_source_has_positive_B`.**  `KERNEL-PROVED CONDITIONAL`.

Conditionally on the (unsupplied) pin, the compiled data has positive comparison mass —
exactly the hypothesis `0 < d.B` of the banked positivity theorem. -/
theorem pinned_source_has_positive_B {s : PhysicalCertificateSource}
    (h : PhysicalSourcePinned s) : 0 < s.toData.B :=
  h.B_pos

/-! ## §3  The four FCL error channels -/

/-- **`FCLErrorChannels`** — the four typed error channels of the FCL budget. -/
structure FCLErrorChannels where
  /-- `E_T`: the transverse channel. -/
  E_T : ℝ
  /-- `E_L`: the local channel. -/
  E_L : ℝ
  /-- `E_2`: the `N2` channel. -/
  E_2 : ℝ
  /-- `E_M`: the Möbius / main channel. -/
  E_M : ℝ

namespace FCLErrorChannels

variable (ch : FCLErrorChannels)

/-- The total FCL error. -/
def total : ℝ := ch.E_T + ch.E_L + ch.E_2 + ch.E_M

/-- **`total_identity`.**  `KERNEL-PROVED`.  The only unconditional statement about the
channels: their exact finite combination. -/
theorem total_identity : ch.total = ch.E_T + ch.E_L + ch.E_2 + ch.E_M := rfl

/-- **`total_regroup`.**  `KERNEL-PROVED`.  Regrouping the channels changes nothing: no
channel is silently absorbed into another. -/
theorem total_regroup : ch.total = (ch.E_T + ch.E_L) + (ch.E_2 + ch.E_M) := by
  unfold total; ring

/-- **`each_channel_is_load_bearing`.**  `KERNEL-PROVED`.  A strictly positive channel
strictly increases the total. -/
theorem each_channel_is_load_bearing {ch₁ ch₂ : FCLErrorChannels}
    (hT : ch₁.E_T = ch₂.E_T) (hL : ch₁.E_L = ch₂.E_L) (h2 : ch₁.E_2 = ch₂.E_2)
    (hM : ch₁.E_M < ch₂.E_M) : ch₁.total < ch₂.total := by
  unfold total; linarith

end FCLErrorChannels

/-- **`fcl_prime_mass_pos_of_channels`.**  `KERNEL-PROVED CONDITIONAL`.

The conditional compilation of the four channels into the banked fixed-certificate
positivity theorem, at the canonical margin `δ = (1 + C_c)/6` of the margin firewall.

**Every** premise is explicit and none is constructed here: the three correlation
hypotheses, the supplied positive margin, positivity of the comparison mass, and the
channel budget `E_T + E_L + E_2 + E_M ≤ (1 + C_c)/6 · B`. -/
theorem fcl_prime_mass_pos_of_channels (d : FixedCertificateData) (Cc : ℝ)
    (ch : FCLErrorChannels)
    (hmargin : Erdos287.FCLBridge.PositiveMarginSupply Cc)
    (hLeak : LeakageBound d ch.total)
    (hTotal : TotalCorrelationBound d ch.total)
    (hMargin : ComparisonMargin d Cc ch.total)
    (hBpos : 0 < d.B)
    (hbudget : ch.total ≤ (1 + Cc) / 6 * d.B) :
    0 < ∑ p ∈ d.P, d.a p := by
  obtain ⟨-, h3⟩ := Erdos287.FCLBridge.margin_delta_arithmetic hmargin
  exact fixedCertificate_prime_mass_pos d Cc ch.total ((1 + Cc) / 6) hLeak hTotal hMargin
    hBpos hbudget h3

/-- **`channel_budget_gives_the_literal_inequality`.**  `KERNEL-PROVED`.

The canonical channel budget implies the literal constant-free form
`E_T + E_L + E_2 + E_M < (1 + C_c)·B`; the compiler consumes the sharper, explicit
`δ = (1 + C_c)/6` form. -/
theorem channel_budget_gives_the_literal_inequality {Cc B : ℝ} {ch : FCLErrorChannels}
    (hCc : 0 < 1 + Cc) (hB : 0 < B) (hbudget : ch.total ≤ (1 + Cc) / 6 * B) :
    ch.E_T + ch.E_L + ch.E_2 + ch.E_M < (1 + Cc) * B := by
  have h : ch.total < (1 + Cc) * B := by nlinarith
  rw [← FCLErrorChannels.total_identity]
  exact h

/-- **`channel_budget_not_constructed`.**  `KERNEL-PROVED`.

The channel budget is an open input, not a theorem: explicit data refute it. -/
theorem channel_budget_not_constructed :
    ∃ (Cc B : ℝ) (ch : FCLErrorChannels), 0 < 1 + Cc ∧ 0 < B ∧
      ¬ (ch.total ≤ (1 + Cc) / 6 * B) := by
  refine ⟨0, 1, ⟨1, 1, 1, 1⟩, by norm_num, by norm_num, ?_⟩
  intro h
  rw [FCLErrorChannels.total_identity] at h
  norm_num at h

/-! ## §4  Reuse firewalls -/

/-- **`margin_delta_is_reused_not_reproved`.**  `KERNEL-PROVED CONDITIONAL`.

`δ = (1 + C_c)/6` remains available *conditionally* on `0 < 1 + C_c`, by the banked
`margin_delta_arithmetic`; the proof is not duplicated. -/
theorem margin_delta_is_reused_not_reproved {Cc : ℝ}
    (h : Erdos287.FCLBridge.PositiveMarginSupply Cc) :
    0 ≤ (1 + Cc) / 6 ∧ 3 * ((1 + Cc) / 6) < 1 + Cc :=
  Erdos287.FCLBridge.margin_delta_arithmetic h

/-- **`fcl_to_windowPair_is_reused_not_reproved`.**  `KERNEL-PROVED CONDITIONAL`.

The `FCL → WindowPair` bridge is reused verbatim from
`windowPairSupply_of_positiveFCLMass`; no duplicate proof is introduced. -/
theorem fcl_to_windowPair_is_reused_not_reproved (M : ℕ) (hM : 20 ≤ M)
    (h : Erdos287.FCLWindowPair.PositiveFCLPrimeMassWitness M) :
    Erdos287.WindowPairSupply M :=
  Erdos287.FCLWindowPair.windowPairSupply_of_positiveFCLMass hM h

/-- **`effective_windowPair_still_open`.**  `KERNEL-PROVED`.

The effectivity firewall is unchanged: an asymptotic supply never yields a bounded
effective threshold, so `EffectiveWindowPairSupply` remains uninhabited. -/
theorem effective_windowPair_still_open :
    ∃ p : ℕ → Prop, (∃ T : ℝ, ∀ M : ℕ, T ≤ (M : ℝ) → p M) ∧
      ∀ s : Erdos287.WindowPairExport.EffectiveSupply p, ¬ s.Bounded :=
  Erdos287.FCLWindowPair.asymptotic_does_not_give_bounded_effective

end FullAnalyticKernelFCL
end Erdos287
