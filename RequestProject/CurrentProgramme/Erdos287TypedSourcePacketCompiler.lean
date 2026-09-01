import RequestProject.CurrentProgramme.Erdos287PerronSingleContour
import RequestProject.CurrentProgramme.Erdos287MasterSourceInterface

/-!
# Erdős #287 — typed source packets: data structure and conditional compiler

This module provides a **generic** typed packet decomposition together with a
deterministic, kernel-proved compiler.  It is a *conditional* compiler: every analytic
quantity it consumes is an explicit hypothesis or structure field.  Nothing here is claimed
to be the actual Erdős #287 source, and nothing here constructs the missing master physical
source: the bridge to the physical source is the uninhabited interface of
`Erdos287MasterSourceInterface`.

Design points demanded by the source-census audit and implemented here:

* the decomposition carries a finite discrete index set, per-packet continuous parameter
  data (as a finite surrogate), coefficients `c η`, packet values `S η`, an error term `E`
  and an **exact** reconstruction identity;
* the **global** field `totalNuclearMass ≤ nuclearBudget` is *source data*, an explicit
  field of the structure.  It is deliberately **not** derived from the packetwise bounds:
  `packetwise_coefficient_bound_does_not_bound_total` proves that no such derivation is
  possible without cardinality control;
* the compiler concludes `‖source‖ ≤ nuclear · packetBound + errorBound`, and the
  logarithmic specialisation uses the single-contour `L¹` budget as the packet bound.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Erdos287
namespace TypedPackets

/-! ## §1  The deterministic compiler, in hypothesis form -/

/-- **`typedPacket_compile`.**  `LEAN_PROVED`.  The deterministic packet compiler:
from an exact reconstruction identity, a **global** nuclear mass bound, a uniform packet
bound and an error bound, one gets `‖source‖ ≤ nuclear · packetBound + errorBound`. -/
theorem typedPacket_compile {ι : Type*} (I : Finset ι) (c S : ι → ℂ) (E source : ℂ)
    (nuclear packetBound errorBound : ℝ)
    (hrec : source = ∑ eta ∈ I, c eta * S eta + E)
    (hnuclear : ∑ eta ∈ I, ‖c eta‖ ≤ nuclear)
    (hpacket : ∀ eta ∈ I, ‖S eta‖ ≤ packetBound)
    (hpacket_nonneg : 0 ≤ packetBound)
    (herror : ‖E‖ ≤ errorBound) :
    ‖source‖ ≤ nuclear * packetBound + errorBound := by
  have hmain : ‖∑ eta ∈ I, c eta * S eta‖ ≤ nuclear * packetBound := by
    calc ‖∑ eta ∈ I, c eta * S eta‖ ≤ ∑ eta ∈ I, ‖c eta * S eta‖ := norm_sum_le _ _
      _ = ∑ eta ∈ I, ‖c eta‖ * ‖S eta‖ := Finset.sum_congr rfl fun eta _ => norm_mul _ _
      _ ≤ ∑ eta ∈ I, ‖c eta‖ * packetBound := by
          refine Finset.sum_le_sum fun eta heta => ?_
          exact mul_le_mul_of_nonneg_left (hpacket eta heta) (norm_nonneg _)
      _ = (∑ eta ∈ I, ‖c eta‖) * packetBound := by rw [Finset.sum_mul]
      _ ≤ nuclear * packetBound := mul_le_mul_of_nonneg_right hnuclear hpacket_nonneg
  calc ‖source‖ = ‖∑ eta ∈ I, c eta * S eta + E‖ := by rw [hrec]
    _ ≤ ‖∑ eta ∈ I, c eta * S eta‖ + ‖E‖ := norm_add_le _ _
    _ ≤ nuclear * packetBound + errorBound := by linarith

/-! ## §2  The typed packet decomposition structure -/

/-- **A typed source-packet decomposition.**  A finite discrete index set, per-index
continuous parameter data (a finite surrogate for the analytic parameters; the genuine
integral layer is kept separate, see `PerronContour.SingleContourL1Bound`), coefficients,
packet values, an error term, an exact reconstruction identity, and the **explicit global**
nuclear-mass field. -/
structure SourcePacketDecomposition where
  /-- The finite discrete packet index set. -/
  I : Finset ℕ
  /-- Continuous parameter data attached to each packet (finite surrogate). -/
  contParam : ℕ → ℝ
  /-- Packet coefficients. -/
  c : ℕ → ℂ
  /-- Packet values. -/
  S : ℕ → ℂ
  /-- The error term. -/
  E : ℂ
  /-- The decomposed quantity. -/
  source : ℂ
  /-- **Exact** reconstruction identity. -/
  reconstruction : source = ∑ eta ∈ I, c eta * S eta + E
  /-- The nuclear budget. -/
  nuclearBudget : ℝ
  /-- The **global** total nuclear mass — an explicit field, i.e. source data. -/
  totalNuclearMass : ℝ
  /-- The global total nuclear mass is what its name says. -/
  totalNuclearMass_eq : totalNuclearMass = ∑ eta ∈ I, ‖c eta‖
  /-- **Global** nuclear-mass field: to be supplied, never derived packetwise. -/
  totalNuclearMass_le : totalNuclearMass ≤ nuclearBudget
  /-- The uniform packet bound. -/
  packetBound : ℝ
  /-- Non-negativity of the packet bound. -/
  packetBound_nonneg : 0 ≤ packetBound
  /-- Every packet is within the packet bound. -/
  packet_le : ∀ eta ∈ I, ‖S eta‖ ≤ packetBound
  /-- The error budget. -/
  errorBound : ℝ
  /-- The error term is within budget. -/
  error_le : ‖E‖ ≤ errorBound

namespace SourcePacketDecomposition

/-- **`SourcePacketDecomposition.compile`.**  `LEAN_PROVED`.  The complete conditional
packet compiler: `‖source‖ ≤ nuclearBudget · packetBound + errorBound`. -/
theorem compile (P : SourcePacketDecomposition) :
    ‖P.source‖ ≤ P.nuclearBudget * P.packetBound + P.errorBound := by
  refine typedPacket_compile P.I P.c P.S P.E P.source P.nuclearBudget P.packetBound
    P.errorBound P.reconstruction ?_ P.packet_le P.packetBound_nonneg P.error_le
  have := P.totalNuclearMass_le
  rw [P.totalNuclearMass_eq] at this
  exact this

end SourcePacketDecomposition

/-! ## §3  Logarithmic budget specialisation (abstract) -/

/-- **`typedPacket_compile_logBudget`.**  `LEAN_PROVED`.  Log-budget specialisation: if
each packet is bounded by the `L¹` mass of a single Perron contour, the compiler gives
`‖source‖ ≤ nuclear · (2 log (1 + 2T/c)) + errorBound`.  Purely deterministic: no
asymptotic source theorem is asserted. -/
theorem typedPacket_compile_logBudget {ι : Type*} (I : Finset ι) (c S : ι → ℂ)
    (E source : ℂ) (nuclear errorBound : ℝ) (B : PerronContour.SingleContourL1Bound)
    (hrec : source = ∑ eta ∈ I, c eta * S eta + E)
    (hnuclear : ∑ eta ∈ I, ‖c eta‖ ≤ nuclear) (hnuclear_nonneg : 0 ≤ nuclear)
    (hpacket : ∀ eta ∈ I, ‖S eta‖ ≤ ∫ t in (-B.T)..B.T, (Real.sqrt (B.c ^ 2 + t ^ 2))⁻¹)
    (herror : ‖E‖ ≤ errorBound) :
    ‖source‖ ≤ nuclear * B.bound + errorBound := by
  have hmass_nonneg : (0 : ℝ) ≤ ∫ t in (-B.T)..B.T, (Real.sqrt (B.c ^ 2 + t ^ 2))⁻¹ := by
    rcases I.eq_empty_or_nonempty with rfl | ⟨eta, heta⟩
    · rw [PerronContour.singleContour_integral_eq_arsinh B.c B.T B.c_pos]
      have : (0 : ℝ) ≤ Real.arsinh (B.T / B.c) := by
        rw [← Real.arsinh_zero]
        exact Real.arsinh_le_arsinh.2 (div_nonneg B.T_nonneg B.c_pos.le)
      linarith
    · exact le_trans (norm_nonneg (S eta)) (hpacket eta heta)
  have hstep := typedPacket_compile I c S E source nuclear
    (∫ t in (-B.T)..B.T, (Real.sqrt (B.c ^ 2 + t ^ 2))⁻¹) errorBound hrec hnuclear hpacket
    hmass_nonneg herror
  have : nuclear * (∫ t in (-B.T)..B.T, (Real.sqrt (B.c ^ 2 + t ^ 2))⁻¹)
      ≤ nuclear * B.bound := mul_le_mul_of_nonneg_left B.l1_le hnuclear_nonneg
  linarith

/-! ## §4  The global mass field is not packetwise data -/

/-- **`packetwise_coefficient_bound_does_not_bound_total`.**  `LEAN_PROVED`.  For every
proposed global nuclear budget `N` there is a finite packet family whose coefficients all
satisfy `‖c η‖ ≤ 1` and whose **total** nuclear mass exceeds `N`.  Hence the global field
`totalNuclearMass ≤ nuclearBudget` is genuine source data and cannot be derived from
`∀ η, packetMass η ≤ B`. -/
theorem packetwise_coefficient_bound_does_not_bound_total (N : ℝ) :
    ∃ (I : Finset ℕ) (c : ℕ → ℂ),
      (∀ eta ∈ I, ‖c eta‖ ≤ 1) ∧ N < ∑ eta ∈ I, ‖c eta‖ := by
  obtain ⟨n, hn⟩ := exists_nat_gt N
  refine ⟨Finset.range n, fun _ => 1, fun eta _ => by simp, ?_⟩
  simpa using hn

/-- Same statement in the shape used by the audit: no function of the packetwise bound
alone can serve as a nuclear budget. -/
theorem no_nuclearBudget_from_packetwise_bound :
    ¬ ∃ N : ℝ, ∀ (I : Finset ℕ) (c : ℕ → ℂ),
        (∀ eta ∈ I, ‖c eta‖ ≤ 1) → ∑ eta ∈ I, ‖c eta‖ ≤ N := by
  rintro ⟨N, hN⟩
  obtain ⟨I, c, hc, hlt⟩ := packetwise_coefficient_bound_does_not_bound_total N
  exact absurd (hN I c hc) (not_le.2 hlt)

/-! ## §5  Scope firewall: the compiler is not the source theorem -/

/-- **`typedPacketCompiler_does_not_construct_masterSource`.**  The packet compiler is a
deterministic implication.  Owning it (indeed, owning a fully populated typed packet
decomposition) does not construct a master physical source realisation: for the
countermodel spec the realisation type is empty while packet decompositions exist. -/
theorem typedPacketCompiler_does_not_construct_masterSource
    (P : SourcePacketDecomposition) :
    ‖P.source‖ ≤ P.nuclearBudget * P.packetBound + P.errorBound ∧
      ¬ Nonempty (MasterSource.MasterPhysicalSourceRealisation
        MasterSource.vanishingWeightSpec) :=
  ⟨P.compile, MasterSource.no_realisation_vanishingWeightSpec⟩

/-- A populated typed packet decomposition exists (the structure is not vacuous): the
trivial one-packet decomposition of `0`. -/
def trivialDecomposition : SourcePacketDecomposition where
  I := {0}
  contParam := fun _ => 0
  c := fun _ => 0
  S := fun _ => 0
  E := 0
  source := 0
  reconstruction := by simp
  nuclearBudget := 0
  totalNuclearMass := 0
  totalNuclearMass_eq := by simp
  totalNuclearMass_le := le_rfl
  packetBound := 0
  packetBound_nonneg := le_rfl
  packet_le := by intro eta _; simp
  errorBound := 0
  error_le := by simp

end TypedPackets
end Erdos287
