import Mathlib
import RequestProject.CurrentProgramme.Erdos287StrictCellProductWeightBridge
import RequestProject.CurrentProgramme.Erdos287StrictCellSemanticRepair
import RequestProject.CurrentProgramme.Erdos287RepeatedPrimePhysicalSource
import RequestProject.CurrentProgramme.Erdos287WeightedSP2PhysicalSource
import RequestProject.CurrentProgramme.Erdos287PhysicalBComparisonV2

/-!
# Semantic repair layer §5 — the corrected physical bridge `V2`

The older interface

```
    BalancedSevenSP2StrictCellProductWeightPhysicalBridge
```

is **preserved unchanged** (it is a valid *abstract sufficient* interface).  It is however
no longer the current physical dictionary, because three of its fields were provisional
abstractions:

* `slotBox_weight : Dat.omega i p = sp2Omega C i p` — a *bare indicator*, superseded by the
  full weighted slot factor `omegaPhysical` (`Erdos287WeightedSP2PhysicalSource`);
* `ford_H_binding : Hphys = hStar U` — the *combinatorial surrogate*, superseded by the
  literal `FordHPhysicalBinding` (`Erdos287StrictCellSemanticRepair`);
* `routing : repeated-prime vectors carry no weight` — superseded: repeated labelled primes
  are physical source points and the repeated-prime sector is included *exactly*
  (`Erdos287RepeatedPrimePhysicalSource`).

`BalancedSevenSP2PhysicalBridgeV2` is the corrected interface.  Its `B`-field is the
independent finite `Bsrc(S₂,·)` source rather than a free real constant, and it carries **no
rank-one / kernel-separability field at all**: the direct product source supplies no such
assumption, so none is assumed.

**`BalancedSevenSP2PhysicalBridgeV2` is left uninhabited**: no inhabitant is constructed
here, and `bridgeV2_not_automatic` exhibits data refuting it.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Erdos287
namespace PhysicalBridgeV2

open Finset
open Erdos287.SP2Source
open Erdos287.V21PrimeBox
open Erdos287.SP2PrimeBox
open Erdos287.StrictCellSingleton
open Erdos287.StrictCellBridge
open Erdos287.SemanticRepair
open Erdos287.RepeatedPrime
open Erdos287.WeightedSP2
open Erdos287.BComparisonV2

/-! ## §1.  The corrected bridge -/

/-- **`BalancedSevenSP2PhysicalBridgeV2`** — `SOURCE_OPEN / UNINHABITED`.

The source-correct successor of the product-weight physical bridge:

* a literal ordered seven-slot physical cell (`slot_cell`);
* the **full weighted** slot factors, not bare indicators (`slot_weight`);
* a product / fixed-nuclear vector source (`weight_form`);
* the literal Ford-`H` physical binding (`ford_binding`), not the combinatorial surrogate;
* the literal Ford cutoff applied to the cell (`cutoff_literal`);
* an *independent* finite `Bsrc` binding (`Bsrc_range`, `B_binding`);
* repeated-prime **ownership**: repeated labelled primes remain physical source points and
  the Ford functional on them is the exact finite `Hrepeat` value (`repeated_ownership`);
* no rank-one / separability assumption beyond what the direct source provides — the
  structure has no such field. -/
structure BalancedSevenSP2PhysicalBridgeV2
    (C : SP2FixedCertificateData) (U : Finset (Fin 7)) (S : PhysicalSlotData)
    (Dat : PrimeBoxData) (w : (Fin 7 → ℕ) → ℤ) (Pset : Finset ℕ) (Hphys : ℕ → ℤ)
    (gammaStar : ℝ) (cut : ℕ → ℕ) (S2 : ℝ) : Prop where
  /-- Literal ordered seven-slot physical cell. -/
  slot_cell : ∀ i : Fin 7, Dat.box i = C.lam i
  /-- Full weighted slot factors (smooth profile and archimedean twist included). -/
  slot_weight : ∀ (i : Fin 7) (p : ℕ), Dat.omega i p = omegaPhysical C S i p
  /-- The strict-cell hypotheses of the certificate and branch label. -/
  strict_cell : StrictCellHypotheses C U
  /-- Product or fixed-nuclear vector source. -/
  weight_form :
    (∃ f : Fin 7 → ℕ → ℤ, ∀ v ∈ cellVectors C, w v = productWeight f v) ∨
      (∃ c : ℤ, ∀ v ∈ cellVectors C, w v = c)
  /-- The **literal** Ford-`H` physical binding. -/
  ford_binding : FordHPhysicalBinding Pset Hphys gammaStar cut
  /-- The literal cutoff binding on the physical cell. -/
  cutoff_literal : ∀ (i : Fin 7), ∀ p ∈ C.lam i, p ≤ cut (∏ p ∈ Pset, p)
  /-- The singular parameter of the independent `B` source lies in its admissible range. -/
  S2_range : 0 < S2 ∧ S2 < 1
  /-- The independent finite `Bsrc` binding. -/
  B_binding : ∀ v ∈ cellVectors C, |(w v : ℝ)| ≤ Bsrc S2 (pushforward v)
  /-- Repeated-prime ownership: repeated labelled primes are kept, and the Ford functional
  at a cell point is the exact finite repeated-prime value of its distinct-prime count. -/
  repeated_ownership : ∀ v ∈ cellVectors C,
    Hphys (pushforward v) = Hrepeat (distinctPrimeCount v)

/-! ## §2.  Consequences, conditional on `V2` -/

/-- Conditional on `V2`: the slot coefficients obey the pointwise law. -/
theorem bridgeV2_slot_pointwise {C : SP2FixedCertificateData} {U : Finset (Fin 7)}
    {S : PhysicalSlotData} {Dat : PrimeBoxData} {w : (Fin 7 → ℕ) → ℤ} {Pset : Finset ℕ}
    {Hphys : ℕ → ℤ} {gammaStar : ℝ} {cut : ℕ → ℕ} {S2 : ℝ}
    (h : BalancedSevenSP2PhysicalBridgeV2 C U S Dat w Pset Hphys gammaStar cut S2)
    (i : Fin 7) (p : ℕ) : ‖Dat.omega i p‖ ≤ 1 := by
  rw [h.slot_weight i p]; exact norm_omegaPhysical_le_one C S i p

/-- Conditional on `V2`: the literal Ford functional of the seven physical primes is `−20`.
This is derived from the *physical* binding, never from the combinatorial surrogate. -/
theorem bridgeV2_fordH_eq_neg_twenty {C : SP2FixedCertificateData} {U : Finset (Fin 7)}
    {S : PhysicalSlotData} {Dat : PrimeBoxData} {w : (Fin 7 → ℕ) → ℤ} {Pset : Finset ℕ}
    {Hphys : ℕ → ℤ} {gammaStar : ℝ} {cut : ℕ → ℕ} {S2 : ℝ}
    (h : BalancedSevenSP2PhysicalBridgeV2 C U S Dat w Pset Hphys gammaStar cut S2) :
    Hphys (∏ p ∈ Pset, p) = -20 :=
  fordH_physical_eq_neg_twenty h.ford_binding

/-- Conditional on `V2`: the cell weights are bounded by the finite `B` source, hence by
`128`, whenever the modulus of the cell point has at most seven prime factors. -/
theorem bridgeV2_weight_lt_128 {C : SP2FixedCertificateData} {U : Finset (Fin 7)}
    {S : PhysicalSlotData} {Dat : PrimeBoxData} {w : (Fin 7 → ℕ) → ℤ} {Pset : Finset ℕ}
    {Hphys : ℕ → ℤ} {gammaStar : ℝ} {cut : ℕ → ℕ} {S2 : ℝ}
    (h : BalancedSevenSP2PhysicalBridgeV2 C U S Dat w Pset Hphys gammaStar cut S2)
    {v : Fin 7 → ℕ} (hv : v ∈ cellVectors C)
    (hP : (pushforward v).primeFactors.card ≤ 7) : |(w v : ℝ)| < 128 :=
  lt_of_le_of_lt (h.B_binding v hv) (Bsrc_lt_128 h.S2_range.2 hP)

/-- Conditional on `V2`: a cell point with a repeated labelled prime is **kept**, and its
Ford value is the exact finite repeated-prime constant.  For six distinct primes this is
`−10`, not `0`: the repeated sector is included exactly. -/
theorem bridgeV2_repeated_included {C : SP2FixedCertificateData} {U : Finset (Fin 7)}
    {S : PhysicalSlotData} {Dat : PrimeBoxData} {w : (Fin 7 → ℕ) → ℤ} {Pset : Finset ℕ}
    {Hphys : ℕ → ℤ} {gammaStar : ℝ} {cut : ℕ → ℕ} {S2 : ℝ}
    (h : BalancedSevenSP2PhysicalBridgeV2 C U S Dat w Pset Hphys gammaStar cut S2)
    {v : Fin 7 → ℕ} (hv : v ∈ cellVectors C) (hsix : distinctPrimeCount v = 6) :
    Hphys (pushforward v) = -10 := by
  rw [h.repeated_ownership v hv, hsix]
  exact Hrepeat_six

/-! ## §3.  Firewalls -/

/-- **`bridgeV2_not_automatic`.**  `LEAN_PROVED`.

`V2` is a genuine source obligation: explicit data refute it, so no compiler manufactures an
inhabitant and none is constructed here. -/
theorem bridgeV2_not_automatic :
    ∃ (C : SP2FixedCertificateData) (U : Finset (Fin 7)) (S : PhysicalSlotData)
      (Dat : PrimeBoxData) (w : (Fin 7 → ℕ) → ℤ) (Pset : Finset ℕ) (Hphys : ℕ → ℤ)
      (gammaStar : ℝ) (cut : ℕ → ℕ) (S2 : ℝ),
      ¬ BalancedSevenSP2PhysicalBridgeV2 C U S Dat w Pset Hphys gammaStar cut S2 := by
  refine ⟨countermodelCert, ∅,
    ⟨fun _ _ => 0, 1, fun _ => 0, by intros; norm_num, by intros; norm_num⟩,
    ⟨fun _ _ => 0, fun _ => ∅⟩, unitWeight, ∅, fun _ => 0, 0, fun _ => 0, 0, ?_⟩
  intro h
  have := h.ford_binding.seven_primes
  simp at this

/-- **`oldBridge_slotWeight_is_not_v2_slotWeight`.**  `LEAN_PROVED`.

The normalisation firewall between the two bridges at the slot field: the old bare-indicator
field can hold while the corrected weighted field fails.  Hence the older bridge is not the
current physical dictionary. -/
theorem oldBridge_slotWeight_is_not_v2_slotWeight :
    ∃ (C : SP2FixedCertificateData) (S : PhysicalSlotData) (Dat : PrimeBoxData),
      (∀ (i : Fin 7) (p : ℕ), Dat.omega i p = sp2Omega C i p) ∧
        ¬ (∀ (i : Fin 7) (p : ℕ), Dat.omega i p = omegaPhysical C S i p) := by
  obtain ⟨C, S, i, p, _, hne⟩ := weighted_omega_ne_bare_indicator
  refine ⟨C, S, ⟨fun j q => sp2Omega C j q, fun j => C.lam j⟩, fun _ _ => rfl, ?_⟩
  intro hall
  exact hne (hall i p).symm

/-- **`bridgeV2_supplies_no_rank_one`.**  `LEAN_PROVED`.

`V2` carries no separability field, and none is derivable: the banked diagonal kernel is not
rank-one separable, whatever the bridge data. -/
theorem bridgeV2_supplies_no_rank_one
    {C : SP2FixedCertificateData} {U : Finset (Fin 7)} {S : PhysicalSlotData}
    {Dat : PrimeBoxData} {w : (Fin 7 → ℕ) → ℤ} {Pset : Finset ℕ} {Hphys : ℕ → ℤ}
    {gammaStar : ℝ} {cut : ℕ → ℕ} {S2 : ℝ}
    (_h : BalancedSevenSP2PhysicalBridgeV2 C U S Dat w Pset Hphys gammaStar cut S2) :
    ¬ ∃ xi kappa : ℕ → ℂ, ∀ m n, diagonalKernel m n = xi m * kappa n :=
  kernel_not_automatically_separable

/-- **`bridgeV2_needs_physical_fordH`.**  `LEAN_PROVED`.

The `V2` Ford field cannot be supplied by the combinatorial surrogate: the surrogate value
`−20` is available for free, while the physical binding is refuted by explicit data. -/
theorem bridgeV2_needs_physical_fordH :
    (∀ U : Finset (Fin 7), hStar U = -20) ∧
      ∃ (Pset : Finset ℕ) (Hphys : ℕ → ℤ) (gammaStar : ℝ) (cut : ℕ → ℕ),
        (∀ n, Hphys n = -20) ∧ ¬ FordHPhysicalBinding Pset Hphys gammaStar cut :=
  combinatorial_hStar_does_not_construct_FordHPhysicalBinding

end PhysicalBridgeV2
end Erdos287
