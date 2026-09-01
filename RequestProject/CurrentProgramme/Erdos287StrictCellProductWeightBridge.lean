import Mathlib
import RequestProject.CurrentProgramme.Erdos287StrictCellCanonicalSingleton

/-!
# Erdős #287 — the strict-cell product-weight physical bridge (append-only, UNINHABITED)

`BALANCED7-SP2-STRICTCELL-PRODUCTWEIGHT-PHYSICAL-BRIDGE45` and
`SP2-LABELLED-SINGLETON-GENERATEDTYPEII45`.

This module adds two **deliberately uninhabited** interfaces and the theorems that are
conditional on the first of them.  Nothing here is a source claim, and nothing here proves
the analytic singleton Type-II estimate.

* `BalancedSevenSP2StrictCellProductWeightPhysicalBridge` — the physical bridge, with
  explicit fields for the slot-box physical cell, the product / fixed-nuclear vector weight,
  the distinctness (repeated-prime) routing, the Ford-`H` binding, the cutoff binding and the
  physical `B` binding, plus the kernel data.  **No inhabitant is constructed anywhere in
  this repository**, and `bridge_not_automatic` exhibits data refuting it, so no compiler can
  manufacture one.

* `SP2LabelledSingletonGeneratedTypeIIInput` — the exact analytic inequality of the labelled
  singleton-generated Type-II packet.  **Uninhabited**; `typeII_input_not_automatic` shows it
  is a genuine restriction.

Conditional on the bridge we prove: the exact rank-one kernel factorisation
`K(m,n) = ξ(m)·κ(n)` with *canonical, deterministic* `ξ` and `κ`; the six-prime complement
definition and its depth `6`; the full physical `k = 0` (7.20) package; the zero Ford
hard-condition Perron contour count; and the exact product-weight mass factorisation (so no
generic subsum inclusion–exclusion is required).

Two counterguards keep the interface honest: an arbitrary cell weight is not product
separable (banked in the previous module) and an arbitrary kernel `C.Om` is not rank-one
separable (`kernel_not_automatically_separable` below).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos287
namespace StrictCellBridge

open Finset
open Erdos287.SP2Source
open Erdos287.V21PrimeBox
open Erdos287.SP2PrimeBox
open Erdos287.StrictCellSingleton

/-! ## §1.  Counterguard: an arbitrary kernel is not rank-one separable -/

/-- The diagonal kernel. -/
noncomputable def diagonalKernel : ℕ → ℕ → ℂ := fun m n => if m = n then 1 else 0

/-- **`kernel_not_automatically_separable`.**  `LEAN_PROVED`.

An arbitrary two-variable coefficient `C.Om` does **not** imply rank-one / product
separation: the diagonal kernel admits no factorisation `K(m,n) = ξ(m)·κ(n)`.  Hence the
separation field of the bridge is a genuine physical input, never a derivation. -/
theorem kernel_not_automatically_separable :
    ¬ ∃ xi kappa : ℕ → ℂ, ∀ m n, diagonalKernel m n = xi m * kappa n := by
  rintro ⟨xi, kappa, h⟩
  have h00 : (1 : ℂ) = xi 0 * kappa 0 := by simpa [diagonalKernel] using h 0 0
  have h11 : (1 : ℂ) = xi 1 * kappa 1 := by simpa [diagonalKernel] using h 1 1
  have h01 : (0 : ℂ) = xi 0 * kappa 1 := by simpa [diagonalKernel] using h 0 1
  have key : (xi 0 * kappa 0) * (xi 1 * kappa 1) = (xi 0 * kappa 1) * (xi 1 * kappa 0) := by
    ring
  rw [← h00, ← h11, ← h01] at key
  norm_num at key

/-! ## §2.  The physical bridge (UNINHABITED) -/

/-- **`BalancedSevenSP2StrictCellProductWeightPhysicalBridge`** —
`OPEN / UNINHABITED`.

The transcription obligation joining the physical balanced-seven SP-2 packet to the
strict-cell product-weight model of this bank.  Its fields are exactly the six physical
bindings that a source reading would have to supply, plus the kernel data:

* *slot-box physical cell*: the physical prime-box datum is the fixed smooth cell `λ`;
* *product or fixed-nuclear vector weight*: the cell weight is either rank-one (a product of
  slot weights) or a fixed nuclear constant;
* *distinctness / repeated-prime routing*: every surviving vector has pairwise distinct prime
  coordinates, repeated-prime vectors being routed to weight zero;
* *Ford-`H` binding*: the physical Ford functional equals `H^* = -20`;
* *cutoff binding*: all cell primes are below the physical cutoff;
* *physical `B` binding*: the cell weight is bounded by the physical `B`;
* the kernel is rank-one separable and normalised at the anchor `(m₀, n₀)`.

No inhabitant is constructed in this repository. -/
structure BalancedSevenSP2StrictCellProductWeightPhysicalBridge
    (C : SP2FixedCertificateData) (U : Finset (Fin 7)) (Dat : PrimeBoxData)
    (w : (Fin 7 → ℕ) → ℤ) (K : ℕ → ℕ → ℂ) (m₀ n₀ : ℕ) (Hphys : ℤ) (cutoff : ℕ)
    (B : ℝ) : Prop where
  /-- Slot-box physical cell: the boxes of the physical datum are the cells of `λ`. -/
  slotBox_cell : ∀ i : Fin 7, Dat.box i = C.lam i
  /-- Slot-box physical cell: the physical coefficients are the SP-2 cell indicators. -/
  slotBox_weight : ∀ (i : Fin 7) (p : ℕ), Dat.omega i p = sp2Omega C i p
  /-- The strict-cell hypotheses hold for the certificate and the branch label. -/
  strict_cell : StrictCellHypotheses C U
  /-- Product or fixed-nuclear vector weight. -/
  weight_form :
    (∃ f : Fin 7 → ℕ → ℤ, ∀ v ∈ cellVectors C, w v = productWeight f v) ∨
      (∃ c : ℤ, ∀ v ∈ cellVectors C, w v = c)
  /-- Distinctness / repeated-prime routing: repeated-prime vectors carry no weight. -/
  routing : ∀ v ∈ cellVectors C,
    (∀ i j : Fin 7, i ≠ j → v i ≠ v j) ∨ w v = 0
  /-- Ford-`H` binding. -/
  ford_H_binding : Hphys = hStar U
  /-- Cutoff binding. -/
  cutoff_binding : ∀ (i : Fin 7), ∀ p ∈ C.lam i, p ≤ cutoff
  /-- Physical `B` binding. -/
  B_binding : ∀ v ∈ cellVectors C, |(w v : ℝ)| ≤ B
  /-- The kernel is rank-one separable. -/
  kernel_separable : ∃ xi kappa : ℕ → ℂ, ∀ m n, K m n = xi m * kappa n
  /-- The kernel is normalised at the anchor. -/
  kernel_normalised : K m₀ n₀ = 1

/-- **`bridge_not_automatic`.**  `LEAN_PROVED`.

The bridge is a genuine restriction: explicit data refute it.  In particular no compiler can
manufacture an inhabitant, and none is constructed here. -/
theorem bridge_not_automatic :
    ∃ (C : SP2FixedCertificateData) (U : Finset (Fin 7)) (Dat : PrimeBoxData)
      (w : (Fin 7 → ℕ) → ℤ) (K : ℕ → ℕ → ℂ) (m₀ n₀ : ℕ) (Hphys : ℤ) (cutoff : ℕ) (B : ℝ),
      ¬ BalancedSevenSP2StrictCellProductWeightPhysicalBridge C U Dat w K m₀ n₀ Hphys cutoff
          B := by
  refine ⟨countermodelCert, ∅, ⟨fun _ _ => 0, fun _ => ∅⟩, unitWeight, diagonalKernel, 0, 0,
    0, 0, 0, ?_⟩
  intro h
  exact kernel_not_automatically_separable h.kernel_separable

/-! ## §3.  The exact kernel factorisation, conditional on the bridge -/

/-- The canonical `ξ`: the kernel restricted to the anchor second coordinate. -/
noncomputable def xiOf (K : ℕ → ℕ → ℂ) (n₀ : ℕ) : ℕ → ℂ := fun m => K m n₀

/-- The canonical `κ`: the kernel restricted to the anchor first coordinate. -/
noncomputable def kappaOf (K : ℕ → ℕ → ℂ) (m₀ : ℕ) : ℕ → ℂ := fun n => K m₀ n

/-- **`bridge_kernel_factorisation`.**  `LEAN_PROVED` (conditional on the bridge).

The exact factorisation `K(m,n) = ξ(m)·κ(n)` with the *canonical deterministic* choices
`ξ(m) = K(m, n₀)` and `κ(n) = K(m₀, n)`.  No choice function is involved: the factors are
literal restrictions of the kernel. -/
theorem bridge_kernel_factorisation
    {C : SP2FixedCertificateData} {U : Finset (Fin 7)} {Dat : PrimeBoxData}
    {w : (Fin 7 → ℕ) → ℤ} {K : ℕ → ℕ → ℂ} {m₀ n₀ : ℕ} {Hphys : ℤ} {cutoff : ℕ} {B : ℝ}
    (h : BalancedSevenSP2StrictCellProductWeightPhysicalBridge C U Dat w K m₀ n₀ Hphys cutoff B)
    (m n : ℕ) : K m n = xiOf K n₀ m * kappaOf K m₀ n := by
  obtain ⟨xi, kappa, hsep⟩ := h.kernel_separable
  have hanchor : xi m₀ * kappa n₀ = 1 := by rw [← hsep]; exact h.kernel_normalised
  calc K m n = K m n * (xi m₀ * kappa n₀) := by rw [hanchor, mul_one]
    _ = (xi m * kappa n₀) * (xi m₀ * kappa n) := by rw [hsep m n]; ring
    _ = xiOf K n₀ m * kappaOf K m₀ n := by rw [xiOf, kappaOf, hsep m n₀, hsep m₀ n]

/-- The canonical factor `ξ` is pinned by *any* factorisation of the kernel: no choice
function and no ambiguity. -/
theorem kernel_canonical_factor_eq {K : ℕ → ℕ → ℂ} {xi' kappa' : ℕ → ℂ}
    (hfac : ∀ m n, K m n = xi' m * kappa' n) (n₀ : ℕ) :
    ∀ m, xi' m * kappa' n₀ = xiOf K n₀ m := by
  intro m
  rw [xiOf, hfac m n₀]

/-! ## §4.  The six-prime complement, conditional consequences of the bridge -/

/-- **`bridgeSixPrimeComplement`** — the six-prime complement of the packet: the prime
coordinates other than the canonical singleton `i(U)`. -/
def bridgeSixPrimeComplement (U : Finset (Fin 7)) : Finset (Fin 7) := sixPrimeComplement U

/-- **`bridge_complement_depth_eq_six`.**  `LEAN_PROVED`.  The complement depth is `6`. -/
theorem bridge_complement_depth_eq_six (U : Finset (Fin 7)) :
    (bridgeSixPrimeComplement U).card = 6 :=
  complementDepth_eq_six U

/-- Conditional on the bridge, the full physical `k = 0` (7.20) package holds. -/
theorem bridge_physicalK0
    {C : SP2FixedCertificateData} {U : Finset (Fin 7)} {Dat : PrimeBoxData}
    {w : (Fin 7 → ℕ) → ℤ} {K : ℕ → ℕ → ℂ} {m₀ n₀ : ℕ} {Hphys : ℤ} {cutoff : ℕ} {B : ℝ}
    (h : BalancedSevenSP2StrictCellProductWeightPhysicalBridge C U Dat w K m₀ n₀ Hphys cutoff B) :
    PhysicalK0Conditions720 C U :=
  physicalK0_of_strictCell h.strict_cell

/-- Conditional on the bridge, the physical Ford functional is `-20`. -/
theorem bridge_H_eq_neg_twenty
    {C : SP2FixedCertificateData} {U : Finset (Fin 7)} {Dat : PrimeBoxData}
    {w : (Fin 7 → ℕ) → ℤ} {K : ℕ → ℕ → ℂ} {m₀ n₀ : ℕ} {Hphys : ℤ} {cutoff : ℕ} {B : ℝ}
    (h : BalancedSevenSP2StrictCellProductWeightPhysicalBridge C U Dat w K m₀ n₀ Hphys cutoff B) :
    Hphys = -20 := by
  rw [h.ford_H_binding, hStar_eq_neg_twenty]

/-- Conditional on the bridge, zero Ford hard-condition Perron contours are opened. -/
theorem bridge_perronContourCount_zero
    {C : SP2FixedCertificateData} {U : Finset (Fin 7)} {Dat : PrimeBoxData}
    {w : (Fin 7 → ℕ) → ℤ} {K : ℕ → ℕ → ℂ} {m₀ n₀ : ℕ} {Hphys : ℤ} {cutoff : ℕ} {B : ℝ}
    (h : BalancedSevenSP2StrictCellProductWeightPhysicalBridge C U Dat w K m₀ n₀ Hphys cutoff B) :
    perronContourCount C = 0 :=
  perronContourCount_eq_zero h.strict_cell

/-- Conditional on the bridge, the physical coefficients obey the pointwise law with
constant `1`. -/
theorem bridge_pointwise
    {C : SP2FixedCertificateData} {U : Finset (Fin 7)} {Dat : PrimeBoxData}
    {w : (Fin 7 → ℕ) → ℤ} {K : ℕ → ℕ → ℂ} {m₀ n₀ : ℕ} {Hphys : ℤ} {cutoff : ℕ} {B : ℝ}
    (h : BalancedSevenSP2StrictCellProductWeightPhysicalBridge C U Dat w K m₀ n₀ Hphys cutoff B) :
    ∀ (i : Fin 7) (p : ℕ), ‖Dat.omega i p‖ ≤ 1 := by
  intro i p
  rw [h.slotBox_weight i p]
  exact sp2Omega_norm_le_one C i p

/-- **`bridge_total_mass`.**  `LEAN_PROVED` (conditional).

In the rank-one branch of the weight field the total cell mass factorises *exactly*: no
generic subsum inclusion–exclusion is required for this source-specific packet. -/
theorem bridge_total_mass
    {C : SP2FixedCertificateData} {U : Finset (Fin 7)} {Dat : PrimeBoxData}
    {w : (Fin 7 → ℕ) → ℤ} {K : ℕ → ℕ → ℂ} {m₀ n₀ : ℕ} {Hphys : ℤ} {cutoff : ℕ} {B : ℝ}
    (h : BalancedSevenSP2StrictCellProductWeightPhysicalBridge C U Dat w K m₀ n₀ Hphys cutoff B) :
    (∃ f : Fin 7 → ℕ → ℤ, ∑ v ∈ cellVectors C, w v = ∏ i, ∑ p ∈ C.lam i, f i p) ∨
      (∃ c : ℤ, ∑ v ∈ cellVectors C, w v = ((cellVectors C).card : ℤ) * c) := by
  rcases h.weight_form with ⟨f, hf⟩ | ⟨c, hc⟩
  · refine Or.inl ⟨f, ?_⟩
    rw [Finset.sum_congr rfl hf]
    exact productWeight_total_mass C f
  · refine Or.inr ⟨c, ?_⟩
    rw [Finset.sum_congr rfl hc, Finset.sum_const, nsmul_eq_mul]

/-- Conditional on the bridge, every cell prime lies under the physical cutoff, so the
singleton coordinate lies in the physical window `[2, cutoff]`. -/
theorem bridge_singleton_window
    {C : SP2FixedCertificateData} {U : Finset (Fin 7)} {Dat : PrimeBoxData}
    {w : (Fin 7 → ℕ) → ℤ} {K : ℕ → ℕ → ℂ} {m₀ n₀ : ℕ} {Hphys : ℤ} {cutoff : ℕ} {B : ℝ}
    (h : BalancedSevenSP2StrictCellProductWeightPhysicalBridge C U Dat w K m₀ n₀ Hphys cutoff B)
    {v : Fin 7 → ℕ} (hv : v ∈ cellVectors C) :
    v (canonicalSingleton U) ∈ Finset.Icc 2 cutoff := by
  have hlo : ∀ (i : Fin 7), ∀ p ∈ C.lam i, 2 ≤ p := by
    intro i p hp
    exact (h.strict_cell.cell_prime i p hp).two_le
  exact singleton_mem_window hlo h.cutoff_binding hv

/-! ## §5.  The labelled singleton-generated Type-II input (UNINHABITED) -/

/-- **`SP2LabelledSingletonGeneratedTypeIIInput`** — `OPEN ANALYTIC / UNINHABITED`.

The exact analytic inequality of the labelled singleton-generated Type-II packet: a bilinear
gain, over the strict cell, in the splitting singleton coordinate `i(U)` against the
six-prime complement.  This project does **not** prove it and constructs no inhabitant. -/
structure SP2LabelledSingletonGeneratedTypeIIInput
    (C : SP2FixedCertificateData) (U : Finset (Fin 7)) (Y Z : ℕ) (target : ℝ) : Prop where
  /-- The branch label is one of the 64 small labels. -/
  labelled : U.card ≤ 3
  /-- The physical prime size window. -/
  window : ∀ (i : Fin 7), ∀ p ∈ C.lam i, Y ≤ p ∧ p ≤ Z
  /-- The gain is a genuine gain. -/
  gain : target < 1
  /-- The analytic bilinear estimate itself. -/
  typeII : ∀ a b : ℕ → ℂ, (∀ n, ‖a n‖ ≤ 1) → (∀ n, ‖b n‖ ≤ 1) →
    ‖∑ v ∈ cellVectors C,
        a (v (canonicalSingleton U)) * b (∏ i ∈ sixPrimeComplement U, v i)‖
      ≤ target * ((cellVectors C).card : ℝ)

/-- **`typeII_input_not_automatic`.**  `LEAN_PROVED`.

The Type-II input is a genuine analytic restriction: for the balanced countermodel cell with
`target = 0` all the finite fields hold but the inequality fails (take `a = b = 1`).  So no
inhabitant can be produced by bookkeeping, and none is produced here. -/
theorem typeII_input_not_automatic :
    ¬ SP2LabelledSingletonGeneratedTypeIIInput countermodelCert ∅ 2 3 0 := by
  intro h
  have hcard : (cellVectors countermodelCert).card = 128 := by
    rw [cellVectors, Fintype.card_piFinset]
    decide
  have hb := h.typeII (fun _ => 1) (fun _ => 1) (by intro n; simp) (by intro n; simp)
  rw [show (∑ v ∈ cellVectors countermodelCert, (1 : ℂ) * 1)
      = ((cellVectors countermodelCert).card : ℂ) by simp, hcard] at hb
  norm_num at hb

/-- The two open interfaces are logically independent of everything proved above: the bridge
is not a theorem, and neither is the Type-II input.  Recorded as an identity map, so that no
reader mistakes the conditional compilers for source or analytic theorems. -/
theorem bridge_is_an_input_not_a_theorem
    (C : SP2FixedCertificateData) (U : Finset (Fin 7)) (Dat : PrimeBoxData)
    (w : (Fin 7 → ℕ) → ℤ) (K : ℕ → ℕ → ℂ) (m₀ n₀ : ℕ) (Hphys : ℤ) (cutoff : ℕ) (B : ℝ) :
    BalancedSevenSP2StrictCellProductWeightPhysicalBridge C U Dat w K m₀ n₀ Hphys cutoff B →
      BalancedSevenSP2StrictCellProductWeightPhysicalBridge C U Dat w K m₀ n₀ Hphys cutoff B :=
  id

end StrictCellBridge
end Erdos287
