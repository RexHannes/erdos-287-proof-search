import Mathlib
import RequestProject.CurrentProgramme.Erdos287BalancedBUnitaryFourierCompiler
import RequestProject.CurrentProgramme.Erdos287ConditionedInverseConvInterface

/-!
# C0 physical / formal normalisation interface — Erdős #287 (append-only)

This module contains **no** analytic theorem and **no** guessed constant.  It records, as named
propositions, the two source pins on which the C0 analytic discussion is conditional, and it
provides one conditional compiler whose every input is an explicit hypothesis.

```
C0 ANALYTIC CORE:
    CLOSED.

C0 PHYSICAL/FORMAL NORMALISATION:
    OPEN SOURCE PIN.

Therefore:
    C0 ANALYTICALLY CLOSED
    CONDITIONAL ON FORMAL NORMALISATION.
```

Contents.

* §1  `PerronNuclearNormalisationHypothesis`: the complete Perron/nuclear contour family mass.
  **Source pin.**  Never assumed; a witness theorem shows it is not automatic.
* §2  `OmegaHL2NormalisationHypothesis`: the `ℓ²` normalisation of `Ω_H`.  **Source pin.**  The
  already-banked *pointwise* shell `Erdos287.ConditionedInverseConv.OmegaHNormalizationHypothesis`
  is reused, not duplicated: §2 proves that the pointwise shell implies the `ℓ²` shell with the
  cardinality constant.
* §3  `C0PhysicalNormalisationData`: the bundle of the two pins.
* §4  the conditional compiler `c0_balanced_branch_bound_of`: from (i) unit support, (ii) an
  explicit product-convolution energy hypothesis, (iii) an explicit `Ω_H` `ℓ²` normalisation and
  (iv) explicit residue-fibre bounds, the balanced reciprocal Fourier bound follows.  Its
  conclusion is an explicit finite inequality — **not** a proposition called "C0 is closed", and
  not `True`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos287
namespace C0PhysicalNormalisation

open Finset
open Erdos287.BalancedBUnitaryFourier

/-! ## §1  Perron / nuclear normalisation — SOURCE PIN -/

/-- Schematic data of the complete Perron contour family: a finite family of contours, the
nuclear mass carried by each, and the claimed uniform bound. -/
structure PerronNuclearData where
  /-- The finite family of Perron contours. -/
  contours : Finset ℕ
  /-- The nuclear (trace-class) mass carried by each contour. -/
  nuclearMass : ℕ → ℝ
  /-- The claimed uniform nuclear bound. -/
  bound : ℝ

/-- **Interface, OPEN SOURCE PIN.**  The complete Perron/nuclear normalisation: every contour of
the family carries at most `bound` nuclear mass.

This is **not** proved anywhere, and no declaration assumes it silently: every consumer takes it
as an explicit argument.  In particular this repository does *not* assert that the complete
physical coefficient already has `L^{O(1)}` nuclear mass. -/
def PerronNuclearNormalisationHypothesis (d : PerronNuclearData) : Prop :=
  ∀ c ∈ d.contours, d.nuclearMass c ≤ d.bound

/-- **`perronNuclear_total_of_normalisation`.**  `LEAN_PROVED (CONDITIONAL)`.  Given the pin,
the total nuclear mass of the family is at most `#contours · bound`.  This is the assumed bound,
summed; it asserts nothing further. -/
theorem perronNuclear_total_of_normalisation (d : PerronNuclearData)
    (hPerron : PerronNuclearNormalisationHypothesis d) :
    ∑ c ∈ d.contours, d.nuclearMass c ≤ (d.contours.card : ℝ) * d.bound := by
  calc ∑ c ∈ d.contours, d.nuclearMass c ≤ ∑ _c ∈ d.contours, d.bound :=
        Finset.sum_le_sum hPerron
    _ = (d.contours.card : ℝ) * d.bound := by rw [Finset.sum_const, nsmul_eq_mul]

/-- **`perronNuclearNormalisation_not_automatic`.**  `LEAN_PROVED`.  The Perron pin is a genuine
hypothesis: there are data for which it fails.  It cannot be discharged by pure logic. -/
theorem perronNuclearNormalisation_not_automatic :
    ∃ d : PerronNuclearData, ¬ PerronNuclearNormalisationHypothesis d := by
  refine ⟨⟨{0}, fun _ => 1, 0⟩, ?_⟩
  intro h
  have h0 := h 0 (by simp)
  norm_num at h0

/-! ## §2  `Ω_H` normalisation — SOURCE PIN, `ℓ²` form -/

/-- Schematic data for the `ℓ²` normalisation of `Ω_H`. -/
structure OmegaHL2Data where
  /-- The index set of the coefficient. -/
  support : Finset ℕ
  /-- The coefficient itself; its pointwise formula is irrelevant to the finite Fourier
  theorems, which see only its `ℓ²` mass. -/
  OmegaH : ℕ → ℂ
  /-- The claimed `ℓ²` bound. -/
  l2Bound : ℝ

/-- **Interface, OPEN SOURCE PIN.**  The `ℓ²` normalisation of `Ω_H`.  This is the *only* input
about `Ω_H` that the finite Fourier theorems of this bank can consume: they quantify over
arbitrary coefficient vectors, so no pointwise description of `Ω_H` enters them. -/
def OmegaHL2NormalisationHypothesis (d : OmegaHL2Data) : Prop :=
  ∑ h ∈ d.support, ‖d.OmegaH h‖ ^ 2 ≤ d.l2Bound

/-- **`omegaHL2_of_pointwise_normalisation`.**  `LEAN_PROVED (CONDITIONAL)`.  Reuse, not
duplication: the previously banked *pointwise* `Ω_H` shell implies the `ℓ²` shell with constant
`#support · normalisation²`. -/
theorem omegaHL2_of_pointwise_normalisation
    (d : Erdos287.ConditionedInverseConv.OmegaHData)
    (hNorm : Erdos287.ConditionedInverseConv.OmegaHNormalizationHypothesis d) :
    OmegaHL2NormalisationHypothesis
      ⟨d.support, d.OmegaH, (d.support.card : ℝ) * d.normalisation ^ 2⟩ :=
  Erdos287.ConditionedInverseConv.omegaH_energy_of_normalization d hNorm

/-- **`omegaHL2Normalisation_not_automatic`.**  `LEAN_PROVED`.  The `ℓ²` `Ω_H` pin is a genuine
hypothesis: there are data for which it fails. -/
theorem omegaHL2Normalisation_not_automatic :
    ∃ d : OmegaHL2Data, ¬ OmegaHL2NormalisationHypothesis d := by
  refine ⟨⟨{0}, fun _ => 1, 0⟩, ?_⟩
  intro h
  simp only [OmegaHL2NormalisationHypothesis] at h
  norm_num at h

/-! ## §3  The bundle -/

/-- The two formal source pins of the C0 physical normalisation, bundled.  No field is filled
from a guess, and the structure carries no proof of either pin. -/
structure C0PhysicalNormalisationData where
  /-- Perron / nuclear contour data. -/
  perron : PerronNuclearData
  /-- `Ω_H` `ℓ²` data. -/
  omegaH : OmegaHL2Data

/-- The conjunction of the two pins. -/
def C0PhysicalNormalisationHypothesis (D : C0PhysicalNormalisationData) : Prop :=
  PerronNuclearNormalisationHypothesis D.perron ∧ OmegaHL2NormalisationHypothesis D.omegaH

/-- **`c0PhysicalNormalisation_not_automatic`.**  `LEAN_PROVED`.  The bundled pin is a genuine
hypothesis. -/
theorem c0PhysicalNormalisation_not_automatic :
    ∃ D : C0PhysicalNormalisationData, ¬ C0PhysicalNormalisationHypothesis D := by
  obtain ⟨d, hd⟩ := perronNuclearNormalisation_not_automatic
  exact ⟨⟨d, ⟨∅, fun _ => 0, 0⟩⟩, fun h => hd h.1⟩

/-- **`c0PhysicalNormalisation_satisfiable`.**  `LEAN_PROVED`.  The bundled pin is not
contradictory either: it holds on empty data.  Together with the previous theorem it is pinned
down as a real, open condition. -/
theorem c0PhysicalNormalisation_satisfiable :
    ∃ D : C0PhysicalNormalisationData, C0PhysicalNormalisationHypothesis D := by
  refine ⟨⟨⟨∅, fun _ => 0, 0⟩, ⟨∅, fun _ => 0, 0⟩⟩, ?_, ?_⟩
  · intro c hc; simp at hc
  · simp [OmegaHL2NormalisationHypothesis]

/-! ## §4  The conditional compiler -/

/-- **`c0_balanced_branch_bound_of`.**  `LEAN_PROVED (CONDITIONAL)`.

The balanced C0 branch, compiled from explicit hypotheses only:

* `hC` : the conditioned coefficient is a **unit** of `ZMod x`;
* `hNunit`, `hEunit` : the two carriers are supported on unit residues;
* `hMN`, `hME` : residue-fibre bounds;
* `hConv` : an explicit product-convolution energy hypothesis for the `n`-coefficient;
* `hOmega` : an explicit `Ω_H` `ℓ²` normalisation for the `e`-coefficient.

The conclusion is the explicit finite bilinear bound.  It is **not** a proposition asserting
that C0 is closed; the C0 branch remains analytically closed only *conditional on* the formal
source normalisation, which this file does not prove. -/
theorem c0_balanced_branch_bound_of {x : ℕ} [NeZero x] {C : ZMod x} (hC : IsUnit C)
    (sN sa salpha : Finset ℕ) (A a alpha : ℕ → ℂ)
    (dOmega : OmegaHL2Data)
    (hNunit : ∀ n ∈ sN, IsUnit ((n : ℕ) : ZMod x))
    (hEunit : ∀ e ∈ dOmega.support, IsUnit ((e : ℕ) : ZMod x))
    (MN ME Cconv : ℝ)
    (hMN : ∀ r : ZMod x, ((sN.filter (fun n => ((n : ℕ) : ZMod x) = r)).card : ℝ) ≤ MN)
    (hME : ∀ r : ZMod x,
      ((dOmega.support.filter (fun e => ((e : ℕ) : ZMod x) = r)).card : ℝ) ≤ ME)
    (hConv : ProductConvolutionEnergyHypothesis sN sa salpha A a alpha Cconv)
    (hOmega : OmegaHL2NormalisationHypothesis dOmega) :
    ‖∑ n ∈ sN, ∑ e ∈ dOmega.support,
        A n * dOmega.OmegaH e *
          ZMod.stdAddChar (C * (((n : ℕ) : ZMod x))⁻¹ * (((e : ℕ) : ZMod x))⁻¹)‖ ^ 2
      ≤ (x : ℝ) * MN * ME *
          (Cconv * (∑ l ∈ sa, ‖a l‖ ^ 2) * (∑ d ∈ salpha, ‖alpha d‖ ^ 2)) * dOmega.l2Bound :=
  balancedReciprocalFourier_compiler hC sN dOmega.support A dOmega.OmegaH hNunit hEunit
    MN ME _ dOmega.l2Bound hMN hME hConv hOmega

end C0PhysicalNormalisation
end Erdos287
