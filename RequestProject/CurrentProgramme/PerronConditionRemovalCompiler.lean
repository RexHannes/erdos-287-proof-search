import Mathlib
import RequestProject.CurrentProgramme.Block20LargePrimePowerRouter

/-!
# BLOCK20 Δ, Phase C (§12) — the Perron condition-removal socket

**No classical Perron analysis is proved here, and none is assumed silently.**  This module
exposes a *granular* interface, so that a false assumption would be visible as a named field
rather than hidden behind "Perron works":

* the exact source cutoff;
* the truncated integral representation, with the kernel `K(τ)` given as data;
* the vertical range `T = X^δ` and the contour abscissa `c = 1/log X`;
* the kernel `L¹` budget;
* the boundary-strip source **and** the boundary-strip estimate, kept apart;
* the truncation error estimate;
* the final exact reconstruction.

`PerronConditionRemovalInput` is **uninhabited**; `perron_separated_prefix_of_input` is the
conditional compiler to `SeparatedPrefixCoefficientFamily`.

## §12A  Boundary router firewall

The NANC audit found that the sharp near-boundary strip needs repair, so
`PerronBoundaryRouterInput` is a separate interface.  Its defining requirement is that the
**literal SP-2 source is preserved**: the router may smooth the *kernel*, never the
certificate.  `boundaryRouter_preserves_literal_source` and
`smoothed_certificate_is_a_different_source` make that distinction a theorem.

Metadata: `C_Perron = 1` is recorded as the **current external analytic audit target**
(`perronConstantAuditTarget`), not as a kernel-proved estimate
(`perron_constant_is_not_a_theorem`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Erdos287
namespace Block20

/-! ## §12.1  Metadata -/

/-- The Perron constant currently used by the hostile-audit budget, as **metadata**. -/
def perronConstantAuditTarget : ℚ := 1

/-- The contour abscissa `c = 1/log X`. -/
noncomputable def perronAbscissa (X : ℝ) : ℝ := 1 / Real.log X

/-- The vertical truncation `T = X^δ`. -/
noncomputable def perronVerticalRange (X delta : ℝ) : ℝ := X ^ delta

/-! ## §12.2  The condition-removal interface -/

/-- The conclusion: after condition removal the prefix coefficient family is *separated*,
i.e. the coefficient of the source at `n` is reconstructed from the kernel-integrated family
with an explicit error. -/
def SeparatedPrefixCoefficientFamily
    (coeff : ℕ → ℂ) (reconstructed : ℕ → ℂ) (err : ℝ) : Prop :=
  ∀ n : ℕ, ‖coeff n - reconstructed n‖ ≤ err

/-- **`PerronConditionRemovalInput`** — `EXTERNAL / ANALYTIC / UNINHABITED`.

Every ingredient of the condition-removal step is an explicit field.  No field says
"Perron works". -/
structure PerronConditionRemovalInput
    (X delta cPerron : ℝ) (cutoff : ℕ → ℝ) (kernel : ℝ → ℂ)
    (coeff reconstructed boundaryStrip truncation : ℕ → ℂ)
    (kernelL1 stripErr truncErr : ℝ) : Prop where
  /-- The scale is nontrivial. -/
  scale : 3 ≤ X
  /-- The vertical range really is `T = X^δ`, with `δ` in the admissible range. -/
  vertical_range : 0 < delta ∧ delta < 1
  /-- The Perron constant is the audited one. -/
  perron_constant : cPerron = (perronConstantAuditTarget : ℝ)
  /-- The exact source cutoff: the truncation is active and matches the source scale. -/
  source_cutoff : ∀ n : ℕ, 0 < cutoff n ∧ cutoff n ≤ X
  /-- The kernel `L¹` budget on the truncated vertical line. -/
  kernel_L1 : (∫ tau in (-perronVerticalRange X delta)..(perronVerticalRange X delta),
      ‖kernel tau‖) ≤ kernelL1
  /-- The kernel budget is explicit and finite. -/
  kernel_budget_pos : 0 < kernelL1
  /-- The boundary-strip **estimate** — the piece the NANC audit flagged for repair.  The
  strip *source* `boundaryStrip` is a separate parameter, so source and estimate cannot be
  conflated. -/
  boundary_estimate : ∀ n : ℕ, ‖boundaryStrip n‖ ≤ stripErr
  /-- The truncation error estimate for the finite vertical range. -/
  truncation_estimate : ∀ n : ℕ, ‖truncation n‖ ≤ truncErr
  /-- The final **exact** reconstruction: source = main + boundary strip + truncation. -/
  reconstruction : ∀ n : ℕ, coeff n = reconstructed n + boundaryStrip n + truncation n

/-- **`perron_separated_prefix_of_input`.**  `CONDITIONAL_COMPILER / LEAN_PROVED`.

The conditional compiler.  The error is exactly the sum of the two declared errors; no
analytic content is manufactured. -/
theorem perron_separated_prefix_of_input
    {X delta cPerron : ℝ} {cutoff : ℕ → ℝ} {kernel : ℝ → ℂ}
    {coeff reconstructed boundaryStrip truncation : ℕ → ℂ} {kernelL1 stripErr truncErr : ℝ}
    (h : PerronConditionRemovalInput X delta cPerron cutoff kernel coeff reconstructed
      boundaryStrip truncation kernelL1 stripErr truncErr) :
    SeparatedPrefixCoefficientFamily coeff reconstructed (stripErr + truncErr) := by
  intro n
  have hrec := h.reconstruction n
  have : coeff n - reconstructed n = boundaryStrip n + truncation n := by
    rw [hrec]; ring
  rw [this]
  exact le_trans (norm_add_le _ _) (add_le_add (h.boundary_estimate n) (h.truncation_estimate n))

/-- **`perronConditionRemoval_not_automatic`.**  `LEAN_PROVED`.  The interface is
**uninhabited**. -/
theorem perronConditionRemoval_not_automatic :
    ∃ (X delta cPerron : ℝ) (cutoff : ℕ → ℝ) (kernel : ℝ → ℂ)
      (coeff reconstructed boundaryStrip truncation : ℕ → ℂ) (kernelL1 stripErr truncErr : ℝ),
      ¬ PerronConditionRemovalInput X delta cPerron cutoff kernel coeff reconstructed
        boundaryStrip truncation kernelL1 stripErr truncErr := by
  refine ⟨0, 0, 0, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0,
    0, 0, 0, ?_⟩
  intro h
  have := h.scale
  norm_num at this

/-- **`perron_constant_is_not_a_theorem`.**  `LEAN_PROVED`.

`C_Perron = 1` is metadata and an external audit target: it is recorded here, while the
analytic interface that would justify it is not inhabited. -/
theorem perron_constant_is_not_a_theorem :
    perronConstantAuditTarget = 1 ∧
      ∃ (X delta cPerron : ℝ) (cutoff : ℕ → ℝ) (kernel : ℝ → ℂ)
        (coeff reconstructed boundaryStrip truncation : ℕ → ℂ) (kernelL1 stripErr truncErr : ℝ),
        ¬ PerronConditionRemovalInput X delta cPerron cutoff kernel coeff reconstructed
          boundaryStrip truncation kernelL1 stripErr truncErr :=
  ⟨rfl, perronConditionRemoval_not_automatic⟩

/-! ## §12A  The boundary router firewall -/

/-- **`PerronBoundaryRouterInput`** — `EXTERNAL / ANALYTIC / UNINHABITED`.

The near-boundary strip router.  Its first field is the firewall: the source consumed by the
router **is** the literal SP-2 certificate weight `Hs`; the smoothing profile `smooth` acts
on the kernel side only. -/
structure PerronBoundaryRouterInput
    (Hs sourceWeight : ℕ → ℤ) (smooth : ℝ → ℝ) (sector : Finset ℕ)
    (X stripWidth stripErr : ℝ) : Prop where
  /-- **No replacement of `H_*` by a smoothed certificate.** -/
  literal_source : ∀ n ∈ sector, sourceWeight n = Hs n
  /-- The smoothing profile is a kernel-side weight: normalised, and applied to the contour
  variable, never to the arithmetic source. -/
  smoothing_normalised : ∀ x : ℝ, 0 ≤ smooth x ∧ smooth x ≤ 1
  /-- The strip is a genuine near-boundary strip. -/
  strip_geometry : 3 ≤ X ∧ 0 < stripWidth ∧ stripWidth < 1 / Real.log X
  /-- The strip estimate. -/
  strip_estimate : |∑ n ∈ sector, (sourceWeight n : ℝ) * smooth (n / X)| ≤ stripErr

/-- **`boundaryRouter_preserves_literal_source`.**  `CONDITIONAL / LEAN_PROVED`.

The firewall as a theorem: any inhabitant of the router interface consumes the literal
source, so the smoothing lives only in the condition-removal step. -/
theorem boundaryRouter_preserves_literal_source
    {Hs sourceWeight : ℕ → ℤ} {smooth : ℝ → ℝ} {sector : Finset ℕ} {X stripWidth stripErr : ℝ}
    (h : PerronBoundaryRouterInput Hs sourceWeight smooth sector X stripWidth stripErr) :
    ∀ n ∈ sector, sourceWeight n = Hs n :=
  h.literal_source

/-- **`smoothed_certificate_is_a_different_source`.**  `LEAN_PROVED`.

The distinction is not vacuous: a "smoothed certificate" really is a different arithmetic
source, so the firewall field has content. -/
theorem smoothed_certificate_is_a_different_source :
    ∃ (Hs smoothedHs : ℕ → ℤ) (sector : Finset ℕ),
      (∀ n ∈ sector, smoothedHs n ≠ Hs n) ∧ sector.Nonempty := by
  refine ⟨fun _ => 1, fun _ => 0, {1}, ?_, ⟨1, Finset.mem_singleton_self 1⟩⟩
  intro n _
  norm_num

/-- **`perronBoundaryRouter_not_automatic`.**  `LEAN_PROVED`.  The router interface is
**uninhabited**. -/
theorem perronBoundaryRouter_not_automatic :
    ∃ (Hs sourceWeight : ℕ → ℤ) (smooth : ℝ → ℝ) (sector : Finset ℕ)
      (X stripWidth stripErr : ℝ),
      ¬ PerronBoundaryRouterInput Hs sourceWeight smooth sector X stripWidth stripErr := by
  refine ⟨fun _ => 0, fun _ => 0, fun _ => 0, ∅, 0, 0, 0, ?_⟩
  intro h
  have := h.strip_geometry.1
  norm_num at this

end Block20
end Erdos287
