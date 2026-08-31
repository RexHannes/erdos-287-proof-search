import Mathlib
import RequestProject.Erdos287.BalancedSevenV20Compiler
import RequestProject.Erdos287.ShiuDivisorAverage3221

/-!
# V21, Phase 7 — the shared high-projector cutoff

`3221-HIGHPROJECTOR-CUTOFF-COMPAT45 : SOURCE_OPEN`

The V20 objects `highConductorCutoff`, `MuLogComparisonAtCutoff` and
`comparison_cutoff_must_match` are **reused, not replaced**.  What V21 adds is a *single
shared cutoff datum* used simultaneously by

* the analytic high-projector decomposition (which produces `Bad_q` and `High_q`), and
* the physical comparison / expected-term convention,

together with the requirement that changing the cutoff does not alter the unaccounted
exceptional/principal mass, and that the low-conductor reassembly stays valid.

`D = log X` is **not** silently imposed: the cutoff exponent `B0` is a free natural
parameter throughout, and `cutoffCompat_does_not_fix_B0` records that no theorem here pins
it to `1`.

The physical instance of `HighProjectorCutoffCompat3221` — the one whose `unaccounted`
function is the literal exceptional/principal mass of the Balanced7 packet — is **not**
constructed in this repository; the programme label stays `SOURCE_OPEN`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos287
namespace V21Cutoff

open Erdos287.V20Compiler

/-- The shared cutoff at exponent `B0 : ℕ`, in terms of the V20 cutoff function. -/
noncomputable def sharedCutoff (B0 : ℕ) (X : ℝ) : ℝ := highConductorCutoff (B0 : ℝ) X

theorem sharedCutoff_eq (B0 : ℕ) (X : ℝ) :
    sharedCutoff B0 X = highConductorCutoff (B0 : ℝ) X := rfl

/-- **`HighProjectorCutoffCompat3221`** — `SOURCE_OPEN`.

One cutoff, two consumers.  `unaccounted` is the physical unaccounted
exceptional/principal mass as a function of the cutoff, and `lowResidual` the
low-conductor reassembly residual.

The fields are: the analytic and the physical cutoff are the *same* `log^{B0} X`; the
unaccounted mass does not move when the cutoff moves; it vanishes at the shared cutoff; and
the low-conductor reassembly residual vanishes there too. -/
structure HighProjectorCutoffCompat3221 (X : ℝ) (B0 : ℕ) (Dana Dphys : ℝ)
    (unaccounted lowResidual : ℝ → ℝ) : Prop where
  /-- The cutoff exponent is positive (`B0 = 0` is excluded, `B0 = 1` is not imposed). -/
  B0_pos : 0 < B0
  /-- The analytic side uses `log^{B0} X`. -/
  ana_cutoff : Dana = sharedCutoff B0 X
  /-- The physical comparison side uses the *same* cutoff. -/
  phys_cutoff : Dphys = sharedCutoff B0 X
  /-- Changing the cutoff does not alter the unaccounted exceptional/principal piece. -/
  unaccounted_cutoff_invariant : ∀ D' : ℝ, unaccounted D' = unaccounted Dana
  /-- The unaccounted piece vanishes at the shared cutoff. -/
  unaccounted_vanishes : unaccounted Dana = 0
  /-- The low-conductor reassembly remains valid at the shared cutoff. -/
  lowCond_reassembly : lowResidual Dana = 0

/-- **`cutoffCompat_cutoffs_match`.**  `LEAN_PROVED`. -/
theorem cutoffCompat_cutoffs_match {X : ℝ} {B0 : ℕ} {Dana Dphys : ℝ}
    {unaccounted lowResidual : ℝ → ℝ}
    (h : HighProjectorCutoffCompat3221 X B0 Dana Dphys unaccounted lowResidual) :
    Dana = Dphys := by rw [h.ana_cutoff, h.phys_cutoff]

/-- **`cutoffCompat_unaccounted_invariant`.**  `LEAN_PROVED`.

Moving the cutoff cannot create or destroy unaccounted exceptional/principal mass. -/
theorem cutoffCompat_unaccounted_invariant {X : ℝ} {B0 : ℕ} {Dana Dphys : ℝ}
    {unaccounted lowResidual : ℝ → ℝ}
    (h : HighProjectorCutoffCompat3221 X B0 Dana Dphys unaccounted lowResidual)
    (D' : ℝ) : unaccounted D' = 0 := by
  rw [h.unaccounted_cutoff_invariant D', h.unaccounted_vanishes]

/-- **`cutoffCompat_matches_v20_comparison`.**  `LEAN_PROVED`.

The shared cutoff is *the same real number* as the cutoff of the V20 `B0`-indexed physical
comparison; the V20 anti-retuning firewall is therefore inherited, not bypassed. -/
theorem cutoffCompat_matches_v20_comparison {X : ℝ} {B0 : ℕ} {Dana Dphys Dcomp : ℝ}
    {unaccounted lowResidual : ℝ → ℝ} {hard model err : ℝ}
    (h : HighProjectorCutoffCompat3221 X B0 Dana Dphys unaccounted lowResidual)
    (hcomp : MuLogComparisonAtCutoff X Dcomp (B0 : ℝ) hard model err) :
    Dcomp = Dana := by
  rw [hcomp.cutoff_at_B0, h.ana_cutoff, sharedCutoff_eq]

/-- **`cutoffCompat_does_not_fix_B0`.**  `LEAN_PROVED` (anti-retuning).

Nothing in the compatibility interface forces `B0 = 1`: the statement is parametric in
`B0`, and for `B0 = 2` the interface is a different (not weaker, not stronger) requirement,
because the two cutoffs differ as soon as `log X ≠ 1`. -/
theorem cutoffCompat_does_not_fix_B0 {X : ℝ} (hX : 1 < Real.log X) :
    sharedCutoff 1 X ≠ sharedCutoff 2 X := by
  have h1 : sharedCutoff 1 X = Real.log X := by
    rw [sharedCutoff, highConductorCutoff]
    norm_num
  have h2 : sharedCutoff 2 X = Real.log X ^ (2 : ℝ) := by
    rw [sharedCutoff, highConductorCutoff]
    norm_num
  rw [h1, h2]
  intro hcon
  have hpos : (0 : ℝ) < Real.log X := lt_trans zero_lt_one hX
  have : Real.log X ^ (2 : ℝ) = Real.log X ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast (Real.log X) 2]
    norm_num
  rw [this] at hcon
  nlinarith [hcon, hX, hpos]

/-- **`cutoffCompat_not_automatic`.**  `LEAN_PROVED`.

The compatibility interface is a genuine restriction: a cutoff-dependent unaccounted mass
refutes it. -/
theorem cutoffCompat_not_automatic :
    ∃ (X : ℝ) (B0 : ℕ) (Dana Dphys : ℝ) (unaccounted lowResidual : ℝ → ℝ),
      ¬ HighProjectorCutoffCompat3221 X B0 Dana Dphys unaccounted lowResidual := by
  refine ⟨2, 1, 0, 0, id, id, ?_⟩
  intro h
  have h1 := h.unaccounted_cutoff_invariant 1
  simp at h1

end V21Cutoff
end Erdos287
