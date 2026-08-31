import Mathlib
import RequestProject.Erdos287.FullQStructuralPartition3221
import RequestProject.CurrentProgramme.ConductorSplitLargeSieve

/-!
# CurrentProgramme (post-Balanced7 pass) §6 — the tiny-modulus (Siegel–Walfisz) child

The conductor split of §5 routes the *low* conductors `f ≤ D` to a classical Siegel–Walfisz
input.  This module banks

* the literal internal cutoff `lowConductorCutoff X = (log X)^30` used by that child;
* a **firewall** showing the internal provider cutoff is *not* the physical comparison cutoff
  `Erdos287.V24FullQ.uCut X = X^{1/3}` of the historical full-`q` partition
  (`lowConductorCutoff_ne_uCut`), so no accidental identification of the two is possible;
* the uninhabited analytic socket `BalancedSevenLowConductorSiegelWalfiszInput`, recording
  the classical Siegel–Walfisz statement uniformly in the affine shift, together with the
  explicit record that the classical constant is **ineffective**
  (`explicitThreshold = none`);
* a purely logical consumer that aggregates the socket over a finite set of tiny moduli.

No analytic statement is proved here and the socket is not inhabited.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Erdos287
namespace PostBalanced7Pro

/-! ## §6.1  The internal low-conductor cutoff -/

/-- The internal cutoff of the tiny-modulus child, `(log X)^30`. -/
noncomputable def lowConductorCutoff (X : ℝ) : ℝ := (Real.log X) ^ 30

/-- **`lowConductorCutoff_nonneg`.**  `LEAN_PROVED`. -/
theorem lowConductorCutoff_nonneg (X : ℝ) : 0 ≤ lowConductorCutoff X :=
  even_iff_two_dvd.mpr ⟨15, by norm_num⟩ |>.pow_nonneg _

/-- **`lowConductorCutoff_mono`.**  `LEAN_PROVED` for `X ≥ 1`. -/
theorem lowConductorCutoff_mono {X Y : ℝ} (hX : 1 ≤ X) (hXY : X ≤ Y) :
    lowConductorCutoff X ≤ lowConductorCutoff Y := by
  have h0 : 0 ≤ Real.log X := Real.log_nonneg hX
  have h1 : Real.log X ≤ Real.log Y := Real.log_le_log (by linarith) hXY
  exact pow_le_pow_left₀ h0 h1 30

/-- **`lowConductorCutoff_ne_uCut`.**  `LEAN_PROVED`.

**Firewall.**  The internal cutoff of the tiny-modulus provider is a *different* function
from the physical comparison cutoff `uCut X = X^{1/3}` of the historical full-`q` structural
partition.  They already disagree at `X = 1`, so the two may never be silently identified. -/
theorem lowConductorCutoff_ne_uCut :
    lowConductorCutoff 1 ≠ Erdos287.V24FullQ.uCut 1 := by
  have h1 : lowConductorCutoff 1 = 0 := by
    simp [lowConductorCutoff]
  have h2 : Erdos287.V24FullQ.uCut 1 = 1 := by
    simp [Erdos287.V24FullQ.uCut]
  rw [h1, h2]
  norm_num

/-- **`lowConductorCutoff_ne_uCut_fun`.**  `LEAN_PROVED`.  The two cutoffs are distinct as
functions. -/
theorem lowConductorCutoff_ne_uCut_fun :
    lowConductorCutoff ≠ Erdos287.V24FullQ.uCut := by
  intro h
  exact lowConductorCutoff_ne_uCut (congrFun h 1)

/-! ## §6.2  The Siegel–Walfisz socket (uninhabited) -/

/-- **`BalancedSevenLowConductorSiegelWalfiszInput`** —
`EXTERNAL / ANALYTIC / UNINHABITED / INEFFECTIVE`.

The tiny-modulus child of the conductor split.  `psi s q a` is the physical prime-weighted
count in the residue class `a mod q` of the affine sequence with shift `s`, and `A` is the
declared log-power saving.

The last field records that the classical Siegel–Walfisz constant is **ineffective**: the
socket may not supply an explicit threshold.  This is exactly the reason
`287-EFFECTIVE-POLYLOG-MODULUS-REPLACEMENT45` stays open. -/
structure BalancedSevenLowConductorSiegelWalfiszInput
    (X : ℝ) (A sMax : ℕ) (psi : ℕ → ℕ → ℕ → ℝ) (explicitThreshold : Option ℕ) : Prop where
  /-- The scale is nontrivial and the declared saving is a genuine log power. -/
  scale : 3 ≤ X ∧ 0 < A
  /-- The classical Siegel–Walfisz bound, uniform over the tiny moduli and over the affine
  shift `s ≤ sMax`. -/
  siegel_walfisz :
    ∀ s q a : ℕ, s ≤ sMax → 0 < q → (q : ℝ) ≤ lowConductorCutoff X → Nat.Coprime a q →
      |psi s q a - X / (Nat.totient q : ℝ)| ≤ X / (Real.log X) ^ A
  /-- The bound is stated against the *internal* provider cutoff, not the physical one. -/
  cutoff_is_internal : (0 : ℝ) ≤ lowConductorCutoff X
  /-- The classical constant is ineffective: no explicit threshold is supplied. -/
  ineffective : explicitThreshold = none

/-- **`lowConductor_aggregate_bound`.**  `LEAN_PROVED` *conditionally on the socket*.

Aggregating the socket over a finite set of tiny moduli and residues costs only the
cardinality of the index set.  This is a finite triangle-inequality consequence, **not** an
analytic theorem. -/
theorem lowConductor_aggregate_bound
    {X : ℝ} {A sMax : ℕ} {psi : ℕ → ℕ → ℕ → ℝ} {explicitThreshold : Option ℕ}
    (h : BalancedSevenLowConductorSiegelWalfiszInput X A sMax psi explicitThreshold)
    (T : Finset (ℕ × ℕ × ℕ))
    (hT : ∀ t ∈ T, t.1 ≤ sMax ∧ 0 < t.2.1 ∧ ((t.2.1 : ℝ) ≤ lowConductorCutoff X) ∧
      Nat.Coprime t.2.2 t.2.1) :
    ∑ t ∈ T, |psi t.1 t.2.1 t.2.2 - X / (Nat.totient t.2.1 : ℝ)| ≤
      T.card * (X / (Real.log X) ^ A) := by
  calc ∑ t ∈ T, |psi t.1 t.2.1 t.2.2 - X / (Nat.totient t.2.1 : ℝ)|
      ≤ ∑ _t ∈ T, X / (Real.log X) ^ A := by
        refine Finset.sum_le_sum fun t ht => ?_
        obtain ⟨h1, h2, h3, h4⟩ := hT t ht
        exact h.siegel_walfisz t.1 t.2.1 t.2.2 h1 h2 h3 h4
    _ = T.card * (X / (Real.log X) ^ A) := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-- **`lowConductorSiegelWalfisz_not_automatic`.**  `LEAN_PROVED`.

The socket is a genuine restriction and is not inhabited here: an effective threshold is
already inconsistent with the ineffectivity record. -/
theorem lowConductorSiegelWalfisz_not_automatic :
    ∃ (X : ℝ) (A sMax : ℕ) (psi : ℕ → ℕ → ℕ → ℝ) (explicitThreshold : Option ℕ),
      ¬ BalancedSevenLowConductorSiegelWalfiszInput X A sMax psi explicitThreshold := by
  refine ⟨3, 1, 0, (fun _ _ _ => 0), some 0, ?_⟩
  intro h
  have hne := h.ineffective
  simp at hne

/-- **`lowConductor_effectivity_firewall`.**  `LEAN_PROVED`.

No inhabitant of the socket ever supplies an explicit threshold.  Hence the tiny-modulus
child can never discharge `287-EFFECTIVE-POLYLOG-MODULUS-REPLACEMENT45`. -/
theorem lowConductor_effectivity_firewall
    {X : ℝ} {A sMax : ℕ} {psi : ℕ → ℕ → ℕ → ℝ} {explicitThreshold : Option ℕ}
    (h : BalancedSevenLowConductorSiegelWalfiszInput X A sMax psi explicitThreshold) :
    ∀ M : ℕ, explicitThreshold ≠ some M := by
  intro M hM
  rw [h.ineffective] at hM
  simp at hM

end PostBalanced7Pro
end Erdos287
