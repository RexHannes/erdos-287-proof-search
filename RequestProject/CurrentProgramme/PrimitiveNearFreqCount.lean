import Mathlib
import RequestProject.CurrentProgramme.PrimitiveFareyNearCollision

/-!
# Near-frequency exact count precursor — Erdős #287, SHARED-g₀ REPAIR Δ, §7

**Exact `Finset` cardinality.**  No asymptotics, no analytic saving.

The existing `PrimitiveFareyNearCollision` machinery is kept verbatim; this module only adds
the *current parameterisation* of the near-frequency count, in which the Farey threshold is

```
‖D/Λ‖ ≤ H/A          (Λ = lcm(g₁,g₂) = g₀r₁r₂),
```

instead of `1/A`.  Proved:

* `nearFreqSet_eq` — the `H`-threshold set is literally the banked near-collision set with
  `A` replaced by `A/H`;
* `nearFreq_D_mem_Icc` — the exact finite range of the admissible `D`: `|D| ≤ ⌊ΛH/A⌋`, so
  there are exactly `2⌊ΛH/A⌋ + 1` possible integers `D`;
* `nearFreqSet_card_le` — combining with the banked fixed-`D` fibre multiplicity `≤ g₀`
  (`DET1-PRIMITIVE-D-MULTIPLICITY45`):

```
N_near ≤ g₀ + 2 g₀ ⌊ΛH/A⌋,
```

the exact finite precursor of the research display `N_near ≪ g₀ + g₁g₂H/A`
(note `g₀ Λ = g₁g₂`, recorded as `g0_mul_lambda_eq`).

Research status: `DET1-PRIMITIVE-NEARFREQ-COUNT45 : FORMALLY PROVED COUNT PRECURSOR.`  The
analytic claim that this yields a fixed-power saving is **not** formalised.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset

namespace Erdos287
namespace NearFreqCount

open Erdos287.PrimitiveD
open Erdos287.PrimitiveFarey

/-- `g₀ · Λ = g₁ · g₂`: the modulus bookkeeping behind the research display. -/
theorem g0_mul_lambda_eq (g0 r1 r2 : ℕ) :
    g0 * (g0 * r1 * r2) = (g0 * r1) * (g0 * r2) := by ring

/-- The near-frequency set at threshold `H/A`. -/
noncomputable def nearFreqSet (g0 r1 r2 : ℕ) (H A : ℚ) : Finset (ℤ × ℤ) :=
  ((Finset.Icc (1 : ℤ) ((g0 : ℤ) * r1)) ×ˢ (Finset.Icc (1 : ℤ) ((g0 : ℤ) * r2))).filter
    (fun p => |(p.1 : ℚ) / ((g0 : ℚ) * r1) - (p.2 : ℚ) / ((g0 : ℚ) * r2)| ≤ H / A)

/-- The `H`-threshold set is the banked near-collision set with `A` replaced by `A/H`. -/
theorem nearFreqSet_eq (g0 r1 r2 : ℕ) (H A : ℚ) :
    nearFreqSet g0 r1 r2 H A = nearCollisionSet g0 r1 r2 (A / H) := by
  unfold nearFreqSet nearCollisionSet
  rw [one_div_div]

/-- **Exact `D`-range.**  `LEAN_PROVED`.  Every near-frequency pair has its `D = r₂t₁ - r₁t₂`
in the explicit integer window `[-⌊ΛH/A⌋, ⌊ΛH/A⌋]`, so at most `2⌊ΛH/A⌋ + 1` integers `D`
occur. -/
theorem nearFreq_D_mem_Icc {g0 r1 r2 : ℕ} (hg0 : 0 < g0) (hr1 : 0 < r1) (hr2 : 0 < r2)
    {H A : ℚ} {p : ℤ × ℤ} (hp : p ∈ nearFreqSet g0 r1 r2 H A) :
    (r2 : ℤ) * p.1 - (r1 : ℤ) * p.2
      ∈ Finset.Icc (-⌊((g0 : ℚ) * r1 * r2) * H / A⌋) ⌊((g0 : ℚ) * r1 * r2) * H / A⌋ := by
  rw [nearFreqSet, Finset.mem_filter] at hp
  have hbound := farey_near_collision_D_bound hg0 hr1 hr2 p.1 p.2
    (A := A / H) (by rw [one_div_div]; exact hp.2)
  rw [div_div_eq_mul_div] at hbound
  have habs : |(r2 : ℤ) * p.1 - (r1 : ℤ) * p.2| ≤ ⌊((g0 : ℚ) * r1 * r2) * H / A⌋ := by
    refine Int.le_floor.2 ?_
    calc ((|(r2 : ℤ) * p.1 - (r1 : ℤ) * p.2| : ℤ) : ℚ)
        = |(((r2 : ℤ) * p.1 - (r1 : ℤ) * p.2 : ℤ) : ℚ)| := by push_cast; simp
      _ ≤ ((g0 : ℚ) * r1 * r2) * H / A := hbound
  rw [Finset.mem_Icc]
  constructor
  · linarith [neg_abs_le ((r2 : ℤ) * p.1 - (r1 : ℤ) * p.2), habs]
  · linarith [le_abs_self ((r2 : ℤ) * p.1 - (r1 : ℤ) * p.2), habs]

/-- **`DET1-PRIMITIVE-NEARFREQ-COUNT45`.**  `LEAN_PROVED`.

The exact finite near-frequency count precursor: with `B = ⌊ΛH/A⌋`,

```
#{near-frequency pairs} ≤ g₀ + 2 g₀ B.
```

Only the exact finite inequality is banked; the asymptotic form `g₀ + g₁g₂H/A` and any
analytic saving derived from it are **not** formalised. -/
theorem nearFreqSet_card_le {g0 r1 r2 : ℕ} (hg0 : 0 < g0) (hr1 : 0 < r1) (hr2 : 0 < r2)
    (hcop : Nat.Coprime r1 r2) {H A : ℚ} (hH : 0 < H) (hA : 0 < A) :
    (nearFreqSet g0 r1 r2 H A).card
      ≤ g0 + 2 * g0 * (⌊((g0 : ℚ) * r1 * r2) * H / A⌋).toNat := by
  have hAH : 0 < A / H := div_pos hA hH
  have hcard := nearCollisionSet_card_le hg0 hr1 hr2 hcop hAH
  rw [nearFreqSet_eq g0 r1 r2 H A]
  have hrw : ((g0 : ℚ) * r1 * r2) / (A / H) = ((g0 : ℚ) * r1 * r2) * H / A := by
    rw [div_div_eq_mul_div]
  rw [hrw] at hcard
  calc (nearCollisionSet g0 r1 r2 (A / H)).card
      ≤ (2 * (⌊((g0 : ℚ) * r1 * r2) * H / A⌋).toNat + 1) * g0 := hcard
    _ = g0 + 2 * g0 * (⌊((g0 : ℚ) * r1 * r2) * H / A⌋).toNat := by ring

end NearFreqCount
end Erdos287
