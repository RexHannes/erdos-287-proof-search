import Mathlib
import RequestProject.Erdos287.HighQuotientShiftedGram3221

/-!
# V20, Phase J — the sixth-moment sufficient bridge

`3221-HIGHCOND-RESIDUE-SIXTH-MOMENT45 : STRONGER SUFFICIENT / OPEN`

The sixth moment of the high-conductor residue source is a **stronger sufficient**
alternative to the controlling HHH Gram socket, *not* the controlling frontier.  It is
recorded here with its finite bridge fully proved and its analytic input left uninhabited.

## Contents

* **§28.**  `sixthMoment` — the purely finite definition
  `M6 = ∑_q ∑_{a unit mod q} |C_q^{>D}(a)|⁶`.
* **§29.**  `injOn_affineSample` — the injectivity of `m ↦ −s(2m)⁻¹` on the physical
  `m`-box under the bankable hypothesis `M < q`, and the finite Hölder inequality
  `sixthMoment_holder_at`, in the cube form
  `(∑_m |C(a_m)|²)³ ≤ (#m)² ∑_a |C(a)|⁶`, followed by the Hölder step over `q`
  (`sixthMoment_holder_over_q`).
* **§30.**  `HighCondResidueSixthMoment3221Input` — uninhabited, with intended bound
  `M6 ≤ Q² T³ polylog`; the algebraic consequence `sixthMoment_variance_exponent`, and the
  capacity ledger `sixthMoment_power_margin` (`117/105 − 116/105 = 1/105 > 0`).

**The sixth-moment route is not promoted to the controlling frontier**; the HHH Gram
remains the first exact analytic residual.  Erdős #287 remains OPEN; Balanced7 remains
OPEN.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4000

open Finset
open scoped BigOperators

namespace Erdos287
namespace V20Sixth

open Erdos287.V20Gram

/-! ## §28. The sixth moment -/

/-- The unit residues modulo `q`, as an explicit finite index set of naturals. -/
def unitResidues (q : ℕ) : Finset ℕ :=
  (Finset.range q).filter (fun a => Nat.Coprime a q)

/-- **The sixth moment** `M6 = ∑_q ∑_{a unit mod q} |C_q(a)|⁶` — a purely finite
definition. -/
noncomputable def sixthMoment (Qbox : Finset ℕ) (C : (q : ℕ) → ZMod q → ℂ) : ℝ :=
  ∑ q ∈ Qbox, ∑ a ∈ unitResidues q, ‖C q ((a : ℕ) : ZMod q)‖ ^ 6

/-- The sixth moment is nonnegative. -/
theorem sixthMoment_nonneg (Qbox : Finset ℕ) (C : (q : ℕ) → ZMod q → ℂ) :
    0 ≤ sixthMoment Qbox C :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity

/-! ## §29. Injectivity of the inverse sample, and the finite Hölder step -/

/-- **`injOn_affineSample`.**  `LEAN_PROVED`.

Under the bankable hypothesis `M < q` (every `m` in the box is smaller than the modulus),
the inverse sampling map `m ↦ −s(2m)⁻¹` is injective on the physical unit `m`-box. -/
theorem injOn_affineSample (q : ℕ) [NeZero q] (s : ℤ) (hs : s ^ 2 = 1) (Mset : Finset ℕ)
    (hlt : ∀ m ∈ Mset, m < q)
    (hu : ∀ m ∈ unitBox q Mset, IsUnit ((2 * m : ℕ) : ZMod q))
    (h2s : IsUnit (((-2 * s : ℤ) : ZMod q))) :
    Set.InjOn (fun m => affineSample q s m) (unitBox q Mset) := by
  intro m hm m' hm' h
  have hmF : m ∈ unitBox q Mset := hm
  have hmF' : m' ∈ unitBox q Mset := hm'
  have h1 : ((-2 * s : ℤ) : ZMod q) * ((m : ℕ) : ZMod q)
      = ((-2 * s : ℤ) : ZMod q) * ((m' : ℕ) : ZMod q) := by
    rw [← affineSample_inv hs (hu m hmF), ← affineSample_inv hs (hu m' hmF')]
    simp only at h
    rw [h]
  have h2 : ((m : ℕ) : ZMod q) = ((m' : ℕ) : ZMod q) := h2s.mul_left_cancel h1
  have hm1 : m < q := hlt m (Finset.mem_filter.mp hmF).1
  have hm2 : m' < q := hlt m' (Finset.mem_filter.mp hmF').1
  have h3 := congrArg ZMod.val h2
  rwa [ZMod.val_natCast_of_lt hm1, ZMod.val_natCast_of_lt hm2] at h3

/-- The sampled sixth-power sum is dominated by the full residue sixth-power sum. -/
theorem sampled_sixth_le (q : ℕ) [NeZero q] (s : ℤ) (hs : s ^ 2 = 1) (Mset : Finset ℕ)
    (C : ZMod q → ℂ) (hlt : ∀ m ∈ Mset, m < q)
    (hu : ∀ m ∈ unitBox q Mset, IsUnit ((2 * m : ℕ) : ZMod q))
    (h2s : IsUnit (((-2 * s : ℤ) : ZMod q))) :
    ∑ m ∈ unitBox q Mset, ‖C (affineSample q s m)‖ ^ 6
      ≤ ∑ a ∈ unitResidues q, ‖C ((a : ℕ) : ZMod q)‖ ^ 6 := by
  classical
  have hrep : ∀ m : ℕ, (((affineSample q s m).val : ℕ) : ZMod q) = affineSample q s m := by
    intro m
    simp [ZMod.natCast_val, ZMod.cast_id]
  have hinj : Set.InjOn (fun m => (affineSample q s m).val) (unitBox q Mset) := by
    intro m hm m' hm' h
    refine injOn_affineSample q s hs Mset hlt hu h2s hm hm' ?_
    have := congrArg (fun a : ℕ => ((a : ℕ) : ZMod q)) h
    simpa [hrep] using this
  have himg : (unitBox q Mset).image (fun m => (affineSample q s m).val) ⊆ unitResidues q := by
    intro a ha
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp ha
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (ZMod.val_lt _), ?_⟩
    have hunit : IsUnit (affineSample q s m) := affineSample_isUnit hs (hu m hm)
    rw [← ZMod.isUnit_iff_coprime]
    simpa [hrep] using hunit
  calc ∑ m ∈ unitBox q Mset, ‖C (affineSample q s m)‖ ^ 6
      = ∑ a ∈ (unitBox q Mset).image (fun m => (affineSample q s m).val),
          ‖C ((a : ℕ) : ZMod q)‖ ^ 6 := by
        rw [Finset.sum_image hinj]
        exact Finset.sum_congr rfl fun m _ => by rw [hrep]
    _ ≤ ∑ a ∈ unitResidues q, ‖C ((a : ℕ) : ZMod q)‖ ^ 6 :=
        Finset.sum_le_sum_of_subset_of_nonneg himg (fun a _ _ => by positivity)

/-- **`sixthMoment_holder_at`.**  `LEAN_PROVED_FINITE`.

The injective-sample Hölder inequality at a single modulus, in cleared (cube) form:

`(∑_m |C(a_m)|²)³ ≤ (#m)² · ∑_{a unit} |C(a)|⁶`.

This is the exact finite content of `∑_m |C(a_m)|² ≤ (#m)^{2/3} (∑_a |C(a)|⁶)^{1/3}`. -/
theorem sixthMoment_holder_at (q : ℕ) [NeZero q] (s : ℤ) (hs : s ^ 2 = 1) (Mset : Finset ℕ)
    (C : ZMod q → ℂ) (hlt : ∀ m ∈ Mset, m < q)
    (hu : ∀ m ∈ unitBox q Mset, IsUnit ((2 * m : ℕ) : ZMod q))
    (h2s : IsUnit (((-2 * s : ℤ) : ZMod q))) :
    (∑ m ∈ unitBox q Mset, ‖C (affineSample q s m)‖ ^ 2) ^ 3
      ≤ ((unitBox q Mset).card : ℝ) ^ 2 *
        ∑ a ∈ unitResidues q, ‖C ((a : ℕ) : ZMod q)‖ ^ 6 := by
  have hstep1 : (∑ m ∈ unitBox q Mset, ‖C (affineSample q s m)‖ ^ 2) ^ 3
      ≤ ((unitBox q Mset).card : ℝ) ^ 2 *
        ∑ m ∈ unitBox q Mset, ‖C (affineSample q s m)‖ ^ 6 := by
    have h := pow_sum_le_card_mul_sum_pow
      (f := fun m => ‖C (affineSample q s m)‖ ^ 2) (s := unitBox q Mset)
      (fun i _ => by positivity) 2
    have hrw : ∀ m : ℕ, (‖C (affineSample q s m)‖ ^ 2) ^ 3
        = ‖C (affineSample q s m)‖ ^ 6 := by
      intro m; ring
    simpa [hrw] using h
  have hstep2 := sampled_sixth_le q s hs Mset C hlt hu h2s
  have hcard : (0 : ℝ) ≤ ((unitBox q Mset).card : ℝ) ^ 2 := by positivity
  exact le_trans hstep1 (mul_le_mul_of_nonneg_left hstep2 hcard)

/-- **`sixthMoment_holder_over_q`.**  `LEAN_PROVED_FINITE`.

The Hölder step over the modulus box: if at each modulus the sampled square-sum is
controlled by the local sixth moment with a uniform prefactor, then the total is controlled
by the global sixth moment. -/
theorem sixthMoment_holder_over_q (Qbox : Finset ℕ) (C : (q : ℕ) → ZMod q → ℂ)
    (V : ℕ → ℝ) (pref : ℝ)
    (hloc : ∀ q ∈ Qbox, V q ≤ pref * ∑ a ∈ unitResidues q, ‖C q ((a : ℕ) : ZMod q)‖ ^ 6) :
    ∑ q ∈ Qbox, V q ≤ pref * sixthMoment Qbox C := by
  rw [sixthMoment, Finset.mul_sum]
  exact Finset.sum_le_sum hloc

/-! ## §30. The sixth-moment capacity ledger — external, uninhabited -/

/-- **`HighCondResidueSixthMoment3221Input`** — `OPEN / STRONGER SUFFICIENT`.

The intended bound `M6 ≤ Q² · T³ · polylog` on the exact sixth moment.  **Never inhabited
in this repository.** -/
structure HighCondResidueSixthMoment3221Input (Qbox : Finset ℕ) (C : (q : ℕ) → ZMod q → ℂ)
    (Qscale Tscale polylog : ℝ) : Prop where
  /-- The modulus scale is positive. -/
  Qscale_pos : 0 < Qscale
  /-- The `T`-scale is positive. -/
  Tscale_pos : 0 < Tscale
  /-- The logarithmic factor is positive. -/
  polylog_pos : 0 < polylog
  /-- **The open analytic estimate.** -/
  sixth_bound : sixthMoment Qbox C ≤ Qscale ^ 2 * Tscale ^ 3 * polylog

/-- The sixth-moment input is not automatic. -/
theorem sixthMoment_input_not_automatic :
    ∃ (Qbox : Finset ℕ) (C : (q : ℕ) → ZMod q → ℂ) (Qscale Tscale polylog : ℝ),
      ¬ HighCondResidueSixthMoment3221Input Qbox C Qscale Tscale polylog := by
  refine ⟨{1}, fun _ _ => 1, 1, 1, 1 / 2, ?_⟩
  intro h
  have h1 := h.sixth_bound
  rw [sixthMoment] at h1
  norm_num [unitResidues] at h1

/-- **`sixthMoment_variance_exponent`.**  `CONDITIONAL_COMPILER / LEAN_PROVED`.

The algebraic bridge: the sixth-moment input, together with the Hölder step, yields the
variance with the recorded exponent budget.  The exponent bookkeeping itself is the
rational ledger below. -/
theorem sixthMoment_variance_exponent {Qbox : Finset ℕ} {C : (q : ℕ) → ZMod q → ℂ}
    {Qscale Tscale polylog pref target : ℝ} (V : ℕ → ℝ) (hpref : 0 ≤ pref)
    (hin : HighCondResidueSixthMoment3221Input Qbox C Qscale Tscale polylog)
    (hloc : ∀ q ∈ Qbox, V q ≤ pref * ∑ a ∈ unitResidues q, ‖C q ((a : ℕ) : ZMod q)‖ ^ 6)
    (hbudget : pref * (Qscale ^ 2 * Tscale ^ 3 * polylog) ≤ target) :
    ∑ q ∈ Qbox, V q ≤ target := by
  have h1 := sixthMoment_holder_over_q Qbox C V pref hloc
  have h2 : pref * sixthMoment Qbox C ≤ pref * (Qscale ^ 2 * Tscale ^ 3 * polylog) :=
    mul_le_mul_of_nonneg_left hin.sixth_bound hpref
  linarith

/-- **`sixthMoment_power_margin`.**  `PROVED_ALGEBRAIC / METADATA_ONLY`.

The conditional power margin of the sixth-moment route: `117/105 − 116/105 = 1/105 > 0`.

This margin is **not** a reason to promote the route: it is conditional on an open input
which is strictly stronger than the controlling HHH Gram socket. -/
theorem sixthMoment_power_margin :
    (117 : ℚ) / 105 - 116 / 105 = 1 / 105 ∧ (0 : ℚ) < 1 / 105 := by
  constructor <;> norm_num

end V20Sixth
end Erdos287
