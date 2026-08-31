import Mathlib
import RequestProject.Erdos287.DoubleOrthogonalityFiveBox3221

/-!
# V21, Phase 5 — the short-shift geometry and the external one-dimensional sieve interface

`ONE-DIMENSIONAL-SIEVE287 : EXTERNAL ANALYTIC PASS CANDIDATE / UNINHABITED INTERFACE`

The **geometry** is Lean-proved (it is the output of the five-box double orthogonality):
for admissible `t` the two five-box products satisfy `W = W' + q t`, `(q, W') = 1` and
`q ∣ 2 m W' + s`.

The **counting** statement — the number of admissible shifts `t` in the physical interval
is `≤ C_sieve · (T / log X) · q/φ(q)` — is an *external* one-dimensional (linear) sieve
input.  Selberg's sieve is not formalised here and no such theorem is proved or
axiomatised: the interface below is a plain `Prop` structure and **is never inhabited**.

The exact sieve parameter metadata is stored with the interface:
`z = T^{1/20}`, sieve dimension `1`, and the `z²` remainder negligible relative to
`T / log X`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset
open scoped BigOperators Classical

namespace Erdos287
namespace V21Sieve

open Erdos287.V21DoubleOrth

/-! ## §1. The Lean-proved short-shift geometry -/

/-- The geometric data produced by the double orthogonality of the `AA` child. -/
structure ShortShiftGeometry (q s m W W' t : ℤ) : Prop where
  /-- `W = W' + q t`. -/
  shift : W = W' + q * t
  /-- `(q, W') = 1`. -/
  coprime : IsCoprime q W'
  /-- `q ∣ 2 m W' + s`. -/
  affine : q ∣ 2 * m * W' + s

/-- **`shortShiftGeometry_of_doubleOrthogonality`.**  `LEAN_PROVED`.

The geometry is a *consequence* of the two full-character orthogonality relations; nothing
about it is assumed. -/
theorem shortShiftGeometry_of_doubleOrthogonality {q s m : ℤ} {p p' : Fin 5 → ℤ}
    (hs : s ^ 2 = 1) (hcop : IsCoprime (2 * m) q)
    (hW : (-2 * s * m * fiveProduct p) ≡ 1 [ZMOD q])
    (hW' : (-2 * s * m * fiveProduct p') ≡ 1 [ZMOD q]) :
    ∃ t : ℤ, ShortShiftGeometry q s m (fiveProduct p) (fiveProduct p') t := by
  obtain ⟨t, hshift, hcop', hdvd⟩ := fiveBox_shift_exists hs hcop hW hW'
  exact ⟨t, ⟨hshift, hcop', hdvd⟩⟩

/-! ## §2. The physical short-shift datum -/

/-- Pure data for the short-shift count: the modulus, the sign, the `m`-sample, the second
five-box product, the physical `t`-interval, the five physical prime boxes, and the sieve
parameters `z`, `T`, `X` with the constant. -/
structure ShortShiftSieveData where
  /-- The modulus. -/
  q : ℕ
  /-- The sign `s = ±1`. -/
  s : ℤ
  /-- The `m`-sample. -/
  m : ℤ
  /-- The second five-box product `W'`. -/
  Wprime : ℤ
  /-- The physical `t`-interval. -/
  Tbox : Finset ℤ
  /-- The five physical `Y`-scale prime boxes. -/
  Ybox : Fin 5 → Finset ℕ
  /-- The sieve level `z`. -/
  z : ℝ
  /-- The physical shift scale `T`. -/
  T : ℝ
  /-- The global scale `X`. -/
  X : ℝ
  /-- The sieve constant. -/
  Csieve : ℝ

/-- The sieve dimension of the linear (one-dimensional) sieve used here. -/
def sieveDimension : ℕ := 1

theorem sieveDimension_eq_one : sieveDimension = 1 := rfl

/-- The recorded sieve level exponent `z = T^{1/20}`. -/
def sieveLevelExponent : ℚ := 1 / 20

theorem sieveLevelExponent_value : sieveLevelExponent = 1 / 20 := rfl

/-- The admissible shifts: those `t` in the physical interval for which `W' + q t` is a
product of five primes taken from the five physical `Y`-scale boxes. -/
noncomputable def admissibleShifts (D : ShortShiftSieveData) : Finset ℤ :=
  D.Tbox.filter (fun t => ∃ p : Fin 5 → ℤ,
    (∀ i : Fin 5, (p i).natAbs ∈ D.Ybox i) ∧
      D.Wprime + (D.q : ℤ) * t = fiveProduct p)

/-! ## §3. The external analytic interface — `UNINHABITED` -/

/-- **`ShortShiftRoughSieve3221Input`** — `EXTERNAL ANALYTIC / UNINHABITED`.

The audited physical implication: given the short-shift geometry, the five-box structure of
`W = W' + q t`, the level `z = T^{1/20}` below every physical prime-box endpoint, the
coprimality `(q, W') = 1` and the negligible `z²` remainder, the number of admissible `t`
in the physical interval is at most `C_sieve · (T/log X) · q/φ(q)`.

**No inhabitant is constructed anywhere in this repository**, and no `axiom` is used. -/
structure ShortShiftRoughSieve3221Input (D : ShortShiftSieveData) : Prop where
  /-- The recorded sieve level: `z = T^{1/20}`. -/
  z_eq : D.z = D.T ^ ((sieveLevelExponent : ℝ))
  /-- The level is below every physical prime-box lower endpoint. -/
  z_below_boxes : ∀ (i : Fin 5) (p : ℕ), p ∈ D.Ybox i → D.z < (p : ℝ)
  /-- `(q, W') = 1`. -/
  coprime_q_Wprime : IsCoprime (D.q : ℤ) D.Wprime
  /-- The `z²` remainder is negligible relative to `T/log X`. -/
  remainder_negligible : D.z ^ 2 ≤ D.T / Real.log D.X
  /-- **The open analytic count.** -/
  count_bound : ((admissibleShifts D).card : ℝ)
      ≤ D.Csieve * (D.T / Real.log D.X) * ((D.q : ℝ) / (Nat.totient D.q : ℝ))

/-- A probe datum (pure data; not an inhabitant of the analytic interface). -/
noncomputable def probeSieveData : ShortShiftSieveData where
  q := 1
  s := 1
  m := 1
  Wprime := 1
  Tbox := ∅
  Ybox := fun _ => ∅
  z := 0
  T := 1
  X := Real.exp 1
  Csieve := -1

/-- **`shortShiftSieve_not_automatic`.**  `LEAN_PROVED`.

The sieve interface is a genuine restriction: explicit data refute it. -/
theorem shortShiftSieve_not_automatic :
    ∃ D : ShortShiftSieveData, ¬ ShortShiftRoughSieve3221Input D := by
  refine ⟨probeSieveData, ?_⟩
  intro h
  have h1 := h.count_bound
  have hlog : Real.log probeSieveData.X = 1 := by
    simp [probeSieveData, Real.log_exp]
  rw [hlog] at h1
  simp only [probeSieveData, Nat.totient_one, Nat.cast_one] at h1
  norm_num at h1

end V21Sieve
end Erdos287
