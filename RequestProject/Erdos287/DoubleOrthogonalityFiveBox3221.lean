import Mathlib
import RequestProject.Erdos287.TwoHighProjector3221

/-!
# V21, Phase 2 — five-box double orthogonality, reproved source-exactly

`3221-TWO-HIGHPROJECTOR-FIVEBOX-SIEVE45 : DOUBLE ORTHOGONALITY / LEAN_PROVED_FINITE`

For the `AA` (full–full) child both characters are summed over the *whole* ambient set, so
character orthogonality applies on both sides.  This file proves, with the signs and the
unit conditions explicit and with **no** coercion shortcuts:

* `fullFull_orthogonality_left`  — a non-vanishing `χ`-sum forces `−2 s m W ≡ 1 (mod q)`;
* `fullFull_orthogonality_right` — the same on the `ψ` side, with `W'`;
* `affine_congruence_iff_dvd`    — `−2 s m W ≡ 1 (mod q) ↔ q ∣ 2 m W + s` (for `s² = 1`);
* `doubleOrthogonality_congruence` — `W ≡ W' (mod q)` once `2m` is invertible;
* `doubleOrthogonality_shift_exists` — the integer `t` with `W − W' = q t`;
* `doubleOrthogonality_affineDivisor` — `q ∣ 2 m W' + s`;
* `doubleOrthogonality_coprime` — `(q, W') = 1`, the coprimality the short-shift sieve needs;
* the two sign branches `s = +1`, `s = −1` (`sign_sq_iff`, `affine_divisor_sign_pos`,
  `affine_divisor_sign_neg`);
* the five-box products `W = p₁p₂p₃p₄p₅`, `W' = p₁'p₂'p₃'p₄'p₅'` (`fiveProduct`), their
  character factorisation `char_fiveProduct` (reusing the V20 five-box factorisation
  convention) and the shifted-product statement `fiveBox_shift_exists`.

Nothing here is analytic.  Erdős #287 remains **OPEN**; Balanced7 remains **OPEN**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4000

open Finset
open scoped BigOperators

namespace Erdos287
namespace V21DoubleOrth

/-! ## §1. The two sign branches -/

/-- `s² = 1` in `ℤ` means exactly `s = ±1`. -/
theorem sign_sq_iff (s : ℤ) : s ^ 2 = 1 ↔ s = 1 ∨ s = -1 := by
  constructor
  · intro h
    have h0 : (s - 1) * (s + 1) = 0 := by ring_nf; linarith [h]
    rcases mul_eq_zero.mp h0 with h1 | h1
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  · rintro (rfl | rfl) <;> norm_num

/-! ## §2. The affine congruence, with the sign explicit -/

/-- **`affine_congruence_iff_dvd`.**  `LEAN_PROVED`.

For `s = ±1`, the orthogonality congruence and the affine divisibility condition are the
same statement:

`−2 s m W ≡ 1 (mod q)  ↔  q ∣ 2 m W + s`. -/
theorem affine_congruence_iff_dvd {q s m W : ℤ} (hs : s ^ 2 = 1) :
    (-2 * s * m * W) ≡ 1 [ZMOD q] ↔ q ∣ 2 * m * W + s := by
  have hss : s * s = 1 := by linear_combination hs
  have hkey : (1 : ℤ) - (-2 * s * m * W) = s * (2 * m * W + s) := by
    linear_combination -hss
  constructor
  · intro h
    have hd : q ∣ 1 - (-2 * s * m * W) := Int.ModEq.dvd h
    rw [hkey] at hd
    have hd2 : q ∣ s * (s * (2 * m * W + s)) := Dvd.dvd.mul_left hd s
    have hcancel : s * (s * (2 * m * W + s)) = 2 * m * W + s := by
      linear_combination (2 * m * W + s) * hss
    rwa [hcancel] at hd2
  · intro h
    have hd : q ∣ 1 - (-2 * s * m * W) := by
      rw [hkey]
      exact Dvd.dvd.mul_left h s
    exact (Int.modEq_iff_dvd.mpr hd)

/-- The `s = +1` branch. -/
theorem affine_divisor_sign_pos {q m W : ℤ} :
    (-2 * (1 : ℤ) * m * W) ≡ 1 [ZMOD q] ↔ q ∣ 2 * m * W + 1 :=
  affine_congruence_iff_dvd (by norm_num)

/-- The `s = −1` branch. -/
theorem affine_divisor_sign_neg {q m W : ℤ} :
    (-2 * (-1 : ℤ) * m * W) ≡ 1 [ZMOD q] ↔ q ∣ 2 * m * W + (-1) :=
  affine_congruence_iff_dvd (by norm_num)

/-! ## §3. The two full-character orthogonality implications -/

/-- **`fullFull_orthogonality_left`.**  `LEAN_PROVED_FINITE`.

The `χ` side of the `AA` child: if the full character sum at `−2 s m W` does not vanish,
then `−2 s m W ≡ 1 (mod q)`.  (Orthogonality over the *whole* ambient character set — this
is exactly why the two-projector reassembly puts the full sums in `AA`.) -/
theorem fullFull_orthogonality_left {q : ℕ} [NeZero q] {s m W : ℤ}
    (hne : (∑ chi : DirichletCharacter ℂ q, chi (((-2 * s * m * W : ℤ) : ZMod q))) ≠ 0) :
    (-2 * s * m * W) ≡ 1 [ZMOD (q : ℤ)] := by
  by_contra hcon
  have hx : (((-2 * s * m * W : ℤ) : ZMod q)) ≠ 1 := by
    intro h
    exact hcon ((ZMod.intCast_eq_intCast_iff _ _ _).mp (by simpa using h))
  exact hne (by rw [DirichletCharacter.sum_characters_eq ℂ, if_neg hx])

/-- **`fullFull_orthogonality_right`.**  `LEAN_PROVED_FINITE`.

The `ψ` side, with the second five-box product `W'`. -/
theorem fullFull_orthogonality_right {q : ℕ} [NeZero q] {s m W' : ℤ}
    (hne : (∑ psi : DirichletCharacter ℂ q, psi (((-2 * s * m * W' : ℤ) : ZMod q))) ≠ 0) :
    (-2 * s * m * W') ≡ 1 [ZMOD (q : ℤ)] :=
  fullFull_orthogonality_left hne

/-! ## §4. The double-orthogonality consequences -/

/-- **`doubleOrthogonality_affineDivisor`.**  `LEAN_PROVED`.

`q ∣ 2 m W' + s`: the affine divisor condition on the second product. -/
theorem doubleOrthogonality_affineDivisor {q s m W' : ℤ} (hs : s ^ 2 = 1)
    (h : (-2 * s * m * W') ≡ 1 [ZMOD q]) : q ∣ 2 * m * W' + s :=
  (affine_congruence_iff_dvd hs).mp h

/-- **`doubleOrthogonality_congruence`.**  `LEAN_PROVED`.

Both full characters produce the same affine condition, hence `W ≡ W' (mod q)`.  The
cancellation uses exactly the inverse-sample unit hypothesis `(2m, q) = 1`. -/
theorem doubleOrthogonality_congruence {q s m W W' : ℤ} (hs : s ^ 2 = 1)
    (hcop : IsCoprime (2 * m) q)
    (hW : (-2 * s * m * W) ≡ 1 [ZMOD q]) (hW' : (-2 * s * m * W') ≡ 1 [ZMOD q]) :
    W ≡ W' [ZMOD q] := by
  have h1 : q ∣ 2 * m * W + s := (affine_congruence_iff_dvd hs).mp hW
  have h2 : q ∣ 2 * m * W' + s := (affine_congruence_iff_dvd hs).mp hW'
  have h3 : q ∣ (2 * m) * (W' - W) := by
    have := dvd_sub h2 h1
    have hrw : 2 * m * W' + s - (2 * m * W + s) = (2 * m) * (W' - W) := by ring
    rwa [hrw] at this
  exact Int.modEq_iff_dvd.mpr (hcop.symm.dvd_of_dvd_mul_left h3)

/-- **`doubleOrthogonality_shift_exists`.**  `LEAN_PROVED`.

The shift `t` with `W − W' = q t`. -/
theorem doubleOrthogonality_shift_exists {q s m W W' : ℤ} (hs : s ^ 2 = 1)
    (hcop : IsCoprime (2 * m) q)
    (hW : (-2 * s * m * W) ≡ 1 [ZMOD q]) (hW' : (-2 * s * m * W') ≡ 1 [ZMOD q]) :
    ∃ t : ℤ, W - W' = q * t := by
  have h := doubleOrthogonality_congruence hs hcop hW hW'
  obtain ⟨t, ht⟩ := Int.ModEq.dvd h.symm
  exact ⟨t, ht⟩

/-- **`doubleOrthogonality_coprime`.**  `LEAN_PROVED`.

`(q, W') = 1`, which is the coprimality hypothesis the short-shift sieve interface
requires.  It is a *consequence* of the affine divisor condition and `s² = 1`; it is not
assumed. -/
theorem doubleOrthogonality_coprime {q s m W' : ℤ} (hs : s ^ 2 = 1)
    (h : q ∣ 2 * m * W' + s) : IsCoprime q W' := by
  obtain ⟨k, hk⟩ := h
  have hss : s * s = 1 := by linear_combination hs
  refine ⟨s * k, -(2 * m * s), ?_⟩
  linear_combination (-s) * hk + hss

/-! ## §5. The five labelled physical primes -/

/-- The labelled five-box product `W = p₁p₂p₃p₄p₅`. -/
def fiveProduct (p : Fin 5 → ℤ) : ℤ := p 0 * p 1 * p 2 * p 3 * p 4

/-- The five-box product is the `Finset` product over the five labels. -/
theorem fiveProduct_eq_prod (p : Fin 5 → ℤ) : fiveProduct p = ∏ i : Fin 5, p i := by
  simp [fiveProduct, Fin.prod_univ_five, mul_assoc]

/-- **`char_fiveProduct`.**  `LEAN_PROVED`.

A Dirichlet character factorises over the five labelled primes, in the V20 convention. -/
theorem char_fiveProduct {q : ℕ} (chi : DirichletCharacter ℂ q) (p : Fin 5 → ℤ) :
    chi ((fiveProduct p : ℤ) : ZMod q) = ∏ i : Fin 5, chi ((p i : ℤ) : ZMod q) := by
  rw [fiveProduct_eq_prod]
  push_cast
  rw [map_prod]

/-- **`fiveBox_shift_exists`.**  `LEAN_PROVED`.

The geometric conclusion of the five-box double orthogonality: the two labelled five-box
products differ by an exact multiple of `q`,

`W = W' + q t`,

with `(q, W') = 1` and `q ∣ 2 m W' + s`. -/
theorem fiveBox_shift_exists {q s m : ℤ} {p p' : Fin 5 → ℤ} (hs : s ^ 2 = 1)
    (hcop : IsCoprime (2 * m) q)
    (hW : (-2 * s * m * fiveProduct p) ≡ 1 [ZMOD q])
    (hW' : (-2 * s * m * fiveProduct p') ≡ 1 [ZMOD q]) :
    ∃ t : ℤ, fiveProduct p = fiveProduct p' + q * t ∧
      IsCoprime q (fiveProduct p') ∧ q ∣ 2 * m * fiveProduct p' + s := by
  obtain ⟨t, ht⟩ := doubleOrthogonality_shift_exists hs hcop hW hW'
  have hdvd : q ∣ 2 * m * fiveProduct p' + s := doubleOrthogonality_affineDivisor hs hW'
  exact ⟨t, by linarith [ht], doubleOrthogonality_coprime hs hdvd, hdvd⟩

end V21DoubleOrth
end Erdos287
