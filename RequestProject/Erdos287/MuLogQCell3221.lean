import Mathlib
import RequestProject.Erdos287.AffineMuLogIdentity

/-!
# V23, §3 — the `μ · log` `q`-cell algebra

`AFFINE287-MULOG-QCELL45`

Everything in this file is exact finite/algebraic arithmetic, and every ingredient is
either already banked in this repository or already in Mathlib.  The independent audit
(`OPUS NANC : CASE F — SOURCE-MISSING`) lists precisely these items as *independently
verified*:

```
    μ * log / log-r identity        : PASS
    affine character q-cell         : PASS
    q odd / unit implications       : PASS
    non-unit routing                : PASS
```

so they are the ones banked here as `LEAN_PROVED`.

## Contents

* `muLog_qCell_identity` — `Λ(N) = ∑_{q ∣ N} μ(q) log(N/q)`, *reused* from the existing
  `AffineMuLogIdentity` bank (which in turn derives it from Mathlib's
  `moebius_mul_log_eq_vonMangoldt`); nothing is re-postulated.
* `muLog_affine_qCell` — the affine specialisation at `N = 2P + s`.
* `aCoeff` — the unit-sector residue `a_s(q) = −s · 2⁻¹ (mod q)`, with
  `aCoeff_spec` : `q ∣ 2P + s ↔ P ≡ a_s(q) (mod q)` for odd `q`, and `aCoeff_isUnit`.
* `qCell_nonunit_impossible` — for even `q` the affine value `2P + s` is never divisible by
  `q`; this is the exact non-unit routing statement.
* `qCell_orthogonality` / `qCell_indicator` — the finite character-orthogonality `q`-cell,
  taken from Mathlib's `DirichletCharacter.sum_char_inv_mul_char_eq`, so **no** external
  interface is needed for this step.

No analytic statement occurs in this file.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open ArithmeticFunction
open scoped BigOperators

namespace Erdos287
namespace V23QCell

open Erdos287.Vaughan Erdos287.MuLog

/-! ## §3.1  The exact finite identity `Λ = μ ∗ log`, in `q`-cell form -/

/-- **`muLog_qCell_identity`.**  `LEAN_PROVED` (reused).

`Λ(N) = ∑_{q ∣ N} μ(q) · log(N/q)`.  This is the repository's own
`Erdos287.MuLog.vonMangoldt_eq_sum_divisors`; it is not restated as a new assumption. -/
theorem muLog_qCell_identity (N : ℕ) :
    vonMangoldt N = ∑ q ∈ N.divisors, (moebius q : ℝ) * ArithmeticFunction.log (N / q) :=
  vonMangoldt_eq_sum_divisors N

/-- **`muLog_affine_qCell`.**  `LEAN_PROVED`.

The affine specialisation `N = 2P + s` of the `q`-cell identity. -/
theorem muLog_affine_qCell (s : AffineSign) (P : ℕ) :
    vonMangoldt (affineNat s 1 P)
      = ∑ q ∈ (affineNat s 1 P).divisors,
          (moebius q : ℝ) * ArithmeticFunction.log (affineNat s 1 P / q) :=
  muLog_qCell_identity _

/-- The affine argument really is `2P + s`. -/
theorem affine_qCell_arg (s : AffineSign) {P : ℕ} (hP : 1 ≤ P) :
    ((affineNat s 1 P : ℕ) : ℤ) = 2 * (P : ℤ) + s.val := by
  simpa using affineNat_cast s (le_refl 1) hP

/-! ## §3.2  The unit sector and the residue `a_s(q) = −s · 2⁻¹` -/

/-- For odd `q`, the residue `2` is a unit mod `q`. -/
theorem two_isUnit_of_odd {q : ℕ} [NeZero q] (hq : ¬ 2 ∣ q) : IsUnit (2 : ZMod q) := by
  have h : ((2 : ℕ) : ZMod q) = (2 : ZMod q) := by push_cast; ring
  rw [← h, ZMod.isUnit_iff_coprime, Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
  exact hq

/-- **`aCoeff`** — the affine unit-sector residue `a_s(q) = −s · 2⁻¹ (mod q)`. -/
def aCoeff (s : AffineSign) (q : ℕ) : ZMod q := -(s.val : ZMod q) * (2 : ZMod q)⁻¹

/-- **`aCoeff_spec`.**  `LEAN_PROVED`.

For odd `q`, the modulus `q` divides the affine value `2P + s` exactly when `P` lies in the
single residue class `a_s(q)`.  This is the affine `q`-cell routing statement. -/
theorem aCoeff_spec {q : ℕ} [NeZero q] (hq : ¬ 2 ∣ q) (s : AffineSign) (P : ℤ) :
    ((q : ℤ) ∣ 2 * P + s.val) ↔ ((P : ZMod q) = aCoeff s q) := by
  have hinv : (2 : ZMod q) * (2 : ZMod q)⁻¹ = 1 :=
    ZMod.mul_inv_of_unit _ (two_isUnit_of_odd hq)
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, aCoeff]
  push_cast
  constructor
  · intro h
    have h2 : (2 : ZMod q) * (P : ZMod q) = -(s.val : ZMod q) := by linear_combination h
    calc (P : ZMod q) = (2 : ZMod q) * (P : ZMod q) * (2 : ZMod q)⁻¹ := by
          linear_combination (P : ZMod q) * hinv.symm
      _ = -(s.val : ZMod q) * (2 : ZMod q)⁻¹ := by rw [h2]
  · intro h
    rw [h]
    linear_combination (-(s.val : ZMod q)) * hinv

/-- **`aCoeff_isUnit`.**  `LEAN_PROVED`.

For odd `q` the residue `a_s(q)` lies in the unit sector: it is `(−s)·2⁻¹` with `s = ±1`. -/
theorem aCoeff_isUnit {q : ℕ} [NeZero q] (hq : ¬ 2 ∣ q) (s : AffineSign) :
    IsUnit (aCoeff s q) := by
  have h2 : IsUnit ((2 : ZMod q)⁻¹) :=
    IsUnit.of_mul_eq_one 2 (ZMod.inv_mul_of_unit 2 (two_isUnit_of_odd hq))
  have hs : IsUnit (-(s.val : ZMod q)) := by
    rcases s.val_eq_one_or with h | h <;> rw [h]
    · simp
    · simp
  exact hs.mul h2

/-! ## §3.3  Non-unit routing -/

/-- **`qCell_nonunit_impossible`.**  `LEAN_PROVED`.

If `q` is even then no `q`-cell exists for the affine family: `2P + s` is odd for `s = ±1`,
so `q ∤ 2P + s`.  This is the exact non-unit routing firewall — the even moduli carry no
`μ·log` mass at all. -/
theorem qCell_nonunit_impossible {q : ℕ} (hq : 2 ∣ q) (s : AffineSign) (P : ℤ) :
    ¬ ((q : ℤ) ∣ 2 * P + s.val) := by
  intro h
  obtain ⟨k, hk⟩ := hq
  have h2 : (2 : ℤ) ∣ 2 * P + s.val := by
    refine dvd_trans ⟨(k : ℤ), ?_⟩ h
    rw [hk]; push_cast; ring
  rcases s.val_eq_one_or with hs | hs <;> rw [hs] at h2 <;> omega

/-! ## §3.4  The finite character-orthogonality `q`-cell -/

/-- **`qCell_orthogonality`.**  `LEAN_PROVED` (Mathlib).

The finite orthogonality relation used to cut out one residue class inside the unit sector:

```
    ∑_{χ mod q} χ(a⁻¹) χ(b) = φ(q)·[a = b].
```

This is Mathlib's `DirichletCharacter.sum_char_inv_mul_char_eq`, so the character `q`-cell
does **not** require an external interface. -/
theorem qCell_orthogonality {q : ℕ} [NeZero q] {a : ZMod q} (ha : IsUnit a) (b : ZMod q) :
    ∑ chi : DirichletCharacter ℂ q, chi a⁻¹ * chi b
      = if a = b then (q.totient : ℂ) else 0 :=
  DirichletCharacter.sum_char_inv_mul_char_eq ℂ ha b

/-- **`qCell_indicator`.**  `LEAN_PROVED`.

Normalised form: `(1/φ(q)) ∑_χ χ(a⁻¹) χ(b)` is the indicator of the class `a`. -/
theorem qCell_indicator {q : ℕ} [NeZero q] {a : ZMod q} (ha : IsUnit a) (b : ZMod q)
    (hphi : 0 < q.totient) :
    ((q.totient : ℂ))⁻¹ * ∑ chi : DirichletCharacter ℂ q, chi a⁻¹ * chi b
      = if a = b then 1 else 0 := by
  have hne : ((q.totient : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr hphi.ne'
  rw [qCell_orthogonality ha b]
  split_ifs with h
  · exact inv_mul_cancel₀ hne
  · exact mul_zero _

/-- **`affine_qCell_indicator`.**  `LEAN_PROVED`.

The affine `q`-cell in its final form: for odd `q`, the orthogonality sum against the
residue `a_s(q)` is the indicator of `q ∣ 2P + s`. -/
theorem affine_qCell_indicator {q : ℕ} [NeZero q] (hq : ¬ 2 ∣ q) (s : AffineSign) (P : ℤ)
    (hphi : 0 < q.totient) :
    ((q.totient : ℂ))⁻¹ *
        ∑ chi : DirichletCharacter ℂ q, chi (aCoeff s q)⁻¹ * chi (P : ZMod q)
      = if ((q : ℤ) ∣ 2 * P + s.val) then 1 else 0 := by
  rw [qCell_indicator (aCoeff_isUnit hq s) _ hphi]
  by_cases h : ((q : ℤ) ∣ 2 * P + s.val)
  · rw [if_pos h, if_pos ((aCoeff_spec hq s P).mp h).symm]
  · rw [if_neg h, if_neg ?_]
    intro hcon
    exact h ((aCoeff_spec hq s P).mpr hcon.symm)

end V23QCell
end Erdos287
