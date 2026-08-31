import Mathlib
import RequestProject.HostileAudit.GeneralModulusInducedCharacter

/-!
# Hostile-audit safe bank §4 — totient / complementary-factor algebra

The elementary arithmetic underlying the `N/D` conductor saving of the general-modulus
conductor-split large sieve.

Banked (all `LEAN_PROVED`):

* `totient_mul_ge` — `φ(f)·φ(j) ≤ φ(f·j)` (Mathlib's super-multiplicativity, restated in the
  notation of this programme);
* `totient_gcd_exact` — the exact gcd formula `φ(gcd(f,j))·φ(f·j) = φ(f)·φ(j)·gcd(f,j)`;
* `complementary_factor_bound` — **the exact source of the `N/D` saving**:

  ```
  f > D   and   R ≤ f·j < 2R    ⇒    j < 2R/D;
  ```

* `divisorVariable_ne_complementaryFactor` — the firewall: the divisor-expansion variable `d`
  of §3 is a variable running over *all* divisors of `j`, and the expansion is **false** if
  one keeps only `d = j`.  The two symbols must not be identified.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open ArithmeticFunction

namespace Erdos287
namespace HostileAudit

/-! ## §4.1  Totient inequalities -/

/-- **`totient_mul_ge`.**  `LEAN_PROVED`.  `φ(f)·φ(j) ≤ φ(f·j)`, with no coprimality
hypothesis. -/
theorem totient_mul_ge (f j : ℕ) : Nat.totient f * Nat.totient j ≤ Nat.totient (f * j) :=
  Nat.totient_super_multiplicative f j

/-- **`totient_gcd_exact`.**  `LEAN_PROVED`.

The exact formula `φ(gcd(f,j))·φ(f·j) = φ(f)·φ(j)·gcd(f,j)`, i.e.

```
φ(f·j) = φ(f)·φ(j)·gcd(f,j)/φ(gcd(f,j)).
```
-/
theorem totient_gcd_exact (f j : ℕ) :
    Nat.totient (Nat.gcd f j) * Nat.totient (f * j)
      = Nat.totient f * Nat.totient j * Nat.gcd f j :=
  Nat.totient_gcd_mul_totient_mul f j

/-- **`totient_mul_eq_of_coprime`.**  `LEAN_PROVED`.  The coprime case of the exact formula. -/
theorem totient_mul_eq_of_coprime {f j : ℕ} (h : Nat.Coprime f j) :
    Nat.totient (f * j) = Nat.totient f * Nat.totient j :=
  Nat.totient_mul h

/-! ## §4.2  The complementary-factor bound — the source of the `N/D` saving -/

/-- **`complementary_factor_bound`.**  `LEAN_PROVED`.

If the primitive conductor exceeds the cutoff, `f > D > 0`, and the modulus `r = f·j` lies in
the dyadic window `R ≤ f·j < 2R`, then the complementary factor obeys

```
j < 2R / D.
```

This single inequality is the exact source of the `N/D` conductor saving: the divisor sum
over `j` is shortened by the factor `D`. -/
theorem complementary_factor_bound {D f j R : ℝ}
    (hD : 0 < D) (hDf : D < f) (hj : 0 ≤ j) (hwin : f * j < 2 * R) :
    j < 2 * R / D := by
  have h1 : j * D ≤ j * f := mul_le_mul_of_nonneg_left hDf.le hj
  have h2 : j * f = f * j := mul_comm j f
  have h3 : j * D < 2 * R := lt_of_le_of_lt (h1.trans_eq h2) hwin
  exact (lt_div_iff₀ hD).2 h3

/-- **`complementary_factor_bound_window`.**  `LEAN_PROVED`.

The same statement in the literal dyadic-window form `R ≤ f·j < 2R` used by the compiler. -/
theorem complementary_factor_bound_window {D f j R : ℝ}
    (hD : 0 < D) (hDf : D < f) (hj : 0 ≤ j)
    (hlow : R ≤ f * j) (hhigh : f * j < 2 * R) :
    R ≤ f * j ∧ j < 2 * R / D :=
  ⟨hlow, complementary_factor_bound hD hDf hj hhigh⟩

/-- **`complementary_factor_saving_is_real`.**  `LEAN_PROVED`.

The saving is genuine: for `D > 1` the bound `2R/D` is strictly smaller than the trivial
bound `2R` available without the conductor restriction. -/
theorem complementary_factor_saving_is_real {D R : ℝ} (hD : 1 < D) (hR : 0 < R) :
    2 * R / D < 2 * R := by
  rw [div_lt_iff₀ (lt_trans zero_lt_one hD)]
  nlinarith

/-! ## §4.3  Firewall: the divisor variable `d` is not the complementary factor `j` -/

/-- **`divisorVariable_ne_complementaryFactor`.**  `LEAN_PROVED`.

The Möbius expansion of §3 runs over *all* divisors `d ∣ j`; the expansion variable `d` must
**not** be identified with the complementary factor `j = r/f`.

Concretely, at `j = 6`, `n = 1` the true expansion equals `1`, while the "`d = j` only"
version equals `0`.  The two are different, so any bookkeeping that silently sets `d = j` is
invalid. -/
theorem divisorVariable_ne_complementaryFactor :
    (∑ d ∈ (6 : ℕ).divisors.filter (fun d => d ∣ 1), moebius d) = 1 ∧
      (if (6 : ℕ) ∣ 1 then moebius 6 else 0) = 0 ∧
      (∑ d ∈ (6 : ℕ).divisors.filter (fun d => d ∣ 1), moebius d)
        ≠ (if (6 : ℕ) ∣ 1 then moebius 6 else 0) := by
  have h1 : (∑ d ∈ (6 : ℕ).divisors.filter (fun d => d ∣ 1), moebius d) = 1 := by
    rw [coprimeIndicator_moebius_expansion (n := 1) (j := 6) (by norm_num)]
    norm_num
  have h2 : (if (6 : ℕ) ∣ 1 then moebius 6 else 0) = 0 := by norm_num
  exact ⟨h1, h2, by rw [h1, h2]; norm_num⟩

/-- **`divisor_expansion_uses_proper_divisors`.**  `LEAN_PROVED`.

Quantitatively: for `j = 6` the expansion involves four divisors, three of which are proper,
so the divisor variable genuinely ranges below `j`. -/
theorem divisor_expansion_uses_proper_divisors :
    (6 : ℕ).divisors.card = 4 ∧ ((6 : ℕ).divisors.filter (fun d => d ≠ 6)).card = 3 := by
  constructor <;> decide +kernel

end HostileAudit
end Erdos287
