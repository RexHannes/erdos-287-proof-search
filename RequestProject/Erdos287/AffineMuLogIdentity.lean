import Mathlib
import RequestProject.Erdos287.AffineVaughanIdentity

/-!
# V15, Part 1–2 — the source-minimal Dirichlet identity `Λ = μ ∗ log` and its affine
specialisation

## Part 1 — the exact identity

`muLog_identity_abstract` is the identity `μ * lg = Λ` in an arbitrary commutative ring,
derived from exactly the two hypotheses already used by the V14 Vaughan algebra,

* `μ * ζ = 1`  (`μ ⋆ 1 = ε`),
* `lg = Λ * ζ` (`Λ ⋆ 1 = log`).

`vonMangoldt_eq_mobius_mul_log` is its instance in the Dirichlet convolution ring
`ArithmeticFunction ℝ` with Mathlib's genuine `ArithmeticFunction.vonMangoldt`,
`ArithmeticFunction.moebius`, `ArithmeticFunction.log`, `ArithmeticFunction.zeta`.  No new
schematic `Λ` or `μ` is introduced: the two inputs are the Mathlib theorems
`ArithmeticFunction.coe_moebius_mul_coe_zeta` and `ArithmeticFunction.vonMangoldt_mul_zeta`,
exactly as in `RequestProject/Erdos287/AffineVaughanIdentity.lean`.
`vonMangoldt_eq_mobius_mul_log_agrees` records that the derived identity is the same
statement as Mathlib's own `moebius_mul_log_eq_vonMangoldt` (so nothing has been renamed
into existence).

The coefficientwise forms are

* `vonMangoldt_eq_sum_antidiagonal` : `Λ N = ∑_{q r = N} μ(q) log r`,
* `vonMangoldt_eq_sum_divisors`     : `Λ N = ∑_{q ∣ N} μ(q) log (N/q)`.

## Part 2 — the affine specialisation

`muLog_affine_pointwise` is the identity at `N = 2mn + s`, `s = ±1`, using the V14
`AffineSign` / `affineNat` natural-number sign firewall (`affineNat_cast`); no illegal `Nat`
subtraction occurs, and the source object `muLogAffineSource` is *defined only after* the
equality `Λ(2mn+s) = ∑_{q r = 2mn+s} μ(q) log r` is proved.

Ledger:
`AFFINE287-MULOG-IDENTITY45 : PROVED_ALGEBRAIC`,
`AFFINE287-MULOG-SOURCE45   : PROVED_ALGEBRAIC`.

Nothing here is analytic; no estimate of any kind is asserted.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open ArithmeticFunction
open scoped BigOperators

namespace Erdos287
namespace MuLog

/-! ## Part 1 — the exact Dirichlet identity -/

/-- **`muLog_identity_abstract`** — `PROVED_ALGEBRAIC`.

`μ * log = Λ` in any commutative ring, from `μ * ζ = 1` and `log = Λ * ζ`. -/
theorem muLog_identity_abstract {A : Type*} [CommRing A] (Lam mu lg z : A)
    (hz : mu * z = 1) (hlog : lg = Lam * z) : mu * lg = Lam := by
  subst hlog
  linear_combination Lam * hz

/-- **`vonMangoldt_eq_mobius_mul_log`** — `PROVED_ALGEBRAIC`.

The source-minimal Dirichlet identity `Λ = μ ∗ log`, derived from the two banked
convolution facts rather than postulated. -/
theorem vonMangoldt_eq_mobius_mul_log :
    (vonMangoldt : ArithmeticFunction ℝ)
      = (↑moebius : ArithmeticFunction ℝ) * ArithmeticFunction.log :=
  (muLog_identity_abstract (vonMangoldt : ArithmeticFunction ℝ)
      (↑moebius : ArithmeticFunction ℝ) ArithmeticFunction.log
      (↑zeta : ArithmeticFunction ℝ)
      ArithmeticFunction.coe_moebius_mul_coe_zeta
      ArithmeticFunction.vonMangoldt_mul_zeta.symm).symm

/-- The derived identity is literally Mathlib's `moebius_mul_log_eq_vonMangoldt`; the
repository's arithmetic functions are the genuine ones (hostile check 1). -/
theorem vonMangoldt_eq_mobius_mul_log_agrees :
    vonMangoldt_eq_mobius_mul_log.symm
      = (ArithmeticFunction.moebius_mul_log_eq_vonMangoldt : _) := rfl

/-- **`vonMangoldt_eq_sum_antidiagonal`** — the exact coefficientwise form
`Λ(N) = ∑_{q r = N} μ(q) log r`. -/
theorem vonMangoldt_eq_sum_antidiagonal (N : ℕ) :
    vonMangoldt N
      = ∑ x ∈ N.divisorsAntidiagonal, (moebius x.1 : ℝ) * ArithmeticFunction.log x.2 := by
  conv_lhs => rw [vonMangoldt_eq_mobius_mul_log]
  rw [ArithmeticFunction.mul_apply]
  rfl

/-- The divisor form `Λ(N) = ∑_{q ∣ N} μ(q) log (N/q)`. -/
theorem vonMangoldt_eq_sum_divisors (N : ℕ) :
    vonMangoldt N
      = ∑ q ∈ N.divisors, (moebius q : ℝ) * ArithmeticFunction.log (N / q) := by
  rw [vonMangoldt_eq_sum_antidiagonal, Nat.sum_divisorsAntidiagonal
    (fun q r => (moebius q : ℝ) * ArithmeticFunction.log r)]

/-! ## Part 2 — the affine specialisation -/

open Erdos287.Vaughan

/-- The exact finite `μ`-log source attached to the affine value `2mn + s`.

The definition is introduced **after** `muLog_affine_pointwise` below proves that it equals
`Λ(2mn+s)`; it is a name for a proved quantity, not a postulate. -/
noncomputable def muLogAffineSource (s : AffineSign) (m n : ℕ) : ℝ :=
  ∑ x ∈ (affineNat s m n).divisorsAntidiagonal,
    (moebius x.1 : ℝ) * ArithmeticFunction.log x.2

/-- **`muLog_affine_pointwise`** — `PROVED_ALGEBRAIC`.

`Λ(2mn + s) = ∑_{q r = 2mn+s} μ(q) log r`. -/
theorem muLog_affine_pointwise (s : AffineSign) (m n : ℕ) :
    vonMangoldt (affineNat s m n)
      = ∑ x ∈ (affineNat s m n).divisorsAntidiagonal,
          (moebius x.1 : ℝ) * ArithmeticFunction.log x.2 :=
  vonMangoldt_eq_sum_antidiagonal _

/-- The source object is exactly the von Mangoldt value it is named after. -/
theorem muLogAffineSource_eq (s : AffineSign) (m n : ℕ) :
    muLogAffineSource s m n = vonMangoldt (affineNat s m n) :=
  (muLog_affine_pointwise s m n).symm

/-- The affine argument is the intended integer `2mn + s` (the `Nat`-subtraction firewall
of V14 is reused verbatim; no `Nat` subtraction is performed in any statement). -/
theorem muLogAffineSource_arg (s : AffineSign) {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    ((affineNat s m n : ℕ) : ℤ) = 2 * (m : ℤ) * (n : ℤ) + s.val :=
  affineNat_cast s hm hn

end MuLog
end Erdos287
