import Mathlib
import RequestProject.Erdos287.AffineVaughanPrimeOuter

/-!
# Prime-modulus orientation, the two-outer source, and the determinant-one line
(V14, Parts 9–12)

## Part 9 — prime-modulus orientation

From the source factorisation `d p r = 2mn + s` the prime `p` is a *modulus*:
`affine_prime_modulus_congruence` gives `2mn ≡ −s (mod p)` in `ℤ`, and
`affine_prime_modulus_residue` gives the unique residue class
`n ≡ −s (2m)^{-1} (mod p)` in `ZMod p`, **under the explicitly checked hypothesis**
`(2m : ZMod p) ≠ 0` (hostile check 9).  The coprimality consequences
`affine_prime_not_dvd_m` / `affine_prime_not_dvd_n` follow from the unit shift `s = ±1`.

No analytic input is used.

## Part 10 — the two-outer quotient

`u = (2mn + s)/p = d r`, and `deltaMuOne` is the source-side two-outer convolution
`∑_{d r = u} μ(d) αD(d) αR(r)` with *generic* coefficient sequences (the first
Möbius-weighted).  Only exact unfolding is proved; `AffinePrimeModulusTwoOuterPacket` is a
finite interface recording the congruence support, **not** a bound.

## Part 11 — the determinant-one line

`p u − 2mn = s` with `s = ±1` forces `IsCoprime p (2m)` (`affine_coprime_of_unit_shift`),
so the solution set through `(u₀, n₀)` is exactly the line
`n_t = n₀ + p t`, `u_t = u₀ + 2m t`.  Both directions are proved
(`affine_line_forward`, `affine_line_complete`, packaged as `affine_det_one_line_param`)
together with uniqueness of `t` (hostile checks 10, 11).

## Part 12 — the exponent ledger

Rational arithmetic only: `twoOuter_line_exponent_lower_bound` proves the **strict**
inequality `1/6 < 1 − exp(M) − exp(P)` from `exp(M) ≤ σ < 1/6` and `exp(P) ≤ 2/3`, and
`twoOuter_line_exponent_margin` gives the explicit margin form.  The ideal endpoint
`1 − 1/6 − 2/3 = 1/6` is recorded separately, so no equality is being passed off as a
strict bound (hostile check 12).

Ledger targets:
`AFFINE287-PRIME-MODULUS-SOURCE : PROVED_ALGEBRAIC`,
`AFFINE287-TWOOUTER-LINE-PARAMETRISATION : PROVED_ALGEBRAIC`,
`AFFINE287-TWOOUTER-LINE-LENGTH45 : PROVED_ALGEBRAIC / EXPONENT_KERNEL`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open ArithmeticFunction
open scoped BigOperators

namespace Erdos287
namespace TwoOuter

open Erdos287.Vaughan Erdos287.VaughanOuter

/-! ## Part 9 — prime-modulus orientation -/

/-- **`affine_prime_modulus_congruence`.**  The source factorisation makes `p` a modulus:
`2mn + s ≡ 0 (mod p)`. -/
theorem affine_prime_modulus_congruence {U V : ℕ} (c : AffineVaughanPrimeCell U V) :
    (c.p : ℤ) ∣ 2 * (c.m : ℤ) * (c.n : ℤ) + c.sign.val := by
  have hcast : ((Vaughan.affineNat c.sign c.m c.n : ℕ) : ℤ)
      = 2 * (c.m : ℤ) * (c.n : ℤ) + c.sign.val :=
    Vaughan.affineNat_cast _ c.m_pos c.n_pos
  refine ⟨(c.d : ℤ) * (c.r : ℤ), ?_⟩
  rw [← hcast, ← c.equation]
  push_cast
  ring

/-- **`affine_prime_modulus_residue`** — the unique residue class of `n` modulo `p`.

Stated for an arbitrary integer shift `s`; the hypothesis `(2m : ZMod p) ≠ 0` is exactly
the invertibility side condition. -/
theorem affine_prime_modulus_residue {p : ℕ} [Fact p.Prime] {m n : ℕ} {s : ℤ}
    (h : (p : ℤ) ∣ 2 * (m : ℤ) * (n : ℤ) + s)
    (hu : ((2 * m : ℤ) : ZMod p) ≠ 0) :
    ((n : ℕ) : ZMod p) = -(s : ZMod p) * ((2 * m : ℤ) : ZMod p)⁻¹ := by
  have h0 : ((2 * (m : ℤ) * (n : ℤ) + s : ℤ) : ZMod p) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).2 h
  rw [eq_mul_inv_iff_mul_eq₀ hu]
  push_cast at h0 ⊢
  linear_combination h0

/-- With a unit shift `s = ±1`, the prime modulus cannot divide `m`. -/
theorem affine_prime_not_dvd_m {p : ℕ} (hp : p.Prime) {m n : ℕ} {s : ℤ}
    (hs : s = 1 ∨ s = -1) (h : (p : ℤ) ∣ 2 * (m : ℤ) * (n : ℤ) + s) :
    ¬ ((p : ℤ) ∣ (m : ℤ)) := by
  intro hm
  have h2 : (p : ℤ) ∣ 2 * (m : ℤ) * (n : ℤ) := Dvd.dvd.mul_right (hm.mul_left 2) _
  have hsdvd : (p : ℤ) ∣ s := (dvd_add_right h2).1 h
  have hple : (p : ℤ) ≤ 1 := by
    rcases hs with rfl | rfl
    · exact Int.le_of_dvd one_pos hsdvd
    · exact Int.le_of_dvd one_pos ((dvd_neg).2 hsdvd)
  have := hp.two_le
  exact absurd hple (by exact_mod_cast by omega)

/-- With a unit shift `s = ±1`, the prime modulus cannot divide `n`. -/
theorem affine_prime_not_dvd_n {p : ℕ} (hp : p.Prime) {m n : ℕ} {s : ℤ}
    (hs : s = 1 ∨ s = -1) (h : (p : ℤ) ∣ 2 * (m : ℤ) * (n : ℤ) + s) :
    ¬ ((p : ℤ) ∣ (n : ℤ)) := by
  intro hn
  have h2 : (p : ℤ) ∣ 2 * (m : ℤ) * (n : ℤ) := hn.mul_left _
  have hsdvd : (p : ℤ) ∣ s := (dvd_add_right h2).1 h
  have hple : (p : ℤ) ≤ 1 := by
    rcases hs with rfl | rfl
    · exact Int.le_of_dvd one_pos hsdvd
    · exact Int.le_of_dvd one_pos ((dvd_neg).2 hsdvd)
  have := hp.two_le
  exact absurd hple (by exact_mod_cast by omega)

/-- The two coprimality consequences for a source cell. -/
theorem cell_coprime {U V : ℕ} (c : AffineVaughanPrimeCell U V) :
    ¬ ((c.p : ℤ) ∣ (c.m : ℤ)) ∧ ¬ ((c.p : ℤ) ∣ (c.n : ℤ)) :=
  ⟨affine_prime_not_dvd_m c.hp (c.sign.val_eq_one_or) (affine_prime_modulus_congruence c),
   affine_prime_not_dvd_n c.hp (c.sign.val_eq_one_or) (affine_prime_modulus_congruence c)⟩

/-! ## Part 10 — the two-outer quotient and its source packet -/

/-- The two-outer quotient `u = (2mn + s)/p = d r` of a source cell. -/
def cellQuotient {U V : ℕ} (c : AffineVaughanPrimeCell U V) : ℕ := c.d * c.r

theorem cellQuotient_mul_p {U V : ℕ} (c : AffineVaughanPrimeCell U V) :
    cellQuotient c * c.p = Vaughan.affineNat c.sign c.m c.n := by
  rw [cellQuotient, ← c.equation]
  ring

theorem cellQuotient_eq_div {U V : ℕ} (c : AffineVaughanPrimeCell U V) :
    cellQuotient c = Vaughan.affineNat c.sign c.m c.n / c.p := by
  rw [← cellQuotient_mul_p c, Nat.mul_div_cancel _ c.hp.pos]

/-- **`deltaMuOne`** — the source-side two-outer convolution
`Δ(u) = ∑_{d r = u} μ(d) αD(d) αR(r)`, with generic coefficient sequences. -/
def deltaMuOne (alphaD alphaR : ℕ → ℝ) (u : ℕ) : ℝ :=
  ∑ d ∈ u.divisors, (moebius d : ℝ) * alphaD d * alphaR (u / d)

/-- Exact unfolding in `d r = u` form. -/
theorem deltaMuOne_antidiagonal (alphaD alphaR : ℕ → ℝ) (u : ℕ) :
    deltaMuOne alphaD alphaR u
      = ∑ x ∈ u.divisorsAntidiagonal, (moebius x.1 : ℝ) * alphaD x.1 * alphaR x.2 := by
  rw [deltaMuOne, Nat.sum_divisorsAntidiagonal
    (fun d r => (moebius d : ℝ) * alphaD d * alphaR r)]

/-- **`AffinePrimeModulusTwoOuterPacket`** — a *finite interface*, not a bound.

It records the source packet
`∑_{p ∈ primes} ∑_{(m,n) ∈ cells p} ξ(m) κ(n) Δ((2mn+s)/p)`
together with the two structural facts that make it the prime-modulus two-outer source:
every `p` is prime, and every `(m,n)` in its cell satisfies `2mn ≡ −s (mod p)`.

There is deliberately **no analytic field** here (hostile check 13). -/
structure AffinePrimeModulusTwoOuterPacket where
  /-- The prime moduli. -/
  primes : Finset ℕ
  /-- For each modulus, the finite set of `(m, n)` in the residue class. -/
  cells : ℕ → Finset (ℕ × ℕ)
  /-- Which shift `±1`. -/
  sign : Vaughan.AffineSign
  /-- Every modulus is prime. -/
  primes_prime : ∀ p ∈ primes, p.Prime
  /-- Every cell entry lies in the residue class `2mn ≡ −s (mod p)`. -/
  cells_congr : ∀ p ∈ primes, ∀ q ∈ cells p,
    (p : ℤ) ∣ 2 * (q.1 : ℤ) * (q.2 : ℤ) + sign.val

namespace AffinePrimeModulusTwoOuterPacket

/-- The source sum attached to the packet, for given outer weights. -/
noncomputable def sum (pk : AffinePrimeModulusTwoOuterPacket)
    (xi kappa alphaD alphaR : ℕ → ℝ) : ℝ :=
  ∑ p ∈ pk.primes, ∑ q ∈ pk.cells p,
    xi q.1 * kappa q.2 * deltaMuOne alphaD alphaR (Vaughan.affineNat pk.sign q.1 q.2 / p)

/-- The packet sum unfolds exactly; nothing is estimated. -/
theorem sum_def (pk : AffinePrimeModulusTwoOuterPacket) (xi kappa alphaD alphaR : ℕ → ℝ) :
    pk.sum xi kappa alphaD alphaR
      = ∑ p ∈ pk.primes, ∑ q ∈ pk.cells p,
          xi q.1 * kappa q.2 *
            deltaMuOne alphaD alphaR (Vaughan.affineNat pk.sign q.1 q.2 / p) := rfl

/-- On the empty packet the source sum is `0` — a sanity check that the definition is a
genuine finite sum. -/
theorem sum_empty (sign : Vaughan.AffineSign) (xi kappa alphaD alphaR : ℕ → ℝ) :
    AffinePrimeModulusTwoOuterPacket.sum
      { primes := ∅, cells := fun _ => ∅, sign := sign,
        primes_prime := by simp, cells_congr := by simp }
      xi kappa alphaD alphaR = 0 := by
  simp [AffinePrimeModulusTwoOuterPacket.sum]

end AffinePrimeModulusTwoOuterPacket

/-! ## Part 11 — the determinant-one line parametrisation -/

/-- The unit shift forces `p` and `2m` to be coprime: this is the determinant-one
property of the line `p u − 2 m n = ±1`. -/
theorem affine_coprime_of_unit_shift {p m u n s : ℤ}
    (h : p * u - 2 * m * n = s) (hs : s = 1 ∨ s = -1) :
    IsCoprime p (2 * m) := by
  rcases hs with rfl | rfl
  · exact ⟨u, -n, by linarith [h]⟩
  · exact ⟨-u, n, by linarith [h]⟩

/-- **`affine_line_forward`** — every point of the line is a solution. -/
theorem affine_line_forward {p m u0 n0 s : ℤ} (h : p * u0 - 2 * m * n0 = s) (t : ℤ) :
    p * (u0 + 2 * m * t) - 2 * m * (n0 + p * t) = s := by
  linear_combination h

/-- **`affine_line_complete`** — every solution lies on the line. -/
theorem affine_line_complete {p m u0 n0 u n s : ℤ} (hp : p ≠ 0)
    (hcop : IsCoprime p (2 * m))
    (h0 : p * u0 - 2 * m * n0 = s) (h : p * u - 2 * m * n = s) :
    ∃ t : ℤ, n = n0 + p * t ∧ u = u0 + 2 * m * t := by
  have key : p * (u - u0) = 2 * m * (n - n0) := by linarith
  have hdvd : p ∣ 2 * m * (n - n0) := ⟨u - u0, key.symm⟩
  have hn : p ∣ (n - n0) := hcop.dvd_of_dvd_mul_left hdvd
  obtain ⟨t, ht⟩ := hn
  refine ⟨t, by linarith [ht], ?_⟩
  have : p * (u - u0) = p * (2 * m * t) := by
    rw [key, ht]; ring
  have := mul_left_cancel₀ hp this
  linarith [this]

/-- **`affine_det_one_line_param`** — `PROVED_ALGEBRAIC`.

For a unit shift `s = ±1` and `p ≠ 0`, the integer solutions of `p u − 2 m n = s` through
a given solution `(u₀, n₀)` are **exactly** the points of the determinant-one line. -/
theorem affine_det_one_line_param {p m u0 n0 s : ℤ} (hp : p ≠ 0)
    (hs : s = 1 ∨ s = -1) (h0 : p * u0 - 2 * m * n0 = s) (u n : ℤ) :
    (p * u - 2 * m * n = s) ↔ ∃ t : ℤ, n = n0 + p * t ∧ u = u0 + 2 * m * t := by
  constructor
  · intro h
    exact affine_line_complete hp (affine_coprime_of_unit_shift h0 hs) h0 h
  · rintro ⟨t, rfl, rfl⟩
    exact affine_line_forward h0 t

/-- **Uniqueness of the line parameter.** -/
theorem affine_line_param_unique {p n0 : ℤ} (hp : p ≠ 0) {t t' : ℤ}
    (h : n0 + p * t = n0 + p * t') : t = t' := by
  have : p * t = p * t' := by linarith
  exact mul_left_cancel₀ hp this

/-! ## Part 12 — the long-line exponent kernel -/

/-- **`twoOuter_line_exponent_lower_bound`** — `PROVED_ALGEBRAIC / EXPONENT_KERNEL`.

If `exp(M) ≤ σ < 1/6` and `exp(P) ≤ 2/3`, the line length exponent
`1 − exp(M) − exp(P)` exceeds `1/6` **strictly**. -/
theorem twoOuter_line_exponent_lower_bound {mExp pExp sigma : ℚ}
    (hM : mExp ≤ sigma) (hs : sigma < 1 / 6) (hP : pExp ≤ 2 / 3) :
    1 / 6 < 1 - mExp - pExp := by linarith

/-- The explicit rational-margin form. -/
theorem twoOuter_line_exponent_margin {mExp pExp sigma delta : ℚ}
    (hM : mExp ≤ sigma) (hs : sigma ≤ 1 / 6 - delta) (hP : pExp ≤ 2 / 3) :
    1 / 6 + delta ≤ 1 - mExp - pExp := by linarith

/-- The ideal endpoint, recorded as an *equality* so that it is never confused with the
strict bound above. -/
theorem twoOuter_line_exponent_endpoint : (1 : ℚ) - 1 / 6 - 2 / 3 = 1 / 6 := by norm_num

end TwoOuter
end Erdos287
