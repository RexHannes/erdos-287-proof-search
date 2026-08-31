import Mathlib

/-!
# Unit-sector `gcd` reduction — Erdős #287, SHARED-g₀ REPAIR Δ, §4

**Exact integer algebra.**

In the shared-`g₀` router the frequency carried by a `b`-pair is

```
C = s ( (2b₁)⁻¹ - (2b₂)⁻¹ )   (mod g₀),
```

with `s` a unit modulo `g₀`.  The load-bearing reduction for the *averaged* `b`-pair router
is that the `gcd` of `g₀` with this reciprocal difference is the `gcd` of `g₀` with the
**original** difference `b₁ - b₂`:

```
gcd(g₀, (2b₁)⁻¹ - (2b₂)⁻¹) = gcd(g₀, b₁ - b₂).
```

Here inverses are *not* postulated: the hypotheses are the literal integer relations
`g₀ ∣ 2b₁x - 1`, `g₀ ∣ 2b₂y - 1`, i.e. `x, y` **are** the inverses.  The unit-sector
coprimality `gcd(2b₁b₂, g₀) = 1` is then a consequence, recorded as
`unitSector_coprime_of_inverses`, rather than an extra assumption.

Research status: `sharedGcd_reciprocalDiff_eq_originalDiff : FORMALLY PROVED
(DET1-SHAREDG0-BPAIR-AVERAGED45, unit sector).`
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos287
namespace SharedG0UnitSector

/-! ## §4.1  Two elementary `gcd` moves -/

/-- `gcd(g, ·)` only depends on the residue modulo `g`. -/
theorem gcd_congr_of_dvd_sub (g a b : ℤ) (h : g ∣ a - b) : Int.gcd g a = Int.gcd g b := by
  apply Nat.dvd_antisymm
  · refine Int.dvd_gcd (Int.gcd_dvd_left _ _) ?_
    have h1 : (Int.gcd g a : ℤ) ∣ a := Int.gcd_dvd_right _ _
    have h2 : (Int.gcd g a : ℤ) ∣ (a - b) := dvd_trans (Int.gcd_dvd_left _ _) h
    simpa using dvd_sub h1 h2
  · refine Int.dvd_gcd (Int.gcd_dvd_left _ _) ?_
    have h1 : (Int.gcd g b : ℤ) ∣ b := Int.gcd_dvd_right _ _
    have h2 : (Int.gcd g b : ℤ) ∣ (a - b) := dvd_trans (Int.gcd_dvd_left _ _) h
    simpa [add_sub_cancel] using dvd_add h1 h2

/-- A unit factor may be cancelled inside `gcd(g, ·)`. -/
theorem gcd_unit_cancel (g u z : ℤ) (h : IsCoprime u g) :
    Int.gcd g (u * z) = Int.gcd g z := by
  have hc : Nat.Coprime u.natAbs g.natAbs := by
    rw [Nat.coprime_iff_gcd_eq_one, ← Int.gcd_eq_natAbs]
    exact Int.isCoprime_iff_gcd_eq_one.mp h
  rw [Int.gcd_eq_natAbs, Int.gcd_eq_natAbs, Int.natAbs_mul]
  exact hc.gcd_mul_left_cancel_right _

/-- `gcd(g, ·)` is insensitive to the order of a difference. -/
theorem gcd_sub_comm (g a b : ℤ) : Int.gcd g (a - b) = Int.gcd g (b - a) := by
  rw [Int.gcd_eq_natAbs, Int.gcd_eq_natAbs, ← neg_sub a b, Int.natAbs_neg]

/-! ## §4.2  The unit sector is genuinely a unit sector -/

/-- If `x` inverts `2b₁` modulo `g₀`, then `2b₁` — and separately `2` and `x` — are units
modulo `g₀`. -/
theorem isCoprime_of_inverse {g0 : ℕ} {c x : ℤ} (h : (g0 : ℤ) ∣ c * x - 1) :
    IsCoprime c (g0 : ℤ) ∧ IsCoprime x (g0 : ℤ) := by
  obtain ⟨m, hm⟩ := h
  constructor
  · exact ⟨x, -m, by linarith [hm]⟩
  · exact ⟨c, -m, by linarith [hm]⟩

/-- **The unit-sector hypothesis is automatic.**  From the existence of the two inverses,
`gcd(2b₁b₂, g₀) = 1`. -/
theorem unitSector_coprime_of_inverses {g0 : ℕ} {b1 b2 x y : ℤ}
    (hx : (g0 : ℤ) ∣ 2 * b1 * x - 1) (hy : (g0 : ℤ) ∣ 2 * b2 * y - 1) :
    IsCoprime (2 * b1 * b2) (g0 : ℤ) := by
  have h1 : IsCoprime (2 * b1) (g0 : ℤ) := (isCoprime_of_inverse hx).1
  have h2 : IsCoprime (2 * b2) (g0 : ℤ) := (isCoprime_of_inverse hy).1
  exact h1.mul_left h2.of_mul_left_right

/-! ## §4.3  The reduction -/

/-- **`sharedGcd_reciprocalDiff_eq_originalDiff`.**  `LEAN_PROVED`.

With `x ≡ (2b₁)⁻¹` and `y ≡ (2b₂)⁻¹` modulo `g₀`:

```
gcd(g₀, x - y) = gcd(g₀, b₁ - b₂).
```

The proof is the exact congruence `x - y ≡ 2xy(b₂ - b₁) (mod g₀)` together with the
cancellation of the unit `2xy`. -/
theorem sharedGcd_reciprocalDiff_eq_originalDiff {g0 : ℕ} {b1 b2 x y : ℤ}
    (hx : (g0 : ℤ) ∣ 2 * b1 * x - 1) (hy : (g0 : ℤ) ∣ 2 * b2 * y - 1) :
    Int.gcd (g0 : ℤ) (x - y) = Int.gcd (g0 : ℤ) (b1 - b2) := by
  obtain ⟨hb1, hxu⟩ := isCoprime_of_inverse hx
  obtain ⟨hb2, hyu⟩ := isCoprime_of_inverse hy
  have h2u : IsCoprime (2 : ℤ) (g0 : ℤ) := by
    obtain ⟨m, hm⟩ := hx
    exact ⟨b1 * x, -m, by linarith [hm]⟩
  have hunit : IsCoprime (2 * x * y) (g0 : ℤ) := (h2u.mul_left hxu).mul_left hyu
  have hcong : (g0 : ℤ) ∣ (x - y) - 2 * x * y * (b2 - b1) := by
    obtain ⟨m, hm⟩ := hx
    obtain ⟨n, hn⟩ := hy
    exact ⟨y * m - x * n, by linear_combination y * hm - x * hn⟩
  calc Int.gcd (g0 : ℤ) (x - y)
      = Int.gcd (g0 : ℤ) (2 * x * y * (b2 - b1)) :=
        gcd_congr_of_dvd_sub _ _ _ hcong
    _ = Int.gcd (g0 : ℤ) (b2 - b1) := gcd_unit_cancel _ _ _ hunit
    _ = Int.gcd (g0 : ℤ) (b1 - b2) := gcd_sub_comm _ _ _

/-- **Unit-twisted form.**  `LEAN_PROVED`.  Multiplying the reciprocal difference by a unit
`s` modulo `g₀` — as in `C = s((2b₁)⁻¹ - (2b₂)⁻¹)` — does not change the reduction:

```
gcd(g₀, s(x - y)) = gcd(g₀, b₁ - b₂).
```
-/
theorem sharedGcd_unitTwisted_reciprocalDiff {g0 : ℕ} {b1 b2 x y s : ℤ}
    (hs : IsCoprime s (g0 : ℤ)) (hx : (g0 : ℤ) ∣ 2 * b1 * x - 1)
    (hy : (g0 : ℤ) ∣ 2 * b2 * y - 1) :
    Int.gcd (g0 : ℤ) (s * (x - y)) = Int.gcd (g0 : ℤ) (b1 - b2) := by
  rw [gcd_unit_cancel _ _ _ hs]
  exact sharedGcd_reciprocalDiff_eq_originalDiff hx hy

end SharedG0UnitSector
end Erdos287
