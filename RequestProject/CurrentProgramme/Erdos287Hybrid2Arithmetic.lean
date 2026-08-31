import Mathlib
import RequestProject.CurrentProgramme.LevelPairProductModulus

/-!
# HYBRID-2 unconditional arithmetic bank — Erdős #287

**Exact arithmetic only.**  Nothing analytic, nothing asymptotic, no `O`/`≪` notation occurs in
this file.  The module is *append-only*: no previously banked module is edited, and the only
pre-existing module it touches is `LevelPairProductModulus`, which it **imports** (and therefore
re-checks) in order to reuse the banked Möbius algebra instead of duplicating it.

Contents.

* §3  `mobius_opening_of_squarefree` — the exact coprimality / Möbius relations behind the
  inclusion–exclusion opening `m₁ = ℓ·u`.
* §4  `coprime_left_of_mul_coprime`, `coprime_right_of_mul_coprime`,
  `reciprocal_cancel_common_factor` — unit propagation and the modular reciprocal cancellation
  `Δ·a·(m₁)⁻¹ ≡ v·a·(u)⁻¹ (mod Q)`.
* §5  `baseConductor_gcd`, `fullConductor_gcd` — the repaired conductor gcd algebra.
* §6  `pairwise_factors_dvd`, `lcm_dvd_e`, `g0_mul_g0prime_dvd_e_mul_difference` — the exact
  `g₀g₀' ∣ e(b₂−b₁)` divisibility, together with the explicit counterguard showing that the
  stronger statement `g₀g₀' ∣ (b₂−b₁)` is **false**.

Everything in this file is unconditional: no analytic hypothesis, no source pin.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open ArithmeticFunction

namespace Erdos287
namespace Hybrid2

/-! ## §3  Möbius `ℓ`-opening on the squarefree support -/

/-- **`mobius_opening_of_squarefree`.**  `LEAN_PROVED` (unconditional).

Let `m₁` be squarefree and let `m₁ = ℓ·u` be *any* factorisation (equivalently: `ℓ ∣ m₁` with
`u = m₁/ℓ`).  Then

* `ℓ` is squarefree (and so is `u`);
* `gcd(ℓ,u) = 1`;
* `μ(m₁) = μ(ℓ)·μ(u)`;
* `μ(m₁)·μ(ℓ) = μ(u)`, because `μ(ℓ)² = 1` on the squarefree support.

The ambient generality is exactly right: the last identity is *false* without squarefreeness of
`ℓ` (see `mobius_opening_needs_squarefree`). -/
theorem mobius_opening_of_squarefree {m1 ell u : ℕ} (hm1 : Squarefree m1) (hfac : m1 = ell * u) :
    Squarefree ell ∧ Squarefree u ∧ Nat.Coprime ell u ∧
      (moebius m1 : ℤ) = (moebius ell : ℤ) * (moebius u : ℤ) ∧
      (moebius m1 : ℤ) * (moebius ell : ℤ) = (moebius u : ℤ) := by
  subst hfac
  obtain ⟨hcop, hell, hu⟩ := Nat.squarefree_mul_iff.mp hm1
  have hmul : (moebius (ell * u) : ℤ) = (moebius ell : ℤ) * (moebius u : ℤ) :=
    isMultiplicative_moebius.map_mul_of_coprime hcop
  refine ⟨hell, hu, hcop, hmul, ?_⟩
  have hsq : (moebius ell : ℤ) ^ 2 = 1 := by
    exact_mod_cast moebius_sq_eq_one_of_squarefree hell
  calc (moebius (ell * u) : ℤ) * (moebius ell : ℤ)
      = (moebius ell : ℤ) ^ 2 * (moebius u : ℤ) := by rw [hmul]; ring
    _ = (moebius u : ℤ) := by rw [hsq, one_mul]

/-- **Counterguard for §3.**  `LEAN_PROVED`.

The relation `μ(m₁)·μ(ℓ) = μ(u)` genuinely needs the squarefree support: for `ℓ = 4`, `u = 1`,
`m₁ = 4` one has `μ(m₁)μ(ℓ) = 0 ≠ 1 = μ(u)`.  So the statement above is *not* banked in a false
ambient generality. -/
theorem mobius_opening_needs_squarefree :
    ¬ (∀ m1 ell u : ℕ, m1 = ell * u →
        (moebius m1 : ℤ) * (moebius ell : ℤ) = (moebius u : ℤ)) := by
  intro h
  have h0 := h 4 4 1 (by norm_num)
  have h4 : (moebius 4 : ℤ) = 0 :=
    ArithmeticFunction.moebius_eq_zero_of_not_squarefree (by decide)
  rw [h4] at h0
  simp at h0

/-! ## §4  Unit propagation and reciprocal cancellation -/

/-- **Unit propagation, left factor.**  `LEAN_PROVED`.  `gcd(ℓu, Q) = 1 → gcd(ℓ, Q) = 1`. -/
theorem coprime_left_of_mul_coprime {ell u Q : ℕ} (h : Nat.Coprime (ell * u) Q) :
    Nat.Coprime ell Q :=
  Nat.Coprime.coprime_dvd_left ⟨u, rfl⟩ h

/-- **Unit propagation, right factor.**  `LEAN_PROVED`.  `gcd(ℓu, Q) = 1 → gcd(u, Q) = 1`. -/
theorem coprime_right_of_mul_coprime {ell u Q : ℕ} (h : Nat.Coprime (ell * u) Q) :
    Nat.Coprime u Q :=
  Nat.Coprime.coprime_dvd_left ⟨ell, mul_comm ell u⟩ h

/-- **Unit propagation, both factors.**  `LEAN_PROVED`. -/
theorem coprime_both_of_mul_coprime {ell u Q : ℕ} (h : Nat.Coprime (ell * u) Q) :
    Nat.Coprime ell Q ∧ Nat.Coprime u Q :=
  ⟨coprime_left_of_mul_coprime h, coprime_right_of_mul_coprime h⟩

/-- The integer form of unit propagation. -/
theorem isCoprime_both_of_mul_isCoprime {ell u Q : ℤ} (h : IsCoprime (ell * u) Q) :
    IsCoprime ell Q ∧ IsCoprime u Q :=
  ⟨IsCoprime.of_mul_left_left h, IsCoprime.of_mul_left_right h⟩

/-- `x` is an inverse of `c` modulo `Q` in the literal sense used throughout the bank:
`Q ∣ c·x − 1`.  No inverse is ever postulated. -/
def IsInverseMod (Q c x : ℤ) : Prop := Q ∣ c * x - 1

/-- Having an inverse modulo `Q` makes the element a unit modulo `Q`. -/
theorem isCoprime_of_isInverseMod {Q c x : ℤ} (h : IsInverseMod Q c x) : IsCoprime c Q := by
  obtain ⟨k, hk⟩ := h
  exact ⟨x, -k, by linarith [hk]⟩

/-- **`reciprocal_cancel_common_factor`.**  `LEAN_PROVED` (unconditional, purely modular).

Let `m₁ = ℓ·u` and `Δ = ℓ·v`, let `x` be an inverse of `m₁` modulo `Q` and `y` an inverse of `u`
modulo `Q`.  Then for every `a`

```
Δ·a·x  ≡  v·a·y   (mod Q).
```

Only `gcd(u,Q) = 1` is needed; `gcd(ℓ,Q) = 1` is *implied* by the existence of `x`
(`isCoprime_of_isInverseMod` together with `isCoprime_both_of_mul_isCoprime`) and is therefore
not carried as a separate hypothesis.  Nothing asymptotic occurs. -/
theorem reciprocal_cancel_common_factor {Q ell u v a m1 Delta x y : ℤ}
    (hu : IsCoprime u Q) (hm1 : m1 = ell * u) (hD : Delta = ell * v)
    (hx : IsInverseMod Q m1 x) (hy : IsInverseMod Q u y) :
    Q ∣ Delta * a * x - v * a * y := by
  subst hm1
  subst hD
  -- `Q ∣ u * (ℓ x − y)` because `u·ℓ·x − 1 = (m₁x − 1)` and `u·y − 1`.
  have hmul : Q ∣ u * (ell * x - y) := by
    have hEq : u * (ell * x - y) = (ell * u * x - 1) - (u * y - 1) := by ring
    rw [hEq]
    exact dvd_sub hx hy
  have hkey : Q ∣ ell * x - y := (hu.symm).dvd_of_dvd_mul_left hmul
  obtain ⟨k, hk⟩ := hkey
  refine ⟨v * a * k, ?_⟩
  have hEq : ell * v * a * x - v * a * y = v * a * (ell * x - y) := by ring
  rw [hEq, hk]; ring

/-- **The unit hypothesis on `ℓ` is automatic.**  `LEAN_PROVED`. -/
theorem isCoprime_ell_of_inverse {Q ell u m1 x : ℤ} (hm1 : m1 = ell * u)
    (hx : IsInverseMod Q m1 x) : IsCoprime ell Q ∧ IsCoprime u Q := by
  subst hm1
  exact isCoprime_both_of_mul_isCoprime (isCoprime_of_isInverseMod hx)

/-! ## §5  Exact conductor data -/

/-- **`baseConductor_gcd`.**  `LEAN_PROVED` (unconditional).

With the two source-exact gcd identities

```
gcd(a₁₂ᵇᵃˢᵉ, C₁) = de₁·c₂,     gcd(a₁₂ᵇᵃˢᵉ, m₂) = d₂
```

and `gcd(C₁, m₂) = 1`, the product conductor factorises:

```
gcd(a₁₂ᵇᵃˢᵉ, C₁·m₂) = de₁·c₂·d₂.
```

The gcd identities are **hypotheses**, not axioms (option B of the audit): they are exposed at
the interface of the compiler. -/
theorem baseConductor_gcd {a12base C1 m2 de1 c2 d2 : ℕ} (hcop : Nat.Coprime C1 m2)
    (h1 : Nat.gcd a12base C1 = de1 * c2) (h2 : Nat.gcd a12base m2 = d2) :
    Nat.gcd a12base (C1 * m2) = de1 * c2 * d2 := by
  have hsplit : Nat.gcd (C1 * m2) a12base = Nat.gcd C1 a12base * Nat.gcd m2 a12base :=
    Nat.Coprime.mul_gcd hcop a12base
  rw [Nat.gcd_comm a12base (C1 * m2), hsplit, Nat.gcd_comm C1 a12base, Nat.gcd_comm m2 a12base,
    h1, h2]

/-- **`fullConductor_gcd`.**  `LEAN_PROVED` (unconditional).

The repaired complete gcd decomposition.  Writing `a₁₂ = Δ·a₁₂ᵇᵃˢᵉ` with `gcd(Δ, a₁₂ᵇᵃˢᵉ) = 1`
and keeping the two source-exact base identities,

```
gcd(a₁₂, C₁·m₂) = gcd(Δ,C₁)·gcd(Δ,m₂)·(de₁·c₂·d₂).
```

The coprimality `gcd(Δ, a₁₂ᵇᵃˢᵉ) = 1` is *necessary*: see `fullConductor_needs_coprime`. -/
theorem fullConductor_gcd {a12 a12base Delta C1 m2 de1 c2 d2 : ℕ} (hcop : Nat.Coprime C1 m2)
    (hDcop : Nat.Coprime Delta a12base) (hfac : a12 = Delta * a12base)
    (h1 : Nat.gcd a12base C1 = de1 * c2) (h2 : Nat.gcd a12base m2 = d2) :
    Nat.gcd a12 (C1 * m2)
      = Nat.gcd Delta C1 * Nat.gcd Delta m2 * (de1 * c2 * d2) := by
  subst hfac
  have hsplit : Nat.gcd (Delta * a12base) (C1 * m2)
      = Nat.gcd Delta (C1 * m2) * Nat.gcd a12base (C1 * m2) :=
    Nat.Coprime.mul_gcd hDcop (C1 * m2)
  have hDelta : Nat.gcd Delta (C1 * m2) = Nat.gcd Delta C1 * Nat.gcd Delta m2 := by
    have h := Nat.Coprime.mul_gcd hcop Delta
    rw [Nat.gcd_comm Delta (C1 * m2), h, Nat.gcd_comm C1 Delta, Nat.gcd_comm m2 Delta]
  rw [hsplit, hDelta, baseConductor_gcd hcop h1 h2]

/-- **Counterguard for §5.**  `LEAN_PROVED`.

Without `gcd(Δ, a₁₂ᵇᵃˢᵉ) = 1` the product decomposition fails.  Take
`Δ = a₁₂ᵇᵃˢᵉ = 2`, `C₁ = 2`, `m₂ = 1` (so `gcd(C₁,m₂) = 1`):

```
gcd(Δ·a₁₂ᵇᵃˢᵉ, C₁·m₂) = gcd(4,2) = 2,
gcd(Δ,C₁)·gcd(Δ,m₂)·gcd(a₁₂ᵇᵃˢᵉ,C₁)·gcd(a₁₂ᵇᵃˢᵉ,m₂) = 2·1·2·1 = 4.
``` -/
theorem fullConductor_needs_coprime :
    ¬ (∀ a12base Delta C1 m2 : ℕ, Nat.Coprime C1 m2 →
        Nat.gcd (Delta * a12base) (C1 * m2)
          = Nat.gcd Delta C1 * Nat.gcd Delta m2 * (Nat.gcd a12base C1 * Nat.gcd a12base m2)) := by
  intro h
  have := h 2 2 2 1 (by decide)
  norm_num at this

/-! ## §6  `g₀·g₀' ∣ e·(b₂−b₁)` -/

/-- **`pairwise_factors_dvd`.**  `LEAN_PROVED` (unconditional).

If `a`, `c₁`, `d₁`, `c₂`, `d₂` each divide `D_b` and are pairwise coprime, then their product
divides `D_b`. -/
theorem pairwise_factors_dvd {a c1 d1 c2 d2 Db : ℕ}
    (ha : a ∣ Db) (hc1 : c1 ∣ Db) (hd1 : d1 ∣ Db) (hc2 : c2 ∣ Db) (hd2 : d2 ∣ Db)
    (hac1 : Nat.Coprime a c1) (had1 : Nat.Coprime a d1) (hac2 : Nat.Coprime a c2)
    (had2 : Nat.Coprime a d2) (hc1d1 : Nat.Coprime c1 d1) (hc1c2 : Nat.Coprime c1 c2)
    (hc1d2 : Nat.Coprime c1 d2) (hd1c2 : Nat.Coprime d1 c2) (hd1d2 : Nat.Coprime d1 d2)
    (hc2d2 : Nat.Coprime c2 d2) :
    a * c1 * d1 * c2 * d2 ∣ Db := by
  have h11 : c1 * d1 ∣ Db := Nat.Coprime.mul_dvd_of_dvd_of_dvd hc1d1 hc1 hd1
  have h22 : c2 * d2 ∣ Db := Nat.Coprime.mul_dvd_of_dvd_of_dvd hc2d2 hc2 hd2
  have hcop12 : Nat.Coprime (c1 * d1) (c2 * d2) :=
    Nat.Coprime.mul_left (Nat.Coprime.mul_right hc1c2 hc1d2) (Nat.Coprime.mul_right hd1c2 hd1d2)
  have h4 : (c1 * d1) * (c2 * d2) ∣ Db :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop12 h11 h22
  have hcopa : Nat.Coprime a ((c1 * d1) * (c2 * d2)) :=
    Nat.Coprime.mul_right (Nat.Coprime.mul_right hac1 had1)
      (Nat.Coprime.mul_right hac2 had2)
  have h5 : a * ((c1 * d1) * (c2 * d2)) ∣ Db :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd hcopa ha h4
  have hEq : a * c1 * d1 * c2 * d2 = a * ((c1 * d1) * (c2 * d2)) := by ring
  rw [hEq]; exact h5

/-- **`lcm_dvd_e`.**  `LEAN_PROVED`.  `a₁ ∣ e` and `a₂ ∣ e` give `lcm(a₁,a₂) ∣ e`. -/
theorem lcm_dvd_e {a1 a2 e : ℕ} (h1 : a1 ∣ e) (h2 : a2 ∣ e) : Nat.lcm a1 a2 ∣ e :=
  Nat.lcm_dvd h1 h2

/-- `a₁·a₂ = gcd(a₁,a₂)·lcm(a₁,a₂)`. -/
theorem mul_eq_gcd_mul_lcm (a1 a2 : ℕ) : a1 * a2 = Nat.gcd a1 a2 * Nat.lcm a1 a2 :=
  (Nat.gcd_mul_lcm a1 a2).symm

/-- **`g0_mul_g0prime_dvd_e_mul_difference`.**  `LEAN_PROVED` (unconditional).

The formal version of `g₀·g₀' ∣ e·(b₂−b₁)`.  With

```
g₀  = a₁·c₂·d₂,      g₀' = a₂·c₁·d₁,      a = gcd(a₁,a₂),
```

`a₁ ∣ e`, `a₂ ∣ e`, each of `a, c₁, d₁, c₂, d₂` dividing `D_b`, and the pairwise coprimalities
supplied by the programme, one has

```
(a₁·c₂·d₂)·(a₂·c₁·d₁)  ∣  e·D_b.
```

The mechanism is exact: `a₁a₂ = a·lcm(a₁,a₂)`, `lcm(a₁,a₂) ∣ e` and
`a·c₁·d₁·c₂·d₂ ∣ D_b`. -/
theorem g0_mul_g0prime_dvd_e_mul_difference {a1 a2 c1 d1 c2 d2 e Db : ℕ}
    (ha1 : a1 ∣ e) (ha2 : a2 ∣ e)
    (ha : Nat.gcd a1 a2 ∣ Db) (hc1 : c1 ∣ Db) (hd1 : d1 ∣ Db) (hc2 : c2 ∣ Db) (hd2 : d2 ∣ Db)
    (hac1 : Nat.Coprime (Nat.gcd a1 a2) c1) (had1 : Nat.Coprime (Nat.gcd a1 a2) d1)
    (hac2 : Nat.Coprime (Nat.gcd a1 a2) c2) (had2 : Nat.Coprime (Nat.gcd a1 a2) d2)
    (hc1d1 : Nat.Coprime c1 d1) (hc1c2 : Nat.Coprime c1 c2) (hc1d2 : Nat.Coprime c1 d2)
    (hd1c2 : Nat.Coprime d1 c2) (hd1d2 : Nat.Coprime d1 d2) (hc2d2 : Nat.Coprime c2 d2) :
    (a1 * c2 * d2) * (a2 * c1 * d1) ∣ e * Db := by
  have hprod : Nat.gcd a1 a2 * c1 * d1 * c2 * d2 ∣ Db :=
    pairwise_factors_dvd ha hc1 hd1 hc2 hd2 hac1 had1 hac2 had2 hc1d1 hc1c2 hc1d2 hd1c2 hd1d2
      hc2d2
  have hlcm : Nat.lcm a1 a2 ∣ e := lcm_dvd_e ha1 ha2
  have hmul : Nat.lcm a1 a2 * (Nat.gcd a1 a2 * c1 * d1 * c2 * d2) ∣ e * Db :=
    mul_dvd_mul hlcm hprod
  have hEq : (a1 * c2 * d2) * (a2 * c1 * d1)
      = Nat.lcm a1 a2 * (Nat.gcd a1 a2 * c1 * d1 * c2 * d2) := by
    have h := mul_eq_gcd_mul_lcm a1 a2
    calc (a1 * c2 * d2) * (a2 * c1 * d1) = (a1 * a2) * (c1 * d1 * c2 * d2) := by ring
      _ = (Nat.gcd a1 a2 * Nat.lcm a1 a2) * (c1 * d1 * c2 * d2) := by rw [h]
      _ = Nat.lcm a1 a2 * (Nat.gcd a1 a2 * c1 * d1 * c2 * d2) := by ring
  rw [hEq]; exact hmul

/-- **Counterguard for §6 — the stronger statement is FALSE.**  `LEAN_PROVED`.

`g₀·g₀' ∣ (b₂−b₁)` does **not** follow.  Take `a₁ = a₂ = 2`, `e = 2`, `D_b = 2` and
`c₁ = d₁ = c₂ = d₂ = 1`.  Then `g₀g₀' = 4` divides `e·D_b = 4` but does **not** divide
`D_b = 2`.  So the `e` factor cannot be dropped. -/
theorem g0_mul_g0prime_does_not_divide_difference :
    ∃ a1 a2 c1 d1 c2 d2 e Db : ℕ,
      a1 ∣ e ∧ a2 ∣ e ∧ Nat.gcd a1 a2 ∣ Db ∧ c1 ∣ Db ∧ d1 ∣ Db ∧ c2 ∣ Db ∧ d2 ∣ Db ∧
      (a1 * c2 * d2) * (a2 * c1 * d1) ∣ e * Db ∧
      ¬ ((a1 * c2 * d2) * (a2 * c1 * d1) ∣ Db) :=
  ⟨2, 2, 1, 1, 1, 1, 2, 2, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, by norm_num, by decide⟩

end Hybrid2
end Erdos287
