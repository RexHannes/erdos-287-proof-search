import Mathlib
import RequestProject.TrustedBank.FixedAffine.LocalRoots

/-!
# Trusted bank — Banks D and E: bounded-cofactor Bézout parametrisation and
local admissibility

Bank D.  For `d, e > 0` and `u, v` with `e v - d u = 1`, the pair of forms

* `P n = e n + u`
* `Q n = d n + v`

satisfies `e Q n - d P n = 1`, and `gcd (d, e) = gcd (u, e) = gcd (v, d) = 1`.

Bank E.  Binary admissibility of the pair `(P, Q)` — for every prime `p` some residue
`n` makes both values nonzero mod `p` — holds **iff** `d e` is even.

Everything is finite algebra; there is no analytic content.
-/

open scoped BigOperators

namespace TrustedBank
namespace BoundedCofactor

/-- Bézout data for a bounded-cofactor pair: `d, e > 0` and `e v - d u = 1`. -/
structure Bez where
  /-- the first cofactor -/
  d : ℤ
  /-- the second cofactor -/
  e : ℤ
  /-- the Bézout witness paired with `e` -/
  u : ℤ
  /-- the Bézout witness paired with `d` -/
  v : ℤ
  /-- positivity of `d` -/
  hd : 0 < d
  /-- positivity of `e` -/
  he : 0 < e
  /-- the Bézout relation -/
  bez : e * v - d * u = 1

namespace Bez

variable (B : Bez)

/-- The first form `P n = e n + u`. -/
def P (n : ℤ) : ℤ := B.e * n + B.u

/-- The second form `Q n = d n + v`. -/
def Q (n : ℤ) : ℤ := B.d * n + B.v

/-- **Bank D.1 — the exact determinant identity** `e Q n - d P n = 1`. -/
theorem key_identity (n : ℤ) : B.e * B.Q n - B.d * B.P n = 1 := by
  simp only [P, Q]
  linear_combination B.bez

/-- Equivalent form: `d P n + 1 = e Q n`. -/
theorem dP_add_one (n : ℤ) : B.d * B.P n + 1 = B.e * B.Q n := by
  have := B.key_identity n; linarith

/-- **Bank D.2 — `d` and `e` are coprime.** -/
theorem isCoprime_d_e : IsCoprime B.d B.e := ⟨-B.u, B.v, by linear_combination B.bez⟩

/-- **Bank D.3 — `u` and `e` are coprime.** -/
theorem isCoprime_u_e : IsCoprime B.u B.e := ⟨-B.d, B.v, by linear_combination B.bez⟩

/-- **Bank D.4 — `v` and `d` are coprime.** -/
theorem isCoprime_v_d : IsCoprime B.v B.d := ⟨B.e, -B.u, by linear_combination B.bez⟩

/-- `gcd (d, e) = 1` in the `Int.gcd` (natural number) form. -/
theorem gcd_d_e : Int.gcd B.d B.e = 1 := Int.isCoprime_iff_gcd_eq_one.mp B.isCoprime_d_e

/-- `gcd (u, e) = 1` in the `Int.gcd` (natural number) form. -/
theorem gcd_u_e : Int.gcd B.u B.e = 1 := Int.isCoprime_iff_gcd_eq_one.mp B.isCoprime_u_e

/-- `gcd (v, d) = 1` in the `Int.gcd` (natural number) form. -/
theorem gcd_v_d : Int.gcd B.v B.d = 1 := Int.isCoprime_iff_gcd_eq_one.mp B.isCoprime_v_d

/-- Coprimality of the coefficient pair of `P`, in the order needed for the local
root lemmas. -/
theorem isCoprime_e_u : IsCoprime B.e B.u := ⟨B.v, -B.d, by linear_combination B.bez⟩

/-- Coprimality of the coefficient pair of `Q`. -/
theorem isCoprime_d_v : IsCoprime B.d B.v := ⟨-B.u, B.e, by linear_combination B.bez⟩

/-! ## Bank E — binary admissibility -/

/-- **Binary admissibility**: for every prime `p` there is a residue `n` with
`P n ≢ 0` and `Q n ≢ 0` modulo `p`. -/
def Admissible : Prop :=
  ∀ p : ℕ, p.Prime → ∃ n : ℤ, ¬ ((p : ℤ) ∣ B.P n) ∧ ¬ ((p : ℤ) ∣ B.Q n)

/-- Odd primes never obstruct: for `p ≥ 3` there is always a good residue, because
`P` and `Q` have at most one root each and `p ≥ 3 > 2`. -/
theorem exists_good_residue_of_three_le {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) :
    ∃ n : ℤ, ¬ ((p : ℤ) ∣ B.P n) ∧ ¬ ((p : ℤ) ∣ B.Q n) := by
  by_contra hcon
  push_neg at hcon
  have H : ∀ n : ℤ, (p : ℤ) ∣ B.e * n + B.u ∨ (p : ℤ) ∣ B.d * n + B.v := by
    intro n
    by_cases h : (p : ℤ) ∣ B.e * n + B.u
    · exact Or.inl h
    · exact Or.inr (hcon n h)
  have hPP : ∀ n₁ n₂ : ℤ, n₁ ≠ n₂ → |n₁ - n₂| ≤ 2 →
      (p : ℤ) ∣ B.e * n₁ + B.u → (p : ℤ) ∣ B.e * n₂ + B.u → False :=
    fun n₁ n₂ hne hcl h₁ h₂ =>
      LocalRoots.no_two_nearby_roots B.isCoprime_e_u hp hp3 hne hcl h₁ h₂
  have hQQ : ∀ n₁ n₂ : ℤ, n₁ ≠ n₂ → |n₁ - n₂| ≤ 2 →
      (p : ℤ) ∣ B.d * n₁ + B.v → (p : ℤ) ∣ B.d * n₂ + B.v → False :=
    fun n₁ n₂ hne hcl h₁ h₂ =>
      LocalRoots.no_two_nearby_roots B.isCoprime_d_v hp hp3 hne hcl h₁ h₂
  have h01 : (0 : ℤ) ≠ 1 := by norm_num
  have h02 : (0 : ℤ) ≠ 2 := by norm_num
  have h12 : (1 : ℤ) ≠ 2 := by norm_num
  have a01 : |(0 : ℤ) - 1| ≤ 2 := by norm_num
  have a02 : |(0 : ℤ) - 2| ≤ 2 := by norm_num
  have a12 : |(1 : ℤ) - 2| ≤ 2 := by norm_num
  rcases H 0 with h0 | h0 <;> rcases H 1 with h1 | h1 <;> rcases H 2 with h2 | h2
  · exact hPP 0 1 h01 a01 h0 h1
  · exact hPP 0 1 h01 a01 h0 h1
  · exact hPP 0 2 h02 a02 h0 h2
  · exact hQQ 1 2 h12 a12 h1 h2
  · exact hPP 1 2 h12 a12 h1 h2
  · exact hQQ 0 2 h02 a02 h0 h2
  · exact hQQ 0 1 h01 a01 h0 h1
  · exact hQQ 0 1 h01 a01 h0 h1

/-- If `2 ∣ e` then `d` and `u` are odd. -/
theorem odd_of_two_dvd_e (hE : (2 : ℤ) ∣ B.e) : ¬ (2 : ℤ) ∣ B.u ∧ ¬ (2 : ℤ) ∣ B.d := by
  have hev : (2 : ℤ) ∣ B.e * B.v := hE.mul_right _
  constructor
  · intro hu
    have hdu : (2 : ℤ) ∣ B.d * B.u := hu.mul_left _
    have : (2 : ℤ) ∣ (1 : ℤ) := by
      have := dvd_sub hev hdu
      rwa [B.bez] at this
    norm_num at this
  · intro hd
    have hdu : (2 : ℤ) ∣ B.d * B.u := hd.mul_right _
    have : (2 : ℤ) ∣ (1 : ℤ) := by
      have := dvd_sub hev hdu
      rwa [B.bez] at this
    norm_num at this

/-- If `2 ∣ d` then `e` and `v` are odd. -/
theorem odd_of_two_dvd_d (hD : (2 : ℤ) ∣ B.d) : ¬ (2 : ℤ) ∣ B.v ∧ ¬ (2 : ℤ) ∣ B.e := by
  have hdu : (2 : ℤ) ∣ B.d * B.u := hD.mul_right _
  constructor
  · intro hv
    have hev : (2 : ℤ) ∣ B.e * B.v := hv.mul_left _
    have : (2 : ℤ) ∣ (1 : ℤ) := by
      have := dvd_sub hev hdu
      rwa [B.bez] at this
    norm_num at this
  · intro he
    have hev : (2 : ℤ) ∣ B.e * B.v := he.mul_right _
    have : (2 : ℤ) ∣ (1 : ℤ) := by
      have := dvd_sub hev hdu
      rwa [B.bez] at this
    norm_num at this

/-- The prime `2` does not obstruct when `d e` is even. -/
theorem exists_good_residue_two (hde : (2 : ℤ) ∣ B.d * B.e) :
    ∃ n : ℤ, ¬ ((2 : ℤ) ∣ B.P n) ∧ ¬ ((2 : ℤ) ∣ B.Q n) := by
  have hprime : Prime (2 : ℤ) := Int.prime_two
  rcases hprime.dvd_mul.1 hde with hD | hE
  · -- `2 ∣ d`: `Q` is always odd; choose `n = u + 1` to make `P` odd.
    obtain ⟨hv, he⟩ := B.odd_of_two_dvd_d hD
    refine ⟨B.u + 1, ?_, ?_⟩
    · -- `P (u+1) = e (u+1) + u ≡ (u+1) + u = 2u+1` since `e` is odd
      intro hcon
      obtain ⟨k, hk⟩ : ∃ k : ℤ, B.e = 2 * k + 1 := by
        rcases Int.even_or_odd B.e with h | h
        · exact absurd h.two_dvd he
        · obtain ⟨k, hk⟩ := h; exact ⟨k, hk⟩
      obtain ⟨t, ht⟩ : ∃ t : ℤ, B.P (B.u + 1) = 2 * t + (2 * B.u + 1) :=
        ⟨k * (B.u + 1), by simp only [P]; linear_combination (B.u + 1) * hk⟩
      rw [ht] at hcon
      omega
    · -- `Q n = d n + v` with `d` even and `v` odd
      intro hcon
      have : (2 : ℤ) ∣ B.d * (B.u + 1) := hD.mul_right _
      have : (2 : ℤ) ∣ B.v := by
        have := dvd_sub hcon this
        simpa [Q] using this
      exact hv this
  · -- `2 ∣ e`: `P` is always odd; choose `n = v + 1` to make `Q` odd.
    obtain ⟨hu, hd⟩ := B.odd_of_two_dvd_e hE
    refine ⟨B.v + 1, ?_, ?_⟩
    · intro hcon
      have h1 : (2 : ℤ) ∣ B.e * (B.v + 1) := hE.mul_right _
      have : (2 : ℤ) ∣ B.u := by
        have := dvd_sub hcon h1
        simpa [P] using this
      exact hu this
    · intro hcon
      obtain ⟨k, hk⟩ : ∃ k : ℤ, B.d = 2 * k + 1 := by
        rcases Int.even_or_odd B.d with h | h
        · exact absurd h.two_dvd hd
        · obtain ⟨k, hk⟩ := h; exact ⟨k, hk⟩
      obtain ⟨t, ht⟩ : ∃ t : ℤ, B.Q (B.v + 1) = 2 * t + (2 * B.v + 1) :=
        ⟨k * (B.v + 1), by simp only [Q]; linear_combination (B.v + 1) * hk⟩
      rw [ht] at hcon
      omega

/-- If `d` and `e` are both odd, the prime `2` obstructs: every residue kills `P` or `Q`. -/
theorem two_obstructs_of_odd (hde : ¬ (2 : ℤ) ∣ B.d * B.e) :
    ∀ n : ℤ, (2 : ℤ) ∣ B.P n ∨ (2 : ℤ) ∣ B.Q n := by
  have hprime : Prime (2 : ℤ) := Int.prime_two
  have hd : ¬ (2 : ℤ) ∣ B.d := fun h => hde (h.mul_right _)
  have he : ¬ (2 : ℤ) ∣ B.e := fun h => hde (h.mul_left _)
  obtain ⟨k₁, hk₁⟩ : ∃ k : ℤ, B.e = 2 * k + 1 := by
    rcases Int.even_or_odd B.e with h | h
    · exact absurd h.two_dvd he
    · obtain ⟨k, hk⟩ := h; exact ⟨k, hk⟩
  obtain ⟨k₂, hk₂⟩ : ∃ k : ℤ, B.d = 2 * k + 1 := by
    rcases Int.even_or_odd B.d with h | h
    · exact absurd h.two_dvd hd
    · obtain ⟨k, hk⟩ := h; exact ⟨k, hk⟩
  intro n
  obtain ⟨s, hs⟩ : ∃ s : ℤ, B.v - B.u = 1 - 2 * s :=
    ⟨k₁ * B.v - k₂ * B.u, by linear_combination B.bez - B.v * hk₁ + B.u * hk₂⟩
  obtain ⟨t₁, ht₁⟩ : ∃ t : ℤ, B.P n = 2 * t + (n + B.u) :=
    ⟨k₁ * n, by simp only [P]; linear_combination n * hk₁⟩
  obtain ⟨t₂, ht₂⟩ : ∃ t : ℤ, B.Q n = 2 * t + (n + B.v) :=
    ⟨k₂ * n, by simp only [Q]; linear_combination n * hk₂⟩
  rw [ht₁, ht₂]
  omega

/-- **Bank E — the local admissibility criterion.**  Under the Bézout relation
`e v - d u = 1` with `d, e > 0`, the pair `(P, Q)` is admissible **iff** `d e` is even.
(Coprimality of `d` and `e` is automatic, see `isCoprime_d_e`.) -/
theorem admissible_iff : B.Admissible ↔ (2 : ℤ) ∣ B.d * B.e := by
  constructor
  · intro hadm
    by_contra hde
    obtain ⟨n, hP, hQ⟩ := hadm 2 Nat.prime_two
    rcases B.two_obstructs_of_odd hde n with h | h
    · exact hP (by exact_mod_cast h)
    · exact hQ (by exact_mod_cast h)
  · intro hde p hp
    have h2 := hp.two_le
    rcases (by omega : p = 2 ∨ 3 ≤ p) with rfl | hp3
    · simpa using B.exists_good_residue_two hde
    · exact B.exists_good_residue_of_three_le hp hp3

/-- The admissibility criterion together with the automatic coprimality. -/
theorem admissible_iff' : B.Admissible ↔ (Int.gcd B.d B.e = 1 ∧ (2 : ℤ) ∣ B.d * B.e) := by
  rw [B.admissible_iff]
  exact ⟨fun h => ⟨B.gcd_d_e, h⟩, fun h => h.2⟩

end Bez

/-! ## Small tests -/

/-- `d = 1, e = 2, u = 1, v = 1`: `2·1 - 1·1 = 1`; `P n = 2n+1`, `Q n = n+1`.
This is the Sophie-Germain-shaped pair; `d e = 2` is even, so it is admissible. -/
def sophie : Bez := ⟨1, 2, 1, 1, by norm_num, by norm_num, by norm_num⟩

example : sophie.Admissible := (Bez.admissible_iff sophie).mpr (by norm_num [sophie])

/-- `d = 1, e = 3, u = 2, v = 1`: `3·1 - 1·2 = 1`, so this is genuine Bézout data with
`d e = 3` odd. -/
def oddPair : Bez := ⟨1, 3, 2, 1, by norm_num, by norm_num, by norm_num⟩

/-- `d e = 3` is odd, so `oddPair` is **not** admissible: `P n = 3n+2`, `Q n = n+1`
always hit an even value. -/
example : ¬ oddPair.Admissible := by
  rw [Bez.admissible_iff]
  norm_num [oddPair]

end BoundedCofactor
end TrustedBank
