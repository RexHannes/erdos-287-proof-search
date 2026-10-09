import RequestProject.Erdos287.AnchoredV4.PrimePowerHeight

/-!
# Anchored V4 — the doubled denominator lattice

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

The correct denominator condition for a rational correction `Δ` at height `y` is

`den (2 * Δ) ∣ L y`,   equivalently   `den Δ ∣ 2 * L y`,   equivalently   `normHeight (den Δ) ≤ y`.

The un-doubled condition `den Δ ∣ L y` is **strictly stronger** and must not be substituted: this
module banks the general exchange lemma `den_two_mul_dvd_iff`, the structural reason that even
denominators `2 m` with `m ∣ P` live in the `2 P` lattice, and the finite regression certificate

`1/1056 + 1/1080 = 89/47520`,  `den (2 Δ) = 23760 ∣ L 30`,  `den Δ = 47520 ∤ L 30`.
-/

namespace Erdos287
namespace AnchoredV4

/-- `q.den ∣ n` exactly when `q * n` is an integer. -/
theorem den_dvd_iff_mul_natCast_isInt (q : ℚ) (n : ℕ) :
    q.den ∣ n ↔ ∃ z : ℤ, q * n = z := by
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨q.num * c, ?_⟩
    rw [hc]
    push_cast
    rw [← mul_assoc, Rat.mul_den_eq_num]
  · rintro ⟨z, hz⟩
    have hd : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_nz
    rw [← Rat.num_div_den q] at hz
    field_simp at hz
    have h2 : (q.den : ℤ) ∣ q.num * (n : ℤ) := ⟨z, by exact_mod_cast hz⟩
    have hcop : IsCoprime (q.den : ℤ) q.num := by
      rw [Int.isCoprime_iff_gcd_eq_one]
      simpa [Int.gcd, Nat.coprime_comm] using q.reduced
    exact_mod_cast hcop.dvd_of_dvd_mul_left h2

/-- **Exchange lemma for the factor of two.**  `den (2 q) ∣ P ↔ den q ∣ 2 P`. -/
theorem den_two_mul_dvd_iff (q : ℚ) (P : ℕ) : (2 * q).den ∣ P ↔ q.den ∣ 2 * P := by
  rw [den_dvd_iff_mul_natCast_isInt, den_dvd_iff_mul_natCast_isInt]
  constructor <;> rintro ⟨z, hz⟩ <;> exact ⟨z, by push_cast at hz ⊢; linarith⟩

/-- The denominator condition of the descent, in its three equivalent forms. -/
theorem den_two_mul_dvd_L_iff_normHeight (q : ℚ) {y : ℕ} (hy : 1 ≤ y) :
    (2 * q).den ∣ L y ↔ normHeight q.den ≤ y := by
  rw [den_two_mul_dvd_iff, normalizedHeight_le_iff_dvd_two_lcm q.den_nz hy]

/-- **Structural reason for the doubled lattice.**  A reciprocal `1 / (2 m)` with `m ∣ P` has its
denominator in the `2 P` lattice, and twice it has denominator in the `P` lattice. -/
theorem den_recip_two_mul (m P : ℕ) (hm : m ≠ 0) (hmP : m ∣ P) :
    ((1 : ℚ) / (2 * m)).den ∣ 2 * P ∧ (2 * ((1 : ℚ) / (2 * m))).den ∣ P := by
  have hden : ((1 : ℚ) / (2 * m)).den ∣ 2 * m := by
    have : ((1 : ℚ) / (2 * m)) * (2 * m : ℕ) = ((1 : ℤ) : ℚ) := by
      have h2m : ((2 * m : ℕ) : ℚ) ≠ 0 := by
        simp only [Nat.cast_mul, Nat.cast_ofNat, ne_eq, mul_eq_zero]
        simpa using hm
      field_simp
      push_cast
      ring
    exact (den_dvd_iff_mul_natCast_isInt _ _).2 ⟨1, this⟩
  refine ⟨hden.trans (Nat.mul_dvd_mul_left 2 hmP), ?_⟩
  exact (den_two_mul_dvd_iff _ _).2 (hden.trans (Nat.mul_dvd_mul_left 2 hmP))

/-! ## Finite regression certificate: `1/1056 + 1/1080` -/

/-- The regression target `Δ = 1/1056 + 1/1080`. -/
def deltaCert : ℚ := 1 / 1056 + 1 / 1080

theorem deltaCert_eq : deltaCert = 89 / 47520 := by norm_num [deltaCert]

theorem deltaCert_den : deltaCert.den = 47520 := by norm_num [deltaCert]

theorem two_deltaCert_den : (2 * deltaCert).den = 23760 := by norm_num [deltaCert]

theorem two_deltaCert_den_dvd_L30 : (2 * deltaCert).den ∣ L 30 := by
  rw [two_deltaCert_den]
  have h16 : (16 : ℕ) ∣ L 30 := dvd_L (by norm_num) (by norm_num)
  have h27 : (27 : ℕ) ∣ L 30 := dvd_L (by norm_num) (by norm_num)
  have h5 : (5 : ℕ) ∣ L 30 := dvd_L (by norm_num) (by norm_num)
  have h11 : (11 : ℕ) ∣ L 30 := dvd_L (by norm_num) (by norm_num)
  have h1 : (432 : ℕ) ∣ L 30 :=
    (Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h16 h27)
  have h2 : (2160 : ℕ) ∣ L 30 :=
    (Nat.Coprime.mul_dvd_of_dvd_of_dvd (show Nat.Coprime 432 5 by norm_num) h1 h5)
  have h3 : (23760 : ℕ) ∣ L 30 :=
    (Nat.Coprime.mul_dvd_of_dvd_of_dvd (show Nat.Coprime 2160 11 by norm_num) h2 h11)
  exact h3

theorem deltaCert_den_not_dvd_L30 : ¬ (deltaCert.den ∣ L 30) := by
  rw [deltaCert_den]
  intro h
  have h32 : (2 : ℕ) ^ 5 ∣ L 30 := dvd_trans (by norm_num) h
  have := (prime_pow_dvd_L_iff Nat.prime_two (by norm_num)).1 h32
  norm_num at this

/-- **Doubled-lattice regression certificate.**  The doubled denominator condition holds at
height `30` while the un-doubled one fails; any future statement replacing `den (2 Δ) ∣ P` by
`den Δ ∣ P` is therefore false. -/
theorem doubled_lattice_regression :
    deltaCert = 89 / 47520 ∧ (2 * deltaCert).den ∣ L 30 ∧ ¬ (deltaCert.den ∣ L 30) :=
  ⟨deltaCert_eq, two_deltaCert_den_dvd_L30, deltaCert_den_not_dvd_L30⟩

/-- **Firewall.**  The two denominator conditions are not equivalent: there is a rational whose
doubled denominator divides `L 30` although its own denominator does not. -/
theorem den_dvd_not_iff_den_two_mul_dvd :
    ¬ (∀ (q : ℚ) (P : ℕ), (2 * q).den ∣ P → q.den ∣ P) := by
  intro h
  exact deltaCert_den_not_dvd_L30 (h deltaCert (L 30) two_deltaCert_den_dvd_L30)

end AnchoredV4
end Erdos287
