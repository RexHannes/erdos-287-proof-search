import Mathlib
import RequestProject.CurrentProgramme.Erdos287BDiagonalProductMod

/-!
# COMMON-x conductor arithmetic and centered-`kappa` CRT arithmetic — Erdős #287

This module is **append-only**: it is added strictly after the HYBRID-2 / critical-rectangle
bank (`Erdos287Hybrid2*`, `Erdos287BDiagonalProductMod`) and edits nothing that was banked
earlier.

Everything below is *unconditional* arithmetic.  No analytic statement, no asymptotic range
claim and no multiplicity bound is encoded here.

Contents.

* §1  **Common-`x` conductors.**  With `Q₁ = a₁ x`, `Q₂ = a₂ x` the exact `Nat` identities
  `gcd (a₁x) (a₂x) = x * gcd a₁ a₂`, `(a₁x)(a₂x) = a₁a₂x²`, `lcm (a₁x) (a₂x) = x * lcm a₁ a₂`,
  their coprime specialisations, and the divisibility consequences.
* §2  **Centered `kappa` CRT arithmetic.**  Existence of a CRT solution
  `kappa ≡ 1 (mod d)`, `kappa ≡ r (mod qLong)`; the fact that with
  `r (1 - d η) ≡ 1 (mod qLong)` the same congruence holds for `kappa`; and the two source-exact
  gcd consequences

  ```
  gcd (kappa - 1) qLong = 1,      gcd (kappa - 1) Q = d      (Q = d * qLong).
  ```

  The second one is stated with the *literal* hypotheses it needs: `kappa - 1 = d * s` together
  with `IsCoprime s qLong`.  It is **not** claimed under weaker hypotheses.

None of this implies anything about the analytic C0 branch; see the frontier ledger in
`RequestProject/Status/CurrentStatusErdos287CommonXFrontier.lean`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos287
namespace CommonX

/-! ## §1  Common-`x` conductor arithmetic

Throughout this section `Q₁ = a₁ * x` and `Q₂ = a₂ * x` are the two conductors sharing the
common factor `x`. -/

/-- **`commonX_gcd`.**  `LEAN_PROVED`.  `gcd (a₁x) (a₂x) = x * gcd a₁ a₂`.
No coprimality hypothesis is needed for this identity. -/
theorem commonX_gcd (a1 a2 x : ℕ) : Nat.gcd (a1 * x) (a2 * x) = x * Nat.gcd a1 a2 := by
  rw [Nat.gcd_mul_right]; ring

/-- **`commonX_mul`.**  `LEAN_PROVED`.  `Q₁ Q₂ = a₁ a₂ x²`. -/
theorem commonX_mul (a1 a2 x : ℕ) : (a1 * x) * (a2 * x) = a1 * a2 * x ^ 2 := by ring

/-- **`commonX_lcm`.**  `LEAN_PROVED`.  `lcm (a₁x) (a₂x) = x * lcm a₁ a₂`. -/
theorem commonX_lcm (a1 a2 x : ℕ) : Nat.lcm (a1 * x) (a2 * x) = x * Nat.lcm a1 a2 := by
  rw [Nat.lcm_mul_right]; ring

/-- **`commonX_gcd_coprime`.**  `LEAN_PROVED`.  Under `(a₁, a₂) = 1` the shared part is exactly
the common factor: `gcd (a₁x) (a₂x) = x`. -/
theorem commonX_gcd_coprime {a1 a2 : ℕ} (x : ℕ) (h : Nat.Coprime a1 a2) :
    Nat.gcd (a1 * x) (a2 * x) = x := by
  rw [commonX_gcd, h, mul_one]

/-- **`commonX_lcm_coprime`.**  `LEAN_PROVED`.  Under `(a₁, a₂) = 1`,
`lcm (a₁x) (a₂x) = a₁ a₂ x`. -/
theorem commonX_lcm_coprime {a1 a2 : ℕ} (x : ℕ) (h : Nat.Coprime a1 a2) :
    Nat.lcm (a1 * x) (a2 * x) = a1 * a2 * x := by
  rw [commonX_lcm, Nat.Coprime.lcm_eq_mul h]; ring

/-- **`commonX_dvd_left`.**  `LEAN_PROVED`.  The shared conductor divides `Q₁`. -/
theorem commonX_dvd_left (a1 a2 x : ℕ) : x * Nat.gcd a1 a2 ∣ a1 * x := by
  rw [← commonX_gcd]; exact Nat.gcd_dvd_left _ _

/-- **`commonX_dvd_right`.**  `LEAN_PROVED`.  The shared conductor divides `Q₂`. -/
theorem commonX_dvd_right (a1 a2 x : ℕ) : x * Nat.gcd a1 a2 ∣ a2 * x := by
  rw [← commonX_gcd]; exact Nat.gcd_dvd_right _ _

/-- **`commonX_dvd_gcd`.**  `LEAN_PROVED`.  The common factor `x` always divides `gcd Q₁ Q₂`. -/
theorem commonX_dvd_gcd (a1 a2 x : ℕ) : x ∣ Nat.gcd (a1 * x) (a2 * x) :=
  ⟨Nat.gcd a1 a2, commonX_gcd a1 a2 x⟩

/-- **`commonX_gcd_mul_lcm`.**  `LEAN_PROVED`.  Consistency of §1:
`gcd Q₁ Q₂ * lcm Q₁ Q₂ = a₁ a₂ x²`. -/
theorem commonX_gcd_mul_lcm (a1 a2 x : ℕ) :
    Nat.gcd (a1 * x) (a2 * x) * Nat.lcm (a1 * x) (a2 * x) = a1 * a2 * x ^ 2 := by
  rw [Nat.gcd_mul_lcm]; ring

/-! ## §2  Centered `kappa` CRT arithmetic

The source situation is `qLong = w * x`, `Q = d * qLong` with `IsCoprime d qLong`, and `eta` a
unit modulo `qLong` such that `1 - d*eta` is again a unit modulo `qLong`.  All statements are in
`ℤ`, and every congruence is written as a literal divisibility so that no inverse has to be
chosen. -/

/-- **`kappa_crt_exists`.**  `LEAN_PROVED`.  The CRT construction: for coprime moduli `d`,
`qLong` and any target residue `r` there is a `kappa` with `kappa ≡ 1 (mod d)` and
`kappa ≡ r (mod qLong)`. -/
theorem kappa_crt_exists {d qLong : ℤ} (h : IsCoprime d qLong) (r : ℤ) :
    ∃ kappa : ℤ, d ∣ kappa - 1 ∧ qLong ∣ kappa - r := by
  obtain ⟨u, v, huv⟩ := h
  refine ⟨u * d * r + v * qLong, ⟨u * (r - 1), ?_⟩, ⟨v * (1 - r), ?_⟩⟩
  · linear_combination huv
  · linear_combination r * huv

/-- **`kappa_mod_small`.**  `LEAN_PROVED`.  `d ∣ kappa - 1` is the congruence
`kappa ≡ 1 (mod d)`. -/
theorem kappa_mod_small {d kappa : ℤ} (h : d ∣ kappa - 1) : kappa % d = 1 % d :=
  Int.ModEq.symm (Int.modEq_iff_dvd.mpr (by simpa using h))

/-- **`kappa_mod_long`.**  `LEAN_PROVED`.  If `kappa ≡ r (mod qLong)` and `r` inverts
`1 - d*eta` modulo `qLong`, then so does `kappa`; i.e.
`kappa ≡ (1 - d*eta)⁻¹ (mod qLong)` in literal divisibility form. -/
theorem kappa_mod_long {qLong kappa r d eta : ℤ} (h : qLong ∣ kappa - r)
    (hr : qLong ∣ r * (1 - d * eta) - 1) :
    qLong ∣ kappa * (1 - d * eta) - 1 := by
  have hsplit : kappa * (1 - d * eta) - 1
      = (kappa - r) * (1 - d * eta) + (r * (1 - d * eta) - 1) := by ring
  rw [hsplit]
  exact dvd_add (h.mul_right _) hr

/-- **`kappa_unit_long`.**  `LEAN_PROVED`.  A `kappa` inverting `1 - d*eta` modulo `qLong` is
itself a unit modulo `qLong`. -/
theorem kappa_unit_long {d eta kappa qLong : ℤ}
    (hk : qLong ∣ kappa * (1 - d * eta) - 1) : IsCoprime kappa qLong := by
  obtain ⟨t, ht⟩ := hk
  exact ⟨1 - d * eta, -t, by linear_combination ht⟩

/-- **`kappa_sub_one_coprime_long`.**  `LEAN_PROVED`.  The first source-exact gcd consequence:

```
gcd (kappa - 1) qLong = 1,
```

written as `IsCoprime`.  Hypotheses: `d` and `eta` are units modulo `qLong`, and `kappa`
inverts `1 - d*eta` modulo `qLong`.  All three are visible in the statement. -/
theorem kappa_sub_one_coprime_long {d eta kappa qLong : ℤ}
    (hd : IsCoprime d qLong) (he : IsCoprime eta qLong)
    (hk : qLong ∣ kappa * (1 - d * eta) - 1) : IsCoprime (kappa - 1) qLong := by
  obtain ⟨t, ht⟩ := hk
  have hkap : IsCoprime kappa qLong := kappa_unit_long ⟨t, ht⟩
  have hprod : IsCoprime (kappa * d * eta) qLong := (hkap.mul_left hd).mul_left he
  have hshift := hprod.add_mul_left_left t
  have heq : kappa * d * eta + qLong * t = kappa - 1 := by linear_combination -ht
  rwa [heq] at hshift

/-- **`kappa_sub_one_gcd_long_eq_one`.**  `LEAN_PROVED`.  The same statement in the literal
`Int.gcd = 1` form. -/
theorem kappa_sub_one_gcd_long_eq_one {d eta kappa qLong : ℤ}
    (hd : IsCoprime d qLong) (he : IsCoprime eta qLong)
    (hk : qLong ∣ kappa * (1 - d * eta) - 1) : Int.gcd (kappa - 1) qLong = 1 :=
  Int.isCoprime_iff_gcd_eq_one.mp (kappa_sub_one_coprime_long hd he hk)

/-- **`gcd_kappa_sub_one_fullConductor`.**  `LEAN_PROVED`.  The second source-exact gcd
consequence:

```
gcd (kappa - 1) Q = d      for Q = d * qLong.
```

The hypotheses are the *literal* ones the equality needs: `d ∣ kappa - 1`, exhibited as
`kappa - 1 = d * s`, and `IsCoprime s qLong`.  Nothing weaker is claimed. -/
theorem gcd_kappa_sub_one_fullConductor {d s kappa qLong Q : ℤ}
    (hQ : Q = d * qLong) (hs : kappa - 1 = d * s) (hcop : IsCoprime s qLong) :
    Int.gcd (kappa - 1) Q = d.natAbs := by
  subst hQ
  rw [hs, Int.gcd_mul_left, Int.isCoprime_iff_gcd_eq_one.mp hcop, mul_one]

/-- **`gcd_kappa_sub_one_fullConductor_of_crt`.**  `LEAN_PROVED`.  Packaging of the two gcd
rows: from the CRT data (`d ∣ kappa - 1` exhibited by `s`, plus the long-modulus unit
hypotheses) one gets simultaneously

```
gcd (kappa - 1) qLong = 1     and     gcd (kappa - 1) (d * qLong) = |d|.
```

The cofactor coprimality `IsCoprime s qLong` is *derived* here from
`kappa_sub_one_coprime_long`, so no extra assumption is smuggled in. -/
theorem gcd_kappa_sub_one_fullConductor_of_crt {d eta s kappa qLong : ℤ}
    (hd : IsCoprime d qLong) (he : IsCoprime eta qLong)
    (hk : qLong ∣ kappa * (1 - d * eta) - 1) (hs : kappa - 1 = d * s) :
    Int.gcd (kappa - 1) qLong = 1 ∧ Int.gcd (kappa - 1) (d * qLong) = d.natAbs := by
  have hcop : IsCoprime (kappa - 1) qLong := kappa_sub_one_coprime_long hd he hk
  refine ⟨Int.isCoprime_iff_gcd_eq_one.mp hcop, ?_⟩
  have hs' : IsCoprime s qLong := by
    rw [hs] at hcop
    exact (IsCoprime.of_mul_left_right hcop)
  exact gcd_kappa_sub_one_fullConductor rfl hs hs'

end CommonX
end Erdos287
