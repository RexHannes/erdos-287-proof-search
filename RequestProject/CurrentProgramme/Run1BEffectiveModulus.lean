import RequestProject.CurrentProgramme.Run1BDwpSourceType

/-!
# RUN1B / d*wp provider — §2  the effective modulus

```
s = gcd(A, r),  r♯ = r/s,  A♯ = A/s            : DEFINED
gcd(A♯, r♯) = 1                                 : KERNEL-PROVED
e_r(A t) = e_{r♯}(A♯ t)                         : KERNEL-PROVED
e_r(A u⁻¹) = e_{r♯}(A♯ u⁻¹)                     : KERNEL-PROVED
```

This module is **append-only** and project-neutral.  Everything here is exact finite
algebra: no analytic input is used and none is produced.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Run1B
namespace EffectiveModulus

open Run1B.Characters Run1B.Source

/-! ## §2.1  The kernelised effective modulus data -/

/-- `s = gcd(A, r)`. -/
def sGcd (A : ℤ) (r : ℕ) : ℕ := Int.gcd A (r : ℤ)

/-- `r♯ = r / gcd(A, r)`, the **effective modulus**. -/
def rSharp (A : ℤ) (r : ℕ) : ℕ := r / sGcd A r

/-- `A♯ = A / gcd(A, r)`, the **effective numerator**. -/
def ASharp (A : ℤ) (r : ℕ) : ℤ := A / (sGcd A r : ℤ)

/-- **`sGcd_pos`.**  `KERNEL-PROVED`. -/
theorem sGcd_pos (A : ℤ) {r : ℕ} (hr : 0 < r) : 0 < sGcd A r := by
  have : sGcd A r = Nat.gcd A.natAbs r := by simp [sGcd, Int.gcd]
  rw [this]
  exact Nat.gcd_pos_of_pos_right _ hr

/-- **`sGcd_dvd_r`.**  `KERNEL-PROVED`. -/
theorem sGcd_dvd_r (A : ℤ) (r : ℕ) : sGcd A r ∣ r := by
  have h : Nat.gcd A.natAbs r ∣ r := Nat.gcd_dvd_right _ _
  simpa [sGcd, Int.gcd] using h

/-- **`sGcd_dvd_A`.**  `KERNEL-PROVED`. -/
theorem sGcd_dvd_A (A : ℤ) (r : ℕ) : ((sGcd A r : ℕ) : ℤ) ∣ A := by
  have h : Nat.gcd A.natAbs r ∣ A.natAbs := Nat.gcd_dvd_left _ _
  have h' : ((Nat.gcd A.natAbs r : ℕ) : ℤ) ∣ (A.natAbs : ℤ) := Int.natCast_dvd_natCast.2 h
  have : ((sGcd A r : ℕ) : ℤ) ∣ (A.natAbs : ℤ) := by simpa [sGcd, Int.gcd] using h'
  exact this.trans (Int.natAbs_dvd.2 dvd_rfl)

/-- **`r_factorisation`.**  `KERNEL-PROVED`.  `r = s · r♯`. -/
theorem r_factorisation (A : ℤ) (r : ℕ) : sGcd A r * rSharp A r = r :=
  Nat.mul_div_cancel' (sGcd_dvd_r A r)

/-- **`A_factorisation`.**  `KERNEL-PROVED`.  `A = s · A♯`. -/
theorem A_factorisation (A : ℤ) (r : ℕ) : ((sGcd A r : ℕ) : ℤ) * ASharp A r = A :=
  Int.mul_ediv_cancel' (sGcd_dvd_A A r)

/-- **`rSharp_pos`.**  `KERNEL-PROVED`. -/
theorem rSharp_pos (A : ℤ) {r : ℕ} (hr : 0 < r) : 0 < rSharp A r := by
  rcases Nat.eq_zero_or_pos (rSharp A r) with h | h
  · exfalso
    have := r_factorisation A r
    rw [h, Nat.mul_zero] at this
    omega
  · exact h

/-- **`rSharp_dvd_r`.**  `KERNEL-PROVED`. -/
theorem rSharp_dvd_r (A : ℤ) (r : ℕ) : rSharp A r ∣ r :=
  ⟨sGcd A r, by rw [mul_comm]; exact (r_factorisation A r).symm⟩

/-- **`gcd_ASharp_rSharp`.**  `KERNEL-PROVED`.  The effective data is coprime:
`gcd(A♯, r♯) = 1`. -/
theorem gcd_ASharp_rSharp (A : ℤ) {r : ℕ} (hr : 0 < r) :
    Int.gcd (ASharp A r) ((rSharp A r : ℕ) : ℤ) = 1 := by
  have hpos : 0 < Int.gcd A (r : ℤ) := sGcd_pos A hr
  have hne : ((Int.gcd A (r : ℤ) : ℕ) : ℤ) ≠ 0 := by exact_mod_cast hpos.ne'
  have hrr : ((sGcd A r : ℕ) : ℤ) * ((rSharp A r : ℕ) : ℤ) = (r : ℤ) := by
    exact_mod_cast congrArg (fun n : ℕ => (n : ℤ)) (r_factorisation A r)
  have key : ∀ g rs : ℤ, g ≠ 0 → g * rs = (r : ℤ) → rs = (r : ℤ) / g := by
    intro g rs hg h
    rw [← h, Int.mul_ediv_cancel_left _ hg]
  have hr' : ((rSharp A r : ℕ) : ℤ) = (r : ℤ) / ((Int.gcd A (r : ℤ) : ℕ) : ℤ) :=
    key _ _ hne hrr
  rw [ASharp, hr']
  exact Int.gcd_div_gcd_div_gcd hpos

/-! ## §2.2  The effective-modulus character identity -/

/-- **`eAdd_effective_modulus`.**  `KERNEL-PROVED`.  Cancelling `s = gcd(A,r)` inside the
additive character is an exact identity, valid for every integer argument `t`. -/
theorem eAdd_effective_modulus (A : ℤ) {r : ℕ} (hr : 0 < r) (t : ℤ) :
    eAdd r (A * t) = eAdd (rSharp A r) (ASharp A r * t) := by
  have hs : 0 < sGcd A r := sGcd_pos A hr
  have hrs : 0 < rSharp A r := rSharp_pos A hr
  have hsC : ((sGcd A r : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hs.ne'
  have hrC : ((rSharp A r : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hrs.ne'
  have hAC : (A : ℂ) = ((sGcd A r : ℕ) : ℂ) * ((ASharp A r : ℤ) : ℂ) := by
    exact_mod_cast congrArg (fun z : ℤ => (z : ℂ)) (A_factorisation A r).symm
  have hrC' : ((r : ℕ) : ℂ) = ((sGcd A r : ℕ) : ℂ) * ((rSharp A r : ℕ) : ℂ) := by
    exact_mod_cast congrArg (fun n : ℕ => (n : ℂ)) (r_factorisation A r).symm
  rw [eAdd, eAdd]
  congr 1
  push_cast
  rw [hAC, hrC']
  field_simp

/-! ## §2.3  Descent of the modular inverse -/

/-- **`invMod_spec`.**  `KERNEL-PROVED`.  `u · u⁻¹ ≡ 1 (mod r)` for `u` coprime to `r`. -/
theorem invMod_spec {r u : ℕ} (hr : 0 < r) (hu : Nat.Coprime u r) :
    (r : ℤ) ∣ (u : ℤ) * invMod r u - 1 := by
  haveI : NeZero r := ⟨hr.ne'⟩
  have h : (((u : ℤ) * invMod r u - 1 : ℤ) : ZMod r) = 0 := by
    push_cast [invMod]
    rw [ZMod.natCast_val, ZMod.cast_id, ZMod.coe_mul_inv_eq_one u hu]
    ring
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 h

/-- **`invMod_descent`.**  `KERNEL-PROVED`.  An inverse modulo `r` is an inverse modulo every
positive divisor `m` of `r`, and inverses mod `m` are unique mod `m`. -/
theorem invMod_descent {r u m : ℕ} (hr : 0 < r) (hu : Nat.Coprime u r) (hm : m ∣ r)
    (hm0 : 0 < m) : (m : ℤ) ∣ invMod r u - invMod m u := by
  have hum : Nat.Coprime u m := Nat.Coprime.coprime_dvd_right hm hu
  have h1 : (m : ℤ) ∣ (u : ℤ) * invMod r u - 1 :=
    dvd_trans (Int.natCast_dvd_natCast.2 hm) (invMod_spec hr hu)
  have h2 : (m : ℤ) ∣ (u : ℤ) * invMod m u - 1 := invMod_spec hm0 hum
  have h3 : (m : ℤ) ∣ (invMod r u - invMod m u) * (u : ℤ) := by
    have : (invMod r u - invMod m u) * (u : ℤ)
        = ((u : ℤ) * invMod r u - 1) - ((u : ℤ) * invMod m u - 1) := by ring
    rw [this]
    exact dvd_sub h1 h2
  have hgcd : Int.gcd (m : ℤ) (u : ℤ) = 1 := by
    have : Nat.gcd m u = 1 := (Nat.Coprime.symm hum)
    simpa [Int.gcd] using this
  exact Int.dvd_of_dvd_mul_left_of_gcd_one h3 hgcd

/-- **`eAdd_effective_modulus_inverse`.**  `KERNEL-PROVED`.  The exact identity requested by
the d*wp provider:

```
e_r(A · u⁻¹)  =  e_{r♯}(A♯ · u⁻¹),
```

where on the right the inverse is taken modulo the **effective** modulus `r♯`. -/
theorem eAdd_effective_modulus_inverse (A : ℤ) {r u : ℕ} (hr : 0 < r) (hu : Nat.Coprime u r) :
    eAdd r (A * invMod r u) = eAdd (rSharp A r) (ASharp A r * invMod (rSharp A r) u) := by
  have hrs : 0 < rSharp A r := rSharp_pos A hr
  rw [eAdd_effective_modulus A hr (invMod r u)]
  refine eAdd_congr_of_modEq hrs ?_
  have hdiff : ((rSharp A r : ℕ) : ℤ) ∣ invMod r u - invMod (rSharp A r) u :=
    invMod_descent hr hu (rSharp_dvd_r A r) hrs
  have : ASharp A r * invMod r u - ASharp A r * invMod (rSharp A r) u
      = ASharp A r * (invMod r u - invMod (rSharp A r) u) := by ring
  rw [this]
  exact Dvd.dvd.mul_left hdiff _

/-! ## §2.4  Semantic firewall -/

/-- **`effective_modulus_is_not_a_size_claim`.**  `KERNEL-PROVED`.  The effective modulus
identity is an identity, not a saving: it holds with `A♯ = 0`, `r♯ = 1`, in which case both
sides are `1`.  Nothing about the size of a character sum is asserted. -/
theorem effective_modulus_is_not_a_size_claim (r : ℕ) (t : ℤ) :
    eAdd r (0 * t) = 1 := by
  simp

end EffectiveModulus
end Run1B
