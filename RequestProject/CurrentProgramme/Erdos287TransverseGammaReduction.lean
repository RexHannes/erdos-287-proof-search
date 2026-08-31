import Mathlib
import RequestProject.CurrentProgramme.Erdos287TransverseOneConductorReciprocity

/-!
# Γ gcd normal form and reduction — Erdős #287 (append-only)

This module is **append-only**: it edits nothing and reproves nothing.

Continuing the one-conductor route, the source numerator

```
Γ = -A + m B t,        m t ≡ 1 (mod r),
```

is reduced by its exact gcd with the composite modulus `r m`.  The two principal new
kernel-safe theorems are

```
transverseGamma_gcd_eq      :  gcd(Γ, r m) = gcd(B - A, r) = g_P,
transverseGammaRed_coprime  :  gcd(Γ / g_P, (r m) / g_P) = 1.
```

Conservatism.

* `gcd(A,m) = 1` is an **explicit** hypothesis; it is what forces `gcd(Γ,m) = 1`, and it is the
  only coprimality the proof consumes.  The frequently quoted extra hypothesis `gcd(r,m) = 1`
  turns out **not** to be needed for the gcd normal form, and is therefore not assumed here;
  `gcd(m,r) = 1` is still needed for the *existence* of `t`
  (`Erdos287.TransverseOneConductor.exists_inverse_of_coprime`), which is where it is stated.
* Every division is exact and proved so: `g_P ∣ Γ` and `g_P ∣ r m` are theorems, and the
  identities `Γ^red · g_P = Γ`, `m_P · g_P = r m` are proved.
* No analytic statement, no length statement, and no claim of closure occurs here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos287
namespace TransverseGammaReduction

open Erdos287.TransverseOneConductor

/-! ## §1  The gcd normal form -/

/-- `g_P := gcd(B - A, r)`. -/
def gP (r : ℕ) (A B : ℤ) : ℕ := Int.gcd (B - A) (r : ℤ)

/-- **`gP_pos`.**  `LEAN_PROVED`. -/
theorem gP_pos {r : ℕ} (hr : 0 < r) (A B : ℤ) : 0 < gP r A B := by
  have hr' : 0 < ((r : ℤ)).natAbs := by simpa using hr
  simp only [gP, Int.gcd]
  exact Nat.gcd_pos_of_pos_right _ hr'

/-- **`gP_dvd_r`.**  `LEAN_PROVED`. -/
theorem gP_dvd_r (r : ℕ) (A B : ℤ) : gP r A B ∣ r := by
  have h : (gP r A B : ℤ) ∣ (r : ℤ) := Int.gcd_dvd_right _ _
  exact_mod_cast h

/-- **`gP_dvd_rm`.**  `LEAN_PROVED`. -/
theorem gP_dvd_rm (r m : ℕ) (A B : ℤ) : gP r A B ∣ r * m :=
  (gP_dvd_r r A B).mul_right m

/-- **`transverseGamma_gcd_eq`.**  `LEAN_PROVED`.  The Γ gcd normal form

`gcd(Γ, r m) = gcd(B - A, r)`,

derived from `Γ ≡ -A (mod m)`, `gcd(A,m) = 1` and `Γ ≡ B - A (mod r)`.  Note that `gcd(r,m) = 1`
is **not** used. -/
theorem transverseGamma_gcd_eq {r m : ℕ} {A B t : ℤ}
    (ht : (m : ℤ) * t ≡ 1 [ZMOD (r : ℤ)]) (hA : Int.gcd A (m : ℤ) = 1) :
    Int.gcd (transverseGammaInt m A B t) ((r * m : ℕ) : ℤ) = gP r A B := by
  set G : ℤ := transverseGammaInt m A B t with hG
  have h1 : Int.gcd G (m : ℤ) = 1 := by
    rw [intGcd_congr (transverseGammaInt_modEq_m m A B t)]
    simpa [Int.gcd] using hA
  have h2 : Int.gcd G ((r * m : ℕ) : ℤ) = Nat.gcd G.natAbs (r * m) := by
    simp [Int.gcd, Int.natAbs_mul]
  have hcop : Nat.Coprime m G.natAbs := by
    have hg : Nat.gcd G.natAbs m = 1 := by simpa [Int.gcd] using h1
    exact Nat.Coprime.symm hg
  have h3 : Nat.gcd G.natAbs (r * m) = Nat.gcd G.natAbs r :=
    Nat.Coprime.gcd_mul_right_cancel_right r hcop
  have h4 : Nat.gcd G.natAbs r = Int.gcd G (r : ℤ) := by simp [Int.gcd]
  rw [h2, h3, h4, intGcd_congr (transverseGammaInt_modEq_r ht)]
  rfl

/-- **`gP_dvd_gamma`.**  `LEAN_PROVED`.  `g_P` divides `Γ`, so the reduction below is exact. -/
theorem gP_dvd_gamma {r m : ℕ} {A B t : ℤ}
    (ht : (m : ℤ) * t ≡ 1 [ZMOD (r : ℤ)]) (hA : Int.gcd A (m : ℤ) = 1) :
    (gP r A B : ℤ) ∣ transverseGammaInt m A B t := by
  have h := transverseGamma_gcd_eq (B := B) ht hA
  have := Int.gcd_dvd_left (transverseGammaInt m A B t) ((r * m : ℕ) : ℤ)
  rwa [h] at this

/-! ## §2  The reduced modulus and the reduced numerator -/

/-- `m_P := r m / g_P`. -/
def mP (r m : ℕ) (A B : ℤ) : ℕ := r * m / gP r A B

/-- `Γ^red := Γ / g_P`. -/
def transverseGammaRed (r m : ℕ) (A B t : ℤ) : ℤ :=
  transverseGammaInt m A B t / (gP r A B : ℤ)

/-- **`mP_mul_gP`.**  `LEAN_PROVED`.  The `m_P` quotient is exact. -/
theorem mP_mul_gP (r m : ℕ) (A B : ℤ) : mP r m A B * gP r A B = r * m :=
  Nat.div_mul_cancel (gP_dvd_rm r m A B)

/-- **`mP_pos`.**  `LEAN_PROVED`. -/
theorem mP_pos {r m : ℕ} (hr : 0 < r) (hm : 0 < m) (A B : ℤ) : 0 < mP r m A B :=
  Nat.div_pos (Nat.le_of_dvd (Nat.mul_pos hr hm) (gP_dvd_rm r m A B)) (gP_pos hr A B)

/-- **`transverseGammaRed_mul_gP`.**  `LEAN_PROVED`.  The `Γ^red` quotient is exact. -/
theorem transverseGammaRed_mul_gP {r m : ℕ} {A B t : ℤ}
    (ht : (m : ℤ) * t ≡ 1 [ZMOD (r : ℤ)]) (hA : Int.gcd A (m : ℤ) = 1) :
    transverseGammaRed r m A B t * (gP r A B : ℤ) = transverseGammaInt m A B t :=
  Int.ediv_mul_cancel (gP_dvd_gamma ht hA)

/-- **`transverseGammaRed_coprime`.**  `LEAN_PROVED`.  One of the principal new kernel-safe
theorems: the reduced numerator is coprime to the reduced modulus,

`gcd(Γ^red, m_P) = 1`. -/
theorem transverseGammaRed_coprime {r m : ℕ} (hr : 0 < r) {A B t : ℤ}
    (ht : (m : ℤ) * t ≡ 1 [ZMOD (r : ℤ)]) (hA : Int.gcd A (m : ℤ) = 1) :
    Int.gcd (transverseGammaRed r m A B t) ((mP r m A B : ℕ) : ℤ) = 1 := by
  have hgcd := transverseGamma_gcd_eq (r := r) (m := m) (A := A) (B := B) ht hA
  have hpos : 0 < gP r A B := gP_pos hr A B
  have h := Int.gcd_div_gcd_div_gcd (i := transverseGammaInt m A B t) (j := ((r * m : ℕ) : ℤ))
    (by rw [hgcd]; exact hpos)
  rw [hgcd] at h
  simpa [transverseGammaRed, mP, Int.natCast_ediv] using h

/-- **`transverseGammaRed_isUnit`.**  `LEAN_PROVED`.  Consequently `Γ^red` is a **unit** of
`ZMod m_P`; this is exactly the input required by the banked reciprocal unitary Fourier
theorem. -/
theorem transverseGammaRed_isUnit {r m : ℕ} (hr : 0 < r) {A B t : ℤ}
    (ht : (m : ℤ) * t ≡ 1 [ZMOD (r : ℤ)]) (hA : Int.gcd A (m : ℤ) = 1) :
    IsUnit ((transverseGammaRed r m A B t : ℤ) : ZMod (mP r m A B)) := by
  set n : ℕ := mP r m A B
  set x : ℤ := transverseGammaRed r m A B t
  have hco : IsCoprime x (n : ℤ) :=
    Int.isCoprime_iff_gcd_eq_one.mpr (transverseGammaRed_coprime hr ht hA)
  obtain ⟨u, v, huv⟩ := hco
  have h2 : ((u * x + v * (n : ℤ) : ℤ) : ZMod n) = ((1 : ℤ) : ZMod n) := by rw [huv]
  push_cast at h2
  simp at h2
  exact IsUnit.of_mul_eq_one (a := ((x : ℤ) : ZMod n)) ((u : ℤ) : ZMod n)
    (by rw [mul_comm]; exact h2)

/-! ## §3  The bundled one-conductor packet -/

/-- Bundled data for one reduced one-conductor phase.  All hypotheses are explicit fields; in
particular the inverse relation `m t ≡ 1 (mod r)` and the coprimality `gcd(A,m) = 1` are carried
by the structure and are never inferred. -/
structure OneConductorData where
  /-- The `r`-modulus. -/
  r : ℕ
  /-- The `m`-modulus. -/
  m : ℕ
  /-- The `q`-residue numerator. -/
  A : ℤ
  /-- The `r`-residue numerator. -/
  B : ℤ
  /-- An integer inverse of `m` modulo `r`. -/
  t : ℤ
  /-- `r` is positive. -/
  r_pos : 0 < r
  /-- `m` is positive. -/
  m_pos : 0 < m
  /-- `t` inverts `m` modulo `r`. -/
  t_inv : (m : ℤ) * t ≡ 1 [ZMOD (r : ℤ)]
  /-- `A` is a unit modulo `m`. -/
  A_coprime_m : Int.gcd A (m : ℤ) = 1

namespace OneConductorData

variable (D : OneConductorData)

/-- The source numerator `Γ` of the packet. -/
def Gamma : ℤ := transverseGammaInt D.m D.A D.B D.t

/-- The gcd `g_P` of the packet. -/
def gcdP : ℕ := gP D.r D.A D.B

/-- The reduced modulus `m_P` of the packet. -/
def modP : ℕ := mP D.r D.m D.A D.B

/-- The reduced numerator `Γ^red` of the packet. -/
def GammaRed : ℤ := transverseGammaRed D.r D.m D.A D.B D.t

/-- **`modP_pos`.**  `LEAN_PROVED`. -/
theorem modP_pos : 0 < D.modP := mP_pos D.r_pos D.m_pos _ _

/-- **`gcd_normal_form`.**  `LEAN_PROVED`.  `gcd(Γ, r m) = g_P`. -/
theorem gcd_normal_form : Int.gcd D.Gamma ((D.r * D.m : ℕ) : ℤ) = D.gcdP :=
  transverseGamma_gcd_eq D.t_inv D.A_coprime_m

/-- **`gammaRed_coprime`.**  `LEAN_PROVED`.  `gcd(Γ^red, m_P) = 1`. -/
theorem gammaRed_coprime : Int.gcd D.GammaRed ((D.modP : ℕ) : ℤ) = 1 :=
  transverseGammaRed_coprime D.r_pos D.t_inv D.A_coprime_m

/-- **`gammaRed_isUnit`.**  `LEAN_PROVED`.  `Γ^red` is a unit of `ZMod m_P`. -/
theorem gammaRed_isUnit : IsUnit ((D.GammaRed : ℤ) : ZMod D.modP) :=
  transverseGammaRed_isUnit D.r_pos D.t_inv D.A_coprime_m

/-- **`modP_neZero`.**  `LEAN_PROVED`.  `NeZero` instance for the reduced modulus, so that the
additive character of `ZMod m_P` is available. -/
instance modP_neZero : NeZero D.modP := ⟨D.modP_pos.ne'⟩

end OneConductorData

/-! ## §4  Tiny finite sanity tests -/

/-- **`gammaReduction_test_r10_m3`.**  `LEAN_PROVED`.  Concrete instance with a *nontrivial*
reduction: `r = 10`, `m = 3`, `t = 7` (`3·7 = 21 ≡ 1 mod 10`), `A = 1`, `B = 5`.  Then
`Γ = -1 + 3·5·7 = 104`, `g_P = gcd(5-1,10) = 2`, `gcd(104, 30) = 2`, `Γ^red = 52`,
`m_P = 15` and `gcd(52,15) = 1`. -/
theorem gammaReduction_test_r10_m3 :
    transverseGammaInt 3 1 5 7 = 104 ∧
    gP 10 1 5 = 2 ∧
    Int.gcd (transverseGammaInt 3 1 5 7) ((10 * 3 : ℕ) : ℤ) = 2 ∧
    transverseGammaRed 10 3 1 5 7 = 52 ∧
    mP 10 3 1 5 = 15 ∧
    Int.gcd (transverseGammaRed 10 3 1 5 7) ((mP 10 3 1 5 : ℕ) : ℤ) = 1 := by
  refine ⟨by norm_num [transverseGammaInt], ?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [gP, mP, transverseGammaRed, transverseGammaInt, Int.gcd]

end TransverseGammaReduction
end Erdos287
