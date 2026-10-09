import Mathlib
import RequestProject.Erdos287.BsrcWeights

/-!
# Erdős #287 effectivity — the EARLY_4490 finite-`a` compiler (§43)

```
FINITE-a COMPILER  F_M = Σ_{d | M_N} μ(d) P_d   : KERNEL-PROVED
LARGE-PRIME MASK IRRELEVANCE (p > N)            : KERNEL-PROVED
DISCRETE PARTIAL SUMMATION (Abel)               : KERNEL-PROVED
COMPILER ⇏ FIBRE ANNIHILATION (firewall)        : KERNEL-PROVED (explicit finite witness)
ERDŐS #287                                      : OPEN
```

For odd squarefree `a` the coefficient is `w(a) = μ(a) B(a)/B₁ = μ(a) B₀(a)`
(`wCoef_eq_mu_B_div_B1`; the global normalisation `B₁` cancels).  With a fixed finite ceiling
`N` the compiler works on the finite odd window

    A(N,t) = { a : 1 ≤ a ≤ min(t,N), a odd },

    P_d(t) = Σ_{a ∈ A(N,t), d ∣ a} w(a),      F_M(t) = Σ_{a ∈ A(N,t), (a,M)=1} w(a),

and `M_N` is the product of the odd prime divisors of `M` not exceeding `N`.  The compiler
identity `finiteA_compiler` is

    F_M(t) = Σ_{d ∣ M_N, d ≤ N} μ(d) P_d(t),

the truncation `d ≤ N` being harmless because `P_d ≡ 0` for `d > N`
(`Pd_eq_zero_of_gt`).  The reason `M_N` may replace `M` is isolated as
`largePrime_mask_irrelevant`: a prime `p > N` dividing `M` cannot divide any `a ≤ N`, and the
even part of `M` cannot divide an odd `a`.

Discrete partial summation is `abel_summation_general` / `finiteA_partial_summation`; the
firewall `compiler_not_fibre_annihilation` exhibits an explicit finite instance in which the
compiler identity holds while the compiled sum is nonzero, so the compiler alone never
annihilates a fibre.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open Finset ArithmeticFunction

namespace Erdos287
namespace Effectivity

/-! ## §43.1  The coefficient `w(a)` -/

/-- The compiler coefficient `w(a) = μ(a) B₀(a)`. -/
def wCoef (a : ℕ) : ℚ := ((moebius a : ℤ) : ℚ) * B0 a

/-- **`wCoef_eq_mu_B_div_B1`.**  `KERNEL-PROVED`.  `w(a) = μ(a) B(a)/B₁`: the global
normalisation cancels. -/
theorem wCoef_eq_mu_B_div_B1 {B1 : ℚ} (hB1 : B1 ≠ 0) (a : ℕ) :
    ((moebius a : ℤ) : ℚ) * B B1 a / B1 = wCoef a := by
  unfold B wCoef
  field_simp

/-- **`wCoef_eq_zero_of_not_squarefree`.**  `KERNEL-PROVED`.  `w` is supported on squarefree
arguments, so no squarefreeness filter is needed in the compiler. -/
theorem wCoef_eq_zero_of_not_squarefree {a : ℕ} (h : ¬ Squarefree a) : wCoef a = 0 := by
  simp [wCoef, ArithmeticFunction.moebius_eq_zero_of_not_squarefree h]

@[simp] theorem wCoef_one : wCoef 1 = 1 := by simp [wCoef]

/-! ## §43.2  The finite odd window and the two compiled sums -/

/-- The finite odd window `A(N,t) = {a : 1 ≤ a ≤ min(t,N), a odd}`. -/
def aWindow (N t : ℕ) : Finset ℕ := (Finset.Icc 1 (min t N)).filter (fun a => ¬ 2 ∣ a)

theorem mem_aWindow {N t a : ℕ} : a ∈ aWindow N t ↔ (1 ≤ a ∧ a ≤ min t N) ∧ ¬ 2 ∣ a := by
  simp [aWindow, Finset.mem_filter, Finset.mem_Icc, and_assoc]

/-- `P_d(t) = Σ_{a ∈ A(N,t), d ∣ a} w(a)`. -/
def Pcompiler (N d t : ℕ) : ℚ := ∑ a ∈ (aWindow N t).filter (fun a => d ∣ a), wCoef a

/-- `F_M(t) = Σ_{a ∈ A(N,t), (a,M)=1} w(a)`. -/
def Fcompiler (N M t : ℕ) : ℚ := ∑ a ∈ (aWindow N t).filter (fun a => Nat.Coprime a M), wCoef a

/-- `M_N`: the product of the odd prime divisors of `M` not exceeding `N`. -/
def MtruncN (M N : ℕ) : ℕ := ∏ p ∈ (oddPrimeFactors M).filter (fun p => p ≤ N), p

theorem MtruncN_ne_zero (M N : ℕ) : MtruncN M N ≠ 0 := by
  refine Finset.prod_ne_zero_iff.2 fun p hp => ?_
  have := oddPrimeFactors_prime (Finset.mem_filter.1 hp).1
  exact this.pos.ne'

/-- **`MtruncN_dvd`.**  `KERNEL-PROVED`.  `M_N ∣ M`. -/
theorem MtruncN_dvd (M N : ℕ) : MtruncN M N ∣ M := by
  refine Finset.prod_primes_dvd _ (fun p hp => ?_) (fun p hp => ?_)
  · exact (oddPrimeFactors_prime (Finset.mem_filter.1 hp).1).prime
  · exact Nat.dvd_of_mem_primeFactors (mem_oddPrimeFactors.1 (Finset.mem_filter.1 hp).1).2

/-- **`largePrime_mask_irrelevant`.**  `KERNEL-PROVED`.  For odd `a` with `1 ≤ a ≤ N` the
coprimality mask against `M` and against `M_N` agree: the even part of `M` cannot divide an
odd `a`, and a prime `p > N` dividing `M` cannot divide any `a ≤ N`. -/
theorem largePrime_mask_irrelevant {M N a : ℕ} (hM : 0 < M) (ha1 : 1 ≤ a) (haN : a ≤ N)
    (hodd : ¬ 2 ∣ a) : Nat.Coprime a M ↔ Nat.Coprime a (MtruncN M N) := by
  constructor
  · intro h
    exact Nat.Coprime.coprime_dvd_right (MtruncN_dvd M N) h
  · intro h
    by_contra hcon
    obtain ⟨p, hp, hpa, hpM⟩ := Nat.Prime.not_coprime_iff_dvd.1 hcon
    have hp2 : p ≠ 2 := fun h2 => hodd (h2 ▸ hpa)
    have hpN : p ≤ N := le_trans (Nat.le_of_dvd (by omega) hpa) haN
    have hmem : p ∈ (oddPrimeFactors M).filter (fun p => p ≤ N) := by
      refine Finset.mem_filter.2 ⟨mem_oddPrimeFactors.2 ⟨hp2, ?_⟩, hpN⟩
      exact Nat.mem_primeFactors.2 ⟨hp, hpM, hM.ne'⟩
    have hpdvd : p ∣ MtruncN M N := Finset.dvd_prod_of_mem _ hmem
    have : p ∣ Nat.gcd a (MtruncN M N) := Nat.dvd_gcd hpa hpdvd
    rw [Nat.Coprime] at h
    rw [h] at this
    exact hp.one_lt.ne' (Nat.dvd_one.1 this)

/-- **`Pcompiler_eq_zero_of_gt`.**  `KERNEL-PROVED`.  `P_d ≡ 0` for `d > N`, so the divisor
truncation `d ≤ N` in the compiler is harmless. -/
theorem Pcompiler_eq_zero_of_gt {N d t : ℕ} (h : N < d) : Pcompiler N d t = 0 := by
  refine Finset.sum_eq_zero fun a ha => ?_
  obtain ⟨ha', hdvd⟩ := Finset.mem_filter.1 ha
  obtain ⟨⟨ha1, haN⟩, -⟩ := mem_aWindow.1 ha'
  have : d ≤ a := Nat.le_of_dvd (by omega) hdvd
  have : a ≤ N := le_trans haN (min_le_right _ _)
  omega

/-! ## §43.3  The compiler identity -/

private theorem sum_moebius_divisors_rat (n : ℕ) :
    ∑ d ∈ n.divisors, ((moebius d : ℤ) : ℚ) = if n = 1 then 1 else 0 := by
  have h : ∑ d ∈ n.divisors, (moebius d : ℤ) = if n = 1 then 1 else 0 := by
    rw [← ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.moebius_mul_coe_zeta,
      ArithmeticFunction.one_apply]
  have := congrArg (fun z : ℤ => (z : ℚ)) h
  push_cast at this
  exact this

/-- **`finiteA_compiler_untruncated`.**  `KERNEL-PROVED`.  The compiler identity with the full
divisor sum over `M_N`. -/
theorem finiteA_compiler_untruncated {M : ℕ} (hM : 0 < M) (N t : ℕ) :
    Fcompiler N M t = ∑ d ∈ (MtruncN M N).divisors, ((moebius d : ℤ) : ℚ) * Pcompiler N d t := by
  set m := MtruncN M N with hm
  have hm0 : m ≠ 0 := MtruncN_ne_zero M N
  have hswap :
      ∑ d ∈ m.divisors, ((moebius d : ℤ) : ℚ) * Pcompiler N d t
        = ∑ a ∈ aWindow N t,
            (∑ d ∈ m.divisors.filter (fun d => d ∣ a), ((moebius d : ℤ) : ℚ)) * wCoef a := by
    simp only [Pcompiler, Finset.sum_filter, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun d _ => ?_
    by_cases h : d ∣ a <;> simp [h]
  rw [hswap, Fcompiler, Finset.sum_filter]
  refine Finset.sum_congr rfl fun a ha => ?_
  obtain ⟨⟨ha1, haN⟩, hodd⟩ := mem_aWindow.1 ha
  have ha0 : a ≠ 0 := by omega
  have hfil : m.divisors.filter (fun d => d ∣ a) = (Nat.gcd a m).divisors := by
    ext d
    simp [Nat.mem_divisors, Nat.dvd_gcd_iff, hm0, ha0, Nat.gcd_eq_zero_iff]
    tauto
  rw [hfil, sum_moebius_divisors_rat]
  have hmask : Nat.Coprime a M ↔ Nat.gcd a m = 1 :=
    largePrime_mask_irrelevant hM ha1 (le_trans haN (min_le_right _ _)) hodd
  by_cases h : Nat.Coprime a M
  · rw [if_pos h, if_pos (hmask.1 h), one_mul]
  · rw [if_neg h, if_neg (fun hc => h (hmask.2 hc)), zero_mul]

/-- **`finiteA_compiler`.**  `KERNEL-PROVED`.  The finite-`a` compiler:

    F_M(t) = Σ_{d ∣ M_N, d ≤ N} μ(d) P_d(t). -/
theorem finiteA_compiler {M : ℕ} (hM : 0 < M) (N t : ℕ) :
    Fcompiler N M t
      = ∑ d ∈ (MtruncN M N).divisors.filter (fun d => d ≤ N),
          ((moebius d : ℤ) : ℚ) * Pcompiler N d t := by
  rw [finiteA_compiler_untruncated hM N t, Finset.sum_filter]
  refine Finset.sum_congr rfl fun d _ => ?_
  by_cases h : d ≤ N
  · simp [h]
  · simp [h, Pcompiler_eq_zero_of_gt (Nat.lt_of_not_le h)]

/-! ## §43.4  Discrete partial summation -/

/-- **`abel_summation_general`.**  `KERNEL-PROVED`.  Discrete partial summation for an
arbitrary finite sequence: if `f(a) = F(a) − F(a−1)` then

    Σ_{a=l}^{u} f(a) K_a = F(u)K_u − F(l−1)K_l − Σ_{a=l}^{u−1} F(a)(K_{a+1} − K_a). -/
theorem abel_summation_general (F K : ℕ → ℚ) {l u : ℕ} (h : l ≤ u) :
    ∑ a ∈ Finset.Icc l u, (F a - F (a - 1)) * K a
      = F u * K u - F (l - 1) * K l - ∑ a ∈ Finset.Ico l u, F a * (K (a + 1) - K a) := by
  induction u, h using Nat.le_induction with
  | base => simp [sub_mul]
  | succ u hu ih =>
      rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_Ico_succ_top hu]
      have : (u + 1) - 1 = u := by omega
      rw [this]
      ring

/-- The masked compiler term `w(a) 1_{(a,M)=1}` on the finite window. -/
def maskedTerm (N M a : ℕ) : ℚ :=
  if 1 ≤ a ∧ a ≤ N ∧ ¬ 2 ∣ a ∧ Nat.Coprime a M then wCoef a else 0

/-- **`Fcompiler_succ_sub`.**  `KERNEL-PROVED`.  `F_M` is the summatory function of the masked
term: `F_M(t+1) − F_M(t) = w(t+1) 1_{(t+1,M)=1}` on the window. -/
theorem Fcompiler_succ_sub (N M t : ℕ) :
    Fcompiler N M (t + 1) - Fcompiler N M t = maskedTerm N M (t + 1) := by
  by_cases hN : t + 1 ≤ N
  · have h1 : min (t + 1) N = t + 1 := by omega
    have h2 : min t N = t := by omega
    have hins : Finset.Icc 1 (t + 1) = insert (t + 1) (Finset.Icc 1 t) := by
      ext k; simp [Finset.mem_Icc, Finset.mem_insert]; omega
    by_cases hodd : ¬ 2 ∣ (t + 1)
    · by_cases hcop : Nat.Coprime (t + 1) M
      · have : Fcompiler N M (t + 1) = wCoef (t + 1) + Fcompiler N M t := by
          unfold Fcompiler aWindow
          rw [h1, h2, hins, Finset.filter_insert, if_pos hodd, Finset.filter_insert, if_pos hcop,
            Finset.sum_insert (by simp)]
        rw [this, maskedTerm, if_pos ⟨by omega, hN, hodd, hcop⟩]; ring
      · have : Fcompiler N M (t + 1) = Fcompiler N M t := by
          unfold Fcompiler aWindow
          rw [h1, h2, hins, Finset.filter_insert, if_pos hodd, Finset.filter_insert, if_neg hcop]
        rw [this, maskedTerm, if_neg (by tauto)]; ring
    · have : Fcompiler N M (t + 1) = Fcompiler N M t := by
        unfold Fcompiler aWindow
        rw [h1, h2, hins, Finset.filter_insert, if_neg hodd]
      rw [this, maskedTerm, if_neg (by tauto)]; ring
  · have h1 : min (t + 1) N = N := by omega
    have h2 : min t N = N := by omega
    have : Fcompiler N M (t + 1) = Fcompiler N M t := by unfold Fcompiler aWindow; rw [h1, h2]
    rw [this, maskedTerm, if_neg (by tauto)]; ring

/-- **`finiteA_partial_summation`.**  `KERNEL-PROVED`.  Discrete partial summation for the
compiled coefficient sequence: for `1 ≤ l ≤ u` and any finite sequence `K`,

    Σ_{a=l}^{u} w(a) 1_{(a,M)=1} K_a
      = F_M(u) K_u − F_M(l−1) K_l − Σ_{a=l}^{u−1} F_M(a)(K_{a+1} − K_a).

No analytic smallness conclusion is drawn. -/
theorem finiteA_partial_summation (N M : ℕ) (K : ℕ → ℚ) {l u : ℕ} (hl : 1 ≤ l) (h : l ≤ u) :
    ∑ a ∈ Finset.Icc l u, maskedTerm N M a * K a
      = Fcompiler N M u * K u - Fcompiler N M (l - 1) * K l
        - ∑ a ∈ Finset.Ico l u, Fcompiler N M a * (K (a + 1) - K a) := by
  have hterm : ∀ a ∈ Finset.Icc l u,
      maskedTerm N M a * K a = (Fcompiler N M a - Fcompiler N M (a - 1)) * K a := by
    intro a ha
    have hal : l ≤ a := (Finset.mem_Icc.1 ha).1
    have ha1 : 1 ≤ a := le_trans hl hal
    obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
    rw [show (b + 1) - 1 = b by omega, Fcompiler_succ_sub]
  rw [Finset.sum_congr rfl hterm, abel_summation_general _ K h]

/-! ## §43.5  Firewall: the compiler does not annihilate a fibre -/

/-- **`compiler_not_fibre_annihilation`.**  `KERNEL-PROVED`.  The finite coefficient compiler
does **not** imply finite-fibre annihilation.  Explicit finite witness, independent of any
large-number certificate: with `N = 1`, `M = 1`, `t = 1` and `K ≡ 1` the compiler identity
holds while the compiled sum equals `1 ≠ 0`. -/
theorem compiler_not_fibre_annihilation :
    Fcompiler 1 1 1 = 1 ∧
      Fcompiler 1 1 1 = ∑ d ∈ (MtruncN 1 1).divisors.filter (fun d => d ≤ 1),
          ((moebius d : ℤ) : ℚ) * Pcompiler 1 d 1 ∧
      (∑ a ∈ Finset.Icc 1 1, maskedTerm 1 1 a * (1 : ℚ)) ≠ 0 := by
  refine ⟨?_, finiteA_compiler (by norm_num) 1 1, ?_⟩
  · norm_num [Fcompiler, aWindow, Nat.Coprime, Finset.filter_singleton]
  · simp [maskedTerm, Nat.Coprime]

end Effectivity
end Erdos287
