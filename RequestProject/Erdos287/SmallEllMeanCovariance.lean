import Mathlib
import RequestProject.Erdos287.SmallEllCRT

/-!
# Erdős #287 effectivity — small-`ℓ` local mean and centred covariance (§58)

```
CRT PRODUCT–SUM FACTORISATION            : KERNEL-PROVED
SMALL-ell LOCAL MEAN  −μ(ℓ)β(ℓ)/ℓ        : KERNEL-PROVED
PRIME SPECIALISATION K_p = β(p)1_{p∣s}   : KERNEL-PROVED (reused)
"COMPLETE FIBRE ⇒ ZERO MEAN" FIREWALL    : KERNEL-PROVED (refuted)
CENTRED COVARIANCE / GRAM POSITIVITY     : KERNEL-PROVED
"PERIOD COVARIANCE ⇒ INTERVAL CONTROL"   : KERNEL-PROVED FIREWALL (refuted)
```

For odd squarefree `ℓ > 1` with `(ℓ,z) = 1`, the complete-period mean of the local formula is

    mean(K_ℓ) = −μ(ℓ) β(ℓ) / ℓ,

proved by the exact CRT product–sum factorisation `crt_prod_sum` together with the two local
evaluations `local_sum_full = 0` and `local_sum_mask = p − 1`.

The centred kernel is `Z_ℓ = K_ℓ − mean(K_ℓ)`; `gram_quadratic_form_nonneg` is the positive
quadratic-form decomposition of the complete-period covariance.  Two firewalls are recorded:
a **complete local divisor fibre does not force a zero local mean** (`K_p` is a counterexample,
its mean being `β(p)/p ≠ 0`), and **complete-period covariance does not control physically
selected intervals** (explicit finite witness).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open Finset

namespace Erdos287
namespace Effectivity

/-! ## §58.1  The CRT product–sum factorisation -/

/-- **`crt_two_factor`.**  `KERNEL-PROVED`.  Two-factor CRT factorisation of a complete
residue sum. -/
theorem crt_two_factor {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hco : Nat.Coprime m n)
    (F G : ℕ → ℚ) :
    ∑ s ∈ Finset.range (m * n), F (s % m) * G (s % n)
      = (∑ i ∈ Finset.range m, F i) * (∑ j ∈ Finset.range n, G j) := by
  rw [Finset.sum_mul_sum, ← Finset.sum_product']
  refine Finset.sum_nbij' (i := fun s => (s % m, s % n))
    (j := fun p => (Nat.chineseRemainder hco p.1 p.2 : ℕ)) ?_ ?_ ?_ ?_ ?_
  · intro a _
    simp [Finset.mem_product, Finset.mem_range, Nat.mod_lt _ hm, Nat.mod_lt _ hn]
  · intro p _
    simp only [Finset.mem_range]
    exact Nat.chineseRemainder_lt_mul hco p.1 p.2 hm.ne' hn.ne'
  · intro a ha
    simp only [Finset.mem_range] at ha
    obtain ⟨h1, h2⟩ := (Nat.chineseRemainder hco (a % m) (a % n)).2
    have hk : (Nat.chineseRemainder hco (a % m) (a % n) : ℕ) ≡ a [MOD m * n] :=
      (Nat.modEq_and_modEq_iff_modEq_mul hco).1
        ⟨h1.trans (Nat.mod_modEq a m), h2.trans (Nat.mod_modEq a n)⟩
    have hlt := Nat.chineseRemainder_lt_mul hco (a % m) (a % n) hm.ne' hn.ne'
    have hk' : (Nat.chineseRemainder hco (a % m) (a % n) : ℕ) % (m * n) = a % (m * n) := hk
    rwa [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt ha] at hk'
  · intro p hp
    simp only [Finset.mem_product, Finset.mem_range] at hp
    obtain ⟨h1, h2⟩ := (Nat.chineseRemainder hco p.1 p.2).2
    have e1 : (Nat.chineseRemainder hco p.1 p.2 : ℕ) % m = p.1 := by
      have h : (Nat.chineseRemainder hco p.1 p.2 : ℕ) % m = p.1 % m := h1
      rw [h, Nat.mod_eq_of_lt hp.1]
    have e2 : (Nat.chineseRemainder hco p.1 p.2 : ℕ) % n = p.2 := by
      have h : (Nat.chineseRemainder hco p.1 p.2 : ℕ) % n = p.2 % n := h2
      rw [h, Nat.mod_eq_of_lt hp.2]
    exact Prod.ext e1 e2
  · intro a _
    rfl

/-- **`crt_prod_sum`.**  `KERNEL-PROVED`.  Complete residue sums of products of local
functions factor over the prime factors of a squarefree modulus. -/
theorem crt_prod_sum : ∀ ell : ℕ, Squarefree ell → ∀ g : ℕ → ℕ → ℚ,
    ∑ s ∈ Finset.range ell, ∏ p ∈ ell.primeFactors, g p (s % p)
      = ∏ p ∈ ell.primeFactors, ∑ i ∈ Finset.range p, g p i := by
  intro ell
  induction ell using Nat.strong_induction_on with
  | _ ell ih =>
    intro hsq g
    rcases eq_or_ne ell 1 with h1 | h1
    · subst h1
      simp
    · have hell0 : ell ≠ 0 := hsq.ne_zero
      set p := ell.minFac with hpdef
      have hp : p.Prime := Nat.minFac_prime h1
      have hpdvd : p ∣ ell := Nat.minFac_dvd ell
      set m := ell / p with hmdef
      have hmul : p * m = ell := Nat.mul_div_cancel' hpdvd
      have hm0 : m ≠ 0 := by
        intro h
        rw [h, mul_zero] at hmul
        exact hell0 hmul.symm
      have hmlt : m < ell := by
        have hp2 := hp.two_le
        have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
        nlinarith [hmul]
      have hmsq : Squarefree m := hsq.squarefree_of_dvd ⟨p, by rw [← hmul]; ring⟩
      have hcop : Nat.Coprime p m := by
        rw [Nat.Prime.coprime_iff_not_dvd hp]
        intro hpm
        obtain ⟨c, hc⟩ := hpm
        have hdd : p * p ∣ ell := ⟨c, by rw [← hmul, hc]; ring⟩
        exact hp.one_lt.ne' (Nat.isUnit_iff.mp (hsq p hdd))
      have hpf : ell.primeFactors = insert p m.primeFactors := by
        rw [← hmul, Nat.primeFactors_mul hp.ne_zero hm0, hp.primeFactors, Finset.insert_eq]
      have hpnot : p ∉ m.primeFactors := by
        intro hmem
        exact (Nat.Prime.coprime_iff_not_dvd hp).1 hcop (Nat.dvd_of_mem_primeFactors hmem)
      have hinner : ∀ s : ℕ, ∏ q ∈ m.primeFactors, g q (s % q)
          = ∏ q ∈ m.primeFactors, g q ((s % m) % q) := by
        intro s
        refine Finset.prod_congr rfl fun q hq => ?_
        rw [Nat.mod_mod_of_dvd s (Nat.dvd_of_mem_primeFactors hq)]
      calc ∑ s ∈ Finset.range ell, ∏ q ∈ ell.primeFactors, g q (s % q)
          = ∑ s ∈ Finset.range (p * m),
              g p (s % p) * ∏ q ∈ m.primeFactors, g q ((s % m) % q) := by
            rw [hmul]
            refine Finset.sum_congr rfl fun s _ => ?_
            rw [hpf, Finset.prod_insert hpnot, hinner s]
        _ = (∑ i ∈ Finset.range p, g p i)
              * ∑ t ∈ Finset.range m, ∏ q ∈ m.primeFactors, g q (t % q) :=
            crt_two_factor hp.pos (Nat.pos_of_ne_zero hm0) hcop (fun i => g p i)
              (fun t => ∏ q ∈ m.primeFactors, g q (t % q))
        _ = (∑ i ∈ Finset.range p, g p i)
              * ∏ q ∈ m.primeFactors, ∑ i ∈ Finset.range q, g q i := by
            rw [ih m hmlt hmsq g]
        _ = ∏ q ∈ ell.primeFactors, ∑ i ∈ Finset.range q, g q i := by
            rw [hpf, Finset.prod_insert hpnot]

/-! ## §58.2  The two local evaluations -/

/-- **`local_sum_mask`.**  `KERNEL-PROVED`.  `∑_{i<p} 1_{i ≠ r} = p − 1`. -/
theorem local_sum_mask {p r : ℕ} (hr : r < p) :
    ∑ i ∈ Finset.range p, (if i = r then (0 : ℚ) else 1) = (p : ℚ) - 1 := by
  have hpoint : ∀ i, (if i = r then (0 : ℚ) else 1) = 1 + (if i = r then (-1 : ℚ) else 0) := by
    intro i
    by_cases h : i = r <;> simp [h]
  rw [Finset.sum_congr rfl (fun i _ => hpoint i), Finset.sum_add_distrib,
    Finset.sum_ite_eq' (Finset.range p) r (fun _ => (-1 : ℚ)), if_pos (Finset.mem_range.2 hr),
    Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  ring

/-- **`local_sum_full`.**  `KERNEL-PROVED`.  The full local factor sums to `0`:
`∑_{i<p} (2−p)^{1_{i=0}} 1_{i ≠ r} = (2−p) + (p−2) = 0` when `r ≠ 0`. -/
theorem local_sum_full {p r : ℕ} (hp : 2 ≤ p) (hr : r < p) (hr0 : r ≠ 0) :
    ∑ i ∈ Finset.range p,
        ((if i = 0 then (2 - (p : ℚ)) else 1) * (if i = r then (0 : ℚ) else 1)) = 0 := by
  have hpoint : ∀ i, ((if i = 0 then (2 - (p : ℚ)) else 1) * (if i = r then (0 : ℚ) else 1))
      = 1 + (if i = 0 then (1 - (p : ℚ)) else 0) + (if i = r then (-1 : ℚ) else 0) := by
    intro i
    by_cases h0 : i = 0
    · subst h0
      have hne : (0 : ℕ) ≠ r := fun h => hr0 h.symm
      rw [if_pos rfl, if_neg hne, if_pos rfl, if_neg hne]
      ring
    · by_cases hrr : i = r
      · rw [if_neg h0, if_pos hrr, if_neg h0, if_pos hrr]
        ring
      · rw [if_neg h0, if_neg hrr, if_neg h0, if_neg hrr]
        ring
  rw [Finset.sum_congr rfl (fun i _ => hpoint i), Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_ite_eq' (Finset.range p) 0 (fun _ => (1 : ℚ) - (p : ℚ)),
    Finset.sum_ite_eq' (Finset.range p) r (fun _ => (-1 : ℚ)),
    if_pos (Finset.mem_range.2 (by omega : 0 < p)), if_pos (Finset.mem_range.2 hr),
    Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  ring

/-! ## §58.3  The small-`ℓ` local mean -/

lemma int_dvd_natCast_iff (p s : ℕ) : ((p : ℤ) ∣ (s : ℤ)) ↔ s % p = 0 := by
  rw [Int.natCast_dvd_natCast]
  exact Nat.dvd_iff_mod_eq_zero

lemma int_dvd_sub_iff (p s z : ℕ) : ((p : ℤ) ∣ ((z : ℤ) - (s : ℤ))) ↔ s % p = z % p :=
  (Nat.modEq_iff_dvd (n := p) (a := s) (b := z)).symm

/-- The complete-period sum of the local formula. -/
def periodSum (ell z : ℕ) : ℚ := ∑ s ∈ Finset.range ell, Kell ell (s : ℤ) (z : ℤ)

/-- The complete-period mean of the local formula. -/
def meanK (ell z : ℕ) : ℚ := periodSum ell z / (ell : ℚ)

/-- The local factors of the mean computation. -/
def glocFactor (z p i : ℕ) : ℚ :=
  (if i = 0 then (2 - (p : ℚ)) else 1) * (if i = z % p then (0 : ℚ) else 1)

/-- The mask-only local factor. -/
def mlocFactor (z p i : ℕ) : ℚ := if i = z % p then (0 : ℚ) else 1

lemma Kell_local_split (ell z s : ℕ) :
    Kell ell (s : ℤ) (z : ℤ)
      = cEll ell * (∏ p ∈ ell.primeFactors, glocFactor z p (s % p))
        - cEll ell * (∏ p ∈ ell.primeFactors, mlocFactor z p (s % p)) := by
  have hmask : coprimeMask ell ((z : ℤ) - (s : ℤ))
      = ∏ p ∈ ell.primeFactors, mlocFactor z p (s % p) := by
    refine Finset.prod_congr rfl fun p hp => ?_
    rw [mlocFactor]
    by_cases h : s % p = z % p
    · rw [if_pos h, if_pos ((int_dvd_sub_iff p s z).2 h)]
    · rw [if_neg h, if_neg (fun hd => h ((int_dvd_sub_iff p s z).1 hd))]
  have hbracket : (∏ p ∈ gcdFactors ell (s : ℤ), (2 - (p : ℚ)))
      = ∏ p ∈ ell.primeFactors, (if s % p = 0 then (2 - (p : ℚ)) else 1) := by
    rw [gcdFactors, Finset.prod_filter]
    refine Finset.prod_congr rfl fun p hp => ?_
    by_cases h : s % p = 0
    · rw [if_pos h, if_pos ((int_dvd_natCast_iff p s).2 h)]
    · rw [if_neg h, if_neg (fun hd => h ((int_dvd_natCast_iff p s).1 hd))]
  have hglob : (∏ p ∈ ell.primeFactors, glocFactor z p (s % p))
      = (∏ p ∈ ell.primeFactors, (if s % p = 0 then (2 - (p : ℚ)) else 1))
        * ∏ p ∈ ell.primeFactors, mlocFactor z p (s % p) := by
    rw [← Finset.prod_mul_distrib]
    rfl
  rw [Kell, hmask, hbracket, mul_sub, mul_one, hglob]
  ring

/-- **`smallEll_periodSum`.**  `KERNEL-PROVED`.  The complete-period sum of `K_ℓ` equals
`−c_ℓ φ(ℓ)`, i.e. `−μ(ℓ)β(ℓ)`. -/
theorem smallEll_periodSum {ell z : ℕ} (hsq : Squarefree ell) (hell : 1 < ell)
    (hz : ∀ p ∈ ell.primeFactors, ¬ p ∣ z) :
    periodSum ell z = - cEll ell * ∏ p ∈ ell.primeFactors, ((p : ℚ) - 1) := by
  have hell0 : ell ≠ 0 := hsq.ne_zero
  have hsplit : periodSum ell z
      = cEll ell * (∑ s ∈ Finset.range ell, ∏ p ∈ ell.primeFactors, glocFactor z p (s % p))
        - cEll ell * (∑ s ∈ Finset.range ell, ∏ p ∈ ell.primeFactors, mlocFactor z p (s % p)) := by
    rw [periodSum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun s _ => Kell_local_split ell z s
  have hfull : ∑ s ∈ Finset.range ell, ∏ p ∈ ell.primeFactors, glocFactor z p (s % p) = 0 := by
    rw [crt_prod_sum ell hsq (fun p i => glocFactor z p i)]
    obtain ⟨p, hp⟩ : ell.primeFactors.Nonempty := by
      rw [Nat.nonempty_primeFactors]
      exact hell
    refine Finset.prod_eq_zero hp ?_
    have hprime := Nat.prime_of_mem_primeFactors hp
    have hzp : z % p ≠ 0 := by
      intro h
      exact hz p hp (Nat.dvd_iff_mod_eq_zero.2 h)
    exact local_sum_full hprime.two_le (Nat.mod_lt _ hprime.pos) hzp
  have hmaskSum : ∑ s ∈ Finset.range ell, ∏ p ∈ ell.primeFactors, mlocFactor z p (s % p)
      = ∏ p ∈ ell.primeFactors, ((p : ℚ) - 1) := by
    rw [crt_prod_sum ell hsq (fun p i => mlocFactor z p i)]
    refine Finset.prod_congr rfl fun p hp => ?_
    have hprime := Nat.prime_of_mem_primeFactors hp
    exact local_sum_mask (Nat.mod_lt _ hprime.pos)
  rw [hsplit, hfull, hmaskSum]
  ring

lemma totient_prod_primeFactors {n : ℕ} (h : Squarefree n) :
    Nat.totient n = ∏ p ∈ n.primeFactors, (p - 1) := by
  have hn : n ≠ 0 := h.ne_zero
  rw [Nat.totient_eq_prod_factorization hn, Nat.prod_factorization_eq_prod_primeFactors]
  refine Finset.prod_congr rfl fun p hp => ?_
  have h1 : n.factorization p = 1 := by
    have hle := (Nat.squarefree_iff_factorization_le_one hn).1 h p
    have h2 : 1 ≤ n.factorization p :=
      Nat.Prime.factorization_pos_of_dvd (Nat.prime_of_mem_primeFactors hp) hn
        (Nat.dvd_of_mem_primeFactors hp)
    omega
  rw [h1]
  simp

lemma totient_cast_prod {n : ℕ} (h : Squarefree n) :
    ((Nat.totient n : ℕ) : ℚ) = ∏ p ∈ n.primeFactors, ((p : ℚ) - 1) := by
  rw [totient_prod_primeFactors h, Nat.cast_prod]
  refine Finset.prod_congr rfl fun p hp => ?_
  have hprime := Nat.prime_of_mem_primeFactors hp
  rw [Nat.cast_sub hprime.one_le]
  norm_num

/-- **`smallEll_local_mean`.**  `KERNEL-PROVED`.  The small-`ℓ` local mean:

    mean(K_ℓ) = − μ(ℓ) β(ℓ) / ℓ    for squarefree `ℓ > 1` with `(ℓ,z) = 1`. -/
theorem smallEll_local_mean {ell z : ℕ} (hsq : Squarefree ell) (hell : 1 < ell)
    (hz : ∀ p ∈ ell.primeFactors, ¬ p ∣ z) :
    meanK ell z = - ((ArithmeticFunction.moebius ell : ℤ) : ℚ) * beta ell / (ell : ℚ) := by
  have hphi : ((Nat.totient ell : ℕ) : ℚ) = ∏ p ∈ ell.primeFactors, ((p : ℚ) - 1) :=
    totient_cast_prod hsq
  have hphine : ((Nat.totient ell : ℕ) : ℚ) ≠ 0 := by
    have := Nat.totient_pos.2 (by omega : 0 < ell)
    exact_mod_cast this.ne'
  rw [meanK, smallEll_periodSum hsq hell hz, ← hphi, cEll]
  field_simp

/-! ## §58.4  Firewall: a complete local divisor fibre does not force a zero mean -/

/-- **`prime_periodSum`.**  `KERNEL-PROVED`.  `∑_{s < p} K_p(s,z) = β(p)`. -/
theorem prime_periodSum {p z : ℕ} (hp : p.Prime) (hz : ¬ p ∣ z) :
    periodSum p z = beta p := by
  have hterm : ∀ s ∈ Finset.range p, Kell p (s : ℤ) (z : ℤ)
      = if s = 0 then beta p else 0 := by
    intro s hs
    rw [Finset.mem_range] at hs
    have hzz : ¬ (p : ℤ) ∣ (z : ℤ) := by
      rw [Int.natCast_dvd_natCast]; exact hz
    rw [Kell_prime_specialisation hp hzz]
    by_cases h : s = 0
    · subst h
      simp
    · have hnd : ¬ (p : ℤ) ∣ (s : ℤ) := by
        rw [int_dvd_natCast_iff p s, Nat.mod_eq_of_lt hs]
        exact h
      rw [if_neg hnd, if_neg h, mul_zero]
  rw [periodSum, Finset.sum_congr rfl hterm,
    Finset.sum_ite_eq' (Finset.range p) 0 (fun _ => beta p),
    if_pos (Finset.mem_range.2 hp.pos)]

/-- **`complete_fibre_not_zero_mean`.**  `KERNEL-PROVED` firewall.  `K_p` carries the complete
local divisor fibre, yet its complete-period mean is `β(p)/p ≠ 0`: a complete fibre does
**not** imply a vanishing local mean. -/
theorem complete_fibre_not_zero_mean {p z : ℕ} (hp : p.Prime) (h2 : p ≠ 2) (hz : ¬ p ∣ z) :
    meanK p z = beta p / (p : ℚ) ∧ meanK p z ≠ 0 := by
  have hpos := beta_pos_of_odd_prime hp h2
  have hp0 : ((p : ℚ)) ≠ 0 := by
    have := hp.pos
    exact_mod_cast this.ne'
  refine ⟨by rw [meanK, prime_periodSum hp hz], ?_⟩
  rw [meanK, prime_periodSum hp hz]
  have : 0 < beta p / (p : ℚ) := by
    apply div_pos hpos
    have := hp.pos
    exact_mod_cast this
  exact ne_of_gt this

/-! ## §58.5  Centred kernel, covariance and Gram positivity -/

/-- The centred local kernel `Z_ℓ = K_ℓ − mean(K_ℓ)`. -/
def Zcent (ell z : ℕ) (s : ℤ) : ℚ := Kell ell s (z : ℤ) - meanK ell z

/-- The complete-period covariance of two centred kernels at a common period `L`. -/
def GammaL (L : ℕ) (f g : ℤ → ℚ) : ℚ :=
  (1 / (L : ℚ)) * ∑ s ∈ Finset.range L, f (s : ℤ) * g (s : ℤ)

/-- **`gram_quadratic_form`.**  `KERNEL-PROVED`.  The exact quadratic-form decomposition of
the complete-period covariance of a finite family. -/
theorem gram_quadratic_form (L : ℕ) (S : Finset ℕ) (x : ℕ → ℚ) (Z : ℕ → ℤ → ℚ) :
    ∑ a ∈ S, ∑ b ∈ S, x a * x b * GammaL L (Z a) (Z b)
      = (1 / (L : ℚ)) * ∑ s ∈ Finset.range L, (∑ a ∈ S, x a * Z a (s : ℤ)) ^ 2 := by
  have step1 : ∀ a b : ℕ, x a * x b * GammaL L (Z a) (Z b)
      = ∑ s ∈ Finset.range L,
          (1 / (L : ℚ)) * ((x a * Z a (s : ℤ)) * (x b * Z b (s : ℤ))) := by
    intro a b
    rw [GammaL, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => by ring
  calc ∑ a ∈ S, ∑ b ∈ S, x a * x b * GammaL L (Z a) (Z b)
      = ∑ a ∈ S, ∑ b ∈ S, ∑ s ∈ Finset.range L,
          (1 / (L : ℚ)) * ((x a * Z a (s : ℤ)) * (x b * Z b (s : ℤ))) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => step1 a b
    _ = ∑ a ∈ S, ∑ s ∈ Finset.range L, ∑ b ∈ S,
          (1 / (L : ℚ)) * ((x a * Z a (s : ℤ)) * (x b * Z b (s : ℤ))) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ s ∈ Finset.range L, ∑ a ∈ S, ∑ b ∈ S,
          (1 / (L : ℚ)) * ((x a * Z a (s : ℤ)) * (x b * Z b (s : ℤ))) := Finset.sum_comm
    _ = (1 / (L : ℚ)) * ∑ s ∈ Finset.range L, (∑ a ∈ S, x a * Z a (s : ℤ)) ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ => by rw [Finset.mul_sum]

/-- **`gram_quadratic_form_nonneg`.**  `KERNEL-PROVED`.  The complete-period covariance form
is positive semidefinite. -/
theorem gram_quadratic_form_nonneg (L : ℕ) (S : Finset ℕ) (x : ℕ → ℚ) (Z : ℕ → ℤ → ℚ) :
    0 ≤ ∑ a ∈ S, ∑ b ∈ S, x a * x b * GammaL L (Z a) (Z b) := by
  rw [gram_quadratic_form]
  have h1 : (0 : ℚ) ≤ 1 / (L : ℚ) := by positivity
  have h2 : (0 : ℚ) ≤ ∑ s ∈ Finset.range L, (∑ a ∈ S, x a * Z a (s : ℤ)) ^ 2 :=
    Finset.sum_nonneg fun s _ => sq_nonneg _
  exact mul_nonneg h1 h2

/-- **`period_covariance_does_not_control_intervals`.**  `KERNEL-PROVED` firewall.  A function
with vanishing complete-period sum can have a nonzero sum on a selected sub-window: the
complete-period covariance never controls physically selected intervals by itself. -/
theorem period_covariance_does_not_control_intervals :
    ∃ f : ℕ → ℚ, (∀ s, f (s + 2) = f s) ∧ (∑ s ∈ Finset.range 2, f s = 0) ∧
      (∑ s ∈ Finset.range 1, f s ≠ 0) := by
  refine ⟨fun s => if s % 2 = 0 then 1 else -1, ?_, ?_, ?_⟩
  · intro s
    simp [Nat.add_mod_right]
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

end Effectivity
end Erdos287
