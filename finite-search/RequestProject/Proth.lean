import RequestProject.PowMod

/-!
# Proth's primality criterion

For a number of *Proth shape* `N = k * 2 ^ e + 1` with `k` odd and `k < 2 ^ e`, a single
Euler-type witness

`a ^ ((N - 1) / 2) ≡ -1 (mod N)`

already proves primality: every prime divisor `r` of `N` satisfies `2 ^ e ∣ r - 1`, hence
`r ≥ 2 ^ e + 1 > √N`, and a composite number has a prime divisor `≤ √N`.

This avoids having to factor `k`, which is what `Erdos287.prime_of_cert` (a Lucas certificate)
requires.  The modular congruence itself is verified by kernel evaluation of
`Erdos287.powMod`.
-/

namespace Erdos287

/-- If `d ∣ k * 2 ^ (f + 1)` but `d ∤ k * 2 ^ f`, then `2 ^ (f + 1) ∣ d`. -/
theorem two_pow_dvd_of_not_dvd {d k f : ℕ} (hd0 : d ≠ 0)
    (h1 : d ∣ k * 2 ^ (f + 1)) (h2 : ¬ d ∣ k * 2 ^ f) : 2 ^ (f + 1) ∣ d := by
  obtain ⟨i, s, hs, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hd0
  have hsdvd : s ∣ k * 2 ^ (f + 1) := dvd_trans ⟨2 ^ i, by ring⟩ h1
  have hcop : Nat.Coprime s (2 ^ (f + 1)) :=
    Nat.Coprime.pow_right _ (Nat.coprime_two_right.2 hs)
  have hsk : s ∣ k := hcop.dvd_of_dvd_mul_right hsdvd
  have hif : f + 1 ≤ i := by
    by_contra hcon
    push_neg at hcon
    have hif' : i ≤ f := by omega
    refine h2 ?_
    obtain ⟨u, hu⟩ := hsk
    refine ⟨u * 2 ^ (f - i), ?_⟩
    have : (2 : ℕ) ^ f = 2 ^ i * 2 ^ (f - i) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hu, this]
    ring
  exact dvd_trans (pow_dvd_pow 2 hif) ⟨s, rfl⟩

/--
**Proth's theorem** (in the "Euler witness" form).  If `N = k * 2 ^ e + 1` with
`0 < k < 2 ^ e`, `1 ≤ e`, and `a ^ ((N - 1) / 2) ≡ N - 1 (mod N)` — the latter checked by kernel
evaluation of `powMod` — then `N` is prime.

Proth's criterion is usually stated with `k` odd; the proof below shows that this hypothesis is
not needed for *sufficiency*, so it is omitted.  (Both `k`'s used in this development are in fact
odd.)
-/
theorem prime_of_proth_half_pow_neg_one {k e a N : ℕ} (hk : 0 < k)
    (hke : k < 2 ^ e) (he : 1 ≤ e) (hN : N = k * 2 ^ e + 1) (hsize : N < 2 ^ 256)
    (hcert : powMod N a ((N - 1) / 2) % N = N - 1) :
    N.Prime := by
  obtain ⟨f, rfl⟩ : ∃ f, e = f + 1 := ⟨e - 1, by omega⟩
  have hq : (0 : ℕ) < 2 ^ (f + 1) := Nat.two_pow_pos _
  have hqf : (0 : ℕ) < 2 ^ f := Nat.two_pow_pos _
  have hN1 : N - 1 = k * 2 ^ (f + 1) := by omega
  have hprod : 2 ≤ k * 2 ^ (f + 1) := by
    calc (2 : ℕ) = 1 * 2 ^ 1 := by norm_num
      _ ≤ k * 2 ^ (f + 1) := Nat.mul_le_mul hk (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hN3 : 3 ≤ N := by omega
  set m := (N - 1) / 2 with hm
  have hsplit : N - 1 = (k * 2 ^ f) * 2 := by rw [hN1, pow_succ]; ring
  have hm2 : m = k * 2 ^ f := by rw [hm]; omega
  have hm0 : 0 < m := by
    rw [hm2]
    positivity
  have h2m : 2 * m = N - 1 := by omega
  -- the certificate as a modular congruence
  have hmod : Nat.ModEq N (a ^ m) (N - 1) := by
    have hlt : m < 2 ^ 256 := by omega
    have := (powMod_modEq N a m hlt).symm
    calc a ^ m ≡ powMod N a m [MOD N] := this
      _ ≡ N - 1 [MOD N] := by
          unfold Nat.ModEq
          rw [hcert, Nat.mod_eq_of_lt (by omega)]
  -- `N` is odd
  have hNodd : ¬ 2 ∣ N := by
    intro hdvd
    have : (2 : ℕ) ∣ k * 2 ^ (f + 1) := Dvd.dvd.mul_left (dvd_pow_self 2 (by omega)) k
    omega
  -- every prime divisor of `N` is `≥ 2 ^ e + 1`
  have key : ∀ r : ℕ, r.Prime → r ∣ N → 2 ^ (f + 1) + 1 ≤ r := by
    intro r hr hrN
    haveI : Fact r.Prime := ⟨hr⟩
    have hr2 : r ≠ 2 := by
      rintro rfl
      exact hNodd hrN
    have hrNzero : ((N : ℕ) : ZMod r) = 0 := by
      exact_mod_cast (ZMod.natCast_eq_zero_iff N r).2 hrN
    have hmodr : Nat.ModEq r (a ^ m) (N - 1) := hmod.of_dvd hrN
    have hcast : ((a : ZMod r)) ^ m = -1 := by
      have h1 : ((a ^ m : ℕ) : ZMod r) = ((N - 1 : ℕ) : ZMod r) :=
        (ZMod.natCast_eq_natCast_iff _ _ _).2 hmodr
      rw [Nat.cast_pow] at h1
      rw [h1, Nat.cast_sub (by omega), hrNzero]
      simp
    -- `-1 ≠ 1` in `ZMod r`
    have hne : (-1 : ZMod r) ≠ 1 := by
      intro hcon
      have : (2 : ZMod r) = 0 := by linear_combination -hcon
      have h2r : ((2 : ℕ) : ZMod r) = 0 := by exact_mod_cast this
      have := (ZMod.natCast_eq_zero_iff 2 r).1 h2r
      have := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 this
      exact hr2 this
    have ha0 : (a : ZMod r) ≠ 0 := by
      intro hcon
      rw [hcon, zero_pow (by omega)] at hcast
      have h10 : (1 : ZMod r) = 0 := by linear_combination hcast
      exact one_ne_zero h10
    have hfull : ((a : ZMod r)) ^ (N - 1) = 1 := by
      rw [← h2m, pow_mul']
      rw [hcast]
      norm_num
    have hdvd1 : orderOf (a : ZMod r) ∣ N - 1 := orderOf_dvd_of_pow_eq_one hfull
    have hdvd2 : ¬ orderOf (a : ZMod r) ∣ m := by
      intro hcon
      have : ((a : ZMod r)) ^ m = 1 := orderOf_dvd_iff_pow_eq_one.1 hcon
      rw [hcast] at this
      exact hne this
    have hord0 : orderOf (a : ZMod r) ≠ 0 := by
      intro hcon
      rw [hcon, Nat.zero_dvd] at hdvd1
      omega
    have h2e : 2 ^ (f + 1) ∣ orderOf (a : ZMod r) := by
      refine two_pow_dvd_of_not_dvd (k := k) (f := f) hord0 ?_ ?_
      · rw [← hN1]; exact hdvd1
      · rw [← hm2]; exact hdvd2
    have hordr : orderOf (a : ZMod r) ∣ r - 1 := by
      refine orderOf_dvd_of_pow_eq_one ?_
      exact ZMod.pow_card_sub_one_eq_one ha0
    have : 2 ^ (f + 1) ∣ r - 1 := h2e.trans hordr
    have hr1 : 0 < r - 1 := by
      have := hr.two_le
      omega
    have := Nat.le_of_dvd hr1 this
    omega
  -- conclude
  by_contra hcomp
  have hmf : (N.minFac).Prime := Nat.minFac_prime (by omega)
  have hsq : N.minFac ^ 2 ≤ N := Nat.minFac_sq_le_self (by omega) hcomp
  have hge := key N.minFac hmf (Nat.minFac_dvd N)
  have hklt : k + 1 ≤ 2 ^ (f + 1) := hke
  nlinarith [hsq, hge, hq, hklt, hN, sq_nonneg (2 ^ (f + 1) : ℕ)]

end Erdos287
