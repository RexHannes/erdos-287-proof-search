import RequestProject.Erdos287.ResearchBankV13.AdjacentPrimeLayer
import RequestProject.CurrentProgramme.Erdos287September3PrattEngine

/-!
# Erdős #287 — Research Bank V13 §23: Proth / Pocklington certificate soundness

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

Mathlib provides the general Lucas test (`lucas_primality`, re-used by the project's Pratt engine
`Erdos287.Pratt.prime_of_certificate`) but no Proth or Pocklington witness checker, so the two
witness formats are formalized here, with **generic soundness proofs** and kernel-computable
checkers (binary modular exponentiation `Pratt.powMod`, proved correct in the Pratt engine).

* **Proth** (`proth_sound`): `q = u·2ⁿ + 1`, `n ≥ 1`, `0 < u < 2ⁿ`, and a witness `a` with
  `a^((q−1)/2) ≡ −1 (mod q)` ⟹ `q` prime.  (Oddness of `u` is part of the witness *format*
  checked by `prothCheck`, but soundness does not need it.)
* **Pocklington** (`pocklington_sound`): `p = c·q + 1`, `c ≥ 1`, `q` prime, `q² > p`, a witness `b`
  with `b^(p−1) ≡ 1 (mod p)` and `gcd(bᶜ − 1, p) = 1` ⟹ `p` prime.  The format checker
  `pocklingtonCheck` restricts to `c ∈ {2, 4}` as specified.
* Checker soundness: `prothCheck_sound`, `pocklingtonCheck_sound`.
* Fixtures: `13` and `97` by Proth; the chain `43 → 173 → 347` by Pocklington (`c = 4`, then
  `c = 2`); malformed witnesses are rejected (`malformed_proth_rejected`,
  `malformed_pocklington_rejected`).

No `native_decide`, `bv_decide`, probable-prime routine or primality axiom is used; the checks
are closed by ordinary kernel `decide` on small numerals.  **No 500-digit prime is certified
here** (no such witness data is present in the workspace).
-/

namespace Erdos287
namespace ResearchBankV13
namespace PrimeCertificates

/-- If `r ∣ m`, reducing mod `m` does not change the class mod `r`. -/
theorem cast_mod_of_dvd {r m x : ℕ} (h : r ∣ m) : ((x % m : ℕ) : ZMod r) = x := by
  conv_rhs => rw [← Nat.mod_add_div x m]
  push_cast
  rw [(ZMod.natCast_eq_zero_iff m r).mpr h]; ring

/-- A composite `n > 1` has a prime factor `r` with `r² ≤ n`. -/
theorem exists_small_prime_factor {n : ℕ} (hn : 1 < n) (hnp : ¬ n.Prime) :
    ∃ r, r.Prime ∧ r ∣ n ∧ r ^ 2 ≤ n :=
  ⟨n.minFac, Nat.minFac_prime (by omega), Nat.minFac_dvd n, Nat.minFac_sq_le_self (by omega) hnp⟩

/-! ## Pocklington -/

/-- **Pocklington soundness** (special form `p = c q + 1`, `q` prime, `q² > p`). -/
theorem pocklington_sound {p q c b : ℕ} (hq : q.Prime) (hc : 1 ≤ c) (hp : p = c * q + 1)
    (hq2 : p < q ^ 2) (hpow : b ^ (p - 1) % p = 1) (hgcd : Nat.gcd (b ^ c - 1) p = 1) :
    p.Prime := by
  have hq2' := hq.two_le
  have hp1 : 1 < p := by rw [hp]; nlinarith
  by_contra hnp
  obtain ⟨r, hr, hrp, hr2⟩ := exists_small_prime_factor hp1 hnp
  haveI := Fact.mk hr
  haveI := Fact.mk hq
  -- `b ≠ 0`
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega), Nat.zero_mod] at hpow; exact absurd hpow (by norm_num)
  have hbc1 : 1 ≤ b ^ c := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero hb0)
  set x : ZMod r := (b : ZMod r) ^ c with hx
  -- `x ^ q = 1`
  have hxq : x ^ q = 1 := by
    have h1 : ((b ^ (p - 1) % p : ℕ) : ZMod r) = ((b ^ (p - 1) : ℕ) : ZMod r) := cast_mod_of_dvd hrp
    rw [hpow] at h1
    rw [hx, ← pow_mul, show c * q = p - 1 by omega]
    push_cast at h1; exact h1.symm
  -- `x ≠ 1`
  have hx1 : x ≠ 1 := by
    intro h
    have h2 : ((b ^ c - 1 : ℕ) : ZMod r) = 0 := by
      rw [Nat.cast_sub hbc1]; push_cast; rw [← hx, h, sub_self]
    have h3 : r ∣ b ^ c - 1 := (ZMod.natCast_eq_zero_iff _ r).mp h2
    have h4 : r ∣ Nat.gcd (b ^ c - 1) p := Nat.dvd_gcd h3 hrp
    rw [hgcd] at h4
    exact hr.one_lt.ne' (Nat.dvd_one.mp h4)
  have hord : orderOf x = q := orderOf_eq_prime hxq hx1
  have hx0 : x ≠ 0 := by
    intro h; rw [h, zero_pow hq.ne_zero] at hxq; exact zero_ne_one hxq
  have hdvd : q ∣ r - 1 := hord ▸ ZMod.orderOf_dvd_card_sub_one hx0
  have hqr : q < r := by
    have := Nat.le_of_dvd (by have := hr.two_le; omega) hdvd; omega
  have : q ^ 2 < r ^ 2 := Nat.pow_lt_pow_left hqr (by norm_num)
  omega

/-! ## Proth -/

/-- **Proth soundness**: `q = u 2ⁿ + 1`, `n ≥ 1`, `0 < u < 2ⁿ`, `a^((q−1)/2) ≡ −1 (mod q)`. -/
theorem proth_sound {u n a : ℕ} (hn : 1 ≤ n) (hu0 : 0 < u) (hu : u < 2 ^ n)
    (hwit : a ^ ((u * 2 ^ n + 1 - 1) / 2) % (u * 2 ^ n + 1) = u * 2 ^ n + 1 - 1) :
    (u * 2 ^ n + 1).Prime := by
  set q := u * 2 ^ n + 1 with hqdef
  have h2n : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hq1 : 1 < q := by rw [hqdef]; nlinarith
  by_contra hnp
  obtain ⟨r, hr, hrq, hr2⟩ := exists_small_prime_factor hq1 hnp
  haveI := Fact.mk hr
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  -- `q` is odd, so `r ≠ 2`
  have hqodd : q % 2 = 1 := by
    have : 2 ∣ u * 2 ^ n := Dvd.dvd.mul_left (dvd_pow_self 2 (by omega)) u
    omega
  have hr2' : r ≠ 2 := by
    rintro rfl
    obtain ⟨k, hk⟩ := hrq; omega
  have hneg : (-1 : ZMod r) ≠ 1 := by
    haveI : Fact (2 < r) := ⟨by have := hr.two_le; omega⟩
    exact ZMod.neg_one_ne_one
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hhalf : (q - 1) / 2 = u * 2 ^ m := by
    rw [hqdef, Nat.add_sub_cancel, pow_succ, ← mul_assoc, Nat.mul_div_cancel _ (by norm_num)]
  set y : ZMod r := (a : ZMod r) ^ u with hy
  -- `y ^ (2^m) = −1`
  have hym : y ^ 2 ^ m = -1 := by
    have h1 : ((a ^ ((q - 1) / 2) % q : ℕ) : ZMod r) = ((a ^ ((q - 1) / 2) : ℕ) : ZMod r) :=
      cast_mod_of_dvd hrq
    rw [hwit, hhalf] at h1
    have hq0 : ((q : ℕ) : ZMod r) = 0 := (ZMod.natCast_eq_zero_iff q r).mpr hrq
    have h3 : ((q - 1 : ℕ) : ZMod r) = -1 := by
      rw [Nat.cast_sub (by omega), hq0]; push_cast; ring
    rw [h3] at h1
    rw [hy, ← pow_mul]; push_cast at h1; exact h1.symm
  have hnot : ¬ y ^ 2 ^ m = 1 := by rw [hym]; exact hneg
  have hfin : y ^ 2 ^ (m + 1) = 1 := by
    rw [pow_succ, pow_mul, hym]; norm_num
  have hord : orderOf y = 2 ^ (m + 1) := orderOf_eq_prime_pow hnot hfin
  have hy0 : y ≠ 0 := by
    intro h; rw [h, zero_pow (by positivity)] at hfin; exact zero_ne_one hfin
  have hdvd : 2 ^ (m + 1) ∣ r - 1 := hord ▸ ZMod.orderOf_dvd_card_sub_one hy0
  have hlt : 2 ^ (m + 1) < r := by
    have := Nat.le_of_dvd (by have := hr.two_le; omega) hdvd; omega
  -- `r² > 2^(2(m+1)) ≥ q`
  have hsq : (2 ^ (m + 1)) ^ 2 < r ^ 2 := Nat.pow_lt_pow_left hlt (by norm_num)
  have hqle : q ≤ (2 ^ (m + 1)) ^ 2 := by
    rw [hqdef, sq]
    have : u + 1 ≤ 2 ^ (m + 1) := hu
    nlinarith
  omega

/-! ## Kernel-computable checkers -/

/-- The Proth witness format check (uses fuel `2n` for `powMod`, enough since
`(q−1)/2 < 2^(2n)`). -/
def prothCheck (u n a : ℕ) : Bool :=
  decide (1 ≤ n) && decide (0 < u) && decide (u < 2 ^ n) && decide (u % 2 = 1) &&
    decide (Pratt.powMod (u * 2 ^ n + 1) (2 * n) a ((u * 2 ^ n + 1 - 1) / 2) = u * 2 ^ n + 1 - 1)

/-- **Proth checker soundness.** -/
theorem prothCheck_sound {u n a : ℕ} (h : prothCheck u n a = true) : (u * 2 ^ n + 1).Prime := by
  simp only [prothCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hn, hu0⟩, hu⟩, -⟩, hw⟩ := h
  refine proth_sound (a := a) hn hu0 hu ?_
  have hlt : (u * 2 ^ n + 1 - 1) / 2 < 2 ^ (2 * n) := by
    have h1 : u * 2 ^ n < 2 ^ n * 2 ^ n := Nat.mul_lt_mul_of_pos_right hu (by positivity)
    rw [two_mul, pow_add]; omega
  rw [← Pratt.powMod_eq _ _ _ _ hlt]; exact hw

/-- The Pocklington witness format check (`c ∈ {2, 4}`; explicit fuel `f` with `p − 1 < 2^f`). -/
def pocklingtonCheck (c q b f : ℕ) : Bool :=
  (decide (c = 2) || decide (c = 4)) && decide (c * q + 1 < q ^ 2) &&
    decide (c * q + 1 - 1 < 2 ^ f) &&
    decide (Pratt.powMod (c * q + 1) f b (c * q + 1 - 1) = 1) &&
    decide (Nat.gcd (b ^ c - 1) (c * q + 1) = 1)

/-- **Pocklington checker soundness** (given that `q` is already prime). -/
theorem pocklingtonCheck_sound {c q b f : ℕ} (hq : q.Prime) (h : pocklingtonCheck c q b f = true) :
    (c * q + 1).Prime := by
  simp only [pocklingtonCheck, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hc, hq2⟩, hf⟩, hpow⟩, hgcd⟩ := h
  refine pocklington_sound hq (by rcases hc with rfl | rfl <;> norm_num) rfl hq2 ?_ hgcd
  rw [← Pratt.powMod_eq _ _ _ _ hf]; exact hpow

/-! ## Fixtures -/

/-- `13 = 3·2² + 1` is prime by Proth with witness `2`. -/
theorem prime_13 : Nat.Prime 13 := prothCheck_sound (u := 3) (n := 2) (a := 2) (by decide)

/-- `97 = 3·2⁵ + 1` is prime by Proth with witness `5`. -/
theorem prime_97 : Nat.Prime 97 := prothCheck_sound (u := 3) (n := 5) (a := 5) (by decide)

/-- `173 = 4·43 + 1` is prime by Pocklington from `43` (witness `2`). -/
theorem prime_173 : Nat.Prime 173 :=
  pocklingtonCheck_sound (c := 4) (q := 43) (b := 2) (f := 8) (by norm_num) (by decide)

/-- `347 = 2·173 + 1` is prime by Pocklington from `173` (witness `2`). -/
theorem prime_347 : Nat.Prime 347 :=
  pocklingtonCheck_sound (c := 2) (q := 173) (b := 2) (f := 9) prime_173 (by decide)

/-- **Regression fixture 8: malformed Proth witnesses are rejected** — `u ≥ 2ⁿ`, even `u`,
a wrong witness, and the composite Proth-form number `9 = 1·2³ + 1` (no witness `a < 9`). -/
theorem malformed_proth_rejected :
    prothCheck 5 2 2 = false ∧ prothCheck 2 3 3 = false ∧ prothCheck 3 2 3 = false ∧
      ∀ a < 9, prothCheck 1 3 a = false := by
  decide

/-- **Regression fixture 9: malformed Pocklington witnesses are rejected** — `c = 3`,
`q² ≤ p`, a wrong witness, and the composite `9 = 2·4 + 1` (no witness `b < 9`). -/
theorem malformed_pocklington_rejected :
    pocklingtonCheck 3 173 2 10 = false ∧ pocklingtonCheck 4 3 2 4 = false ∧
      pocklingtonCheck 2 173 1 9 = false ∧ ∀ b < 9, pocklingtonCheck 2 4 b 4 = false := by
  decide

/-- A Family-A certificate instance built from the Pocklington chain (`q = 173`, `p = 347`). -/
theorem familyA_from_certificates :
    ∀ M, 346 ≤ M → M ≤ HarmonicTwoHole.etaFloor 347 →
      FiniteRepresentationModel.NoCounterexampleAt M :=
  AdjacentPrimeLayer.familyA_interval prime_347 prime_173 rfl (by norm_num)

end PrimeCertificates
end ResearchBankV13
end Erdos287
