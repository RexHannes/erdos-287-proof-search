import Mathlib

/-!
# Erdős Problem #287 — kernel-checkable recursive primality certificates (Pratt / Lucas)

This module supplies the *trusted certificate chain* used by the September-3 finite
extension of the unconditional window bank.

The existing finite bank (`RequestProject/Erdos287/FiniteRangeExtension.lean`) discharges
every primality side condition by `norm_num`, i.e. by trial division.  That is fine up to
roughly `10^9`, but the extension of the window chain past `4·10^9` needs primes of size
up to `3.4·10^16`, for which trial division is hopeless inside the kernel.

The replacement is a **recursive (Pratt) primality certificate**:

* a fuel-driven binary modular exponentiation `powMod`, which the kernel evaluates on
  numerals in `O(log e)` GMP-accelerated steps, together with its *proved* correctness
  statement `powMod_eq : powMod m f a e = a ^ e % m` (for `e < 2 ^ f`);
* the complete prime factorisation of `p - 1`, presented as an explicit list of
  `(prime, exponent)` pairs, each entry of which carries **its own** primality proof
  (recursively a Pratt certificate, or `norm_num` trial division at the leaves);
* a Lucas witness `a` with `a ^ (p-1) ≡ 1 (mod p)` and `a ^ ((p-1)/q) ≢ 1 (mod p)` for
  every prime `q ∣ p - 1`.

`prime_of_certificate` turns such data into `Nat.Prime p` through Mathlib's
`lucas_primality`.  Nothing here is an oracle: every numeric side condition is closed by
`decide`/`norm_num`, i.e. by kernel computation on numerals.  There is no
`native_decide`, no `axiom`, no `sorry`, no `implemented_by`, no `unsafe`.
-/

namespace Erdos287
namespace Pratt

/-- Fuel-driven binary modular exponentiation.  `powMod m f a e = a ^ e % m` whenever
`e < 2 ^ f` (`powMod_eq`).  The definition is structurally recursive in the fuel, so the
kernel reduces it on numerals in `f` steps, each step a GMP-accelerated `Nat` operation. -/
def powMod (m : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 1 % m
  | f + 1, a, e =>
      if e = 0 then 1 % m
      else
        let r := powMod m f (a * a % m) (e / 2)
        if e % 2 = 1 then r * a % m else r

/-- **Correctness of `powMod`.**  With enough fuel, `powMod` computes `a ^ e % m`. -/
theorem powMod_eq (m : ℕ) : ∀ (f a e : ℕ), e < 2 ^ f → powMod m f a e = a ^ e % m := by
  intro f
  induction f with
  | zero =>
      intro a e he
      simp at he
      subst he
      simp [powMod]
  | succ f ih =>
      intro a e he
      rw [powMod]
      by_cases h0 : e = 0
      · simp [h0]
      · simp only [h0, if_false]
        have hlt : e / 2 < 2 ^ f := by
          have : e < 2 ^ f * 2 := by rw [pow_succ] at he; exact he
          omega
        have hr := ih (a * a % m) (e / 2) hlt
        have hsq : (a * a % m) ^ (e / 2) % m = a ^ (2 * (e / 2)) % m := by
          rw [← Nat.pow_mod, show a * a = a ^ 2 by ring, ← pow_mul, mul_comm 2 (e / 2)]
        rw [hr, hsq]
        by_cases h1 : e % 2 = 1
        · simp only [h1, if_true]
          have hee : 2 * (e / 2) + 1 = e := by omega
          conv_rhs => rw [← hee]
          rw [pow_succ, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
        · simp only [h1, if_false]
          have : 2 * (e / 2) = e := by omega
          rw [this]

/-- `prodPow [(q₁,e₁), …] = q₁ ^ e₁ * ⋯`.  Kernel-computable on numerals. -/
def prodPow : List (ℕ × ℕ) → ℕ
  | [] => 1
  | x :: t => x.1 ^ x.2 * prodPow t

/-- Every base in the factorisation list is prime. -/
def AllPrimeFst : List (ℕ × ℕ) → Prop
  | [] => True
  | x :: t => Nat.Prime x.1 ∧ AllPrimeFst t

/-- The Lucas witness condition, one entry per prime factor of `p - 1`. -/
def AllWitness (p f a : ℕ) : List (ℕ × ℕ) → Prop
  | [] => True
  | x :: t => powMod p f a ((p - 1) / x.1) ≠ 1 ∧ AllWitness p f a t

theorem allPrimeFst_of_mem : ∀ {l : List (ℕ × ℕ)}, AllPrimeFst l → ∀ x ∈ l, Nat.Prime x.1
  | [], _, _, hx => absurd hx (List.not_mem_nil)
  | y :: t, h, x, hx => by
      rcases List.mem_cons.1 hx with rfl | hx'
      · exact h.1
      · exact allPrimeFst_of_mem h.2 x hx'

theorem allWitness_of_mem {p f a : ℕ} :
    ∀ {l : List (ℕ × ℕ)}, AllWitness p f a l → ∀ x ∈ l, powMod p f a ((p - 1) / x.1) ≠ 1
  | [], _, _, hx => absurd hx (List.not_mem_nil)
  | y :: t, h, x, hx => by
      rcases List.mem_cons.1 hx with rfl | hx'
      · exact h.1
      · exact allWitness_of_mem h.2 x hx'

/-- A prime dividing `prodPow l` occurs as one of the listed bases. -/
theorem exists_mem_of_prime_dvd :
    ∀ {l : List (ℕ × ℕ)}, AllPrimeFst l → ∀ {q : ℕ}, Nat.Prime q → q ∣ prodPow l →
      ∃ x ∈ l, x.1 = q
  | [], _, q, hq, hd => by
      rw [prodPow] at hd
      exact absurd (Nat.eq_one_of_dvd_one hd) hq.ne_one
  | y :: t, hl, q, hq, hd => by
      rw [prodPow] at hd
      rcases (Nat.Prime.dvd_mul hq).1 hd with h | h
      · exact ⟨y, List.mem_cons_self,
          ((Nat.prime_dvd_prime_iff_eq hq hl.1).1 (hq.dvd_of_dvd_pow h)).symm⟩
      · obtain ⟨x, hx, hx1⟩ := exists_mem_of_prime_dvd hl.2 hq h
        exact ⟨x, List.mem_cons_of_mem _ hx, hx1⟩

theorem natCast_pow_eq_one_iff {p a k : ℕ} (hp : 1 < p) :
    ((a : ZMod p) ^ k = 1) ↔ a ^ k % p = 1 := by
  constructor
  · intro h
    have : ((a ^ k : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by push_cast; simpa using h
    have := (ZMod.natCast_eq_natCast_iff _ _ _).1 this
    have h1 : (1 : ℕ) % p = 1 := Nat.mod_eq_of_lt hp
    simpa [Nat.ModEq, h1] using this
  · intro h
    have h1 : (1 : ℕ) % p = 1 := Nat.mod_eq_of_lt hp
    have : (a ^ k) ≡ 1 [MOD p] := by simp [Nat.ModEq, h, h1]
    have := (ZMod.natCast_eq_natCast_iff _ _ _).2 this
    push_cast at this
    simpa using this

/-- **Recursive (Pratt) primality certificate.**

`p` is prime as soon as one exhibits

* the full prime factorisation `l` of `p - 1` (`prodPow l = p - 1`, all bases prime),
* enough fuel `f` (`p - 1 < 2 ^ f`),
* a base `a` with `a ^ (p-1) ≡ 1 (mod p)` and `a ^ ((p-1)/q) ≢ 1 (mod p)` for every
  listed prime `q`.

All four conditions are decidable numeric facts, closed by kernel computation. -/
theorem prime_of_certificate {p a f : ℕ} {l : List (ℕ × ℕ)}
    (hp : 1 < p) (hf : p - 1 < 2 ^ f)
    (hl : AllPrimeFst l) (hprod : prodPow l = p - 1)
    (hpow : powMod p f a (p - 1) = 1)
    (hwit : AllWitness p f a l) : Nat.Prime p := by
  have hpow' : a ^ (p - 1) % p = 1 := by rw [← powMod_eq p f a (p - 1) hf]; exact hpow
  refine lucas_primality p (a : ZMod p) ((natCast_pow_eq_one_iff hp).2 hpow') ?_
  intro q hq hdvd hcon
  obtain ⟨x, hx, hx1⟩ := exists_mem_of_prime_dvd (l := l) hl hq (by rw [hprod]; exact hdvd)
  have hlt : (p - 1) / q < 2 ^ f := lt_of_le_of_lt (Nat.div_le_self _ _) hf
  have hne := allWitness_of_mem hwit x hx
  rw [hx1, powMod_eq p f a ((p - 1) / q) hlt] at hne
  exact hne ((natCast_pow_eq_one_iff hp).1 hcon)

end Pratt
end Erdos287
