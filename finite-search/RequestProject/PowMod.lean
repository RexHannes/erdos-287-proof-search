import Mathlib

/-!
# Kernel-checkable primality certificates

We implement binary modular exponentiation with an explicit fuel parameter, so that it reduces
efficiently inside the Lean kernel, prove it correct, and package Lucas' primality criterion
(`lucas_primality`) into a certificate of "Proth shape" `N = c * 2 ^ t + 1` with `c` fully
factored.

Nothing here is axiomatic: every certificate is discharged by kernel evaluation of `Nat`
arithmetic together with `lucas_primality`.
-/

namespace Erdos287

/-- Binary modular exponentiation with fuel.  `powModAux n f a k acc` is `acc * a ^ k mod n`
provided `k < 2 ^ f`.  Written with structural recursion on the fuel so that it reduces in the
kernel. -/
def powModAux (n : ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, _, acc => acc
  | f + 1, a, k, acc =>
      if k = 0 then acc
      else powModAux n f (a * a % n) (k / 2) (if k % 2 = 1 then acc * a % n else acc)

/-- `powMod n a k` computes `a ^ k mod n` for `k < 2 ^ 256`. -/
def powMod (n a k : ℕ) : ℕ := powModAux n 256 a k 1

theorem powModAux_modEq (n : ℕ) :
    ∀ (f a k acc : ℕ), k < 2 ^ f → Nat.ModEq n (powModAux n f a k acc) (acc * a ^ k)
  | 0, a, k, acc, hk => by
      have hk' : k < 1 := by simpa using hk
      have hk0 : k = 0 := by omega
      subst hk0
      simp [powModAux, Nat.ModEq]
  | f + 1, a, k, acc, hk => by
      rw [powModAux]
      by_cases hk0 : k = 0
      · subst hk0; simp [Nat.ModEq]
      · rw [if_neg hk0]
        have hk2 : k / 2 < 2 ^ f := by
          have h2 : 2 ^ (f + 1) = 2 * 2 ^ f := by ring
          omega
        have ih := powModAux_modEq n f (a * a % n) (k / 2)
          (if k % 2 = 1 then acc * a % n else acc) hk2
        refine ih.trans ?_
        have ha : Nat.ModEq n (a * a % n) (a ^ 2) := by
          have := Nat.mod_modEq (a * a) n
          simpa [pow_two] using this
        have hpow : Nat.ModEq n ((a * a % n) ^ (k / 2)) ((a ^ 2) ^ (k / 2)) := ha.pow _
        have hacc : Nat.ModEq n (if k % 2 = 1 then acc * a % n else acc) (acc * a ^ (k % 2)) := by
          by_cases h1 : k % 2 = 1
          · rw [if_pos h1, h1, pow_one]
            exact Nat.mod_modEq _ _
          · rw [if_neg h1]
            have h0 : k % 2 = 0 := by omega
            rw [h0]
            simp [Nat.ModEq]
        have hmul := hacc.mul hpow
        have heq : acc * a ^ (k % 2) * (a ^ 2) ^ (k / 2) = acc * a ^ k := by
          rw [← pow_mul, mul_assoc, ← pow_add, Nat.mod_add_div]
        rw [heq] at hmul
        exact hmul

theorem powMod_modEq (n a k : ℕ) (hk : k < 2 ^ 256) : Nat.ModEq n (powMod n a k) (a ^ k) := by
  have := powModAux_modEq n 256 a k 1 hk
  simpa [powMod] using this

/-- If `powMod N a k` is congruent to `1`, then `a ^ k = 1` in `ZMod N`. -/
theorem zmod_pow_eq_one_of_powMod (N a k : ℕ) (hk : k < 2 ^ 256)
    (h : powMod N a k % N = 1 % N) : (a : ZMod N) ^ k = 1 := by
  have h1 : Nat.ModEq N (a ^ k) 1 := ((powMod_modEq N a k hk).symm).trans h
  have := (ZMod.natCast_eq_natCast_iff _ _ _).2 h1
  simpa using this

/-- If `powMod N a k` is not congruent to `1`, then `a ^ k ≠ 1` in `ZMod N`. -/
theorem zmod_pow_ne_one_of_powMod (N a k : ℕ) (hk : k < 2 ^ 256)
    (h : powMod N a k % N ≠ 1 % N) : (a : ZMod N) ^ k ≠ 1 := by
  intro hcon
  apply h
  have h1 : ((a ^ k : ℕ) : ZMod N) = ((1 : ℕ) : ZMod N) := by push_cast; simpa using hcon
  have h2 : Nat.ModEq N (a ^ k) 1 := (ZMod.natCast_eq_natCast_iff _ _ _).1 h1
  exact ((powMod_modEq N a k hk).trans h2)

/-- The Boolean certificate check for a Proth-shaped number `N = c * 2 ^ t + 1` with witness `a`
and the list `ps` of prime factors of `c` (with multiplicity). -/
def certOK (c t a : ℕ) (ps : List ℕ) : Bool :=
  let N := c * 2 ^ t + 1
  (c == ps.prod) &&
  (powMod N a (N - 1) % N == 1 % N) &&
  (powMod N a ((N - 1) / 2) % N != 1 % N) &&
  ps.all (fun p => powMod N a ((N - 1) / p) % N != 1 % N)

/--
**Certified primality.**  If `c = ∏ ps` with every entry of `ps` prime, `t ≥ 1`, `c ≥ 1`,
`c * 2 ^ t < 2 ^ 256`, and the Boolean certificate check succeeds, then `c * 2 ^ t + 1` is prime.
-/
theorem prime_of_cert {c t a : ℕ} {ps : List ℕ} (hps : ∀ p ∈ ps, Nat.Prime p)
    (hsize : c * 2 ^ t < 2 ^ 256)
    (h : certOK c t a ps = true) :
    Nat.Prime (c * 2 ^ t + 1) := by
  set N := c * 2 ^ t + 1 with hNdef
  have hNsub : N - 1 = c * 2 ^ t := by omega
  simp only [certOK, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq,
    List.all_eq_true] at h
  obtain ⟨⟨⟨hprod, h1⟩, h2⟩, h3⟩ := h
  have hbound : ∀ k : ℕ, k ≤ N - 1 → k < 2 ^ 256 := by
    intro k hk
    omega
  refine lucas_primality N (a : ZMod N) ?_ ?_
  · exact zmod_pow_eq_one_of_powMod N a (N - 1) (hbound _ le_rfl) h1
  · intro q hq hqd
    have hqcase : q = 2 ∨ q ∈ ps := by
      rw [hNsub] at hqd
      rcases (Nat.Prime.dvd_mul hq).1 hqd with hd | hd
      · right
        rw [hprod] at hd
        obtain ⟨r, hr, hqr⟩ := (Prime.dvd_prod_iff (Nat.prime_iff.1 hq)).1 hd
        have := (Nat.prime_dvd_prime_iff_eq hq (hps r hr)).1 hqr
        exact this ▸ hr
      · left
        exact (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 (hq.dvd_of_dvd_pow hd)
    have hdivle : (N - 1) / q ≤ N - 1 := Nat.div_le_self _ _
    rcases hqcase with rfl | hmem
    · exact zmod_pow_ne_one_of_powMod N a _ (hbound _ hdivle) h2
    · have := h3 q hmem
      exact zmod_pow_ne_one_of_powMod N a _ (hbound _ hdivle) this

/-- Convenience form of `prime_of_cert` stating primality of an explicit numeral `N`. -/
theorem prime_of_cert' {N c t a : ℕ} {ps : List ℕ} (hps : ∀ p ∈ ps, Nat.Prime p)
    (hsize : c * 2 ^ t < 2 ^ 256) (hN : N = c * 2 ^ t + 1) (h : certOK c t a ps = true) :
    Nat.Prime N := hN ▸ prime_of_cert hps hsize h

end Erdos287
