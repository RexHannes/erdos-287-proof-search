import RequestProject.Chain
import RequestProject.Harmonic
import RequestProject.Proth
import RequestProject.Factorial

/-!
# Extending the finite range past the prime-pair chain

The certified chain of prime pairs of `RequestProject/Chain.lean` covers every maximum
`M ≤ CHAIN_CEILING`.  This file adds a *single* further blocker, which pushes the finite range up
to

`U2 = ⌊8 * (x + 1) / 3⌋`, where `x = 15 * Q`, `x + 1 = 16 * P`,

for the two Proth primes

`P = 15 * c * 2 ^ 100 + 1`, `Q = c * 2 ^ 104 + 1`, `c = 4609040761224086961713861467`.

Since `x + 1 < CHAIN_CEILING`, the new interval `(CHAIN_CEILING, U2]` overlaps the range already
covered, so the two results together cover `[2, U2]`.

The reason a *single* pair suffices so far above `x` is that the crude counting bound of
`WindowPairSupply` (`M ≤ 2 * x`) is replaced here by the harmonic bound of
`RequestProject/Harmonic.lean` (`3 * M ≤ 8 * (x + 1)`).
-/

namespace Erdos287

set_option maxRecDepth 100000

/-- The largest maximum covered by the certified prime-pair chain. -/
def CHAIN_CEILING : ℕ := 1516965997302524373612172717550681525506538629288954643349506

/-- The common coefficient of the two new Proth primes. -/
def bigC : ℕ := 4609040761224086961713861467

/-- The Proth prime `P = 15 * c * 2 ^ 100 + 1`. -/
def bigP : ℕ := 87639799311631337788152543462179066689689528722839704698881

/-- The Proth prime `Q = c * 2 ^ 104 + 1`. -/
def bigQ : ℕ := 93482452599073426974029379692991004469002163971029018345473

/-- The auxiliary number `t = 1 + 5 * c * 2 ^ 102`, which satisfies `3 * t + 1 = 4 * P` and
`4 * t + 1 = 5 * Q`. -/
def bigT : ℕ := 116853065748841783717536724616238755586252704963786272931841

/-- The blocker position `x = 15 * Q`; its successor is `x + 1 = 16 * P`. -/
def bigX : ℕ := 1402236788986101404610440695394865067035032459565435275182095

/-- The new ceiling `U2 = ⌊8 * (x + 1) / 3⌋`. -/
def U2 : ℕ := 3739298103962937078961175187719640178760086558841160733818922

/-! ### The arithmetic of the blocker -/

theorem bigC_odd : Odd bigC := by decide

theorem bigP_eq : bigP = 15 * bigC * 2 ^ 100 + 1 := by norm_num [bigP, bigC]

theorem bigQ_eq : bigQ = bigC * 2 ^ 104 + 1 := by norm_num [bigQ, bigC]

theorem bigT_eq : bigT = 1 + 5 * bigC * 2 ^ 102 := by norm_num [bigT, bigC]

theorem three_bigT_add_one : 3 * bigT + 1 = 4 * bigP := by norm_num [bigT, bigP]

theorem four_bigT_add_one : 4 * bigT + 1 = 5 * bigQ := by norm_num [bigT, bigQ]

theorem sixteen_bigP_sub_fifteen_bigQ : 16 * bigP = 15 * bigQ + 1 := by norm_num [bigP, bigQ]

theorem bigX_eq : bigX = 15 * bigQ := by norm_num [bigX, bigQ]

theorem bigX_succ_eq : bigX + 1 = 16 * bigP := by norm_num [bigX, bigP]

theorem U2_eq_floor : U2 = 8 * (bigX + 1) / 3 := by norm_num [U2, bigX]

/-- **The overlap.**  The new blocker sits strictly below the ceiling of the certified chain. -/
theorem bigX_succ_lt_chainCeiling : bigX + 1 < CHAIN_CEILING := by
  norm_num [bigX, CHAIN_CEILING]

/-! ### Primality -/

/-- `P` is prime, by Proth's criterion with the witness `11`; the modular power is evaluated by
the kernel. -/
theorem prime_bigP : Nat.Prime bigP := by
  rw [bigP_eq, bigC]
  exact prime_of_proth_half_pow_neg_one (k := 15 * 4609040761224086961713861467) (e := 100)
    (a := 11) (by norm_num) (by norm_num) (by norm_num) rfl (by norm_num) (by decide)

/-- `Q` is prime, by Proth's criterion with the witness `3`; the modular power is evaluated by
the kernel. -/
theorem prime_bigQ : Nat.Prime bigQ := by
  rw [bigQ_eq, bigC]
  exact prime_of_proth_half_pow_neg_one (k := 4609040761224086961713861467) (e := 104)
    (a := 3) (by norm_num) (by norm_num) (by norm_num) rfl (by norm_num) (by decide)

/-! ### The two forbidden prime powers -/

/-- For every `M ≤ U2` the multiplier window of `P` is at most `42`, and `42 * 42 ! < P`, so `P`
is a forbidden divisor at `M`. -/
theorem forbidden_bigP {M : ℕ} (hM : M ≤ U2) : ForbiddenPP M bigP 1 42 (Nat.factorial 42) := by
  refine forbiddenPP_of_factorial_bound prime_bigP one_pos (by norm_num) ?_ ?_
  · have hlt : U2 < (42 + 1) * bigP ^ 1 := by norm_num [U2, bigP]
    omega
  · show 42 * Nat.factorial 42 < bigP
    rw [bigP]
    decide

/-- For every `M ≤ U2` the multiplier window of `Q` is at most `40`, and `40 * 40 ! < Q`, so `Q`
is a forbidden divisor at `M`. -/
theorem forbidden_bigQ {M : ℕ} (hM : M ≤ U2) : ForbiddenPP M bigQ 1 40 (Nat.factorial 40) := by
  refine forbiddenPP_of_factorial_bound prime_bigQ one_pos (by norm_num) ?_ ?_
  · have hlt : U2 < (40 + 1) * bigQ ^ 1 := by norm_num [U2, bigQ]
    omega
  · show 40 * Nat.factorial 40 < bigQ
    rw [bigQ]
    decide

theorem bigQ_dvd_bigX : bigQ ^ 1 ∣ bigX := ⟨15, by rw [pow_one, bigX_eq]; ring⟩

theorem bigP_dvd_bigX_succ : bigP ^ 1 ∣ bigX + 1 := ⟨16, by rw [pow_one, bigX_succ_eq]; ring⟩

/-! ### The new interval -/

/--
**No counterexample has maximum in `(CHAIN_CEILING, U2]`.**

The two consecutive positions `x = 15 * Q` and `x + 1 = 16 * P` are both forbidden throughout
this range, and they lie below `CHAIN_CEILING < M`; the harmonic blocker then applies because
`3 * M ≤ 3 * U2 ≤ 8 * (x + 1)`.
-/
theorem no_counterexample_of_chainCeiling_lt_max_le_U2 {A : Finset ℕ}
    (h : Erdos287Counterexample A)
    (hlo : CHAIN_CEILING < A.max' h.nonempty)
    (hhi : A.max' h.nonempty ≤ U2) :
    False := by
  obtain ⟨hgt1, -, hsum, -⟩ := id h
  set M := A.max' h.nonempty with hMdef
  have hA0 : ∀ n ∈ A, 0 < n := fun n hn => lt_trans one_pos (hgt1 n hn)
  have hAM : ∀ n ∈ A, n ≤ M := fun n hn => Finset.le_max' _ n hn
  have hxA : bigX ∉ A := fun hmem =>
    (forbidden_bigQ hhi).not_dvd hA0 hAM hsum bigX hmem bigQ_dvd_bigX
  have hx1A : bigX + 1 ∉ A := fun hmem =>
    (forbidden_bigP hhi).not_dvd hA0 hAM hsum (bigX + 1) hmem bigP_dvd_bigX_succ
  refine not_counterexample_of_harmonic_forbidden_pair h hxA hx1A ?_ ?_
  · have := bigX_succ_lt_chainCeiling
    omega
  · have h8 : 3 * U2 ≤ 8 * (bigX + 1) := by norm_num [U2, bigX]
    omega

end Erdos287
