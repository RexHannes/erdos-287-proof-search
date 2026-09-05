import Mathlib

/-!
# Erdős #287 — September-4 signed-floor bank, §4: the interior `B_src` local Möbius collapse

```
LOCAL PRIME-FACTOR IDENTITY                        : KERNEL-PROVED
MULTIPLICATIVITY OVER q.primeFactors               : KERNEL-PROVED
DIVISOR-SUM COLLAPSE (interiorLocalMobiusCollapse45): KERNEL-PROVED
Σ = S₂^{ω(q)}·μ(q)  IN THIS ABSTRACT MODEL          : KERNEL-PROVED, **NOT PHYSICAL**
BOUNDARY / TRUNCATED FIBRE                         : NOT ASSERTED (firewall below)
```

## P0 NORMALISATION NOTICE (September 4 repair)

Everything in this module is a theorem about the **abstract, artificially locally
normalised** model in which the source weight is a pure local product
`Bsrc Bloc d = ∏_{p ∣ d} Bloc p` and the constant `S₂` is inserted into *each* local factor
through the hypothesis `bloc p − Bloc p = −S₂`.  Multiplying that hypothesis over
`q.primeFactors` necessarily produces `S₂^{ω(q)}`.  **This is not the physical source
normalisation**, which carries one global `S₂`:

    B0(d) = ∏_{p ∣ d} (p−1)/(p−2),   B_src(d) = S₂ · B0(d),   β(d) = ∏_{p ∣ d} 1/(p−2).

Under the physical normalisation the correct identity for **odd squarefree** `q` is

    ∑_{d ∣ q} μ(d) B_src(d) β(q/d) = S₂ · μ(q),

proved as `Erdos287.SourceWeights.physicalBsrcMobiusCollapse45` in
`RequestProject/Erdos287/SourceWeights.lean`.  The theorems below remain true and are kept
(they are what `interiorLocalMobiusCollapse45` is used for downstream), but **no physical
claim of the form `S₂^{ω(q)}·μ(q)` is made anywhere**: the `S₂^{ω(q)}` statements below are
statements about the abstract local model only, and the counterexample in §4.5 refutes the
over-general *abstract* form, not the physical identity.

This module is **append-only**.  It is finite multiplicative algebra over
`Finset ℕ`: there is no infinite Euler product, no analytic continuation and no estimate.

## The objects

For a *local factor datum* `Bloc, bloc : ℕ → ℚ` (values at primes) put, on squarefree
moduli,

    B_src(d) = ∏_{p ∣ d} Bloc p,        β(k) = ∏_{p ∣ k} bloc p.

`S₂` is the **global constant** of the source: it enters only through the *local
normalisation* hypothesis

    bloc p − Bloc p = −S₂        for every `p ∣ q`,

which is the exact local-factor statement the interior collapse consumes.

## Firewall

`interiorLocalMobiusCollapse45` applies **only** when the physical selector is constant over
the *complete* divisor-assignment fibre — in the formalisation, when the sum runs over the
full divisor set `q.divisors` (equivalently the full cube `q.primeFactors.powerset`).  It
asserts nothing about a truncated or boundary fibre; those are the business of §5.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open scoped ArithmeticFunction.omega
open Finset ArithmeticFunction

namespace Erdos287
namespace September4BsrcCollapse

/-! ## §4.1  The finite source objects -/

/-- The project version of `B_src` on squarefree moduli: the product of the local factors
`Bloc p` over the prime factors. -/
def Bsrc (Bloc : ℕ → ℚ) (d : ℕ) : ℚ := ∏ p ∈ d.primeFactors, Bloc p

/-- The project version of `β` on squarefree moduli. -/
def beta (bloc : ℕ → ℚ) (k : ℕ) : ℚ := ∏ p ∈ k.primeFactors, bloc p

/-- The **complete divisor cube** of `q`: the powerset of its prime factors.  A divisor
assignment is *complete/interior* exactly when it ranges over this whole cube. -/
def divisorCube (q : ℕ) : Finset (Finset ℕ) := q.primeFactors.powerset

@[simp] theorem Bsrc_one (Bloc : ℕ → ℚ) : Bsrc Bloc 1 = 1 := by simp [Bsrc]

@[simp] theorem beta_one (bloc : ℕ → ℚ) : beta bloc 1 = 1 := by simp [beta]

/-- `B_src` evaluated at a squarefree product of primes is the product of the local
factors. -/
theorem Bsrc_prod (Bloc : ℕ → ℚ) {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) :
    Bsrc Bloc (∏ p ∈ s, p) = ∏ p ∈ s, Bloc p := by
  rw [Bsrc, Nat.primeFactors_prod hs]

/-- `β` evaluated at a squarefree product of primes is the product of the local factors. -/
theorem beta_prod (bloc : ℕ → ℚ) {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) :
    beta bloc (∏ p ∈ s, p) = ∏ p ∈ s, bloc p := by
  rw [beta, Nat.primeFactors_prod hs]

/-! ## §4.2  The local prime-factor identity -/

/-- **`localFactorIdentity`.**  `KERNEL-PROVED`.  The single-prime (local) Möbius collapse:
at one prime the divisor cube has the two points `d = 1` and `d = p`, and

    β(p) + μ(p)·B_src(p)·β(1) = bloc p − Bloc p. -/
theorem localFactorIdentity (Bloc bloc : ℕ → ℚ) {p : ℕ} (hp : p.Prime) :
    beta bloc p + (moebius p : ℚ) * Bsrc Bloc p * beta bloc 1 = bloc p - Bloc p := by
  have hbeta : beta bloc p = bloc p := by
    rw [beta, Nat.Prime.primeFactors hp, Finset.prod_singleton]
  have hB : Bsrc Bloc p = Bloc p := by
    rw [Bsrc, Nat.Prime.primeFactors hp, Finset.prod_singleton]
  rw [hbeta, hB, beta_one, ArithmeticFunction.moebius_apply_prime hp]
  push_cast
  ring

/-! ## §4.3  The cube form and the divisor form -/

/-- **`moebius_prod_primes`.**  `KERNEL-PROVED`.  The Möbius value of a squarefree product of
distinct primes is the parity sign of the number of factors. -/
theorem moebius_prod_primes {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) :
    (moebius (∏ p ∈ s, p) : ℤ) = (-1) ^ s.card := by
  have hpair : (↑s : Set ℕ).Pairwise (Function.onFun Nat.Coprime (fun p : ℕ => p)) := by
    intro a ha b hb hab
    exact (Nat.coprime_primes (hs a ha) (hs b hb)).2 hab
  rw [ArithmeticFunction.IsMultiplicative.map_prod (fun p : ℕ => p)
      ArithmeticFunction.isMultiplicative_moebius s hpair,
    Finset.prod_congr rfl (fun p hp => ArithmeticFunction.moebius_apply_prime (hs p hp))]
  simp

/-- **`cubeLocalMobiusCollapse`.**  `KERNEL-PROVED`.  The complete-cube form of the collapse:
summing over the *whole* divisor cube of a squarefree `q` multiplies the local factors. -/
theorem cubeLocalMobiusCollapse (Bloc bloc : ℕ → ℚ) {q : ℕ} (hq : Squarefree q) :
    ∑ s ∈ divisorCube q,
        (moebius (∏ p ∈ s, p) : ℚ) * Bsrc Bloc (∏ p ∈ s, p) * beta bloc (q / ∏ p ∈ s, p)
      = ∏ p ∈ q.primeFactors, (bloc p - Bloc p) := by
  classical
  simp only [divisorCube, Bsrc, beta]
  rw [Finset.prod_congr rfl (fun p _ => (by ring : bloc p - Bloc p = (- Bloc p) + bloc p)),
    Finset.prod_add]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hsub : s ⊆ q.primeFactors := Finset.mem_powerset.1 hs
  have hprime : ∀ p ∈ s, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors (hsub hp)
  have hprimeC : ∀ p ∈ q.primeFactors \ s, p.Prime := fun p hp =>
    Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.1 hp).1
  have hpf : (∏ p ∈ s, p).primeFactors = s := Nat.primeFactors_prod hprime
  have hne : (∏ p ∈ s, p) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.2 fun p hp => ?_
    exact (hprime p hp).pos.ne'
  have hsplit : q = (∏ p ∈ q.primeFactors \ s, p) * (∏ p ∈ s, p) := by
    rw [Finset.prod_sdiff hsub, Nat.prod_primeFactors_of_squarefree hq]
  have hq' : q / ∏ p ∈ s, p = ∏ p ∈ q.primeFactors \ s, p :=
    Nat.div_eq_of_eq_mul_left (Nat.pos_of_ne_zero hne) hsplit
  rw [hpf, hq', Nat.primeFactors_prod hprimeC, moebius_prod_primes hprime, Finset.prod_neg]
  push_cast
  ring

/-- **`interiorLocalMobiusCollapse45`.**  `KERNEL-PROVED`.  The divisor-sum form:

    ∑_{d ∣ q} μ(d) · B_src(d) · β(q/d) = ∏_{p ∣ q} (β_loc p − B_loc p)

for squarefree `q`.  The sum is over the **complete** divisor set. -/
theorem interiorLocalMobiusCollapse45 (Bloc bloc : ℕ → ℚ) {q : ℕ} (hq : Squarefree q) :
    ∑ d ∈ q.divisors, (moebius d : ℚ) * Bsrc Bloc d * beta bloc (q / d)
      = ∏ p ∈ q.primeFactors, (bloc p - Bloc p) := by
  classical
  rw [← cubeLocalMobiusCollapse Bloc bloc hq]
  refine Finset.sum_nbij' (fun d => d.primeFactors) (fun s => ∏ p ∈ s, p) ?_ ?_ ?_ ?_ ?_
  · intro d hd
    obtain ⟨hdvd, hq0⟩ := Nat.mem_divisors.1 hd
    exact Finset.mem_powerset.2 (Nat.primeFactors_mono hdvd hq0)
  · intro s hs
    have hsub : s ⊆ q.primeFactors := Finset.mem_powerset.1 hs
    refine Nat.mem_divisors.2 ⟨⟨∏ p ∈ q.primeFactors \ s, p, ?_⟩, hq.ne_zero⟩
    rw [mul_comm, Finset.prod_sdiff hsub, Nat.prod_primeFactors_of_squarefree hq]
  · intro d hd
    obtain ⟨hdvd, -⟩ := Nat.mem_divisors.1 hd
    exact Nat.prod_primeFactors_of_squarefree (hq.squarefree_of_dvd hdvd)
  · intro s hs
    exact Nat.primeFactors_prod
      (fun p hp => Nat.prime_of_mem_primeFactors (Finset.mem_powerset.1 hs hp))
  · intro d hd
    obtain ⟨hdvd, -⟩ := Nat.mem_divisors.1 hd
    rw [Nat.prod_primeFactors_of_squarefree (hq.squarefree_of_dvd hdvd)]

/-! ## §4.4  The **abstract** locally-normalised form (NOT the physical normalisation) -/

/-- **`interiorCollapse_normalized`.**  `KERNEL-PROVED`.  Under the exact local
normalisation `bloc p − Bloc p = −S₂` at every prime of `q`, the interior collapse evaluates
to

    ∑_{d ∣ q} μ(d) B_src(d) β(q/d) = S₂^{ω(q)} · μ(q).

**Abstract model only.**  The exponent `ω(q)` is an artefact of inserting the global `S₂`
into every local factor; see the P0 normalisation notice at the top of this file and the
physical identity `Erdos287.SourceWeights.physicalBsrcMobiusCollapse45`. -/
theorem interiorCollapse_normalized (Bloc bloc : ℕ → ℚ) {q : ℕ} (S2 : ℚ) (hq : Squarefree q)
    (hnorm : ∀ p ∈ q.primeFactors, bloc p - Bloc p = -S2) :
    ∑ d ∈ q.divisors, (moebius d : ℚ) * Bsrc Bloc d * beta bloc (q / d)
      = S2 ^ (ω q) * (moebius q : ℚ) := by
  classical
  have homega : ω q = q.primeFactors.card := by
    rw [ArithmeticFunction.cardDistinctFactors_apply]; rfl
  have hmu : (moebius q : ℚ) = (-1) ^ q.primeFactors.card := by
    have hprime : ∀ p ∈ q.primeFactors, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
    have := moebius_prod_primes hprime
    rw [Nat.prod_primeFactors_of_squarefree hq] at this
    exact_mod_cast congrArg (fun z : ℤ => (z : ℚ)) this
  rw [interiorLocalMobiusCollapse45 Bloc bloc hq, Finset.prod_congr rfl hnorm,
    Finset.prod_const, homega, hmu]
  rw [neg_pow]
  ring

/-- **`interiorCollapse_S2_mu`.**  `KERNEL-PROVED`.  The literally requested form

    ∑_{d ∣ q} μ(d) B_src(d) β(q/d) = S₂ · μ(q)

holds exactly under the extra explicit hypothesis `S₂^{ω(q)} = S₂` — in particular for a
single-prime fibre `ω(q) = 1`, and for the normalisation `S₂ = 1`. -/
theorem interiorCollapse_S2_mu (Bloc bloc : ℕ → ℚ) {q : ℕ} (S2 : ℚ) (hq : Squarefree q)
    (hnorm : ∀ p ∈ q.primeFactors, bloc p - Bloc p = -S2) (hpow : S2 ^ (ω q) = S2) :
    ∑ d ∈ q.divisors, (moebius d : ℚ) * Bsrc Bloc d * beta bloc (q / d)
      = S2 * (moebius q : ℚ) := by
  rw [interiorCollapse_normalized Bloc bloc S2 hq hnorm, hpow]

/-- The one-prime case of the requested form, with no side condition. -/
theorem interiorCollapse_S2_mu_of_prime (Bloc bloc : ℕ → ℚ) {q : ℕ} (S2 : ℚ)
    (hq : Squarefree q) (hprime : q.Prime)
    (hnorm : ∀ p ∈ q.primeFactors, bloc p - Bloc p = -S2) :
    ∑ d ∈ q.divisors, (moebius d : ℚ) * Bsrc Bloc d * beta bloc (q / d)
      = S2 * (moebius q : ℚ) := by
  refine interiorCollapse_S2_mu Bloc bloc S2 hq hnorm ?_
  rw [ArithmeticFunction.cardDistinctFactors_apply_prime hprime, pow_one]

/-! ## §4.5  The over-general **abstract** form fails for `ω(q) ≥ 2`

This is a counterexample to the *abstract* local-normalisation hypothesis
`bloc p − Bloc p = −S₂` at every prime, **not** to the physical identity.  The witness uses
artificial local values (`Bloc ≡ 0`, `bloc ≡ −2`) which are not the physical
`(p−1)/(p−2)`, `1/(p−2)`.  For the physical weights the `q = 15` value is `S₂`, exactly as
`Erdos287.SourceWeights.regression_q15_physical` shows. -/

/-- **`abstractLocalNormalisation_S2_mu_form_fails`.**  `KERNEL-PROVED` *counterexample to the
over-general abstract model*.  With `S₂ = 2`, artificial local data `Bloc ≡ 0`, `bloc ≡ −2`
and the odd squarefree modulus `q = 15`, the abstract normalisation `bloc p − Bloc p = −S₂`
holds at both primes, yet the divisor sum equals `S₂² μ(q) = 4`, not `S₂ μ(q) = 2`.  Hence
the *abstract* model only supports the form `S₂^{ω(q)} μ(q)`.  The **physical** source, with
one global `S₂`, does satisfy `Σ = S₂·μ(q)`. -/
theorem abstractLocalNormalisation_S2_mu_form_fails :
    ∃ (Bloc bloc : ℕ → ℚ) (q : ℕ) (S2 : ℚ), Squarefree q ∧ Odd q ∧
      (∀ p ∈ q.primeFactors, bloc p - Bloc p = -S2) ∧
      ∑ d ∈ q.divisors, (moebius d : ℚ) * Bsrc Bloc d * beta bloc (q / d)
        ≠ S2 * (moebius q : ℚ) := by
  classical
  have hq : Squarefree (15 : ℕ) := by
    have h35 : (15 : ℕ) = 3 * 5 := by norm_num
    rw [h35]
    exact (Nat.squarefree_mul (by norm_num)).2
      ⟨Nat.prime_three.squarefree, (by norm_num : Nat.Prime 5).squarefree⟩
  refine ⟨fun _ => 0, fun _ => -2, 15, 2, hq, ⟨7, by norm_num⟩, ?_, ?_⟩
  · intro p _; norm_num
  · have hval := interiorCollapse_normalized (fun _ => (0 : ℚ)) (fun _ => (-2 : ℚ)) (q := 15) 2 hq
      (by intro p _; norm_num)
    have homega : ω (15 : ℕ) = 2 := by simp [ArithmeticFunction.cardDistinctFactors_apply]
    have hmu : (moebius 15 : ℚ) = 1 := by
      rw [ArithmeticFunction.moebius_apply_of_squarefree hq]
      simp [ArithmeticFunction.cardFactors_apply]
    rw [hval, homega, hmu]
    norm_num

end September4BsrcCollapse
end Erdos287
