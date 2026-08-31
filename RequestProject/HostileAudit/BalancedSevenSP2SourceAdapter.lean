import Mathlib
import RequestProject.Erdos287.SP2PrimeBoxWeights3221
import RequestProject.Erdos287.FixedCertificateOrderCounterguard
import RequestProject.CurrentProgramme.SevenBoxPrimeWeights

/-!
# Hostile-audit safe bank §2 — the SP-2 → seven-box **source seal**

The independent hostile audit of the Balanced7 analysis warned that the analytic argument
took *as given* both

* the literal SP-2 fixed-certificate source `H_*`, and
* the seven-box source law `ω_i(p) = 1_{p prime} · V_i(p/Y) · phase_i(p)`.

This module banks the exact finite/source algebra of that adapter, so that the two objects
are related by theorems rather than by assertion.

## What is proved here

* `truncMobius_of_primeProduct` — the *literal* repository weight
  `H_*(n) = ∑_{d ∣ n, d ≤ T} μ(d)` (`Erdos287.SmoothParity.truncMobius`) evaluated at a
  product of distinct primes equals the subset-lattice alternating sum, whenever the
  truncation cuts the divisor lattice at a fixed number `r` of prime factors;
* `subsetAlternatingSum_eq_binomial` — that subset sum in binomial form;
* `truncMobius_sevenBox_eq_neg20` — the mandated finite identity
  `H_*(P) = 1 − 7 + 21 − 35 = −20` for `P = p₁⋯p₇` at divisor depth `r = 3`;
* `boxWeight`, the seven-box source law with an *arbitrary* unimodular phase, its pointwise
  law `‖ω_i(p)‖ ≤ 1` and its prime support, and `boxWeight_eq_omegaBox`, the proof that the
  repository's literal archimedean weight `omegaBox` is the special case
  `phase_i(p) = p^{it}`.

## What is **not** proved here

The identification of the *physical* Balanced7 analytic packet with the SP-2 packet requires
the `cell_identity` obligation of the fixed smooth-parity certificate, which this repository
does **not** discharge (`Erdos287.SmoothParity.FixedCertificateSmoothParityPacket` is an
uninhabited source interface).  Accordingly:

```
BALANCED7-SP2-SOURCE-ADAPTER45 : SOURCE_OPEN
```

and Balanced7 is **not** recorded as source-sealed.  What the seal below does buy is
*rigidity*: any two analytic packets satisfying it are pointwise equal, and every finite
consequence used downstream (`−20`, `‖ω‖ ≤ 1`, prime support) is a theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open ArithmeticFunction

namespace Erdos287
namespace HostileAudit

open Erdos287.SmoothParity
open Erdos287.SP2Source
open Erdos287.Counterguard
open Erdos287.PostBalanced7Pro

/-! ## §2.1  Products of distinct primes -/

/-- **`squarefree_prod_of_primes`.**  `LEAN_PROVED`.

A product of *distinct* primes is squarefree.  (The finset carries the distinctness.) -/
theorem squarefree_prod_of_primes (s : Finset ℕ) (h : ∀ p ∈ s, p.Prime) :
    Squarefree (∏ p ∈ s, p) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      have hp : a.Prime := h a (Finset.mem_insert_self a s)
      have hs : Squarefree (∏ p ∈ s, p) := ih fun p hp => h p (Finset.mem_insert_of_mem hp)
      refine Nat.squarefree_mul_iff.2 ⟨?_, hp.squarefree, hs⟩
      refine (Nat.Prime.coprime_iff_not_dvd hp).2 ?_
      intro hdvd
      obtain ⟨q, hq, hdq⟩ := (Nat.Prime.prime hp).exists_mem_finset_dvd hdvd
      have hqp : q.Prime := h q (Finset.mem_insert_of_mem hq)
      have haq : a = q := (Nat.prime_dvd_prime_iff_eq hp hqp).1 hdq
      exact ha (haq ▸ hq)

/-- **`cardFactors_eq_card_primeFactors`.**  `LEAN_PROVED`.

For squarefree `d`, `Ω(d) = ω(d)`. -/
theorem cardFactors_eq_card_primeFactors {d : ℕ} (h : Squarefree d) :
    ArithmeticFunction.cardFactors d = d.primeFactors.card := by
  have h0 : d ≠ 0 := h.ne_zero
  have hEq := (ArithmeticFunction.cardDistinctFactors_eq_cardFactors_iff_squarefree h0).2 h
  rw [← hEq, ArithmeticFunction.cardDistinctFactors_apply, Nat.primeFactors]
  rfl

/-! ## §2.2  The literal fixed-certificate weight at a product of distinct primes -/

/-- **`truncMobius_of_primeProduct`.**  `LEAN_PROVED`.

The *literal* repository weight `truncMobius n T = ∑_{d ∣ n, d ≤ T} μ(d)` evaluated at
`n = ∏_{p ∈ S} p` (distinct primes) equals the subset-lattice alternating sum, provided the
truncation `T` cuts the lattice exactly at divisor depth `r`, i.e. a sub-product of the
primes is `≤ T` precisely when it uses at most `r` of them.

This is the exact bridge between the fixed-certificate source and the balanced-cell
combinatorial model of `Erdos287.Counterguard`. -/
theorem truncMobius_of_primeProduct {S : Finset ℕ} {T r : ℕ}
    (hprime : ∀ p ∈ S, p.Prime)
    (hcut : ∀ t ⊆ S, ((∏ p ∈ t, p) ≤ T ↔ t.card ≤ r)) :
    truncMobius (∏ p ∈ S, p) T
      = ∑ t ∈ S.powerset.filter (fun t => t.card ≤ r), (-1 : ℤ) ^ t.card := by
  classical
  have hP : Squarefree (∏ p ∈ S, p) := squarefree_prod_of_primes S hprime
  have hP0 : (∏ p ∈ S, p) ≠ 0 := hP.ne_zero
  rw [truncMobius]
  refine Finset.sum_nbij' (fun d : ℕ => d.primeFactors) (fun t : Finset ℕ => ∏ p ∈ t, p)
    ?_ ?_ ?_ ?_ ?_
  · intro d hd
    simp only [Finset.mem_filter, Nat.mem_divisors] at hd
    obtain ⟨⟨hdvd, _⟩, hle⟩ := hd
    have hdsq : Squarefree d := hP.squarefree_of_dvd hdvd
    have hsub : d.primeFactors ⊆ S := by
      have hmono := Nat.primeFactors_mono hdvd hP0
      rwa [Nat.primeFactors_prod hprime] at hmono
    have hprod : ∏ p ∈ d.primeFactors, p = d := Nat.prod_primeFactors_of_squarefree hdsq
    simp only [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨hsub, (hcut _ hsub).1 (by rw [hprod]; exact hle)⟩
  · intro t ht
    simp only [Finset.mem_filter, Finset.mem_powerset] at ht
    simp only [Finset.mem_filter, Nat.mem_divisors]
    exact ⟨⟨Finset.prod_dvd_prod_of_subset _ _ _ ht.1, hP0⟩, (hcut t ht.1).2 ht.2⟩
  · intro d hd
    simp only [Finset.mem_filter, Nat.mem_divisors] at hd
    exact Nat.prod_primeFactors_of_squarefree (hP.squarefree_of_dvd hd.1.1)
  · intro t ht
    simp only [Finset.mem_filter, Finset.mem_powerset] at ht
    exact Nat.primeFactors_prod fun p hp => hprime p (ht.1 hp)
  · intro d hd
    simp only [Finset.mem_filter, Nat.mem_divisors] at hd
    have hdsq : Squarefree d := hP.squarefree_of_dvd hd.1.1
    rw [moebius_apply_of_squarefree hdsq, cardFactors_eq_card_primeFactors hdsq]

/-- **`subsetAlternatingSum_eq_binomial`.**  `LEAN_PROVED`.

The subset-lattice alternating sum in binomial form. -/
theorem subsetAlternatingSum_eq_binomial (S : Finset ℕ) (r : ℕ) :
    ∑ t ∈ S.powerset.filter (fun t => t.card ≤ r), (-1 : ℤ) ^ t.card
      = ∑ j ∈ Finset.range (r + 1), (-1 : ℤ) ^ j * (S.card.choose j) := by
  classical
  have hEq : S.powerset.filter (fun t => t.card ≤ r)
      = (Finset.range (r + 1)).biUnion fun j => Finset.powersetCard j S := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_biUnion, Finset.mem_range,
      Finset.mem_powersetCard, Nat.lt_succ_iff]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨t.card, h2, h1, rfl⟩
    · rintro ⟨a, ha, h1, rfl⟩
      exact ⟨h1, ha⟩
  rw [hEq, Finset.sum_biUnion]
  · refine Finset.sum_congr rfl ?_
    intro j _
    rw [Finset.sum_powersetCard j S fun c => (-1 : ℤ) ^ c]
    simp [mul_comm]
  · intro i _ j _ hij
    simp only [Finset.disjoint_left]
    intro t ht ht'
    rw [Finset.mem_powersetCard] at ht ht'
    exact hij (ht.2 ▸ ht'.2 ▸ rfl)

/-- **`truncMobius_sevenBox_eq_neg20`.**  `LEAN_PROVED`.

The mandated finite identity of the source seal.  For `P = p₁⋯p₇` a product of seven
distinct primes, with the truncation cutting the divisor lattice at depth `r = 3`,

```
H_*(P) = 1 − 7 + 21 − 35 = −20.
```
-/
theorem truncMobius_sevenBox_eq_neg20 {S : Finset ℕ} {T : ℕ}
    (hprime : ∀ p ∈ S, p.Prime) (hcard : S.card = 7)
    (hcut : ∀ t ⊆ S, ((∏ p ∈ t, p) ≤ T ↔ t.card ≤ 3)) :
    truncMobius (∏ p ∈ S, p) T = -20 := by
  rw [truncMobius_of_primeProduct hprime hcut, subsetAlternatingSum_eq_binomial, hcard]
  decide +kernel

/-- **`truncMobius_sevenBox_matches_counterguard`.**  `LEAN_PROVED`.

The literal value agrees with the banked balanced-cell weight of `Erdos287.Counterguard`
at `k = 7`, `r = (7−1)/2 = 3`. -/
theorem truncMobius_sevenBox_matches_counterguard {S : Finset ℕ} {T : ℕ}
    (hprime : ∀ p ∈ S, p.Prime) (hcard : S.card = 7)
    (hcut : ∀ t ⊆ S, ((∏ p ∈ t, p) ≤ T ↔ t.card ≤ 3)) :
    truncMobius (∏ p ∈ S, p) T = balancedCellWeight 7 (halfCut 7) := by
  rw [truncMobius_sevenBox_eq_neg20 hprime hcard hcut, counterguard_k7]

/-- **`sevenBox_alternating_expansion`.**  `LEAN_PROVED`.

The explicit expansion `1 − 7 + 21 − 35 = −20` of the depth-`3` coefficient. -/
theorem sevenBox_alternating_expansion :
    (1 : ℤ) - 7 + 21 - 35 = -20 ∧
      ∑ j ∈ Finset.range 4, (-1 : ℤ) ^ j * (Nat.choose 7 j : ℤ) = -20 := by
  refine ⟨by norm_num, ?_⟩
  decide +kernel

/-! ## §2.3  The seven-box source law with a general unimodular phase -/

/-- **`boxWeight`** — the seven-box source law

```
ω_i(p) = 1_{p prime} · V_i(p/Y) · phase_i(p).
```

The phase is an *arbitrary* function; unimodularity is a hypothesis of the seal, not part of
the definition, so nothing is smuggled in. -/
noncomputable def boxWeight (V : ℝ → ℝ) (phase : ℕ → ℂ) (Y : ℝ) (p : ℕ) : ℂ :=
  if p.Prime then (V ((p : ℝ) / Y) : ℂ) * phase p else 0

/-- **`boxWeight_eq_omegaBox`.**  `LEAN_PROVED`.

The repository's literal archimedean weight `omegaBox V Y t` is the special case of the
general source law with the unimodular phase `phase(p) = p^{i t} = exp(i t log p)`. -/
theorem boxWeight_eq_omegaBox (V : ℝ → ℝ) (Y t : ℝ) (p : ℕ) :
    boxWeight V (fun p => Complex.exp (t * Real.log p * Complex.I)) Y p = omegaBox V Y t p := by
  unfold boxWeight omegaBox
  split <;> rfl

/-- **`boxWeight_eq_zero_of_not_prime`.**  `LEAN_PROVED`. -/
theorem boxWeight_eq_zero_of_not_prime {V : ℝ → ℝ} {phase : ℕ → ℂ} {Y : ℝ} {p : ℕ}
    (hp : ¬ p.Prime) : boxWeight V phase Y p = 0 := by
  simp [boxWeight, hp]

/-- **`boxWeight_support_is_primes`.**  `LEAN_PROVED`. -/
theorem boxWeight_support_is_primes {V : ℝ → ℝ} {phase : ℕ → ℂ} {Y : ℝ} {p : ℕ}
    (h : boxWeight V phase Y p ≠ 0) : p.Prime := by
  by_contra hp
  exact h (boxWeight_eq_zero_of_not_prime hp)

/-- **`norm_boxWeight_le_one`.**  `LEAN_PROVED`.

`|phase| = 1` and `0 ≤ V ≤ 1` give the pointwise law `‖ω_i(p)‖ ≤ 1` as a *theorem*. -/
theorem norm_boxWeight_le_one {V : ℝ → ℝ} {phase : ℕ → ℂ} {Y : ℝ}
    (hV : ∀ x : ℝ, 0 ≤ V x ∧ V x ≤ 1) (hph : ∀ p : ℕ, ‖phase p‖ = 1) (p : ℕ) :
    ‖boxWeight V phase Y p‖ ≤ 1 := by
  unfold boxWeight
  by_cases hp : p.Prime
  · simp only [hp, if_true, norm_mul, Complex.norm_real, Real.norm_eq_abs, hph p, mul_one]
    rw [abs_of_nonneg (hV _).1]
    exact (hV _).2
  · simp [hp]

/-! ## §2.4  The source seal (SOURCE_OPEN) -/

/-- **`BalancedSevenSP2SourceSeal`** — `SOURCE_OPEN / UNINHABITED`.

The literal adapter demanded by the hostile audit: the analytic Balanced7 packet consumed by
the compiler *is* the SP-2 packet.

Fields:

* the SP-2 fixed-certificate metadata (`k = 0`, `J = ∅`, `Ω = 7`, depth `3`, unit sign,
  prime-supported cell);
* the fixed-certificate **cell identity** `H_*(n) = ∑_{d ∣ n, d ≤ cut n} μ(d)` on the
  sector — this is the repository's own uninhabited source obligation;
* the smooth profile normalisation `0 ≤ V_i ≤ 1`;
* the unimodularity `|phase_i(p)| = 1`;
* the slot-by-slot identification of the analytic source with the seven-box law.

No inhabitant exists in this repository. -/
structure BalancedSevenSP2SourceSeal
    (C : SP2FixedCertificateData) (sector : Finset ℕ) (Hs : ℕ → ℤ) (cut : ℕ → ℕ)
    (V : Fin 7 → ℝ → ℝ) (phase : Fin 7 → ℕ → ℂ) (Y : ℝ) (omegaSrc : Fin 7 → ℕ → ℂ) : Prop where
  /-- SP-2 packet metadata. -/
  packet : SP2PacketNormalization C
  /-- The fixed-certificate cell identity (the missing source obligation). -/
  cell_identity : ∀ n ∈ sector, Hs n = truncMobius n (cut n)
  /-- The smooth profiles are normalised. -/
  profile_bounds : ∀ (i : Fin 7) (x : ℝ), 0 ≤ V i x ∧ V i x ≤ 1
  /-- The phases are unimodular. -/
  phase_unimodular : ∀ (i : Fin 7) (p : ℕ), ‖phase i p‖ = 1
  /-- The analytic source really is the seven-box law. -/
  source_form : ∀ (i : Fin 7) (p : ℕ), omegaSrc i p = boxWeight (V i) (phase i) Y p

variable {C : SP2FixedCertificateData} {sector : Finset ℕ} {Hs : ℕ → ℤ} {cut : ℕ → ℕ}
  {V : Fin 7 → ℝ → ℝ} {phase : Fin 7 → ℕ → ℂ} {Y : ℝ} {omegaSrc : Fin 7 → ℕ → ℂ}

/-- **`seal_pointwise_law`.**  `CONDITIONAL / LEAN_PROVED`. -/
theorem seal_pointwise_law
    (h : BalancedSevenSP2SourceSeal C sector Hs cut V phase Y omegaSrc)
    (i : Fin 7) (p : ℕ) : ‖omegaSrc i p‖ ≤ 1 := by
  rw [h.source_form i p]
  exact norm_boxWeight_le_one (h.profile_bounds i) (h.phase_unimodular i) p

/-- **`seal_prime_support`.**  `CONDITIONAL / LEAN_PROVED`. -/
theorem seal_prime_support
    (h : BalancedSevenSP2SourceSeal C sector Hs cut V phase Y omegaSrc)
    {i : Fin 7} {p : ℕ} (hne : omegaSrc i p ≠ 0) : p.Prime := by
  rw [h.source_form i p] at hne
  exact boxWeight_support_is_primes hne

/-- **`seal_certificate_value_neg20`.**  `CONDITIONAL / LEAN_PROVED`.

Under the seal, the *literal* certificate weight of a seven-prime product in the sector is
exactly `−20`, provided the truncation cuts at depth `3`. -/
theorem seal_certificate_value_neg20
    (h : BalancedSevenSP2SourceSeal C sector Hs cut V phase Y omegaSrc)
    {S : Finset ℕ} (hprime : ∀ p ∈ S, p.Prime) (hcard : S.card = 7)
    (hmem : (∏ p ∈ S, p) ∈ sector)
    (hcut : ∀ t ⊆ S, ((∏ p ∈ t, p) ≤ cut (∏ p ∈ S, p) ↔ t.card ≤ 3)) :
    Hs (∏ p ∈ S, p) = -20 := by
  rw [h.cell_identity _ hmem]
  exact truncMobius_sevenBox_eq_neg20 hprime hcard hcut

/-- **`seal_rigidity`.**  `LEAN_PROVED`.

The seal pins the analytic packet: two sources sealed to the same profiles, phases and scale
are pointwise equal.  So the seal is a genuine identification, not a "model with the same
dimensions". -/
theorem seal_rigidity {omegaSrc' : Fin 7 → ℕ → ℂ}
    (h : BalancedSevenSP2SourceSeal C sector Hs cut V phase Y omegaSrc)
    (h' : BalancedSevenSP2SourceSeal C sector Hs cut V phase Y omegaSrc') :
    ∀ (i : Fin 7) (p : ℕ), omegaSrc i p = omegaSrc' i p := by
  intro i p
  rw [h.source_form i p, h'.source_form i p]

/-- **`sp2SourceSeal_not_automatic`.**  `LEAN_PROVED`.

The seal is a genuine restriction, refuted by explicit data: with the seven-box slots taken
to be the constant `2` the pointwise law already fails.  Consequently

```
BALANCED7-SP2-SOURCE-ADAPTER45 : SOURCE_OPEN
```

and Balanced7 is **not** source-sealed in this repository. -/
theorem sp2SourceSeal_not_automatic :
    ∃ (C : SP2FixedCertificateData) (sector : Finset ℕ) (Hs : ℕ → ℤ) (cut : ℕ → ℕ)
      (V : Fin 7 → ℝ → ℝ) (phase : Fin 7 → ℕ → ℂ) (Y : ℝ) (omegaSrc : Fin 7 → ℕ → ℂ),
      ¬ BalancedSevenSP2SourceSeal C sector Hs cut V phase Y omegaSrc := by
  refine ⟨⟨0, ∅, 7, 3, 1, fun _ => {2}⟩, ∅, fun _ => 0, fun _ => 0, fun _ _ => 0,
    fun _ _ => 1, 1, fun _ _ => 2, ?_⟩
  intro h
  have h1 := seal_pointwise_law h 0 2
  simp only [Complex.norm_ofNat] at h1
  norm_num at h1

end HostileAudit
end Erdos287
