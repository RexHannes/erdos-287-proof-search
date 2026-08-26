import RequestProject.Erdos287.Blocker

/-!
# Erdős Problem #287 — the Ceiling–CRT Pairing package and Large-Ceiling reduction

For a gap-`≤2` counterexample `A` with endpoints `N, M` and a prime `p`, let
`eₚ = maxₐ vₚ(a)` (the top `p`-adic exponent) and set the **ceiling modulus**
`qₚ = p^(eₚ + 1)`.  Since `eₚ` is the maximal `p`-adic valuation, no element of `A`
is divisible by `qₚ`; every multiple of `qₚ` in the window `[N, M]` is a *hole*.

The main results:

* `Gap2CE.ceilingMultiples_are_holes` — any multiple of `qₚ` in `[N, M]` is not in `A`.
* `Gap2CE.HoleForcing` — the abstract property "every multiple of `Q` in `[N,M]` is a hole".
* `exists_crt_adjacent` — the CRT interval-residue lemma.
* `Gap2CE.coprimeHoleModuli_CRT_pair` — two coprime positive hole-forcing moduli
  `Q₁, Q₂` with `Q₁·Q₂ ≤ M - N` produce two adjacent holes, hence a contradiction.
* `Gap2CE.ceilingCRT_pairing` — for distinct primes `p, r`, `qₚ·q_r > M - N`.
* `Gap2CE.atMostOne_small_ceiling` — at most one prime `p` has `qₚ² ≤ M - N`.
* `Gap2CE.AP_prime_kills_minCeil` — for `M ≥ 8152`, no prime `ℓ ∈ [N+1, M-1]` is
  `≡ 1 (mod Q)` where `Q = minₚ qₚ`.
* `Gap2CE.LargeCeilingReduction` — the packaged reduction.

No claim that #287 is solved; only the elementary CRT-pairing structure is certified.
-/

open scoped BigOperators

namespace Erdos287

namespace Gap2CE

variable (ce : Gap2CE)

/-- The **ceiling modulus** `qₚ = p^(eₚ + 1)`, where `eₚ = maxₐ vₚ(a)` is the top
`p`-adic exponent over `A`. -/
def ceilMod (p : ℕ) : ℕ := p ^ (topExp ce.A p + 1)

/-- The ceiling modulus is positive for a prime base. -/
theorem one_le_ceilMod {p : ℕ} (hp : p.Prime) : 1 ≤ ce.ceilMod p := by
  exact Nat.one_le_pow _ _ hp.pos

/-- **Ceiling multiples are holes (Target 1).** If `p` is prime, `x ∈ [N, M]`, and
`qₚ ∣ x`, then `x ∉ A`.

(The hypothesis `x ∈ [N, M]` is requested by the problem statement so that `x` is
literally a hole *in the window*; the divisibility alone already forces `x ∉ A`.) -/
theorem ceilingMultiples_are_holes {p x : ℕ} (hp : p.Prime)
    (hx : x ∈ Finset.Icc ce.N ce.M) (hdvd : ce.ceilMod p ∣ x) : x ∉ ce.A := by
  contrapose! hdvd;
  unfold ceilMod;
  rw [ Nat.Prime.pow_dvd_iff_le_factorization ] <;> norm_num;
  · exact Finset.le_sup ( f := fun a => Nat.factorization a p ) hdvd;
  · assumption;
  · linarith [ Finset.mem_Icc.mp hx, ce.hpos x hdvd ]

/-! ## Abstract hole-forcing moduli -/

/-- `Q` is **hole-forcing** if every multiple of `Q` inside the window `[N, M]`
is absent from `A`. -/
def HoleForcing (Q : ℕ) : Prop :=
  ∀ x, x ∈ Finset.Icc ce.N ce.M → Q ∣ x → x ∉ ce.A

/-- Each ceiling modulus of a prime is hole-forcing (immediate from
`ceilingMultiples_are_holes`). -/
theorem holeForcing_ceilMod {p : ℕ} (hp : p.Prime) : ce.HoleForcing (ce.ceilMod p) :=
  fun x hx hdvd => ce.ceilingMultiples_are_holes hp hx hdvd

end Gap2CE

/-- **CRT interval-residue lemma.** Given coprime `Q₁, Q₂ ≥ 1` with `Q₁·Q₂ ≤ M - N`,
there is an `x` with `N ≤ x`, `x + 1 ≤ M`, `Q₁ ∣ x`, and `Q₂ ∣ (x+1)`.

(Any interval of length at least `Q₁·Q₂` contains a representative of the CRT residue
class `x ≡ 0 (mod Q₁)`, `x ≡ -1 (mod Q₂)`.) -/
theorem exists_crt_adjacent {N M Q1 Q2 : ℕ} (hcop : Nat.Coprime Q1 Q2)
    (h1 : 1 ≤ Q1) (h2 : 1 ≤ Q2) (hle : Q1 * Q2 ≤ M - N) :
    ∃ x, N ≤ x ∧ x + 1 ≤ M ∧ Q1 ∣ x ∧ Q2 ∣ (x + 1) := by
  -- By the Chinese Remainder Theorem, there exists an integer $k$ such that $k \equiv 0 \pmod{Q1}$ and $k \equiv -1 \pmod{Q2}$.
  obtain ⟨k, hk⟩ : ∃ k : ℕ, k ≡ 0 [MOD Q1] ∧ k ≡ -1 [ZMOD Q2] := by
    have := Nat.chineseRemainder hcop 0 ( Q2 - 1 ) ; simp_all +decide [ ← Int.natCast_modEq_iff ] ;
    exact ⟨ this.1, Int.natCast_modEq_iff.mpr this.2.1, Int.ModEq.trans ( Int.natCast_modEq_iff.mpr this.2.2 ) ( Int.modEq_iff_dvd.mpr ⟨ -1, by rw [ Int.ofNat_sub h2 ] ; ring ⟩ ) ⟩;
  refine' ⟨ N + ( ( k % ( Q1 * Q2 ) + Q1 * Q2 - N % ( Q1 * Q2 ) ) % ( Q1 * Q2 ) ), _, _, _, _ ⟩;
  · exact Nat.le_add_right _ _;
  · have := Nat.mod_lt ( k % ( Q1 * Q2 ) + Q1 * Q2 - N % ( Q1 * Q2 ) ) ( by positivity : 0 < Q1 * Q2 );
    omega;
  · rw [ Nat.dvd_iff_mod_eq_zero ];
    simp_all +decide [ ← ZMod.val_natCast, Nat.ModEq ];
    rw [ Nat.cast_sub ] <;> norm_num [ hk ];
    · cases Q1 <;> cases Q2 <;> aesop;
    · exact le_add_of_nonneg_of_le ( Nat.zero_le _ ) ( Nat.le_of_lt ( Nat.mod_lt _ ( by positivity ) ) );
  · rw [ ← Int.natCast_dvd_natCast ] ; simp_all +decide [ ← ZMod.intCast_zmod_eq_zero_iff_dvd, ← ZMod.intCast_eq_intCast_iff ] ;
    rw [ Nat.cast_sub ] <;> norm_num [ Int.add_emod, Int.sub_emod, Int.mul_emod, hk.2 ];
    · simp_all +decide [ ← ZMod.intCast_eq_intCast_iff', Int.emod_def ];
    · exact le_add_of_nonneg_of_le ( Nat.zero_le _ ) ( Nat.le_of_lt ( Nat.mod_lt _ ( by positivity ) ) )

namespace Gap2CE

variable (ce : Gap2CE)

/-
**Coprime hole-forcing pairing (Target 2).** If `Q₁, Q₂` are coprime positive
hole-forcing moduli with `Q₁·Q₂ ≤ M - N`, then no gap-`≤2` counterexample exists.
-/
theorem coprimeHoleModuli_CRT_pair {Q1 Q2 : ℕ}
    (hcop : Nat.Coprime Q1 Q2) (h1 : 1 ≤ Q1) (h2 : 1 ≤ Q2)
    (hf1 : ce.HoleForcing Q1) (hf2 : ce.HoleForcing Q2)
    (hle : Q1 * Q2 ≤ ce.M - ce.N) : False := by
  obtain ⟨x, hx⟩ := exists_crt_adjacent hcop h1 h2 hle;
  exact ce.blockerPair_contradiction hx.1 hx.2.1 ( hf1 x ( Finset.mem_Icc.mpr ⟨ hx.1, by linarith ⟩ ) hx.2.2.1 ) ( hf2 ( x + 1 ) ( Finset.mem_Icc.mpr ⟨ by linarith, by linarith ⟩ ) hx.2.2.2 )

/-- Alias of `coprimeHoleModuli_CRT_pair`. -/
theorem coprime_holeForcing_contradiction {Q1 Q2 : ℕ}
    (hcop : Nat.Coprime Q1 Q2) (h1 : 1 ≤ Q1) (h2 : 1 ≤ Q2)
    (hf1 : ce.HoleForcing Q1) (hf2 : ce.HoleForcing Q2)
    (hle : Q1 * Q2 ≤ ce.M - ce.N) : False :=
  ce.coprimeHoleModuli_CRT_pair hcop h1 h2 hf1 hf2 hle

/-- Two distinct primes' ceiling moduli are coprime. -/
theorem coprime_ceilMod {p r : ℕ} (hp : p.Prime) (hr : r.Prime) (hpr : p ≠ r) :
    Nat.Coprime (ce.ceilMod p) (ce.ceilMod r) :=
  Nat.Coprime.pow _ _ ((Nat.coprime_primes hp hr).mpr hpr)

/-- **Ceiling–CRT contradiction.** For distinct primes `p, r`, `qₚ·q_r ≤ M - N`
is impossible. -/
theorem ceilingCRT_contradiction {p r : ℕ} (hp : p.Prime) (hr : r.Prime) (hpr : p ≠ r)
    (hle : ce.ceilMod p * ce.ceilMod r ≤ ce.M - ce.N) : False :=
  ce.coprimeHoleModuli_CRT_pair (ce.coprime_ceilMod hp hr hpr)
    (ce.one_le_ceilMod hp) (ce.one_le_ceilMod hr)
    (ce.holeForcing_ceilMod hp) (ce.holeForcing_ceilMod hr) hle

/-- **Ceiling–CRT pairing (Target 3).** For distinct primes `p, r`, `qₚ·q_r > M - N`. -/
theorem ceilingCRT_pairing {p r : ℕ} (hp : p.Prime) (hr : r.Prime) (hpr : p ≠ r) :
    ce.M - ce.N < ce.ceilMod p * ce.ceilMod r := by
  by_contra h
  exact ce.ceilingCRT_contradiction hp hr hpr (not_lt.mp h)

/-- Alias of `ceilingCRT_pairing`. -/
theorem ceilMod_mul_gt {p r : ℕ} (hp : p.Prime) (hr : r.Prime) (hpr : p ≠ r) :
    ce.M - ce.N < ce.ceilMod p * ce.ceilMod r :=
  ce.ceilingCRT_pairing hp hr hpr

/-! ## Corollaries (Target 4) -/

/-
**At most one small ceiling modulus (Target 4, Nat form).** For distinct primes
`p, r`, the ceiling moduli cannot both satisfy `qₚ² ≤ M - N`.
-/
theorem atMostOne_small_ceiling {p r : ℕ} (hp : p.Prime) (hr : r.Prime) (hpr : p ≠ r) :
    ¬ (ce.ceilMod p ^ 2 ≤ ce.M - ce.N ∧ ce.ceilMod r ^ 2 ≤ ce.M - ce.N) := by
  intro h
  have h_prod : (ce.ceilMod p * ce.ceilMod r)^2 ≤ (ce.M - ce.N)^2 := by
    nlinarith;
  exact absurd h_prod ( by nlinarith only [ show 0 < ce.ceilMod p * ce.ceilMod r from mul_pos ( pow_pos hp.pos _ ) ( pow_pos hr.pos _ ), show ce.M - ce.N < ce.ceilMod p * ce.ceilMod r from ceilingCRT_pairing ce hp hr hpr ] )

/-
**At most one small ceiling modulus (√ form).** For distinct primes `p, r`, the
ceiling moduli cannot both be `≤ √(M - N)`.
-/
theorem at_most_one_ceilMod_le_sqrt {p r : ℕ} (hp : p.Prime) (hr : r.Prime)
    (hpr : p ≠ r) :
    ¬ (ce.ceilMod p ≤ Nat.sqrt (ce.M - ce.N) ∧ ce.ceilMod r ≤ Nat.sqrt (ce.M - ce.N)) := by
  intro h
  have h1 : (ce.ceilMod p ^ 2 ≤ ce.M - ce.N) := by
    exact le_trans ( Nat.pow_le_pow_left h.1 2 ) ( Nat.sqrt_le' _ )
  have h2 : (ce.ceilMod r ^ 2 ≤ ce.M - ce.N) := by
    exact le_trans ( Nat.pow_le_pow_left h.2 2 ) ( Nat.sqrt_le' _ )
  exact atMostOne_small_ceiling ce hp hr hpr ⟨h1, h2⟩

/-- **`q₂·q₃ > M - N`.** -/
theorem ceilMod_two_three_gt :
    ce.M - ce.N < ce.ceilMod 2 * ce.ceilMod 3 :=
  ce.ceilingCRT_pairing Nat.prime_two Nat.prime_three (by norm_num)

/-
**`max(q₂, q₃) > √(M - N)`.**
-/
theorem max_ceilMod_two_three_gt_sqrt :
    Nat.sqrt (ce.M - ce.N) < max (ce.ceilMod 2) (ce.ceilMod 3) := by
  have := @at_most_one_ceilMod_le_sqrt ce 2 3 Nat.prime_two Nat.prime_three ( by norm_num );
  grind +extAll

/-! ## The minimal ceiling modulus and the AP-prime reduction (Targets 5–6) -/

/-- `Q` is a ceiling modulus of some prime. -/
def isCeilModOfPrime (Q : ℕ) : Prop := ∃ p : ℕ, p.Prime ∧ Q = ce.ceilMod p

/-- The **minimal ceiling modulus** `Q = minₚ qₚ`. -/
noncomputable def minCeil : ℕ := sInf {Q | ce.isCeilModOfPrime Q}

/-
The minimal ceiling modulus is itself a ceiling modulus of some prime.
-/
theorem minCeil_isCeilMod : ce.isCeilModOfPrime ce.minCeil := by
  convert Nat.sInf_mem ?_;
  exact ⟨ _, ⟨ 2, Nat.prime_two, rfl ⟩ ⟩

/-
The minimal ceiling modulus is hole-forcing.
-/
theorem minCeil_holeForcing : ce.HoleForcing ce.minCeil := by
  -- By definition of minCeil, obtain the prime p such that minCeil = ceilMod p.
  obtain ⟨p, hp_prime, hp_ceil⟩ : ∃ p : ℕ, p.Prime ∧ ce.minCeil = ce.ceilMod p := by
    convert ce.minCeil_isCeilMod using 1;
  exact hp_ceil ▸ ce.holeForcing_ceilMod hp_prime

/-
**AP-prime kills a hole-forcing modulus (core).** If `M ≥ 8152`, `Q` is
hole-forcing, and `ℓ` is a prime in `[N+1, M-1]` with `Q ∣ ℓ - 1`, then no gap-`≤2`
counterexample exists: `ℓ` is a hole (prime, so not a denominator) and `ℓ-1` is a
`Q`-multiple hole, giving two adjacent holes.
-/
theorem AP_prime_kills_holeForcing {Q ℓ : ℕ} (hM : 8152 ≤ ce.M)
    (hf : ce.HoleForcing Q) (hℓ : ℓ.Prime)
    (hlo : ce.N + 1 ≤ ℓ) (hhi : ℓ ≤ ce.M - 1) (hdvd : Q ∣ (ℓ - 1)) : False := by
  contrapose! hf;
  intro h; have := h ( ℓ - 1 ) ?_ hdvd <;> rcases ℓ with ( _ | _ | ℓ ) <;> simp_all +arith +decide;
  · grind +suggestions;
  · omega

/-- **AP-prime kills a ceiling modulus.** Specialization of `AP_prime_kills_holeForcing`
to `Q = qₚ`. -/
theorem AP_prime_kills_ceiling {p ℓ : ℕ} (hp : p.Prime) (hM : 8152 ≤ ce.M)
    (hℓ : ℓ.Prime) (hlo : ce.N + 1 ≤ ℓ) (hhi : ℓ ≤ ce.M - 1)
    (hdvd : ce.ceilMod p ∣ (ℓ - 1)) : False :=
  ce.AP_prime_kills_holeForcing hM (ce.holeForcing_ceilMod hp) hℓ hlo hhi hdvd

/-
**AP-prime kills the minimal ceiling (Target 5).** If `M ≥ 8152` and there is a
prime `ℓ ∈ [N+1, M-1]` with `ℓ ≡ 1 (mod Q)` for `Q = minₚ qₚ`, contradiction.
-/
theorem AP_prime_kills_minCeil {ℓ : ℕ} (hM : 8152 ≤ ce.M)
    (hℓ : ℓ.Prime) (hlo : ce.N + 1 ≤ ℓ) (hhi : ℓ ≤ ce.M - 1)
    (hcong : ℓ ≡ 1 [MOD ce.minCeil]) : False := by
  convert ce.AP_prime_kills_holeForcing hM _ _ _ _ _;
  exact ce.minCeil;
  exact ℓ;
  · grind +suggestions;
  · assumption;
  · linarith;
  · grind;
  · rw [ ← Nat.modEq_zero_iff_dvd ];
    cases ℓ <;> simp_all +decide [ ← ZMod.natCast_eq_natCast_iff ]

/-- **The analytic AP-prime hypothesis.** `APPrimeInInterval Q N M` asserts the
existence of a prime `ℓ ∈ [N+1, M-1]` with `ℓ ≡ 1 (mod Q)`.  This is *stated*, not
proved; it is the arithmetic-progression input the reduction consumes. -/
def APPrimeInInterval (Q N M : ℕ) : Prop :=
  ∃ ℓ : ℕ, ℓ.Prime ∧ N + 1 ≤ ℓ ∧ ℓ ≤ M - 1 ∧ ℓ ≡ 1 [MOD Q]

/-- **Large-Ceiling reduction (Target 6).** Any gap-`≤2` counterexample with
`M ≥ 8152` satisfies both structural conclusions:
* `qₚ·q_r > M - N` for all distinct primes `p, r`;
* no prime `ℓ ∈ [N+1, M-1]` is `≡ 1 (mod Q)` for `Q = minₚ qₚ`. -/
theorem LargeCeilingReduction (hM : 8152 ≤ ce.M) :
    (∀ p r : ℕ, p.Prime → r.Prime → p ≠ r →
      ce.M - ce.N < ce.ceilMod p * ce.ceilMod r) ∧
    (∀ ℓ : ℕ, ℓ.Prime → ce.N + 1 ≤ ℓ → ℓ ≤ ce.M - 1 → ¬ (ℓ ≡ 1 [MOD ce.minCeil])) := by
  refine ⟨fun p r hp hr hpr => ce.ceilingCRT_pairing hp hr hpr, ?_⟩
  intro ℓ hℓ hlo hhi hcong
  exact ce.AP_prime_kills_minCeil hM hℓ hlo hhi hcong

/-- **The AP-prime hypothesis refutes a large counterexample (Target 6, optional).**
If the analytic input `APPrimeInInterval Q N M` holds for `Q = minₚ qₚ`, then no
gap-`≤2` counterexample with `M ≥ 8152` exists. -/
theorem no_Gap2CE_of_APPrime (hM : 8152 ≤ ce.M)
    (h : APPrimeInInterval ce.minCeil ce.N ce.M) : False := by
  obtain ⟨ℓ, hℓ, hlo, hhi, hcong⟩ := h
  exact ce.AP_prime_kills_minCeil hM hℓ hlo hhi hcong

end Gap2CE

end Erdos287