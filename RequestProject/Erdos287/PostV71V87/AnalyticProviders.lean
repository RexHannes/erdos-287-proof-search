import RequestProject.Erdos287.PostV71V87.Positional

/-!
# Erdős #287 — V84/V85 analytic prime-supply providers and conditional deductions

**Search record.**  The project, Mathlib (`Mathlib.NumberTheory.Bertrand`,
`Mathlib.NumberTheory.LSeries.PrimesInAP`, `Mathlib.NumberTheory.Chebyshev`) and the
vendored packages were searched.  Mathlib contains Bertrand's postulate and Dirichlet's
theorem (`Nat.forall_exists_prime_gt_and_eq_mod`: infinitely many primes in a class), but
**no** prime number theorem in arithmetic progressions, hence no theorem giving a prime
`ℓ ≡ 1 (mod q)` in a dyadic interval `(X/2, X)`.  No vendored formal PNT library is present.
Only the modulus-one case matches exactly; it is proved from Bertrand
(`dyadic_supply_modulus_one`).  All other inputs are explicit `Prop` providers, which are
**never inhabited** in this development:

* `FixedModulusDyadicSupply` — pointwise in the modulus (PNT in APs, fixed `q`);
* `UniformDyadicSupply f` — uniform over all moduli `q ≤ f(X)` (Siegel–Walfisz-type
  uniformity for `f = (log X)^A`; stronger for faster `f`).

Analytic uniformity and effectivity are **not** hidden in any definition: the threshold
`X0` is existential and the uniformity range `f` is an explicit parameter.

Conditional deductions:

* `fixed_modulus_saturation`, `fixed_base_primary_growth`, `qstar_tendsto_of_fixed` —
  from the pointwise provider: for every fixed `K`, all sufficiently large exact words have
  no absent modulus in `[2, K]` (so `Q_p > K` and `q_* > K`);
* `uniform_modulus_saturation`, `growing_base_primary_growth`, `qstar_gt_of_uniform`,
  `maximal_carrier_of_uniform` — from the uniform provider: every absent modulus exceeds
  `f(M)`, hence `Q_p > f(M)` for all (growing) primes `p` and `p·P_p > f(M)`.

The unconditional engine is `absent_modulus_excluded_by_prime`.
-/

open scoped BigOperators

namespace Erdos287.PostV71V87

/-- **(Provider, pointwise.)**  For every modulus `q ≥ 1` there is a threshold `X0(q)` such
that every `X ≥ X0(q)` admits a prime `ℓ ≡ 1 (mod q)` with `X < 2ℓ` and `ℓ < X`.
A consequence of the prime number theorem in arithmetic progressions; not in Mathlib. -/
def FixedModulusDyadicSupply : Prop :=
  ∀ q : ℕ, 1 ≤ q → ∃ X0 : ℕ, ∀ X : ℕ, X0 ≤ X →
    ∃ ℓ : ℕ, ℓ.Prime ∧ X < 2 * ℓ ∧ ℓ < X ∧ ℓ ≡ 1 [MOD q]

/-- **(Provider, uniform.)**  A single threshold `X0` such that for all `X ≥ X0` and every
modulus `1 ≤ q ≤ f(X)` there is a prime `ℓ ≡ 1 (mod q)` with `X < 2ℓ`, `ℓ < X`. -/
def UniformDyadicSupply (f : ℕ → ℕ) : Prop :=
  ∃ X0 : ℕ, ∀ X : ℕ, X0 ≤ X → ∀ q : ℕ, 1 ≤ q → q ≤ f X →
    ∃ ℓ : ℕ, ℓ.Prime ∧ X < 2 * ℓ ∧ ℓ < X ∧ ℓ ≡ 1 [MOD q]

/-- The only exactly matching imported theorem: modulus one, from Bertrand's postulate. -/
theorem dyadic_supply_modulus_one :
    ∀ X : ℕ, 4 ≤ X → ∃ ℓ : ℕ, ℓ.Prime ∧ X < 2 * ℓ ∧ ℓ < X ∧ ℓ ≡ 1 [MOD 1] := by
  intro X hX
  obtain ⟨p, hp, h1, h2⟩ := Nat.exists_prime_lt_and_le_two_mul (X / 2) (by omega)
  refine ⟨p, hp, by omega, ?_, Nat.modEq_one⟩
  rcases Nat.even_or_odd X with ⟨k, hk⟩ | ⟨k, hk⟩
  · -- `X = 2k`; `p ≤ 2k`, and `p = 2k` is impossible since `2k` is even and `> 2`
    have hk' : X / 2 = k := by omega
    rw [hk'] at h1 h2
    rcases lt_or_eq_of_le h2 with h | h
    · omega
    · exfalso
      have : 2 ∣ p := ⟨k, by omega⟩
      have := (Nat.Prime.eq_one_or_self_of_dvd hp 2 this)
      omega
  · have hk' : X / 2 = k := by omega
    rw [hk'] at h2
    omega

/-- The left endpoint of an exact word equals the minimum of the counterexample. -/
theorem ExactWord.gap2_N_eq (W : ExactWord) (ha : 1 < W.a) :
    (W.toCounterexample ha).toGap2CE.N = W.a := by
  show W.A.min' _ = W.a
  refine le_antisymm (Finset.min'_le _ _ W.a_mem) (Finset.le_min' _ _ _ ?_)
  intro y hy; exact (W.mem_Icc hy).1

theorem ExactWord.gap2_M_eq (W : ExactWord) (ha : 1 < W.a) :
    (W.toCounterexample ha).toGap2CE.M = W.M := by
  show W.A.max' _ = W.M
  refine le_antisymm (Finset.max'_le _ _ _ ?_) (Finset.le_max' _ _ W.M_mem)
  intro y hy; exact (W.mem_Icc hy).2

/-- **Size bound.**  An exact word with `a > 1` and `M ≥ 16` has `2a + 2 ≤ M`
(from the project's `e·(N − 1) < M`). -/
theorem ExactWord.two_mul_a_add_two_le (W : ExactWord) (ha : 1 < W.a) (hM : 16 ≤ W.M) :
    2 * W.a + 2 ≤ W.M := by
  have h := (W.toCounterexample ha).toGap2CE.exp_lower
  rw [W.gap2_N_eq ha, W.gap2_M_eq ha] at h
  have he := Real.exp_one_gt_d9
  have hM' : (16 : ℝ) ≤ W.M := by exact_mod_cast hM
  have ha' : (1 : ℝ) < W.a := by exact_mod_cast ha
  have : (2 : ℝ) * W.a + 2 ≤ W.M := by nlinarith
  exact_mod_cast this

/-- **Unconditional engine.**  In an exact word with `a > 1`, `M ≥ 16`, an absent modulus
`d` admits no prime `ℓ ≡ 1 (mod d)` with `M < 2ℓ` and `ℓ < M`: `ℓ - 1` would be a forced
omission whose right neighbour `ℓ` is forced, but `ℓ` has a singleton row. -/
theorem ExactWord.absent_modulus_excluded_by_prime (W : ExactWord) (ha : 1 < W.a)
    (hM : 16 ≤ W.M) {d ℓ : ℕ} (hd : W.Absent d) (hℓ : ℓ.Prime) (h1 : W.M < 2 * ℓ)
    (h2 : ℓ < W.M) (hmod : ℓ ≡ 1 [MOD d]) : False := by
  have hs := W.two_mul_a_add_two_le ha hM
  have hℓ1 : 1 ≤ ℓ := hℓ.one_lt.le
  have hdvd : d ∣ ℓ - 1 := (Nat.modEq_iff_dvd' hℓ1).1 hmod.symm
  exact W.positional_chain hd hdvd ⟨by omega, by omega⟩ hℓ h1 (Or.inr (by omega))

/-- **Fixed-modulus saturation (conditional on `FixedModulusDyadicSupply`).**  For every
fixed `K` there is `M0` such that every exact word with `a > 1`, `M ≥ M0` has no absent
modulus in `[2, K]`. -/
theorem fixed_modulus_saturation (hsup : FixedModulusDyadicSupply) (K : ℕ) :
    ∃ M0 : ℕ, ∀ W : ExactWord, 1 < W.a → M0 ≤ W.M →
      ∀ d, 2 ≤ d → d ≤ K → ¬ W.Absent d := by
  classical
  let g : ℕ → ℕ := fun d => if h : 1 ≤ d then Classical.choose (hsup d h) else 0
  refine ⟨max 16 ((Finset.Icc 1 K).sup g + 1), ?_⟩
  intro W ha hM d hd hdK habs
  have hd1 : 1 ≤ d := by omega
  have hgd : g d = Classical.choose (hsup d hd1) := by simp [g, hd1]
  have hle : g d ≤ (Finset.Icc 1 K).sup g :=
    Finset.le_sup (f := g) (Finset.mem_Icc.2 ⟨hd1, hdK⟩)
  have hX : Classical.choose (hsup d hd1) ≤ W.M := by
    rw [← hgd]; have := le_max_right 16 ((Finset.Icc 1 K).sup g + 1); omega
  obtain ⟨ℓ, hℓ, h1, h2, hmod⟩ := Classical.choose_spec (hsup d hd1) W.M hX
  exact W.absent_modulus_excluded_by_prime ha (le_trans (le_max_left _ _) hM) habs hℓ h1 h2
    hmod

/-- **Fixed-base primary growth (conditional).**  For every fixed prime `p` and bound `K`,
all sufficiently large exact words have `Q_p > K`. -/
theorem fixed_base_primary_growth (hsup : FixedModulusDyadicSupply) (K : ℕ) :
    ∃ M0 : ℕ, ∀ W : ExactWord, 1 < W.a → M0 ≤ W.M → ∀ p, p.Prime → K < W.Q p := by
  obtain ⟨M0, h⟩ := fixed_modulus_saturation hsup K
  refine ⟨M0, fun W ha hM p hp => ?_⟩
  by_contra hc; push_neg at hc
  exact h W ha hM (W.Q p) (W.one_lt_Q hp) hc (W.Q_absent hp)

/-- **Minimal ceiling growth (conditional).**  `q_* → ∞` along exact words. -/
theorem qstar_tendsto_of_fixed (hsup : FixedModulusDyadicSupply) (K : ℕ) :
    ∃ M0 : ℕ, ∀ W : ExactWord, 1 < W.a → M0 ≤ W.M → K < W.qstar := by
  obtain ⟨M0, h⟩ := fixed_base_primary_growth hsup K
  refine ⟨M0, fun W ha hM => ?_⟩
  obtain ⟨p, hp, hq⟩ := W.qstar_spec
  rw [← hq]; exact h W ha hM p hp

/-- **Uniform modulus saturation (conditional on `UniformDyadicSupply f`).**  Every absent
modulus `d ≥ 2` of a sufficiently large exact word exceeds `f(M)`. -/
theorem uniform_modulus_saturation {f : ℕ → ℕ} (hsup : UniformDyadicSupply f) :
    ∃ M0 : ℕ, ∀ W : ExactWord, 1 < W.a → M0 ≤ W.M →
      ∀ d, 2 ≤ d → W.Absent d → f W.M < d := by
  obtain ⟨X0, hX0⟩ := hsup
  refine ⟨max 16 X0, fun W ha hM d hd habs => ?_⟩
  by_contra hc; push_neg at hc
  obtain ⟨ℓ, hℓ, h1, h2, hmod⟩ :=
    hX0 W.M (le_trans (le_max_right _ _) hM) d (by omega) hc
  exact W.absent_modulus_excluded_by_prime ha (le_trans (le_max_left _ _) hM) habs hℓ h1 h2
    hmod

/-- **Growing-base primary growth (conditional on the uniform provider).**  For every prime
`p` (allowed to grow with `M`), `Q_p > f(M)`. -/
theorem growing_base_primary_growth {f : ℕ → ℕ} (hsup : UniformDyadicSupply f) :
    ∃ M0 : ℕ, ∀ W : ExactWord, 1 < W.a → M0 ≤ W.M → ∀ p, p.Prime → f W.M < W.Q p := by
  obtain ⟨M0, h⟩ := uniform_modulus_saturation hsup
  exact ⟨M0, fun W ha hM p hp => h W ha hM _ (W.one_lt_Q hp) (W.Q_absent hp)⟩

/-- `q_* > f(M)` (conditional on the uniform provider). -/
theorem qstar_gt_of_uniform {f : ℕ → ℕ} (hsup : UniformDyadicSupply f) :
    ∃ M0 : ℕ, ∀ W : ExactWord, 1 < W.a → M0 ≤ W.M → f W.M < W.qstar := by
  obtain ⟨M0, h⟩ := growing_base_primary_growth hsup
  refine ⟨M0, fun W ha hM => ?_⟩
  obtain ⟨p, hp, hq⟩ := W.qstar_spec
  rw [← hq]; exact h W ha hM p hp

/-- **Maximal-carrier consequence (conditional on the uniform provider).**  For every prime
`p`, the maximal primary power satisfies `p · P_p > f(M)`, every carrier element is a
multiple of `P_p`, and the carrier set has at least two elements when `p` is active. -/
theorem maximal_carrier_of_uniform {f : ℕ → ℕ} (hsup : UniformDyadicSupply f) :
    ∃ M0 : ℕ, ∀ W : ExactWord, 1 < W.a → M0 ≤ W.M → ∀ p, p.Prime →
      f W.M < p * W.P p ∧ (∀ n ∈ W.carrier p, W.P p ∣ n) ∧
      (W.Active p → 2 ≤ (W.carrier p).card) := by
  obtain ⟨M0, h⟩ := growing_base_primary_growth hsup
  refine ⟨M0, fun W ha hM p hp => ⟨?_, ?_, ?_⟩⟩
  · rw [← W.Q_eq_mul]; exact h W ha hM p hp
  · intro n hn; simp only [Word.carrier, Finset.mem_filter] at hn; exact hn.2
  · intro hact; rw [W.carrier_eq_layer hp]; exact W.two_le_layer_card hp hact

end Erdos287.PostV71V87
