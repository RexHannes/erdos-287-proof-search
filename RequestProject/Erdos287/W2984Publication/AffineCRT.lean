import Mathlib

/-!
# W2.984 — exact congruence transfer for the fixed affine forms `L_i(t) = a_i t + 1`

**ERDŐS #287 REMAINS OPEN.  Exact integer / `ZMod` algebra; no analytic input.**

This file proves, as theorems, every arithmetic step of the affine `S₁, S₂, S₃` source
transformations of `AFFINE_CHEN_TRANSFER_W2984.md` (§§4, 6, 8).  The point is that **no local
density is inferred**: each density used in the paper is a literal residue count proved here.

## Designated prime coordinate (`S₁`, `S₂`)

* `transfer_identity` — `a_j (a_i t + 1) = a_i (a_j t + 1) + (a_j - a_i)`.
* `dvd_form_iff` — if `e` is coprime to `a_j` and `p = a_j t + 1`, then
  `e ∣ a_i t + 1 ↔ e ∣ a_i p + (a_j - a_i)` (the **literal congruence for `p`**).
* `coprime_of_dvd_form` — **every residue is a unit**: if moreover `e` is coprime to `a_j - a_i`,
  then `p` is coprime to `e`.
* `progression_iff` — `W ∣ t - t₀ ↔ a_j W ∣ p - (a_j t₀ + 1)`; `progression_surj` — every
  `p ≡ a_j t₀ + 1 (mod a_j W)` is `a_j t + 1` with `t ≡ t₀ (mod W)`: the **complete modulus
  includes `a_j W`**, and the map `t ↦ p` is a bijection of the two progressions.
* `base_residue_unit` — `a_j t₀ + 1` is a unit mod `a_j W` iff it is a unit mod `W`; with `t₀ = 0`
  it is `1`.
* `totient_mul_of_primeFactors_subset` — **`φ(a_j W) = a_j φ(W)`** when every prime factor of
  `a_j` divides `W` (exact normalisation); `totient_normalisation_needs_radical` shows the
  hypothesis cannot be dropped (`φ(3·2) ≠ 3 φ(2)`).

## CRT compatibility: distinct affine roots

* `prime_dvd_two_forms` — a prime dividing `a_i t + 1` and `a_k t + 1` divides `a_k - a_i`
  (and not `a_i`).
* `coprime_of_dvd_forms` — hence divisors of two different forms that are coprime to `W` are
  coprime whenever every prime factor of `a_k - a_i` divides `W`: the moduli
  `d`, `[d_i, d_i']`, `a_j W` are **pairwise coprime on the support**, not "may be assumed".
* `roots_distinct` — modulo a prime `q ∤ a_i a_k (a_i - a_k)` the roots `-a_i⁻¹`, `-a_k⁻¹` are
  distinct; `card_root_one` — exactly one residue class; `local_density_designated` —
  among the `q - 1` classes with `q ∤ L_j(t)` exactly one has `q ∣ L_ℓ(t)`: the literal
  local factor `g(q) = 1/(q - 1)` of Merikoski's Lemma 15.
* `overlap_empty` — **the spectator-overlap set is empty**: if `q ∣ L_ℓ(t)` and `q ∣ L_i(t)`
  for `i ≠ ℓ` with `q` prime to the slope difference, there is no such `t`.  This is the precise
  reason the first sum in Merikoski's `r_d` vanishes while the second does not (v3 §6).

## Switched coordinate (`S₃`)

* `switched_identity` — with `x = a_ℓ t + 1`: `a_ℓ (a_j t + 1) = a_j x + a_ℓ - a_j`.
* `switched_progression` — `W ∣ t → a_ℓ W ∣ x - 1`; the base progression is
  `x ≡ 1 (mod a_ℓ W)`; `switched_modulus_not_squarefree` — `a_ℓ W` need not be squarefree
  (`a_ℓ = 4`, `W = 2`).
-/

namespace Erdos287.W2984Publication

/-! ### Designated prime coordinate -/

theorem transfer_identity (ai aj t : ℤ) :
    aj * (ai * t + 1) = ai * (aj * t + 1) + (aj - ai) := by ring

/-- The literal congruence for `p = a_j t + 1`. -/
theorem dvd_form_iff {e ai aj t : ℤ} (hcop : IsCoprime e aj) :
    e ∣ ai * t + 1 ↔ e ∣ ai * (aj * t + 1) + (aj - ai) := by
  rw [← transfer_identity]
  constructor
  · intro h; exact Dvd.dvd.mul_left h aj
  · intro h; exact hcop.dvd_of_dvd_mul_left h

/-- Every residue is a unit. -/
theorem coprime_of_dvd_form {e ai aj p : ℤ} (hd : e ∣ ai * p + (aj - ai))
    (hcop : IsCoprime e (aj - ai)) : IsCoprime e p := by
  obtain ⟨k, hk⟩ := hd
  obtain ⟨u, v, huv⟩ := hcop
  refine ⟨u + v * k, -(v * ai), ?_⟩
  have : aj - ai = e * k - ai * p := by linarith
  rw [this] at huv
  linarith [huv]

theorem progression_iff {aj W t t₀ : ℤ} (haj : aj ≠ 0) :
    W ∣ t - t₀ ↔ aj * W ∣ (aj * t + 1) - (aj * t₀ + 1) := by
  rw [show (aj * t + 1) - (aj * t₀ + 1) = aj * (t - t₀) by ring]
  exact (mul_dvd_mul_iff_left haj).symm

theorem progression_surj {aj W t₀ p : ℤ} (h : aj * W ∣ p - (aj * t₀ + 1)) :
    ∃ t : ℤ, p = aj * t + 1 ∧ W ∣ t - t₀ := by
  obtain ⟨m, hm⟩ := h
  refine ⟨t₀ + W * m, by linarith [hm], ⟨m, by ring⟩⟩

theorem base_residue_unit {aj W t₀ : ℤ} :
    IsCoprime (aj * t₀ + 1) (aj * W) ↔ IsCoprime (aj * t₀ + 1) W := by
  have ha : IsCoprime (aj * t₀ + 1) aj := ⟨1, -t₀, by ring⟩
  constructor
  · intro h; exact h.of_mul_right_right
  · intro h; exact IsCoprime.mul_right ha h

theorem base_residue_zero (aj W : ℤ) : IsCoprime (aj * 0 + 1) (aj * W) := by
  simpa using isCoprime_one_left

/-- **Exact normalisation** `φ(a W) = a φ(W)` when `rad a ∣ W`. -/
theorem totient_mul_of_primeFactors_subset {a W : ℕ} (ha : 0 < a) (hW : 0 < W)
    (hsub : ∀ q, q.Prime → q ∣ a → q ∣ W) : Nat.totient (a * W) = a * Nat.totient W := by
  have hpf : (a * W).primeFactors = W.primeFactors := by
    rw [Nat.primeFactors_mul ha.ne' hW.ne']
    apply Finset.union_eq_right.2
    intro q hq
    rw [Nat.mem_primeFactors] at hq ⊢
    exact ⟨hq.1, hsub q hq.1 hq.2.1, hW.ne'⟩
  rw [Nat.totient_eq_div_primeFactors_mul, Nat.totient_eq_div_primeFactors_mul W, hpf]
  have hdvd : (∏ p ∈ W.primeFactors, p) ∣ W := Nat.prod_primeFactors_dvd W
  rw [Nat.mul_div_assoc a hdvd, mul_assoc]

/-- The radical hypothesis cannot be dropped. -/
theorem totient_normalisation_needs_radical : Nat.totient (3 * 2) ≠ 3 * Nat.totient 2 := by
  decide

/-! ### Distinct affine roots and CRT compatibility -/

theorem prime_dvd_two_forms {q : ℕ} {ai ak t : ℤ} (hi : (q : ℤ) ∣ ai * t + 1)
    (hk : (q : ℤ) ∣ ak * t + 1) : (q : ℤ) ∣ ak - ai := by
  have : ak - ai = ak * (ai * t + 1) - ai * (ak * t + 1) := by ring
  rw [this]
  exact dvd_sub (Dvd.dvd.mul_left hi _) (Dvd.dvd.mul_left hk _)

theorem prime_not_dvd_slope {q : ℕ} (hq : q.Prime) {ai t : ℤ} (hi : (q : ℤ) ∣ ai * t + 1) :
    ¬ (q : ℤ) ∣ ai := by
  intro h
  have : (q : ℤ) ∣ 1 := by
    have := dvd_sub hi (Dvd.dvd.mul_right h t)
    simpa using this
  have := Int.eq_one_of_dvd_one (by positivity) this
  exact hq.one_lt.ne' (by exact_mod_cast this)

/-- **Pairwise coprimality on the support.** Divisors of two different forms that are coprime
to `W` are coprime, when every prime factor of the slope difference divides `W`. -/
theorem coprime_of_dvd_forms {di dk W : ℕ} {ai ak t : ℤ}
    (hdi : (di : ℤ) ∣ ai * t + 1) (hdk : (dk : ℤ) ∣ ak * t + 1)
    (hW : ∀ q : ℕ, q.Prime → (q : ℤ) ∣ ak - ai → q ∣ W) (hiW : Nat.Coprime di W) :
    Nat.Coprime di dk := by
  apply Nat.coprime_of_dvd
  intro q hq hqi hqk
  have h1 : (q : ℤ) ∣ ai * t + 1 := (Int.natCast_dvd_natCast.2 hqi).trans hdi
  have h2 : (q : ℤ) ∣ ak * t + 1 := (Int.natCast_dvd_natCast.2 hqk).trans hdk
  have hqW := hW q hq (prime_dvd_two_forms h1 h2)
  exact hq.one_lt.ne' (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hqi hiW) hqW)

section ZModRoots

variable {q : ℕ} [Fact q.Prime]

/-- Distinct roots modulo `q`. -/
theorem roots_distinct {ai ak : ZMod q} (hd : ai ≠ ak) :
    -ai⁻¹ ≠ -ak⁻¹ := by
  intro h
  apply hd
  have := neg_inj.1 h
  exact inv_inj.1 this

theorem form_eq_zero_iff {a t : ZMod q} (ha : a ≠ 0) : a * t + 1 = 0 ↔ t = -a⁻¹ := by
  constructor
  · intro h
    have : a * t = -1 := by linear_combination h
    calc t = a⁻¹ * (a * t) := by rw [← mul_assoc, inv_mul_cancel₀ ha, one_mul]
      _ = -a⁻¹ := by rw [this]; ring
  · rintro rfl; rw [mul_neg, mul_inv_cancel₀ ha]; ring

/-- Exactly one residue class `t` with `q ∣ a t + 1`. -/
theorem card_root_one {a : ZMod q} (ha : a ≠ 0) :
    (Finset.univ.filter (fun t : ZMod q => a * t + 1 = 0)).card = 1 := by
  rw [Finset.card_eq_one]
  exact ⟨-a⁻¹, by ext t; simp [form_eq_zero_iff ha]⟩

/-- **Literal local factor of Merikoski's Lemma 15.**  Among residue classes `t` with
`q ∤ L_j(t)` (there are `q - 1`), exactly one has `q ∣ L_ℓ(t)`. -/
theorem local_density_designated {aj aℓ : ZMod q} (hj : aj ≠ 0) (hℓ : aℓ ≠ 0) (hd : aj ≠ aℓ) :
    (Finset.univ.filter (fun t : ZMod q => aj * t + 1 ≠ 0)).card = q - 1 ∧
      (Finset.univ.filter (fun t : ZMod q => aj * t + 1 ≠ 0 ∧ aℓ * t + 1 = 0)).card = 1 := by
  constructor
  · have h := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (ZMod q))) (fun t : ZMod q => aj * t + 1 = 0)
    rw [card_root_one hj, Finset.card_univ, ZMod.card] at h
    simp only [ne_eq]
    omega
  · rw [Finset.card_eq_one]
    refine ⟨-aℓ⁻¹, ?_⟩
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, ne_eq]
    rw [form_eq_zero_iff hℓ, form_eq_zero_iff hj]
    constructor
    · exact fun h => h.2
    · rintro rfl
      exact ⟨fun h => roots_distinct (Ne.symm hd) h, rfl⟩

/-- **Spectator-overlap set is empty** (distinct affine roots). -/
theorem overlap_empty {ai aℓ : ZMod q} (hi : ai ≠ 0) (hℓ : aℓ ≠ 0) (hd : ai ≠ aℓ) :
    (Finset.univ.filter (fun t : ZMod q => ai * t + 1 = 0 ∧ aℓ * t + 1 = 0)).card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro t - ⟨h1, h2⟩
  rw [form_eq_zero_iff hi] at h1
  rw [form_eq_zero_iff hℓ] at h2
  exact roots_distinct hd (h1 ▸ h2 ▸ rfl)

end ZModRoots

/-! ### Switched coordinate -/

theorem switched_identity (aj aℓ t : ℤ) :
    aℓ * (aj * t + 1) = aj * (aℓ * t + 1) + aℓ - aj := by ring

theorem switched_progression {aℓ W t : ℤ} (h : W ∣ t) : aℓ * W ∣ (aℓ * t + 1) - 1 := by
  rw [show aℓ * t + 1 - 1 = aℓ * t by ring]
  exact mul_dvd_mul_left aℓ h

/-- The switched base modulus `a_ℓ W` need not be squarefree. -/
theorem switched_modulus_not_squarefree : ¬ Squarefree (4 * 2 : ℕ) := by decide

end Erdos287.W2984Publication
