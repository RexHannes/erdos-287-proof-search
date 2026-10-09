import Mathlib

/-!
# W2.984 — the affine Chen decomposition (analogue of Merikoski v3, Lemma 13)

**ERDŐS #287 REMAINS OPEN.  Exact combinatorics; no analytic input.**

Fix a finite set `Ps` of primes (the sifting primes; Merikoski's `P₀` variant is `Ps = {p ≤ Z,
p ∤ Z_exc}`), and levels `Y ≤ Z`.  For an integer `n` put

* `rough Ps w n` : no `p ∈ Ps` with `p ≤ w` divides `n` (i.e. `(n, P_Ps(w)) = 1`);
* `band Ps Y Z n = {p ∈ Ps : Y < p ≤ Z, p ∣ n}`, `k(n) = #band`;
* `T₃(n) = #{(p,q,r) ∈ Ps³ : Y < p < q < r ≤ Z, pqr ∣ n, rough Ps q (n/(pqr))}` — this is
  Merikoski's `∑_{Y<p<q<r≤Z} ∑_{(s,P(q))=1} 1_{n = pqrs}`;
* `sq(n) = k(n) · #{p ∈ band : p² ∣ n}` — the **non-squarefree correction** (new).

## Audit finding (kernel-checked)

Merikoski's proof of Lemma 13 asserts the pointwise inequality
`1_{(n,P(Z))=1} ≤ 1_{(n,P(Y))=1} - ½ k(n) 1_{(n,P(Y))=1} + ½ T₃(n)`
"for any `n`", arguing that for `k ≥ 2` there are exactly `k - 2` triples.  That count is only
right when the two smallest band primes divide `n` exactly once.  **The pointwise inequality is
false** (`merikoski_pointwise_fails`): with `Ps = {primes ≤ 20}`, `Y = 4`, `Z = 20`,
`n = 1925 = 5²·7·11` the left side is `0` and the right side is `1 - 3/2 + 0 = -1/2`.
Consequently Lemma 13 is **not** a consequence of positivity of the weight alone
(`merikoski_weighted_fails`: one parameter, weight `1`, `L_j = 2`, `L_ℓ = 1925`).

## Repair (kernel-checked)

* `chen_pointwise` — for **every** `n` (and `Y ≤ Z`):
  `1_{rough Z} ≤ 1_{rough Y} - ½ k 1_{rough Y} + ½ T₃ + ½ sq`.
* `chen_weighted` — for any finite parameter set, any **non-negative** weight `ν` (the only
  place positivity is used), and any two integer-valued maps `L_j, L_ℓ` with
  `L_ℓ(t)` prime `⇒ L_ℓ(t) > Z`:
  `S ≤ S₁ - ½ S₂ + ½ S₃ + ½ S_sq`.
* `affine_chen_weighted` — the specialisation to the fixed affine forms `L_i(t) = a_i t + 1`.
  Nothing about shifts, equal slopes, or the shape of the forms is used: the inequality is
  pointwise in the single integer `n = L_ℓ(t)`.

`S_sq` is a trivially negligible tail (`≪ X^{1-α+o(1)}`, see the written proof §5.4); it is a
separate, narrow analytic estimate (`AffineChenSquareTail` in `Providers.lean`).
-/

open scoped BigOperators
open Finset

namespace Erdos287.W2984Publication

/-- `(n, P_Ps(w)) = 1`. -/
def rough (Ps : Finset ℕ) (w n : ℕ) : Prop := ∀ p ∈ Ps, p ≤ w → ¬ p ∣ n

instance (Ps : Finset ℕ) (w n : ℕ) : Decidable (rough Ps w n) := by
  unfold rough; infer_instance

/-- Band primes `Y < p ≤ Z` of `Ps` dividing `n`. -/
def band (Ps : Finset ℕ) (Y Z n : ℕ) : Finset ℕ := Ps.filter (fun p => Y < p ∧ p ≤ Z ∧ p ∣ n)

/-- Merikoski's triple set: `Y < p < q < r ≤ Z`, `n = pqrs`, `(s, P_Ps(q)) = 1`. -/
def triples (Ps : Finset ℕ) (Y Z n : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (Ps ×ˢ Ps ×ˢ Ps).filter (fun x => Y < x.1 ∧ x.1 < x.2.1 ∧ x.2.1 < x.2.2 ∧ x.2.2 ≤ Z ∧
    x.1 * x.2.1 * x.2.2 ∣ n ∧ rough Ps x.2.1 (n / (x.1 * x.2.1 * x.2.2)))

/-- Non-squarefree correction `sq(n) = k(n) · #{p ∈ band : p² ∣ n}`. -/
def sqCorr (Ps : Finset ℕ) (Y Z n : ℕ) : ℕ :=
  (band Ps Y Z n).card * ((band Ps Y Z n).filter (fun p => p ^ 2 ∣ n)).card

/-- Indicator as a real number. -/
noncomputable def ind (P : Prop) [Decidable P] : ℝ := if P then 1 else 0

theorem ind_nonneg (P : Prop) [Decidable P] : 0 ≤ ind P := by unfold ind; split_ifs <;> norm_num

/-- Merikoski's literal right-hand side (no square correction). -/
noncomputable def chenRHSLiteral (Ps : Finset ℕ) (Y Z n : ℕ) : ℝ :=
  ind (rough Ps Y n) - 1/2 * (ind (rough Ps Y n) * (band Ps Y Z n).card) +
    1/2 * ((triples Ps Y Z n).card : ℝ)

/-- Corrected right-hand side. -/
noncomputable def chenRHS (Ps : Finset ℕ) (Y Z n : ℕ) : ℝ :=
  chenRHSLiteral Ps Y Z n + 1/2 * (sqCorr Ps Y Z n : ℝ)

section Pointwise

variable {Ps : Finset ℕ} {Y Z : ℕ}

theorem rough_mono {w w' n : ℕ} (h : w ≤ w') (hr : rough Ps w' n) : rough Ps w n :=
  fun p hp hpw => hr p hp (le_trans hpw h)

/-- Key counting step: if `n` is `Y`-rough, all band primes divide `n` exactly once and
`k ≥ 2`, then `T₃(n) ≥ k - 2`. -/
theorem card_triples_ge (hP : ∀ p ∈ Ps, p.Prime) {n : ℕ} (hY : rough Ps Y n)
    (hsf : ∀ p ∈ band Ps Y Z n, ¬ p ^ 2 ∣ n) (hk : 2 ≤ (band Ps Y Z n).card) :
    (band Ps Y Z n).card - 2 ≤ (triples Ps Y Z n).card := by
  set B := band Ps Y Z n with hB
  have hBne : B.Nonempty := card_pos.1 (by omega)
  set p₁ := B.min' hBne with hp₁
  have hp₁B : p₁ ∈ B := min'_mem B hBne
  have hB'card : (B.erase p₁).card = B.card - 1 := card_erase_of_mem hp₁B
  have hB'ne : (B.erase p₁).Nonempty := card_pos.1 (by omega)
  set p₂ := (B.erase p₁).min' hB'ne with hp₂
  have hp₂B' : p₂ ∈ B.erase p₁ := min'_mem _ hB'ne
  have hp₂B : p₂ ∈ B := mem_of_mem_erase hp₂B'
  have hp₁₂ : p₁ < p₂ := lt_of_le_of_ne (min'_le B p₂ hp₂B) (fun h => (ne_of_mem_erase hp₂B') h.symm)
  have hB''card : ((B.erase p₁).erase p₂).card = B.card - 2 := by
    rw [card_erase_of_mem hp₂B', hB'card]; omega
  have memB : ∀ {p}, p ∈ B → p ∈ Ps ∧ Y < p ∧ p ≤ Z ∧ p ∣ n := fun h => by
    rw [hB, band, mem_filter] at h; exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩
  -- every band prime `≤ p₂` is `p₁` or `p₂`
  have small : ∀ p ∈ B, p ≤ p₂ → p = p₁ ∨ p = p₂ := by
    intro p hp hle
    by_cases h1 : p = p₁
    · exact Or.inl h1
    · right
      exact le_antisymm hle (min'_le _ p (mem_erase.2 ⟨h1, hp⟩))
  rw [← hB''card]
  refine card_le_card_of_injOn (fun r => (p₁, p₂, r)) ?_ ?_
  · intro r hr
    have hr' : r ∈ B.erase p₁ := mem_of_mem_erase hr
    have hrB : r ∈ B := mem_of_mem_erase hr'
    have hp₂r : p₂ < r := lt_of_le_of_ne (min'_le _ r hr') (fun h => (ne_of_mem_erase hr) h.symm)
    obtain ⟨h1P, h1Y, h1Z, h1n⟩ := memB hp₁B
    obtain ⟨h2P, -, h2Z, h2n⟩ := memB hp₂B
    obtain ⟨hrP, -, hrZ, hrn⟩ := memB hrB
    have pr1 := hP _ h1P
    have pr2 := hP _ h2P
    have prr := hP _ hrP
    have c12 : Nat.Coprime p₁ p₂ := (Nat.coprime_primes pr1 pr2).2 (ne_of_lt hp₁₂)
    have c1r : Nat.Coprime p₁ r := (Nat.coprime_primes pr1 prr).2 (by omega)
    have c2r : Nat.Coprime p₂ r := (Nat.coprime_primes pr2 prr).2 (ne_of_lt hp₂r)
    have hdiv : p₁ * p₂ * r ∣ n :=
      Nat.Coprime.mul_dvd_of_dvd_of_dvd (Nat.Coprime.mul_left c1r c2r)
        (Nat.Coprime.mul_dvd_of_dvd_of_dvd c12 h1n h2n) hrn
    simp only [coe_filter, triples, Set.mem_setOf_eq, mem_product]
    refine ⟨⟨h1P, h2P, hrP⟩, h1Y, hp₁₂, hp₂r, hrZ, hdiv, ?_⟩
    -- roughness of the cofactor below `p₂`
    intro p hp hle hps
    obtain ⟨s, hs⟩ := hdiv
    have hsn : n / (p₁ * p₂ * r) = s := by
      rw [hs]; exact Nat.mul_div_cancel_left s (by positivity [pr1.pos, pr2.pos, prr.pos])
    rw [hsn] at hps
    have hpn : p ∣ n := hs ▸ Dvd.dvd.mul_left hps _
    by_cases hpY : p ≤ Y
    · exact hY p hp hpY hpn
    · have hpB : p ∈ B := by
        rw [hB, band, mem_filter]; exact ⟨hp, by omega, le_trans hle h2Z, hpn⟩
      rcases small p hpB hle with rfl | rfl
      · apply hsf _ hp₁B
        rw [hs, pow_two, show p₁ * p₂ * r * s = p₁ * (p₂ * r * s) by ring]
        exact Nat.mul_dvd_mul_left _ (Dvd.dvd.mul_left hps _)
      · apply hsf _ hp₂B
        rw [hs, pow_two, show p₁ * p₂ * r * s = p₂ * (p₁ * r * s) by ring]
        exact Nat.mul_dvd_mul_left _ (Dvd.dvd.mul_left hps _)
  · intro a _ b _ h
    simp only [Prod.mk.injEq] at h
    exact h.2.2

/-- **Corrected Chen pointwise inequality** (all `n`, `Y ≤ Z`). -/
theorem chen_pointwise (hP : ∀ p ∈ Ps, p.Prime) (hYZ : Y ≤ Z) (n : ℕ) :
    ind (rough Ps Z n) ≤ chenRHS Ps Y Z n := by
  unfold chenRHS chenRHSLiteral
  have hT : (0 : ℝ) ≤ (triples Ps Y Z n).card := by positivity
  have hS : (0 : ℝ) ≤ (sqCorr Ps Y Z n : ℝ) := by positivity
  by_cases hY : rough Ps Y n
  · have hYi : ind (rough Ps Y n) = 1 := if_pos hY
    rw [hYi]
    set k := (band Ps Y Z n).card with hk
    by_cases hk0 : k = 0
    · -- `Z`-rough
      have hZ : rough Ps Z n := by
        intro p hp hpZ hpn
        by_cases hpY : p ≤ Y
        · exact hY p hp hpY hpn
        · have : p ∈ band Ps Y Z n := by
            rw [band, mem_filter]; exact ⟨hp, by omega, hpZ, hpn⟩
          rw [hk, card_eq_zero] at hk0
          rw [hk0] at this; simp at this
      have : ind (rough Ps Z n) = 1 := if_pos hZ
      rw [this, hk0]; push_cast; linarith
    · -- not `Z`-rough
      obtain ⟨p, hp⟩ : (band Ps Y Z n).Nonempty := card_pos.1 (by omega)
      have hnZ : ¬ rough Ps Z n := by
        rw [band, mem_filter] at hp
        exact fun h => h p hp.1 hp.2.2.1 hp.2.2.2
      have : ind (rough Ps Z n) = 0 := if_neg hnZ
      rw [this]
      by_cases hsq : ∃ q ∈ band Ps Y Z n, q ^ 2 ∣ n
      · obtain ⟨q, hq, hq2⟩ := hsq
        have h1 : 1 ≤ ((band Ps Y Z n).filter (fun p => p ^ 2 ∣ n)).card :=
          card_pos.2 ⟨q, mem_filter.2 ⟨hq, hq2⟩⟩
        have : (k : ℝ) ≤ sqCorr Ps Y Z n := by
          unfold sqCorr; rw [← hk]; push_cast
          have : (1 : ℝ) ≤ ((band Ps Y Z n).filter (fun p => p ^ 2 ∣ n)).card := by
            exact_mod_cast h1
          nlinarith [show (0 : ℝ) ≤ k by positivity]
        nlinarith
      · push_neg at hsq
        by_cases hk2 : 2 ≤ k
        · have := card_triples_ge hP hY hsq hk2
          have : (k : ℝ) - 2 ≤ (triples Ps Y Z n).card := by
            have h' : ((k - 2 : ℕ) : ℝ) ≤ (triples Ps Y Z n).card := by exact_mod_cast this
            rw [Nat.cast_sub hk2] at h'; push_cast at h'; exact h'
          nlinarith
        · have : (k : ℝ) ≤ 2 := by exact_mod_cast (by omega : k ≤ 2)
          nlinarith
  · have hYi : ind (rough Ps Y n) = 0 := if_neg hY
    have hZ : ind (rough Ps Z n) = 0 := if_neg (fun h => hY (rough_mono hYZ h))
    rw [hYi, hZ]
    nlinarith

end Pointwise

/-! ### Kernel-checked failure of the uncorrected pointwise inequality -/

/-- The sifting primes `≤ 20`. -/
def primesTo20 : Finset ℕ := {2, 3, 5, 7, 11, 13, 17, 19}

theorem primesTo20_prime : ∀ p ∈ primesTo20, p.Prime := by decide

/-- Triples live on band primes. -/
theorem triples_eq_band (Ps : Finset ℕ) (Y Z n : ℕ) :
    triples Ps Y Z n = (band Ps Y Z n ×ˢ band Ps Y Z n ×ˢ band Ps Y Z n).filter
      (fun x => Y < x.1 ∧ x.1 < x.2.1 ∧ x.2.1 < x.2.2 ∧ x.2.2 ≤ Z ∧
        x.1 * x.2.1 * x.2.2 ∣ n ∧ rough Ps x.2.1 (n / (x.1 * x.2.1 * x.2.2))) := by
  ext ⟨p, q, r⟩
  simp only [triples, band, mem_filter, mem_product]
  constructor
  · rintro ⟨⟨hp, hq, hr⟩, h1, h2, h3, h4, h5, h6⟩
    have hpn : p ∣ n := (dvd_mul_right p q).mul_right r |>.trans h5
    have hqn : q ∣ n := (dvd_mul_left q p).mul_right r |>.trans h5
    have hrn : r ∣ n := (dvd_mul_left r (p * q)).trans h5
    exact ⟨⟨⟨hp, h1, by omega, hpn⟩, ⟨hq, by omega, by omega, hqn⟩, ⟨hr, by omega, h4, hrn⟩⟩,
      h1, h2, h3, h4, h5, h6⟩
  · rintro ⟨⟨⟨hp, -⟩, ⟨hq, -⟩, ⟨hr, -⟩⟩, h⟩
    exact ⟨⟨hp, hq, hr⟩, h⟩

theorem band_1925 : band primesTo20 4 20 1925 = {5, 7, 11} := by decide

theorem fixture_1925 :
    rough primesTo20 4 1925 ∧ ¬ rough primesTo20 20 1925 ∧ (band primesTo20 4 20 1925).card = 3 ∧
      (triples primesTo20 4 20 1925).card = 0 := by
  refine ⟨by decide, by decide, by rw [band_1925]; rfl, ?_⟩
  rw [triples_eq_band, band_1925]
  decide

/-- **Audit: Merikoski's pointwise inequality (Lemma 13 proof) is false as stated.** -/
theorem merikoski_pointwise_fails :
    ¬ ∀ n : ℕ, ind (rough primesTo20 20 n) ≤ chenRHSLiteral primesTo20 4 20 n := by
  intro h
  have h1 := h 1925
  obtain ⟨h4, h20, hk, hT⟩ := fixture_1925
  unfold chenRHSLiteral ind at h1
  rw [if_neg h20, if_pos h4, hk, hT] at h1
  norm_num at h1

/-- **Audit: Lemma 13 does not follow from positivity of the weight alone.**  With one
parameter, weight `1`, `L_j = 2` (prime) and `L_ℓ = 1925`, the literal Chen combination is
`-1/2 < 0 = S`. -/
theorem merikoski_weighted_fails :
    ¬ (ind ((2 : ℕ).Prime ∧ (1925 : ℕ).Prime) ≤
        ind (Nat.Prime 2) * chenRHSLiteral primesTo20 4 20 1925) := by
  obtain ⟨h4, h20, hk, hT⟩ := fixture_1925
  have hn : ¬ (1925 : ℕ).Prime := by norm_num
  unfold chenRHSLiteral ind
  rw [if_neg (fun h => hn h.2), if_pos Nat.prime_two, if_pos h4, hk, hT]
  norm_num

/-! ### The weighted (summed) affine Chen decomposition -/

section Weighted

variable (Ps : Finset ℕ) (Y Z : ℕ) (T : Finset ℕ) (ν : ℕ → ℝ) (Lj Lℓ : ℕ → ℕ)

/-- `S = ∑ ν 1_P(L_j) 1_P(L_ℓ)`. -/
noncomputable def chenS : ℝ := ∑ t ∈ T, ν t * ind (Lj t).Prime * ind (Lℓ t).Prime

/-- `S₁ = ∑ ν 1_P(L_j) 1_{(L_ℓ, P(Y))=1}`. -/
noncomputable def chenS1 : ℝ := ∑ t ∈ T, ν t * ind (Lj t).Prime * ind (rough Ps Y (Lℓ t))

/-- `S₂ = ∑_{Y<p≤Z} ∑ ν 1_P(L_j) 1_{p ∣ L_ℓ} 1_{(L_ℓ,P(Y))=1}`. -/
noncomputable def chenS2 : ℝ :=
  ∑ t ∈ T, ν t * ind (Lj t).Prime * (ind (rough Ps Y (Lℓ t)) * (band Ps Y Z (Lℓ t)).card)

/-- `S₃ = ∑ ν 1_P(L_j) ∑_{Y<p<q<r≤Z} ∑_{(s,P(q))=1} 1_{L_ℓ = pqrs}`. -/
noncomputable def chenS3 : ℝ :=
  ∑ t ∈ T, ν t * ind (Lj t).Prime * ((triples Ps Y Z (Lℓ t)).card : ℝ)

/-- Non-squarefree tail `S_sq = ∑ ν 1_P(L_j) sq(L_ℓ)`. -/
noncomputable def chenSsq : ℝ :=
  ∑ t ∈ T, ν t * ind (Lj t).Prime * (sqCorr Ps Y Z (Lℓ t) : ℝ)

/-- **Weighted Chen decomposition.**  Positivity of `ν` is used exactly once: to multiply the
pointwise inequality by `ν(t) 1_P(L_j(t)) ≥ 0`. -/
theorem chen_weighted (hP : ∀ p ∈ Ps, p.Prime) (hYZ : Y ≤ Z) (hν : ∀ t ∈ T, 0 ≤ ν t)
    (hbig : ∀ t ∈ T, (Lℓ t).Prime → Z < Lℓ t) :
    chenS T ν Lj Lℓ ≤ chenS1 Ps Y T ν Lj Lℓ - 1/2 * chenS2 Ps Y Z T ν Lj Lℓ +
      1/2 * chenS3 Ps Y Z T ν Lj Lℓ + 1/2 * chenSsq Ps Y Z T ν Lj Lℓ := by
  unfold chenS chenS1 chenS2 chenS3 chenSsq
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro t ht
  have hw : 0 ≤ ν t * ind (Lj t).Prime := mul_nonneg (hν t ht) (ind_nonneg _)
  -- `1_P(L_ℓ) ≤ 1_{rough Z}(L_ℓ)`
  have hprime : ind (Lℓ t).Prime ≤ ind (rough Ps Z (Lℓ t)) := by
    unfold ind
    by_cases hp : (Lℓ t).Prime
    · have hr : rough Ps Z (Lℓ t) := by
        intro p hpPs hpZ hpd
        have := (Nat.prime_dvd_prime_iff_eq (hP p hpPs) hp).1 hpd
        have := hbig t ht hp
        omega
      rw [if_pos hp, if_pos hr]
    · rw [if_neg hp]; split_ifs <;> norm_num
  have key := le_trans hprime (chen_pointwise hP hYZ (Lℓ t))
  have := mul_le_mul_of_nonneg_left key hw
  unfold chenRHS chenRHSLiteral at this
  linarith

/-- **Affine Chen decomposition** for the fixed affine forms `L_i(t) = a_i t + 1`. -/
theorem affine_chen_weighted (aj aℓ : ℕ) (hP : ∀ p ∈ Ps, p.Prime) (hYZ : Y ≤ Z)
    (hν : ∀ t ∈ T, 0 ≤ ν t) (hbig : ∀ t ∈ T, Z < aℓ * t + 1) :
    chenS T ν (fun t => aj * t + 1) (fun t => aℓ * t + 1) ≤
      chenS1 Ps Y T ν (fun t => aj * t + 1) (fun t => aℓ * t + 1) -
        1/2 * chenS2 Ps Y Z T ν (fun t => aj * t + 1) (fun t => aℓ * t + 1) +
        1/2 * chenS3 Ps Y Z T ν (fun t => aj * t + 1) (fun t => aℓ * t + 1) +
        1/2 * chenSsq Ps Y Z T ν (fun t => aj * t + 1) (fun t => aℓ * t + 1) :=
  chen_weighted Ps Y Z T ν _ _ hP hYZ hν (fun t ht _ => hbig t ht)

end Weighted

end Erdos287.W2984Publication
