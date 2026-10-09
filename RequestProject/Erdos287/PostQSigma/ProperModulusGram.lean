import RequestProject.Erdos287.PostQSigma.HardCore

/-!
# Erdős #287 — post-`Q_Σ` bank, §34–36, §40, §42 (V64): the proper-modulus Gram certificate

**Status: BANK (proved in Lean, completely kernel-checked).**

Abstract setting: a finite family `Ω`, integer defects `X : α → ℤ`, and a finite set of moduli
`L`.  For `q ∈ L`:

* `hq q E = [q ∣ X(E)]`, `Nq q = #{E : q ∣ X(E)}`;
* `Gram q r = N_{lcm(q,r)}`.

Results:

* `gram_eq_sum` — `G_{q,r} = ∑_E h_q(E) h_r(E)`;
* `quadForm_eq_sum_sq` / `gram_psd` — `λᵀ G λ = ∑_E (∑_q λ_q h_q(E))² ≥ 0` (PSD);
* `gram_majorant` — if `∑_{q∈L} λ_q = 1` then `#{E : X(E) = 0} ≤ λᵀ G λ`;
* `lcm_lt_of_mem_Lset` — **proper-modulus firewall**: `q, r ∣ W` with `q^25 ≤ W^12`,
  `r^25 ≤ W^12` and `W > 1` give `lcm(q,r) ≤ q r < W`, so **no Gram entry uses
  `N_W(T) = N_T`**;
* `zero_count_certificate` — an unreachable proper modulus (`N_q = 0`) gives the single
  projector certificate `λ = δ_q` with energy `0` (relation to the old hierarchy);
* `W30` fixture — **DIAGNOSTIC**: target `0` absent, yet every unit-sum `λ` on
  `L = {1,2,3,5}` has energy `≥ 1`; so PG-type certificates are not automatic.

Physical instance (`R = ∅`): `Lset W = {q ∣ W : q^25 ≤ W^12}` (integer-safe form of
`q ≤ W^{12/25}`), `proper_modulus_gram_psd`, `proper_modulus_majorant` (`N_T ≤ λᵀ G λ`),
`proper_modulus_firewall`.
-/

open scoped BigOperators

namespace Erdos287.PostQSigma

section Abstract

variable {α : Type*} (Ω : Finset α) (X : α → ℤ)

open Classical in
/-- `h_q(E) = [q ∣ X(E)]`. -/
noncomputable def hq (q : ℕ) (E : α) : ℚ := if (q : ℤ) ∣ X E then 1 else 0

open Classical in
/-- `N_q = #{E ∈ Ω : q ∣ X(E)}`. -/
noncomputable def Nq (q : ℕ) : ℕ := (Ω.filter (fun E => (q : ℤ) ∣ X E)).card

/-- The Gram matrix `G_{q,r} = N_{lcm(q,r)}`. -/
noncomputable def Gram (q r : ℕ) : ℕ := Nq Ω X (Nat.lcm q r)

/-- The quadratic energy `λᵀ G λ` on the modulus set `L`. -/
noncomputable def quadForm (L : Finset ℕ) (lam : ℕ → ℚ) : ℚ :=
  ∑ q ∈ L, ∑ r ∈ L, lam q * lam r * (Gram Ω X q r : ℚ)

/-- `V_λ(E) = ∑_q λ_q h_q(E)`. -/
noncomputable def Vlam (L : Finset ℕ) (lam : ℕ → ℚ) (E : α) : ℚ := ∑ q ∈ L, lam q * hq X q E

lemma lcm_dvd_int_iff (q r : ℕ) (x : ℤ) :
    ((Nat.lcm q r : ℕ) : ℤ) ∣ x ↔ (q : ℤ) ∣ x ∧ (r : ℤ) ∣ x := by
  simp only [Int.natCast_dvd]
  exact Nat.lcm_dvd_iff

/-- `G_{q,r} = ∑_E h_q(E) h_r(E)`. -/
theorem gram_eq_sum (q r : ℕ) : (Gram Ω X q r : ℚ) = ∑ E ∈ Ω, hq X q E * hq X r E := by
  classical
  unfold Gram Nq hq
  rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun E _ => ?_)
  by_cases h1 : (q : ℤ) ∣ X E <;> by_cases h2 : (r : ℤ) ∣ X E <;>
    simp [lcm_dvd_int_iff, h1, h2]

/-- `λᵀ G λ = ∑_E V_λ(E)²`. -/
theorem quadForm_eq_sum_sq (L : Finset ℕ) (lam : ℕ → ℚ) :
    quadForm Ω X L lam = ∑ E ∈ Ω, (Vlam X L lam E) ^ 2 := by
  have hR : ∀ E ∈ Ω, (Vlam X L lam E) ^ 2 =
      ∑ q ∈ L, ∑ r ∈ L, lam q * lam r * (hq X q E * hq X r E) := by
    intro E _
    rw [Vlam, sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun q _ => Finset.sum_congr rfl (fun r _ => by ring))
  rw [Finset.sum_congr rfl hR, quadForm]
  have hL : ∀ q ∈ L, ∀ r ∈ L, lam q * lam r * (Gram Ω X q r : ℚ) =
      ∑ E ∈ Ω, lam q * lam r * (hq X q E * hq X r E) := by
    intro q _ r _
    rw [gram_eq_sum Ω X, Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun q hq => Finset.sum_congr rfl (fun r hr => hL q hq r hr))]
  rw [Finset.sum_comm' (t' := L) (s' := fun _ => Ω) (h := fun _ _ => by simp)]
  exact Finset.sum_congr rfl (fun q _ => Finset.sum_comm)

/-- **The Gram matrix is positive semidefinite.** -/
theorem gram_psd (L : Finset ℕ) (lam : ℕ → ℚ) : 0 ≤ quadForm Ω X L lam := by
  rw [quadForm_eq_sum_sq]; positivity

open Classical in
/-- **Exact Gram majorant**: if `∑_{q∈L} λ_q = 1` then `#{E : X(E) = 0} ≤ λᵀ G λ`. -/
theorem gram_majorant (L : Finset ℕ) (lam : ℕ → ℚ) (hsum : ∑ q ∈ L, lam q = 1) :
    ((Ω.filter (fun E => X E = 0)).card : ℚ) ≤ quadForm Ω X L lam := by
  rw [quadForm_eq_sum_sq]
  have hV : ∀ E, X E = 0 → Vlam X L lam E = 1 := by
    intro E hE
    unfold Vlam hq
    simp [hE, hsum]
  calc ((Ω.filter (fun E => X E = 0)).card : ℚ)
      = ∑ E ∈ Ω.filter (fun E => X E = 0), (Vlam X L lam E) ^ 2 := by
        rw [Finset.card_eq_sum_ones, Nat.cast_sum]
        refine Finset.sum_congr rfl (fun E hE => ?_)
        rw [hV E (Finset.mem_filter.1 hE).2]; norm_num
    _ ≤ ∑ E ∈ Ω, (Vlam X L lam E) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun _ _ _ => sq_nonneg _)

/-- **Relation to the old hierarchy**: an unreachable modulus `q ∈ L` (`N_q = 0`) is a
single-projector certificate of energy `0`, hence `#{E : X(E) = 0} = 0`. -/
theorem zero_count_certificate {L : Finset ℕ} {q : ℕ} (hq : q ∈ L) (h0 : Nq Ω X q = 0) :
    quadForm Ω X L (fun r => if r = q then 1 else 0) = 0 ∧
      ∑ r ∈ L, (fun r => if r = q then (1 : ℚ) else 0) r = 1 := by
  refine ⟨?_, by simp [Finset.sum_ite_eq', hq]⟩
  unfold quadForm
  rw [Finset.sum_eq_single q (fun b _ hb => by simp [hb]) (fun h => absurd hq h)]
  rw [Finset.sum_eq_single q (fun b _ hb => by simp [hb]) (fun h => absurd hq h)]
  simp [Gram, Nat.lcm_self, h0]

end Abstract

/-! ## The proper-modulus family and the firewall -/

/-- `Lset W = {q ∣ W : q^25 ≤ W^12}` — the integer-safe form of `q ≤ W^{12/25}`. -/
def Lset (W : ℕ) : Finset ℕ := W.divisors.filter (fun q => q ^ 25 ≤ W ^ 12)

lemma mem_Lset {W q : ℕ} : q ∈ Lset W ↔ q ∣ W ∧ W ≠ 0 ∧ q ^ 25 ≤ W ^ 12 := by
  simp [Lset, Nat.mem_divisors, and_assoc]

/-- **Proper-modulus firewall**: `q, r ∈ Lset W`, `W > 1` ⇒ `lcm(q,r) ≤ q r < W`.
In particular no Gram entry is `N_W(T) = N_T`. -/
theorem lcm_lt_of_mem_Lset {W q r : ℕ} (hW : 1 < W) (hq : q ∈ Lset W) (hr : r ∈ Lset W) :
    Nat.lcm q r ≤ q * r ∧ q * r < W := by
  obtain ⟨hqW, -, hq25⟩ := mem_Lset.1 hq
  obtain ⟨hrW, -, hr25⟩ := mem_Lset.1 hr
  have hq0 : 0 < q := Nat.pos_of_dvd_of_pos hqW (by omega)
  have hr0 : 0 < r := Nat.pos_of_dvd_of_pos hrW (by omega)
  refine ⟨?_, ?_⟩
  · have := Nat.gcd_mul_lcm q r
    have hg : 0 < Nat.gcd q r := Nat.gcd_pos_of_pos_left r hq0
    nlinarith [Nat.lcm_pos hq0 hr0]
  · have h1 : (q * r) ^ 25 ≤ W ^ 24 := by
      rw [mul_pow, show W ^ 24 = W ^ 12 * W ^ 12 by ring]
      exact Nat.mul_le_mul hq25 hr25
    have h2 : W ^ 24 < W ^ 25 := Nat.pow_lt_pow_right hW (by norm_num)
    exact lt_of_pow_lt_pow_left₀ 25 (Nat.zero_le _) (lt_of_le_of_lt h1 h2)

theorem lcm_ne_of_mem_Lset {W q r : ℕ} (hW : 1 < W) (hq : q ∈ Lset W) (hr : r ∈ Lset W) :
    Nat.lcm q r ≠ W := by
  have := lcm_lt_of_mem_Lset hW hq hr; omega

/-! ## Physical instance -/

open Erdos287.ExactSource

variable {a M : ℕ}

/-- The physical Gram matrix `G_{q,r} = N_{lcm(q,r)}(T)` on `Ω`. -/
noncomputable def physGram (a M : ℕ) (q r : ℕ) : ℕ := Gram (Omega a M) (Xd a M) q r

/-- The physical quadratic energy on the proper-modulus set. -/
noncomputable def physQuad (a M : ℕ) (lam : ℕ → ℚ) : ℚ :=
  quadForm (Omega a M) (Xd a M) (Lset (W a M ∅)) lam

/-- **Proper-modulus Gram matrix is PSD.** -/
theorem proper_modulus_gram_psd (lam : ℕ → ℚ) : 0 ≤ physQuad a M lam :=
  gram_psd _ _ _ _

/-- **Exact proper-modulus majorant**: `∑_{q ∈ L} λ_q = 1` ⇒ `N_T ≤ λᵀ G λ`. -/
theorem proper_modulus_majorant (lam : ℕ → ℚ) (hsum : ∑ q ∈ Lset (W a M ∅), lam q = 1) :
    (NT a M : ℚ) ≤ physQuad a M lam :=
  gram_majorant _ _ _ _ hsum

/-- **Proper-modulus firewall (physical)**: for `q, r` in the proper family, the Gram entry
`G_{q,r}` is a count at a modulus `lcm(q,r) < W`; it is never the full count `N_W(T)`. -/
theorem proper_modulus_firewall (hW : 1 < W a M ∅) {q r : ℕ} (hq : q ∈ Lset (W a M ∅))
    (hr : r ∈ Lset (W a M ∅)) : Nat.lcm q r < W a M ∅ := by
  have := lcm_lt_of_mem_Lset hW hq hr; omega

/-! ## Fixture: PG is not a tautology (`W = 30`, DIAGNOSTIC) -/

namespace W30

/-- The defect values `{1, 2, 3, 5, 6, 10, 15}` (indexed by themselves). -/
def Ω30 : Finset ℕ := {1, 2, 3, 5, 6, 10, 15}

/-- `X(E) = E`. -/
def X30 (E : ℕ) : ℤ := E

/-- `L = {1, 2, 3, 5}`. -/
def L30 : Finset ℕ := {1, 2, 3, 5}

/-- The target `0` is absent. -/
theorem target_absent : ∀ E ∈ Ω30, X30 E ≠ 0 := by decide

/-- `L30` is exactly the proper family of `W = 30`. -/
theorem L30_eq : Lset 30 = L30 := by decide

/-- The Gram matrix `[[7,3,3,3],[3,3,1,1],[3,1,3,1],[3,1,1,3]]`. -/
theorem gram_values :
    Gram Ω30 X30 1 1 = 7 ∧ Gram Ω30 X30 1 2 = 3 ∧ Gram Ω30 X30 1 3 = 3 ∧ Gram Ω30 X30 1 5 = 3 ∧
    Gram Ω30 X30 2 2 = 3 ∧ Gram Ω30 X30 2 3 = 1 ∧ Gram Ω30 X30 2 5 = 1 ∧
    Gram Ω30 X30 3 3 = 3 ∧ Gram Ω30 X30 3 5 = 1 ∧ Gram Ω30 X30 5 5 = 3 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · unfold Gram Nq Ω30 X30; decide

/-- **Strictness**: every unit-sum weight on `L = {1,2,3,5}` has Gram energy `≥ 1`, although
the target count is `0`. -/
theorem constrained_optimum_ge_one (lam : ℕ → ℚ) (hsum : ∑ q ∈ L30, lam q = 1) :
    1 ≤ quadForm Ω30 X30 L30 lam := by
  rw [quadForm_eq_sum_sq]
  have hs : lam 1 + lam 2 + lam 3 + lam 5 = 1 := by
    simpa [L30, Finset.sum_insert, add_assoc] using hsum
  simp only [Vlam, hq, L30, Ω30, X30]
  simp [Finset.sum_insert]
  nlinarith [sq_nonneg (lam 1 - (lam 1 + lam 2 + lam 3 + lam 5) * (-1 / 2)),
    sq_nonneg (lam 1 + lam 2 + lam 3 - (lam 1 + lam 2 + lam 3 + lam 5) * (1 / 2)),
    sq_nonneg (lam 1 + lam 2 + lam 5 - (lam 1 + lam 2 + lam 3 + lam 5) * (1 / 2)),
    sq_nonneg (lam 1 + lam 3 + lam 5 - (lam 1 + lam 2 + lam 3 + lam 5) * (1 / 2)),
    sq_nonneg (lam 1 + lam 2), sq_nonneg (lam 1 + lam 3), sq_nonneg (lam 1 + lam 5)]

end W30

end Erdos287.PostQSigma
