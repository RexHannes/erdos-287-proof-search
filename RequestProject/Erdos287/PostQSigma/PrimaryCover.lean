import RequestProject.Erdos287.QSigma.Certificate

/-!
# Erdős #287 — post-`Q_Σ` bank, §6 (V55): the weighted primary cover

**Status: BANK (proved in Lean).**  Independent of the product compression.

Physical prime-depth constraints are indexed by pairs `i = (p, d)` in a finite index set `I`
with `p` prime and `d ≤ e_p = v_p(W)`.  For nonnegative rational weights `λ_i` put

  `weight_λ(n) = ∑_{i ∈ I, n ∈ S_i} λ_i`,
  `C_RT(λ) = max { ∑_{n∈E} weight_λ(n) : E ⊆ V independent, |E| ≤ R_T }`.

* `weighted_primary_cover_excludes` — `∑_i λ_i κ_i > C_RT(λ)` ⇒ no exact source solution.
* `marginalLP_feasible_of_solution` — the compact marginal LP system at `t = 1` is feasible
  (by the indicator vector) whenever an exact solution exists; hence LP infeasibility excludes.
  No LP duality/minimax is assumed anywhere.
-/

open scoped BigOperators

namespace Erdos287.PostQSigma

open Erdos287.ExactSource

variable {a M : ℕ} {R : Finset ℕ}

/-- A finite family of physical prime-depth constraints. -/
def ValidIdx (a M : ℕ) (R : Finset ℕ) (I : Finset (ℕ × ℕ)) : Prop :=
  ∀ i ∈ I, i.1.Prime ∧ i.2 ≤ eW a M R i.1

open Classical in
/-- `weight_λ(n) = ∑_{i ∈ I, n ∈ S_i} λ_i`. -/
noncomputable def coverWeight (a M : ℕ) (R : Finset ℕ) (I : Finset (ℕ × ℕ))
    (lam : ℕ × ℕ → ℚ) (n : ℕ) : ℚ :=
  ∑ i ∈ I, if n ∈ S a M R i.1 i.2 then lam i else 0

open Classical in
/-- The admissible sets: independent `E ⊆ V` with `|E| ≤ k`. -/
noncomputable def admissible (a M : ℕ) (R : Finset ℕ) (k : ℕ) : Finset (Finset ℕ) :=
  (V a M R).powerset.filter (fun E => Indep E ∧ E.card ≤ k)

lemma empty_mem_admissible (k : ℕ) : (∅ : Finset ℕ) ∈ admissible a M R k := by
  classical
  simp [admissible, Indep]

/-- The exact cardinality capacity `C_k(λ)`. -/
noncomputable def coverCapacity (a M : ℕ) (R : Finset ℕ) (I : Finset (ℕ × ℕ))
    (lam : ℕ × ℕ → ℚ) (k : ℕ) : ℚ :=
  (admissible a M R k).sup' ⟨∅, empty_mem_admissible k⟩
    (fun E => ∑ n ∈ E, coverWeight a M R I lam n)

/-- Double counting: `∑_{n∈E} weight_λ(n) = ∑_i λ_i |E ∩ S_i|`. -/
theorem sum_coverWeight (I : Finset (ℕ × ℕ)) (lam : ℕ × ℕ → ℚ) (E : Finset ℕ) :
    ∑ n ∈ E, coverWeight a M R I lam n = ∑ i ∈ I, lam i * (E ∩ S a M R i.1 i.2).card := by
  classical
  unfold coverWeight
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  rw [Finset.filter_mem_eq_inter]

/-- Inside `V`, the filtered part of a solution is exactly `E ∩ S_{p,d}`. -/
lemma filter_eq_inter {E : Finset ℕ} (hE : E ⊆ V a M R) (p d : ℕ) :
    E.filter (fun n => p ^ (eW a M R p - d + 1) ∣ n) = E ∩ S a M R p d := by
  ext n
  simp only [Finset.mem_filter, Finset.mem_inter, S]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, hE h1, h2⟩
  · rintro ⟨h1, -, h2⟩; exact ⟨h1, h2⟩

/-- Every solution meets every physical layer in at least `κ_i` points. -/
theorem kappa_le_card_inter_S (ha : 0 < a) {E : Finset ℕ} (h : SourceSol a M R E) {p d : ℕ}
    (hp : p.Prime) (hd : d ≤ eW a M R p) : kappa a M R p d ≤ (E ∩ S a M R p d).card := by
  rw [← filter_eq_inter h.1]
  exact kappa_le_card_inter ha h hp hd

/-- **V55 weighted primary cover.**  If `∑_i λ_i κ_i > C_{R_T}(λ)` for nonnegative weights,
the exact source has no solution. -/
theorem weighted_primary_cover_excludes (ha : 0 < a) {I : Finset (ℕ × ℕ)}
    (hI : ValidIdx a M R I) {lam : ℕ × ℕ → ℚ} (hlam : ∀ i ∈ I, 0 ≤ lam i)
    (hgt : coverCapacity a M R I lam (RT a M R) < ∑ i ∈ I, lam i * kappa a M R i.1 i.2)
    (E : Finset ℕ) : ¬ SourceSol a M R E := by
  classical
  intro h
  have hmem : E ∈ admissible a M R (RT a M R) := by
    simp only [admissible, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨h.1, h.2.1, h.card_le_RT ha⟩
  have hle : ∑ n ∈ E, coverWeight a M R I lam n ≤ coverCapacity a M R I lam (RT a M R) :=
    Finset.le_sup' (fun E => ∑ n ∈ E, coverWeight a M R I lam n) hmem
  rw [sum_coverWeight] at hle
  have hge : ∑ i ∈ I, lam i * kappa a M R i.1 i.2 ≤
      ∑ i ∈ I, lam i * (E ∩ S a M R i.1 i.2).card := by
    refine Finset.sum_le_sum (fun i hi => ?_)
    refine mul_le_mul_of_nonneg_left ?_ (hlam i hi)
    exact_mod_cast kappa_le_card_inter_S ha h (hI i hi).1 (hI i hi).2
  linarith

/-! ## The compact marginal LP system (finite; no duality assumed) -/

/-- The marginal LP system at level `t`:
`0 ≤ x_n ≤ 1`, `x_n + x_{n+1} ≤ 1`, `∑ x_n ≤ R_T`, `∑_{n∈S_i} x_n ≥ t κ_i`. -/
def MarginalLP (a M : ℕ) (R : Finset ℕ) (I : Finset (ℕ × ℕ)) (t : ℚ) (x : ℕ → ℚ) : Prop :=
  (∀ n ∈ V a M R, 0 ≤ x n ∧ x n ≤ 1) ∧
  (∀ n ∈ V a M R, n + 1 ∈ V a M R → x n + x (n + 1) ≤ 1) ∧
  (∑ n ∈ V a M R, x n ≤ RT a M R) ∧
  (∀ i ∈ I, t * kappa a M R i.1 i.2 ≤ ∑ n ∈ S a M R i.1 i.2, x n)

open Classical in
/-- **Soundness of the LP relaxation.**  An exact solution gives a feasible point at `t = 1`. -/
theorem marginalLP_feasible_of_solution (ha : 0 < a) {I : Finset (ℕ × ℕ)}
    (hI : ValidIdx a M R I) {E : Finset ℕ} (h : SourceSol a M R E) :
    MarginalLP a M R I 1 (fun n => if n ∈ E then 1 else 0) := by
  refine ⟨fun n _ => by dsimp only; split_ifs <;> norm_num, fun n _ _ => ?_, ?_, fun i hi => ?_⟩
  · dsimp only
    by_cases hn : n ∈ E
    · have := h.2.1 n hn; simp [hn, this]
    · simp only [hn, if_false]; split_ifs <;> norm_num
  · rw [← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    have : (V a M R).filter (fun n => n ∈ E) = E := by
      ext n; simp only [Finset.mem_filter]; exact ⟨fun h' => h'.2, fun h' => ⟨h.1 h', h'⟩⟩
    rw [this]; exact_mod_cast h.card_le_RT ha
  · rw [← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one, one_mul]
    have : (S a M R i.1 i.2).filter (fun n => n ∈ E) = E ∩ S a M R i.1 i.2 := by
      ext n; simp [Finset.mem_inter, and_comm]
    rw [this]; exact_mod_cast kappa_le_card_inter_S ha h (hI i hi).1 (hI i hi).2

/-- **LP exclusion.**  If the marginal system is infeasible at `t = 1`, no solution exists. -/
theorem no_solution_of_marginalLP_infeasible (ha : 0 < a) {I : Finset (ℕ × ℕ)}
    (hI : ValidIdx a M R I) (hinf : ∀ x, ¬ MarginalLP a M R I 1 x) (E : Finset ℕ) :
    ¬ SourceSol a M R E := fun h => hinf _ (marginalLP_feasible_of_solution ha hI h)

end Erdos287.PostQSigma
