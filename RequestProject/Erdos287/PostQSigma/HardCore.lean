import RequestProject.Erdos287.PostQSigma.RawSource
import RequestProject.Erdos287.PostQSigma.MandatoryLocal

/-!
# Erdős #287 — post-`Q_Σ` bank, §26–27 (V63): exact hard-core coefficient and no-wrap

**Status: BANK (proved in Lean).**  This is literal original-source counting.

Raw source `(a, M)`, `R = ∅`:

* `V = {a+1, …, M-1}` (`= V a M ∅`, `V_empty_eq`);
* `Omega a M` — the independent omission subsets of `V`;
* `W = lcm(a,…,M)` (`= W a M ∅`), `b_n = W/n`, `T = W(H(a,M) - 1)` (`= T a M ∅`);
* `Bm a M E = ∑_{n∈E} b_n`, `Xd a M E = B(E) - T`;
* `hardCorePoly a M = ∑_{E ∈ Ω} z^{B(E)}` (a polynomial with natural coefficients);
* `NT a M = #{E ∈ Ω : B(E) = T}`.

Results:

* `hard_core_coefficient_exact` — `N_T = [z^T] F_{a,M}` (for `T ≥ 0`);
* `sourceSol_iff` — `SourceSol a M ∅ E ↔ E ∈ Ω ∧ B(E) = T`, so `N_T = 0` iff no source solution;
* `no_wrap_recip` — for nonempty `E ∈ Ω`: `2 ∑_{n∈E} 1/n < H(a,M)` (injection `n ↦ n-1`);
* `Bm_lt_W`, `T_nonneg`, `T_lt_W` — `0 ≤ B(E) < W` and `0 ≤ T < W` on the domain `1 ≤ H < 2`;
* `no_wrap` — `W ∣ (B(E) - T) ↔ B(E) = T`.
-/

open scoped BigOperators

namespace Erdos287.PostQSigma

open Erdos287.ExactSource

variable {a M : ℕ}

open Classical in
/-- `Ω`: the independent omission subsets of `V = {a+1,…,M-1}`. -/
noncomputable def Omega (a M : ℕ) : Finset (Finset ℕ) := (Finset.Ioo a M).powerset.filter Indep

/-- `B(E) = ∑_{n∈E} W/n`. -/
def Bm (a M : ℕ) (E : Finset ℕ) : ℕ := ∑ n ∈ E, W a M ∅ / n

/-- `X(E) = B(E) - T`. -/
def Xd (a M : ℕ) (E : Finset ℕ) : ℤ := (Bm a M E : ℤ) - T a M ∅

/-- The hard-core polynomial `F_{a,M}(z) = ∑_{E∈Ω} z^{B(E)}`. -/
noncomputable def hardCorePoly (a M : ℕ) : Polynomial ℕ := ∑ E ∈ Omega a M, Polynomial.X ^ Bm a M E

open Classical in
/-- `N_T = #{E ∈ Ω : B(E) = T}`. -/
noncomputable def NT (a M : ℕ) : ℕ := ((Omega a M).filter (fun E => Xd a M E = 0)).card

/-- The total path-word count `P = |Ω|`. -/
noncomputable def Ptot (a M : ℕ) : ℕ := (Omega a M).card

theorem mem_Omega {E : Finset ℕ} : E ∈ Omega a M ↔ E ⊆ Finset.Ioo a M ∧ Indep E := by
  classical
  simp [Omega]

lemma cast_Bm (E : Finset ℕ) : ((Bm a M E : ℕ) : ℤ) = ∑ n ∈ E, ((W a M ∅ / n : ℕ) : ℤ) := by
  unfold Bm; push_cast; rfl

/-- The exact source with `R = ∅` is literally `E ∈ Ω ∧ B(E) = T`. -/
theorem sourceSol_iff {E : Finset ℕ} : SourceSol a M ∅ E ↔ E ∈ Omega a M ∧ Xd a M E = 0 := by
  rw [mem_Omega, Xd, cast_Bm, SourceSol, V_empty_eq, sub_eq_zero, and_assoc]

/-- `N_T = 0` iff the raw source has no solution. -/
theorem NT_eq_zero_iff : NT a M = 0 ↔ ∀ E, ¬ SourceSol a M ∅ E := by
  classical
  rw [NT, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  constructor
  · intro h E hE
    rw [sourceSol_iff] at hE
    exact h hE.1 hE.2
  · intro h E hE hX
    exact h E (sourceSol_iff.2 ⟨hE, hX⟩)

/-- **Exact hard-core coefficient**: `N_T = [z^T] F_{a,M}(z)` (for `T ≥ 0`). -/
theorem hard_core_coefficient_exact (hT : 0 ≤ T a M ∅) :
    (hardCorePoly a M).coeff (T a M ∅).toNat = NT a M := by
  classical
  rw [hardCorePoly, Polynomial.finset_sum_coeff]
  simp only [Polynomial.coeff_X_pow]
  rw [NT, Finset.card_eq_sum_ones, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun E _ => ?_)
  have : ((T a M ∅).toNat = Bm a M E) ↔ Xd a M E = 0 := by
    rw [Xd, sub_eq_zero]; omega
  by_cases h : Xd a M E = 0
  · rw [if_pos (this.2 h), if_pos h]
  · rw [if_neg (fun h' => h (this.1 h')), if_neg h]

/-! ## No-wrap -/

/-- Reciprocal form of `B(E)`. -/
lemma Bm_cast_rat (ha : 0 < a) {E : Finset ℕ} (hE : E ⊆ Finset.Ioo a M) :
    ((Bm a M E : ℕ) : ℚ) = (W a M ∅ : ℚ) * ∑ n ∈ E, (1 : ℚ) / n := by
  have hEB : E ⊆ B a M ∅ := by
    intro n hn; rw [mem_B]; have := Finset.mem_Ioo.1 (hE hn)
    exact ⟨by omega, by omega, by simp⟩
  have := sum_W_div_cast (R := ∅) (M := M) ha hEB
  rw [← this, ← cast_Bm, Int.cast_natCast]

/-- `T = W · (H - 1)`. -/
lemma T_cast_rat (ha : 0 < a) : ((T a M ∅ : ℤ) : ℚ) = (W a M ∅ : ℚ) * (Hm a M - 1) := by
  have hW : (W a M ∅ : ℚ) ≠ 0 := by exact_mod_cast W_ne_zero ha
  have h := tau_raw_eq (M := M) ha
  rw [tau] at h
  rw [← h]; field_simp

/-- **No-wrap reciprocal bound**: for nonempty independent `E ⊆ (a, M)`,
`2 ∑_{n∈E} 1/n < H(a, M)`. -/
theorem no_wrap_recip (ha : 0 < a) {E : Finset ℕ} (hE : E ∈ Omega a M) (hne : E.Nonempty) :
    2 * ∑ n ∈ E, (1 : ℚ) / n < Hm a M := by
  classical
  obtain ⟨hEsub, hind⟩ := mem_Omega.1 hE
  have hmem : ∀ n ∈ E, a < n ∧ n < M := fun n hn => Finset.mem_Ioo.1 (hEsub hn)
  set E' := E.image (fun n => n - 1) with hE'
  have hinj : Set.InjOn (fun n => n - 1) (E : Set ℕ) := by
    intro x hx y hy hxy
    have := hmem x hx; have := hmem y hy
    simp only at hxy; omega
  have hdisj : Disjoint E E' := by
    rw [Finset.disjoint_left]
    intro n hn hn'
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 hn'
    have := hmem m hm
    exact hind (m - 1) hn (by rwa [Nat.sub_add_cancel (by omega)])
  have hsub : E ∪ E' ⊆ Finset.Icc a M := by
    intro n hn
    rcases Finset.mem_union.1 hn with hn | hn
    · have := hmem n hn; exact Finset.mem_Icc.2 ⟨by omega, by omega⟩
    · obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 hn
      have := hmem m hm; exact Finset.mem_Icc.2 ⟨by omega, by omega⟩
  have hsumE' : ∑ n ∈ E', (1 : ℚ) / n = ∑ n ∈ E, (1 : ℚ) / ((n - 1 : ℕ) : ℚ) :=
    Finset.sum_image hinj
  have hlt : ∑ n ∈ E, (1 : ℚ) / n < ∑ n ∈ E', (1 : ℚ) / n := by
    rw [hsumE']
    apply Finset.sum_lt_sum_of_nonempty hne
    intro n hn
    have := hmem n hn
    have h1 : (0 : ℚ) < ((n - 1 : ℕ) : ℚ) := by exact_mod_cast (by omega : 0 < n - 1)
    apply one_div_lt_one_div_of_lt h1
    exact_mod_cast (by omega : n - 1 < n)
  have hle : ∑ n ∈ E ∪ E', (1 : ℚ) / n ≤ Hm a M :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
  rw [Finset.sum_union hdisj] at hle
  linarith

/-- `0 ≤ B(E) < W` on the domain `H < 2`. -/
theorem Bm_lt_W (ha : 0 < a) (hH2 : Hm a M < 2) {E : Finset ℕ} (hE : E ∈ Omega a M) :
    Bm a M E < W a M ∅ := by
  have hWpos : (0 : ℚ) < W a M ∅ := by exact_mod_cast Nat.pos_of_ne_zero (W_ne_zero ha)
  rcases E.eq_empty_or_nonempty with rfl | hne
  · simp [Bm]; exact Nat.pos_of_ne_zero (W_ne_zero ha)
  · have h1 := no_wrap_recip ha hE hne
    have h2 := Bm_cast_rat (M := M) ha (mem_Omega.1 hE).1
    have : ((Bm a M E : ℕ) : ℚ) < W a M ∅ := by
      rw [h2]; nlinarith
    exact_mod_cast this

/-- `0 ≤ T` on the domain `1 ≤ H`. -/
theorem T_nonneg (ha : 0 < a) (hH1 : 1 ≤ Hm a M) : 0 ≤ T a M ∅ := by
  have hWpos : (0 : ℚ) < W a M ∅ := by exact_mod_cast Nat.pos_of_ne_zero (W_ne_zero ha)
  have h := T_cast_rat (M := M) ha
  have : (0 : ℚ) ≤ ((T a M ∅ : ℤ) : ℚ) := by rw [h]; nlinarith
  exact_mod_cast this

/-- `T < W` on the domain `H < 2`. -/
theorem T_lt_W (ha : 0 < a) (hH2 : Hm a M < 2) : T a M ∅ < W a M ∅ := by
  have hWpos : (0 : ℚ) < W a M ∅ := by exact_mod_cast Nat.pos_of_ne_zero (W_ne_zero ha)
  have h := T_cast_rat (M := M) ha
  have : ((T a M ∅ : ℤ) : ℚ) < ((W a M ∅ : ℕ) : ℚ) := by rw [h]; nlinarith
  exact_mod_cast this

/-- **No-wrap theorem**: on `1 ≤ H(a,M) < 2`, for every `E ∈ Ω`,
`W ∣ (B(E) - T) ↔ B(E) = T`. -/
theorem no_wrap (ha : 0 < a) (hH1 : 1 ≤ Hm a M) (hH2 : Hm a M < 2) {E : Finset ℕ}
    (hE : E ∈ Omega a M) : (W a M ∅ : ℤ) ∣ Xd a M E ↔ Xd a M E = 0 := by
  constructor
  · intro h
    have hB := Bm_lt_W ha hH2 hE
    have hT0 := T_nonneg ha hH1
    have hT1 := T_lt_W ha hH2
    have hB' : ((Bm a M E : ℕ) : ℤ) < W a M ∅ := by exact_mod_cast hB
    have hlt : |Xd a M E| < (W a M ∅ : ℤ) := by
      rw [abs_lt, Xd]; constructor <;> omega
    exact Int.eq_zero_of_abs_lt_dvd h hlt
  · intro h; rw [h]; exact dvd_zero _

end Erdos287.PostQSigma
