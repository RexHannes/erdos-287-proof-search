import RequestProject.Erdos287.SourceChain.Separation

/-!
# Erdős #287 — final-Astra-audit upstream repairs (kernel-proved parts)

**ERDŐS #287 REMAINS OPEN.  TAIL-287 IS NOT BANKED.**  Manuscript / referee status labels are
metadata and appear in no hypothesis below.

1. **Upper linear-sieve support** `𝒟⁺(D)`: `UpperSieveSupport D ps` (primes in decreasing
   order, odd-prefix conditions `p₁⋯p_{m-1} p_m³ < D`); `upperSieveSupport_prod_lt` proves
   that membership implies `d < D`.  The *well-factorability* of `𝒟⁺(D)` needed to export the
   three critical inequalities is stated exactly as `UpperSieveWellFactorable` (purely
   combinatorial; not proved here — see the report).
2. **V97 noncritical coverage**: `large_count_le_two` (at most two variables exceed `1/3`),
   `complement_one_large`, `complement_two_large` (the complementary product `U`),
   `prefix_hits_window` (a run of small variables has a partial product in any window of
   length `≥` the largest small variable), `TwoLargeEstimate` (the exact analytic estimate
   `|𝒟(Q,b)| ≤ Λ(x/(QN₁) + UQ^{1/2})`) and `twoLarge_cell_saving` (exponent summation).
3. **Scalar-majorant level normalisation**: `pair_coefficient` —
   `D_tot = x^{59/100} = D^{1+ε₀+τ}` ⟹ `2 log x / log D = (200/59)(1+ε₀+τ)`;
   `pair_coefficient_safety` — `(200/59)(1+10⁻³) + 1/295 = 17/5 - 1/295 < 17/5`.
6. **Partition placement**: `partition_after_power_saving` (a subpower partition count times a
   fixed power saving is still a power saving) and the regression
   `partition_on_log_saving_fails` (a subpower count `exp((log log x)^5)` times any
   inverse-logarithmic saving `(log x)^{-A}` is unbounded).
-/

namespace Erdos287.SourceChain

/-! ### 1. Upper linear-sieve support -/

/-- Product of the first `m` entries. -/
def prefixProd (ps : List ℕ) (m : ℕ) : ℕ := (ps.take m).prod

/-- **Upper linear-sieve support** `d = p₁ ⋯ p_r ∈ 𝒟⁺(D)`: primes, strictly decreasing, and for
every odd `m ≤ r`, `p₁ ⋯ p_{m-1} · p_m³ < D`. -/
def UpperSieveSupport (D : ℕ) (ps : List ℕ) : Prop :=
  (∀ p ∈ ps, p.Prime) ∧ ps.Pairwise (· > ·) ∧
    ∀ m < ps.length, m % 2 = 0 → prefixProd ps m * ps[m]! ^ 3 < D

theorem prefixProd_succ (ps : List ℕ) (m : ℕ) (hm : m < ps.length) :
    prefixProd ps (m + 1) = prefixProd ps m * ps[m]! := by
  unfold prefixProd
  rw [List.take_add_one, List.prod_append]
  simp [List.getElem?_eq_getElem hm, List.getElem!_eq_getElem?_getD]

/-- **Membership implies `d < D`** (for `D > 1`). -/
theorem upperSieveSupport_prod_lt {D : ℕ} (hD : 1 < D) {ps : List ℕ}
    (h : UpperSieveSupport D ps) : ps.prod < D := by
  obtain ⟨hpr, hdec, hodd⟩ := h
  have hpos : ∀ p ∈ ps, 1 ≤ p := fun p hp => (hpr p hp).one_lt.le
  rcases Nat.even_or_odd ps.length with ⟨k, hk⟩ | ⟨k, hk⟩
  · -- even length `2k`
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · have : ps = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst this; simpa using hD
    · -- last two entries: index `2k-2` (odd position `m = 2k-2`, even index) and `2k-1`
      set m := 2 * k - 2 with hm
      have hm1 : m + 1 < ps.length := by omega
      have hm0 : m < ps.length := by omega
      have hcond := hodd m hm0 (by omega)
      have hlt : ps[m + 1]! < ps[m]! := by
        have := List.pairwise_iff_getElem.1 hdec m (m + 1) hm0 hm1 (by omega)
        simpa [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hm0,
          List.getElem?_eq_getElem hm1] using this
      have hprod : ps.prod = prefixProd ps m * ps[m]! * ps[m + 1]! := by
        rw [← prefixProd_succ ps m hm0, ← prefixProd_succ ps (m + 1) hm1]
        unfold prefixProd; rw [List.take_of_length_le (by omega)]
      have hpm : 1 ≤ ps[m]! := by
        have := hpos (ps[m]'hm0) (List.getElem_mem hm0)
        simpa [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hm0] using this
      rw [hprod]
      calc prefixProd ps m * ps[m]! * ps[m + 1]! ≤ prefixProd ps m * ps[m]! * ps[m]! :=
            Nat.mul_le_mul_left _ hlt.le
        _ ≤ prefixProd ps m * ps[m]! ^ 3 := by
            rw [pow_succ, pow_two, mul_assoc]
            exact Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ (by omega))
        _ < D := hcond
  · -- odd length `2k+1`: last index `2k` is an even index
    have hm0 : 2 * k < ps.length := by omega
    have hcond := hodd (2 * k) hm0 (by omega)
    have hprod : ps.prod = prefixProd ps (2 * k) * ps[2 * k]! := by
      rw [← prefixProd_succ ps (2 * k) hm0]
      unfold prefixProd; rw [List.take_of_length_le (by omega)]
    have hpm : 1 ≤ ps[2 * k]! := by
      have := hpos (ps[2 * k]'hm0) (List.getElem_mem hm0)
      simpa [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hm0] using this
    rw [hprod]
    calc prefixProd ps (2 * k) * ps[2 * k]! ≤ prefixProd ps (2 * k) * ps[2 * k]! ^ 3 :=
          Nat.mul_le_mul_left _ (by
            calc ps[2 * k]! = ps[2 * k]! ^ 1 := (pow_one _).symm
              _ ≤ ps[2 * k]! ^ 3 := Nat.pow_le_pow_right hpm (by norm_num))
      _ < D := hcond

/-- **Well-factorability of `𝒟⁺(D)`** (Iwaniec; the combinatorial input behind Pascadi
Prop. 5.2's factorisation export): every support element splits as `d = d₁ d₂` with
`d₁ ≤ D₁`, `d₂ ≤ D₂` whenever `D₁ D₂ = D`.  Exact statement only. -/
def UpperSieveWellFactorable : Prop :=
  ∀ (D D1 D2 : ℕ) (ps : List ℕ), 1 ≤ D1 → 1 ≤ D2 → D1 * D2 = D → UpperSieveSupport D ps →
    ∃ d1 d2 : ℕ, d1 * d2 = ps.prod ∧ d1 ≤ D1 ∧ d2 ≤ D2

/-! ### 2. V97 noncritical coverage -/

/-- At most two of finitely many non-negative exponents summing to `1` exceed `1/3`. -/
theorem large_count_le_two {ι : Type*} (s : Finset ι) (e : ι → ℝ) (he : ∀ i ∈ s, 0 ≤ e i)
    (hsum : ∑ i ∈ s, e i = 1) {b : ℝ} (hb : 1 / 3 ≤ b) :
    (s.filter (fun i => b < e i)).card ≤ 2 := by
  by_contra hc
  push_neg at hc
  have h1 : ∑ i ∈ s.filter (fun i => b < e i), e i ≤ 1 := by
    rw [← hsum]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun i hi _ => he i hi)
  have h2 : ((s.filter (fun i => b < e i)).card : ℝ) * b <
      ∑ i ∈ s.filter (fun i => b < e i), e i := by
    have hne : (s.filter (fun i => b < e i)).Nonempty := Finset.card_pos.1 (by omega)
    calc ((s.filter (fun i => b < e i)).card : ℝ) * b =
          ∑ _i ∈ s.filter (fun i => b < e i), b := by rw [Finset.sum_const, nsmul_eq_mul]
      _ < _ := Finset.sum_lt_sum_of_nonempty hne (fun i hi => (Finset.mem_filter.1 hi).2)
  have h3 : (3 : ℝ) ≤ (s.filter (fun i => b < e i)).card := by exact_mod_cast hc
  nlinarith

/-- One large variable `e₁ > b`: the complementary exponent `u = 1 - e₁ < 1 - b`. -/
theorem complement_one_large {e1 b : ℝ} (h : b < e1) : 1 - e1 < 1 - b := by linarith

/-- Two large variables: `u = 1 - e₁ - e₂ < 1 - 2b`. -/
theorem complement_two_large {e1 e2 b : ℝ} (h1 : b < e1) (h2 : b < e2) :
    1 - e1 - e2 < 1 - 2 * b := by linarith

/-- **Window lemma.** For non-negative steps each at most `L`, whose total is at least `a`,
some prefix sum lies in `[a, a + L]`. -/
theorem prefix_hits_window (l : List ℝ) {a L : ℝ} (ha : 0 ≤ a) (hL : 0 ≤ L)
    (hl : ∀ y ∈ l, 0 ≤ y ∧ y ≤ L) (htot : a ≤ l.sum) :
    ∃ m ≤ l.length, a ≤ (l.take m).sum ∧ (l.take m).sum ≤ a + L := by
  induction l generalizing a with
  | nil => exact ⟨0, le_rfl, by simp at htot ⊢; linarith, by simp; linarith⟩
  | cons y t ih =>
    have hy := hl y (List.mem_cons_self ..)
    by_cases hya : a ≤ y
    · exact ⟨1, by simp, by simpa using hya, by simp; linarith [hy.2]⟩
    · push_neg at hya
      obtain ⟨m, hm, h1, h2⟩ := ih (a := a - y) (by linarith)
        (fun z hz => hl z (List.mem_cons_of_mem _ hz)) (by simp at htot; linarith)
      exact ⟨m + 1, by simp; omega, by simp; linarith, by simp; linarith⟩

/-- **Two-large-variable analytic estimate** (exact statement, external): for the bilinear
divisor-in-progression sum `𝒟(Q,b)` with one large variable of size `N₁` and complementary
product `U`, `|𝒟(Q,b)| ≤ Λ (x/(QN₁) + U Q^{1/2})`. -/
def TwoLargeEstimate (Dqb Λ x Q N1 U : ℝ) : Prop :=
  |Dqb| ≤ Λ * (x / (Q * N1) + U * Q ^ ((1 : ℝ) / 2))

/-- **Exponent summation for a two-large cell**: with `N₁ = x^{n₁}`, `U ≤ x^u`, `Q ≤ x^θ`,
summing over `Q` moduli costs a factor `Q`, giving `Λ (x^{1-n₁} + x^{u + 3θ/2})`. -/
theorem twoLarge_cell_saving {x Q N1 U Λ Dqb n1 u θ : ℝ} (hx : 1 ≤ x) (hQ : 0 < Q)
    (hΛ : 0 ≤ Λ) (hN1 : N1 = x ^ n1) (hU : U ≤ x ^ u) (hQθ : Q ≤ x ^ θ)
    (h : TwoLargeEstimate Dqb Λ x Q N1 U) :
    Q * |Dqb| ≤ Λ * (x ^ (1 - n1) + x ^ (u + 3 / 2 * θ)) := by
  have hx0 : 0 < x := by linarith
  unfold TwoLargeEstimate at h
  have e1 : Q * (x / (Q * N1)) = x ^ (1 - n1) := by
    rw [hN1, Real.rpow_sub hx0, Real.rpow_one]; field_simp
  have e2 : Q * (U * Q ^ ((1 : ℝ) / 2)) ≤ x ^ (u + 3 / 2 * θ) := by
    have hq : Q * Q ^ ((1 : ℝ) / 2) = Q ^ ((3 : ℝ) / 2) := by
      rw [← Real.rpow_one_add' hQ.le (by norm_num)]; norm_num
    have hq2 : Q ^ ((3 : ℝ) / 2) ≤ x ^ (3 / 2 * θ) := by
      calc Q ^ ((3 : ℝ) / 2) ≤ (x ^ θ) ^ ((3 : ℝ) / 2) := Real.rpow_le_rpow hQ.le hQθ (by norm_num)
        _ = _ := by rw [← Real.rpow_mul hx0.le]; ring_nf
    calc Q * (U * Q ^ ((1 : ℝ) / 2)) = U * Q ^ ((3 : ℝ) / 2) := by rw [← hq]; ring
      _ ≤ x ^ u * x ^ (3 / 2 * θ) := mul_le_mul hU hq2 (by positivity) (by positivity)
      _ = _ := by rw [← Real.rpow_add hx0]
  calc Q * |Dqb| ≤ Q * (Λ * (x / (Q * N1) + U * Q ^ ((1 : ℝ) / 2))) :=
        mul_le_mul_of_nonneg_left h hQ.le
    _ = Λ * (Q * (x / (Q * N1)) + Q * (U * Q ^ ((1 : ℝ) / 2))) := by ring
    _ ≤ Λ * (x ^ (1 - n1) + x ^ (u + 3 / 2 * θ)) := by
        rw [e1]; exact mul_le_mul_of_nonneg_left (by linarith) hΛ

/-! ### 3. Scalar-majorant level normalisation -/

/-- **Pair coefficient**: `D_tot = x^{59/100} = D^{1+ε₀+τ}` ⟹ `2 log x / log D = (200/59)(1+ε₀+τ)`. -/
theorem pair_coefficient {x D ε0 τ : ℝ} (hx : 1 < x) (hD : 0 < D) (hk : 0 < 1 + ε0 + τ)
    (hlevel : x ^ ((59 : ℝ) / 100) = D ^ (1 + ε0 + τ)) :
    2 * Real.log x / Real.log D = 200 / 59 * (1 + ε0 + τ) := by
  have hlx : 0 < Real.log x := Real.log_pos hx
  have h := congrArg Real.log hlevel
  rw [Real.log_rpow (by linarith), Real.log_rpow hD] at h
  have hlD : Real.log D = 59 / 100 * Real.log x / (1 + ε0 + τ) := by
    field_simp; linarith
  rw [hlD]; field_simp; ring

/-- `200/59` alone is **not** the complete coefficient once `ε₀ + τ > 0`. -/
theorem pair_coefficient_exceeds {ε0 τ : ℝ} (h : 0 < ε0 + τ) :
    (200 : ℝ) / 59 < 200 / 59 * (1 + ε0 + τ) := by nlinarith

/-- **Exact rational safety calculation.** -/
theorem pair_coefficient_safety :
    (200 : ℚ) / 59 * (1 + 1 / 1000) + 1 / 295 = 17 / 5 - 1 / 295 ∧
      (200 : ℚ) / 59 * (1 + 1 / 1000) + 1 / 295 < 17 / 5 := by norm_num

/-! ### 6. Placement of the cross-coprime partition -/

/-- Partition multiplicity applied **after** a fixed power saving: still a power saving. -/
theorem partition_after_power_saving {P : ℝ → ℝ}
    (hP : ∀ η : ℝ, 0 < η → ∃ x0 : ℝ, ∀ x ≥ x0, P x ≤ x ^ η) {κ : ℝ} (hκ : 0 < κ) :
    ∃ x0 : ℝ, ∀ x ≥ x0, P x * x ^ (-κ) ≤ x ^ (-κ / 2) :=
  subpower_absorbed_by_power hP hκ

/-- **Regression**: a subpower partition count `exp((log log x)^5)` multiplied by a merely
inverse-logarithmic saving `(log x)^{-A}` is unbounded, for every `A`. -/
theorem partition_on_log_saving_fails (A C : ℝ) :
    ∃ x : ℝ, 1 < x ∧ C < Real.exp (Real.log (Real.log x) ^ 5) * Real.log x ^ (-A) := by
  set B := Real.log (max C 1)
  have hB : 0 ≤ B := Real.log_nonneg (le_max_right _ _)
  set t := |A| + B + 2
  have ht : 2 ≤ t := by have := abs_nonneg A; linarith
  refine ⟨Real.exp (Real.exp t), ?_, ?_⟩
  · rw [← Real.exp_zero]; exact Real.exp_lt_exp.2 (Real.exp_pos _)
  · rw [Real.log_exp, Real.log_exp, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp,
      ← Real.exp_add]
    have ht4 : t ≤ t ^ 4 := by
      have : 1 ≤ t ^ 3 := one_le_pow₀ (by linarith)
      nlinarith
    have hA : -A * t ≥ -|A| * t := by have := le_abs_self A; nlinarith
    have key : B < t ^ 5 + -A * t := by nlinarith
    calc C ≤ max C 1 := le_max_left _ _
      _ = Real.exp B := (Real.exp_log (by positivity)).symm
      _ < Real.exp (t ^ 5 + Real.log (Real.exp t) * -A) := by
          rw [Real.log_exp]; exact Real.exp_lt_exp.2 (by linarith)
      _ = _ := by rw [Real.log_exp]

end Erdos287.SourceChain
