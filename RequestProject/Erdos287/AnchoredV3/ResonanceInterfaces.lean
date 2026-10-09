import RequestProject.Erdos287.AnchoredV3.FourierHitInterface

/-!
# Anchored V3 — resonance classification interface

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

For a divisor conductor `q ∣ D` the **active row set** is

```
S(q) = { r : q ∤ D / m r }.
```

`SparseActive q s_max` is the combinatorial predicate `1 ≤ #S(q) ≤ s_max`, parameterised by a
generic cutoff `s_max` (no logarithmic arithmetic is assumed).

Exact finite facts proved here:

* a row carries zero phase at a divisor frequency exactly when the conductor divides its
  cofactor (`zero_phase_of_dvd`, `notMem_activeRows_iff`);
* a private core prime activates only its own row (`activeRows_private_prime`);
* the terminal characteristic function factors over distinct columns and the factorisation is
  norm-multiplicative (`norm_columnProduct`);
* mobility characteristic factors have modulus at most `1` (`norm_mobilityFactor_le_one`).

The three analytic budgets are **OPEN**: `SparseResonanceArcBudget`, `CentralLobeBudget`,
`RemainingSpectrumBudget` are stated as explicit finite inequalities about a supplied spectrum
split, and are never inhabited here.
-/

open scoped BigOperators

namespace Erdos287
namespace AnchoredV3
namespace Resonance

/-- The active row set of a divisor conductor: the rows whose cofactor is *not* killed by the
conductor. -/
def activeRows (rows : Finset ℕ) (cof : ℕ → ℕ) (q : ℕ) : Finset ℕ :=
  rows.filter (fun r => ¬ q ∣ cof r)

theorem notMem_activeRows_iff {rows : Finset ℕ} {cof : ℕ → ℕ} {q r : ℕ} (hr : r ∈ rows) :
    r ∉ activeRows rows cof q ↔ q ∣ cof r := by
  classical
  simp [activeRows, hr]

/-- A conductor is **sparsely active** when its active row set is nonempty and smaller than the
supplied cutoff. -/
def SparseActive (rows : Finset ℕ) (cof : ℕ → ℕ) (q smax : ℕ) : Prop :=
  1 ≤ (activeRows rows cof q).card ∧ (activeRows rows cof q).card ≤ smax

/-- **A private core prime activates only its own row.**  If `r₀ ∤ cof r₀` while `r₀ ∣ cof s` for
every other row `s`, the active row set of `r₀` is exactly `{r₀}`. -/
theorem activeRows_private_prime {rows : Finset ℕ} {cof : ℕ → ℕ} {r₀ : ℕ} (hr₀ : r₀ ∈ rows)
    (hself : ¬ r₀ ∣ cof r₀) (hother : ∀ s ∈ rows, s ≠ r₀ → r₀ ∣ cof s) :
    activeRows rows cof r₀ = {r₀} := by
  classical
  ext r
  simp only [activeRows, Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨hr, hnd⟩
    by_contra hne
    exact hnd (hother r hr hne)
  · rintro rfl
    exact ⟨hr₀, hself⟩

/-- **Zero phase at a divisor frequency.**  If the conductor `q` divides the cofactor `c`, the
phase of that row at the frequency `2π b / q` is trivial. -/
theorem zero_phase_of_dvd {q c : ℕ} (hq : 0 < q) (h : q ∣ c) (b : ℕ) :
    Complex.exp ((((c : ℝ) * b / q : ℝ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) = 1 := by
  obtain ⟨t, rfl⟩ := h
  have hq' : (q : ℝ) ≠ 0 := by positivity
  have hre : ((q * t : ℕ) : ℝ) * b / q = ((t * b : ℕ) : ℝ) := by
    push_cast
    field_simp
  rw [hre]
  have : (((t * b : ℕ) : ℝ) : ℂ) = ((t * b : ℕ) : ℂ) := by push_cast; ring
  rw [this]
  exact Complex.exp_nat_mul_two_pi_mul_I (t * b)

/-- The terminal characteristic function factors over distinct columns. -/
noncomputable def columnProduct (bands : Finset ℕ) (w : ℕ → ℂ) : ℂ := ∏ ℓ ∈ bands, w ℓ

theorem norm_columnProduct (bands : Finset ℕ) (w : ℕ → ℂ) :
    ‖columnProduct bands w‖ = ∏ ℓ ∈ bands, ‖w ℓ‖ := by
  simp [columnProduct, norm_prod]

theorem norm_columnProduct_le_one {bands : Finset ℕ} {w : ℕ → ℂ}
    (h : ∀ ℓ ∈ bands, ‖w ℓ‖ ≤ 1) : ‖columnProduct bands w‖ ≤ 1 := by
  rw [norm_columnProduct]
  calc ∏ ℓ ∈ bands, ‖w ℓ‖ ≤ ∏ _ℓ ∈ bands, (1:ℝ) :=
        Finset.prod_le_prod (fun ℓ _ => norm_nonneg _) h
    _ = 1 := by simp

/-- A mobility characteristic factor `(1 + e^{iθa}) / 2`. -/
noncomputable def mobilityFactor (a : ℕ) (θ : ℝ) : ℂ :=
  (1 + Complex.exp (((θ * a : ℝ) : ℂ) * Complex.I)) / 2

/-- **Mobility characteristic factors have modulus at most one.** -/
theorem norm_mobilityFactor_le_one (a : ℕ) (θ : ℝ) : ‖mobilityFactor a θ‖ ≤ 1 := by
  have hexp : ‖Complex.exp (((θ * a : ℝ) : ℂ) * Complex.I)‖ = 1 :=
    Complex.norm_exp_ofReal_mul_I _
  have h1 : ‖1 + Complex.exp (((θ * a : ℝ) : ℂ) * Complex.I)‖ ≤ 2 := by
    calc ‖1 + Complex.exp (((θ * a : ℝ) : ℂ) * Complex.I)‖
        ≤ ‖(1 : ℂ)‖ + ‖Complex.exp (((θ * a : ℝ) : ℂ) * Complex.I)‖ := norm_add_le _ _
      _ = 2 := by rw [hexp]; norm_num
  rw [mobilityFactor, norm_div]
  simp only [Complex.norm_ofNat]
  linarith

/-- A supplied decomposition of the arc integral of a tilted characteristic function into the
sparse-resonance arcs, the central lobe and the remaining spectrum. -/
structure SpectrumSplit (K : FiniteCoeff) where
  /-- the tilt parameter -/
  lam : ℝ
  /-- the standard deviation scale -/
  sigma : ℝ
  /-- the scale is at least one -/
  hsigma : 1 ≤ sigma
  /-- contribution of the sparse-active divisor-resonance arcs -/
  arc : ℝ
  /-- contribution of the near-zero noncentral lobe -/
  lobe : ℝ
  /-- contribution of the remaining spectrum -/
  rest : ℝ
  /-- the total arc integral `∫_{1/σ ≤ θ ≤ π} ‖φ_λ‖` -/
  total : ℝ
  /-- the total is the arc integral -/
  htotal : total = ∫ θ in (1 / sigma)..Real.pi, ‖K.char lam θ‖
  /-- the supplied decomposition bound -/
  hsplit : total ≤ arc + lobe + rest

/-- **OPEN analytic owner.**  The sparse-resonance arc payment: the total characteristic-function
integral over all sparse-active divisor-resonance arcs is at most `b / σ`.  Not inhabited. -/
def SparseResonanceArcBudget {K : FiniteCoeff} (S : SpectrumSplit K) (b : ℝ) : Prop :=
  S.arc ≤ b / S.sigma

/-- **OPEN analytic owner.**  The central-lobe estimate.  Not inhabited. -/
def CentralLobeBudget {K : FiniteCoeff} (S : SpectrumSplit K) (b : ℝ) : Prop :=
  S.lobe ≤ b / S.sigma

/-- **OPEN analytic owner.**  The remaining-spectrum estimate.  Not inhabited. -/
def RemainingSpectrumBudget {K : FiniteCoeff} (S : SpectrumSplit K) (b : ℝ) : Prop :=
  S.rest ≤ b / S.sigma

/-- The three budgets combine into the exact arc bound required by the Fourier anti-hole
criterion. -/
theorem arc_bound_of_budgets {K : FiniteCoeff} (S : SpectrumSplit K) {b₁ b₂ b₃ : ℝ}
    (h₁ : SparseResonanceArcBudget S b₁) (h₂ : CentralLobeBudget S b₂)
    (h₃ : RemainingSpectrumBudget S b₃) (hb : b₁ + b₂ + b₃ < 5 / 6) :
    2 * (∫ θ in (1 / S.sigma)..Real.pi, ‖K.char S.lam θ‖) < 5 / (3 * S.sigma) := by
  have hσ : (0:ℝ) < S.sigma := lt_of_lt_of_le zero_lt_one S.hsigma
  have hsum : S.arc + S.lobe + S.rest ≤ (b₁ + b₂ + b₃) / S.sigma := by
    unfold SparseResonanceArcBudget at h₁
    unfold CentralLobeBudget at h₂
    unfold RemainingSpectrumBudget at h₃
    rw [add_div, add_div]
    linarith
  have htot : S.total ≤ (b₁ + b₂ + b₃) / S.sigma := le_trans S.hsplit hsum
  have hpos : (0:ℝ) < (5 / 6 - (b₁ + b₂ + b₃)) / S.sigma := div_pos (by linarith) hσ
  have heq : (5 / 6 - (b₁ + b₂ + b₃)) / S.sigma
      = (5 / 6) / S.sigma - (b₁ + b₂ + b₃) / S.sigma := by ring
  have h5 : 2 * ((5:ℝ) / 6 / S.sigma) = 5 / (3 * S.sigma) := by ring
  rw [← S.htotal, ← h5]
  linarith

end Resonance
end AnchoredV3
end Erdos287
