import RequestProject.Erdos287.ResearchBankV10.HBSupportCoverage
import RequestProject.Erdos287.ResearchBankV10.RoughSeedIdentities
import RequestProject.Erdos287.ResearchBankV10.TypeIRescaling
import RequestProject.Erdos287.ResearchBankV10.TypeIRoughness
import RequestProject.Erdos287.ResearchBankV10.TypeIICompatibleCells
import RequestProject.Erdos287.ResearchBankV10.TypeIICoefficient

/-!
# Erdős #287 — Research Bank V10 §C: external analytic providers (no custom axioms)

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

Every genuinely analytic input is a `Prop`-valued **structure** (never an `axiom`).  No theorem
constructs any of them for a nontrivial error term: the only inhabitants in this bank are the
zero-error / zero-kernel models (`*_zero`), used to show the hypotheses are satisfiable.

* `LogPowerSaving f` — `∀ A > 0, ∃ C X₀, ∀ X ≥ X₀, |f X| ≤ C · X · (log X)^{-A}`;
* `ZhengKloostermanInput Kl κ` — `|Kl(c)| ≤ C_ε c^{κ+ε}`;
* `GeneralizedBVInput Δ` — log-power saving of a generalized BV error;
* `OrdinaryBVInput P E` — log-power saving of every box in the small-total-modulus region;
* `SiegelWalfiszSeedInput Δ` — the pointwise rough-seed SW bound (`RoughSeedSWProvider`);
* `SmoothTypeIInput P E Kl κ` — the (external) Type-I reduction: *spectral input + the exact
  Type-I combinatorics (`TypeICombinatorialFacts`: `e`-lattice count, Bonferroni sandwich) ⟹*
  log-power saving on the frozen Type-I region;
* `RestoredTypeIIInput P E Kl κ packets` — the (external) restored Type-II reduction: *spectral
  input + the compatible-cell count (`CompatibleCellFacts`) + the reciprocal phases of the packets
  (`ReciprocalPhaseFacts`) ⟹* log-power saving on the restored Type-II region.

The combinatorial premises are **proved** in this bank (`typeICombinatorialFacts_holds`,
`compatibleCellFacts_holds`, `reciprocalPhaseFacts_of_coprime`), so the analytic reductions are
visibly fed by kernel-checked finite inputs.

Proved here:
* closure of `LogPowerSaving` under `+` and finite sums, and `not_logPowerSaving_sq`;
* `seed_aggregate_of_SW` — the **elementary** aggregation of the pointwise SW seed bound over the
  `≤ (log X)^B` small moduli (a genuine, if easy, proof — no analytic input beyond the provider);
* **dependency checks** (`*_not_automatic`, `providers_not_from_frozen`): each provider is
  satisfiable (e.g. by the zero error) but is **false** for an explicit bad error/kernel, so no
  provider follows from combinatorial facts alone.
-/

namespace Erdos287
namespace ResearchBankV10
namespace Providers

open HBSelection HBSupportCoverage RoughSeedIdentities Real

/-- Log-power saving. -/
def LogPowerSaving (f : ℝ → ℝ) : Prop :=
  ∀ A : ℝ, 0 < A → ∃ C X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → |f X| ≤ C * X * Real.log X ^ (-A)

theorem logPowerSaving_zero : LogPowerSaving (fun _ => 0) :=
  fun _ _ => ⟨0, 0, fun X _ => by simp⟩

theorem logPowerSaving_add {f g : ℝ → ℝ} (hf : LogPowerSaving f) (hg : LogPowerSaving g) :
    LogPowerSaving (fun X => f X + g X) := by
  intro A hA
  obtain ⟨C₁, X₁, h₁⟩ := hf A hA
  obtain ⟨C₂, X₂, h₂⟩ := hg A hA
  refine ⟨C₁ + C₂, max X₁ X₂, fun X hX => ?_⟩
  have := h₁ X (le_of_max_le_left hX)
  have := h₂ X (le_of_max_le_right hX)
  calc |f X + g X| ≤ |f X| + |g X| := abs_add_le _ _
    _ ≤ C₁ * X * Real.log X ^ (-A) + C₂ * X * Real.log X ^ (-A) := by linarith
    _ = (C₁ + C₂) * X * Real.log X ^ (-A) := by ring

theorem logPowerSaving_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ)
    (hf : ∀ i ∈ s, LogPowerSaving (f i)) : LogPowerSaving (fun X => ∑ i ∈ s, f i X) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using logPowerSaving_zero
  | insert a s ha ih =>
    have h1 := hf a (Finset.mem_insert_self a s)
    have h2 := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    have := logPowerSaving_add h1 h2
    simpa [Finset.sum_insert ha] using this

/-- An explicit error with no log-power saving: `f(X) = X²`. -/
theorem not_logPowerSaving_sq : ¬ LogPowerSaving (fun X => X ^ 2) := by
  intro h
  obtain ⟨C, X₀, hC⟩ := h 1 one_pos
  set X : ℝ := max (max 3 (|C| + 3)) X₀
  have hX3 : 3 ≤ X := le_trans (le_max_left _ _) (le_max_left _ _)
  have hXC : |C| + 3 ≤ X := le_trans (le_max_right _ _) (le_max_left _ _)
  have hX0 : X₀ ≤ X := le_max_right _ _
  have hlog : 1 ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9; linarith
  have h := hC X hX0
  rw [Real.rpow_neg_one] at h
  have hXpos : 0 < X := by linarith
  rw [abs_of_nonneg (by positivity)] at h
  have hinv : (Real.log X)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hlog
  have hinv0 : 0 ≤ (Real.log X)⁻¹ := by positivity
  have : C * X * (Real.log X)⁻¹ ≤ |C| * X := by
    calc C * X * (Real.log X)⁻¹ ≤ |C| * X * (Real.log X)⁻¹ := by
          gcongr; exact le_abs_self C
      _ ≤ |C| * X * 1 := by gcongr
      _ = |C| * X := by ring
  nlinarith [abs_nonneg C]

/-! ## The provider structures -/

/-- **Zheng-type Kloosterman input** (external): `|Kl(c)| ≤ C_ε c^{κ+ε}`. -/
structure ZhengKloostermanInput (Kl : ℕ → ℝ) (κ : ℝ) : Prop where
  bound : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ c : ℕ, 1 ≤ c → |Kl c| ≤ C * (c : ℝ) ^ (κ + ε)

/-- **Generalized BV input** (external). -/
structure GeneralizedBVInput (Δ : ℝ → ℝ) : Prop where
  bound : LogPowerSaving Δ

/-- **Ordinary BV input** (external): log-power saving on the small-total-modulus region. -/
structure OrdinaryBVInput (P : CoverageParams) (E : SupportBox → ℝ → ℝ) : Prop where
  bound : ∀ b, InBV P b → LogPowerSaving (E b)

/-- **Siegel–Walfisz seed input** (external): the pointwise rough-seed SW bound. -/
structure SiegelWalfiszSeedInput (Δ : ℕ → ℤ → ℝ → ℝ) : Prop where
  sw : RoughSeedSWProvider Δ

/-- The exact Type-I combinatorics consumed by the Type-I reduction (proved below). -/
def TypeICombinatorialFacts : Prop :=
  (∀ e X : ℕ, 0 < e →
    ((Finset.Icc 1 (e * X)).filter (fun v => e ∣ v)).card = X) ∧
  (∀ (z₀ L J m : ℕ), Odd J →
    TypeIRoughness.bonf (TypeIRoughness.allowedPrimes z₀ L) J m ≤
        TypeIRoughness.roughInd (TypeIRoughness.allowedPrimes z₀ L) m ∧
      TypeIRoughness.roughInd (TypeIRoughness.allowedPrimes z₀ L) m ≤
        TypeIRoughness.bonf (TypeIRoughness.allowedPrimes z₀ L) (J - 1) m)

theorem typeICombinatorialFacts_holds : TypeICombinatorialFacts :=
  ⟨fun _ X he => TypeIRescaling.lattice_card he X,
   fun _ _ _ m hJ => ⟨TypeIRoughness.lowerBonf_le TypeIRoughness.allowedPrimes_prime hJ m,
     TypeIRoughness.le_upperBonf TypeIRoughness.allowedPrimes_prime hJ m⟩⟩

/-- The compatible-cell count consumed by the Type-II reduction (proved below). -/
def CompatibleCellFacts : Prop :=
  ∀ K d n₁ : ℕ, 0 < K → (TypeIICompatibleCells.compatibleAlpha K d n₁).card = d

theorem compatibleCellFacts_holds : CompatibleCellFacts :=
  fun _ d n₁ hK => TypeIICompatibleCells.compatibleAlpha_card_eq_d hK d n₁

/-- The reciprocal phases `ū (mod v)` of a finite set of Type-II packets. -/
def ReciprocalPhaseFacts (packets : Finset TypeIICoefficient.CoeffVars) : Prop :=
  ∀ x ∈ packets, ∃ ubar : ℤ,
    (TypeIICoefficient.indexMap x).1 * ubar ≡ 1 [ZMOD (TypeIICoefficient.indexMap x).2.1]

/-- The packet coprimality (conductor/root/base) hypotheses. -/
def PacketCoprime (packets : Finset TypeIICoefficient.CoeffVars) : Prop :=
  ∀ x ∈ packets, IsCoprime x.C x.q₂ ∧ IsCoprime x.q₁ x.q₂ ∧ IsCoprime x.n₂ x.q₂ ∧
    IsCoprime x.n₂' x.q₂

theorem reciprocalPhaseFacts_of_coprime {packets : Finset TypeIICoefficient.CoeffVars}
    (h : PacketCoprime packets) : ReciprocalPhaseFacts packets :=
  fun x hx => TypeIICoefficient.exists_reciprocal x (h x hx).1 (h x hx).2.1 (h x hx).2.2.1
    (h x hx).2.2.2

/-- **Smooth Type-I input** (external): the Type-I reduction, *relative to the explicit spectral
input* and the exact Type-I combinatorics. -/
structure SmoothTypeIInput (P : CoverageParams) (E : SupportBox → ℝ → ℝ) (Kl : ℕ → ℝ) (κ : ℝ) :
    Prop where
  reduction : ZhengKloostermanInput Kl κ → TypeICombinatorialFacts →
    ∀ b, InTypeI P b → LogPowerSaving (E b)

/-- **Restored Type-II input** (external): the restored compatible-cell Type-II reduction,
*relative to the explicit spectral input*, the compatible-cell count and the reciprocal phases. -/
structure RestoredTypeIIInput (P : CoverageParams) (E : SupportBox → ℝ → ℝ) (Kl : ℕ → ℝ) (κ : ℝ)
    (packets : Finset TypeIICoefficient.CoeffVars) : Prop where
  reduction : ZhengKloostermanInput Kl κ → CompatibleCellFacts → ReciprocalPhaseFacts packets →
    ∀ b, InTypeII P b → LogPowerSaving (E b)

/-! ## Elementary aggregation of the seed bound -/

/-- The aggregated seed error over the small moduli `q ≤ (log X)^B` (one residue `a(q)` each). -/
noncomputable def seedAggregate (Δ : ℕ → ℤ → ℝ → ℝ) (a : ℕ → ℤ) (B : ℝ) (X : ℝ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 ⌊Real.log X ^ B⌋₊, |Δ q (a q) X|

/-- **Aggregation**: the pointwise SW seed bound implies log-power saving of the aggregate over
`q ≤ (log X)^B`. -/
theorem seed_aggregate_of_SW {Δ : ℕ → ℤ → ℝ → ℝ} (hSW : SiegelWalfiszSeedInput Δ) (a : ℕ → ℤ)
    {B : ℝ} (hB : 0 ≤ B) : LogPowerSaving (seedAggregate Δ a B) := by
  intro A hA
  obtain ⟨C, hC⟩ := hSW.sw.bound (A + B) (by linarith)
  refine ⟨|C|, 3, fun X hX => ?_⟩
  have hlog : 1 ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9; linarith
  have hlogpos : 0 < Real.log X := by linarith
  have hXpos : 0 < X := by linarith
  have hLB : 1 ≤ Real.log X ^ B := Real.one_le_rpow hlog hB
  have hLAB : Real.log X ^ B ≤ Real.log X ^ (A + B) :=
    Real.rpow_le_rpow_of_exponent_le hlog (by linarith)
  unfold seedAggregate
  rw [abs_of_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _)]
  have hterm : ∀ q ∈ Finset.Icc 1 ⌊Real.log X ^ B⌋₊,
      |Δ q (a q) X| ≤ |C| * X * Real.log X ^ (-(A + B)) := by
    intro q hq
    have hq' : (q : ℝ) ≤ Real.log X ^ (A + B) := by
      have h1 : q ≤ ⌊Real.log X ^ B⌋₊ := (Finset.mem_Icc.1 hq).2
      have h2 : (q : ℝ) ≤ Real.log X ^ B :=
        le_trans (by exact_mod_cast h1) (Nat.floor_le (by positivity))
      linarith
    refine (hC q (a q) X (by linarith) hq').trans ?_
    gcongr; exact le_abs_self C
  calc ∑ q ∈ Finset.Icc 1 ⌊Real.log X ^ B⌋₊, |Δ q (a q) X|
      ≤ ∑ _q ∈ Finset.Icc 1 ⌊Real.log X ^ B⌋₊, |C| * X * Real.log X ^ (-(A + B)) :=
        Finset.sum_le_sum hterm
    _ = (⌊Real.log X ^ B⌋₊ : ℝ) * (|C| * X * Real.log X ^ (-(A + B))) := by simp
    _ ≤ Real.log X ^ B * (|C| * X * Real.log X ^ (-(A + B))) := by
        gcongr; exact Nat.floor_le (by positivity)
    _ = |C| * X * (Real.log X ^ B * Real.log X ^ (-(A + B))) := by ring
    _ = |C| * X * Real.log X ^ (-A) := by
        rw [← Real.rpow_add hlogpos]; ring_nf

/-! ## Dependency checks: providers are not automatic -/

/-- A Case I box (`μ = 1`). -/
def boxI : SupportBox :=
  ⟨0, ⟨[(1, true)], by simp, by simp, by simp, by simp⟩, 0, 0⟩

/-- A Case II box (factors `1/4, 3/4`, partial product `1/4`). -/
def boxII : SupportBox :=
  ⟨0, ⟨[(1 / 4, true), (3 / 4, true)], by simp, by
    intro x hx; simp at hx; rcases hx with rfl | rfl <;> norm_num, by norm_num, by
    intro x hx; simp at hx; rcases hx with rfl | rfl <;> simp⟩, 0, 0⟩

theorem boxI_typeI (P : CoverageParams) : InTypeI P boxI := by
  left; unfold CaseI maxSmooth; norm_num [boxI]

theorem boxII_typeII (P : CoverageParams) : InTypeII P boxII :=
  Or.inl ⟨1 / 4, ⟨[(1 / 4, true)], by simp [boxII], by simp⟩, by norm_num, le_rfl⟩

theorem boxI_BV (P : CoverageParams) : InBV P boxI := by
  unfold InBV; simp [boxI]; have := P.ζ_le; linarith

/-- The bad error `E(b, X) = X²`. -/
def badError : SupportBox → ℝ → ℝ := fun _ X => X ^ 2

theorem zheng_zero (κ : ℝ) : ZhengKloostermanInput (fun _ => 0) κ :=
  ⟨fun _ _ => ⟨0, fun c _ => by simp⟩⟩

/-- Zheng input is not automatic: `Kl(c) = c` with `κ = 0` violates it. -/
theorem zheng_not_automatic : ¬ ZhengKloostermanInput (fun c => (c : ℝ)) 0 := by
  intro ⟨h⟩
  obtain ⟨C, hC⟩ := h (1 / 2) (by norm_num)
  set n : ℕ := ⌈|C|⌉₊ + 1
  have hn : |C| < n := by
    have := Nat.le_ceil |C|; push_cast [n]; linarith
  have h1 := hC (n ^ 2) (Nat.one_le_pow 2 n (by omega))
  have hsq : ((n ^ 2 : ℕ) : ℝ) ^ ((0 : ℝ) + 1 / 2) = n := by
    rw [zero_add, ← Real.sqrt_eq_rpow]; push_cast; exact Real.sqrt_sq (by positivity)
  rw [hsq, abs_of_nonneg (by positivity)] at h1
  push_cast at h1
  have hn0 : (0 : ℝ) < n := by positivity
  have : (n : ℝ) ^ 2 ≤ |C| * n := h1.trans (by gcongr; exact le_abs_self C)
  nlinarith

theorem ordinaryBV_zero (P : CoverageParams) : OrdinaryBVInput P (fun _ _ => 0) :=
  ⟨fun _ _ => logPowerSaving_zero⟩

theorem ordinaryBV_not_automatic (P : CoverageParams) : ¬ OrdinaryBVInput P badError :=
  fun h => not_logPowerSaving_sq (h.bound boxI (boxI_BV P))

theorem typeI_zero (P : CoverageParams) (Kl : ℕ → ℝ) (κ : ℝ) :
    SmoothTypeIInput P (fun _ _ => 0) Kl κ :=
  ⟨fun _ _ _ _ => logPowerSaving_zero⟩

theorem typeI_not_automatic (P : CoverageParams) (κ : ℝ) :
    ¬ SmoothTypeIInput P badError (fun _ => 0) κ :=
  fun h => not_logPowerSaving_sq
    (h.reduction (zheng_zero κ) typeICombinatorialFacts_holds boxI (boxI_typeI P))

theorem typeII_zero (P : CoverageParams) (Kl : ℕ → ℝ) (κ : ℝ) (packets) :
    RestoredTypeIIInput P (fun _ _ => 0) Kl κ packets :=
  ⟨fun _ _ _ _ _ => logPowerSaving_zero⟩

theorem typeII_not_automatic (P : CoverageParams) (κ : ℝ) :
    ¬ RestoredTypeIIInput P badError (fun _ => 0) κ ∅ :=
  fun h => not_logPowerSaving_sq (h.reduction (zheng_zero κ) compatibleCellFacts_holds
    (fun x hx => absurd hx (Finset.notMem_empty x)) boxII (boxII_typeII P))

theorem gbv_not_automatic : ¬ GeneralizedBVInput (fun X => X ^ 2) :=
  fun h => not_logPowerSaving_sq h.bound

theorem sw_not_automatic : ¬ SiegelWalfiszSeedInput (fun _ _ X => X ^ 2) :=
  fun h => roughSeedSW_not_automatic h.sw

end Providers
end ResearchBankV10
end Erdos287
