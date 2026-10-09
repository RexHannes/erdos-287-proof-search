import RequestProject.Erdos287.ResearchBankV12.TypeIIWholeRectangle
import RequestProject.Erdos287.ResearchBankV12.CompatibleCellsConcrete

/-!
# Erdős #287 — Research Bank V12 §6: the restored Type-II envelope (three separated layers)

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

The repaired local estimate (research record, **not** a Lean fact):

  `|R11_rest| / (x N / S) ≪ C^{O(1)} x^ε [ Q³ R N / √(x S) + Q^{5/2} R^{1/2} N^{5/4} / √x
                                          + Q^{17/8} R^{3/4} N / √x ]`.

`≪`, `O(1)` and `x^ε` are **not** formalized as Lean facts.  Instead:

* **Layer A (exact exponents).**  With `Q = x^θ`, `R = x^r`, `S = x^s`, `N = x^ν`, the three
  envelope terms are exactly `x^{e₁}, x^{e₂}, x^{e₃}` (`term1_eq`, `term2_eq`, `term3_eq`, real
  `rpow` algebra), and `eᵢ = −gᵢ` for the three restored Type-II gaps of §10 (`e_eq_neg_g`).
* **Layer B (exact finite factors).**  The compatible-cell count `d` (§5) and the Cauchy–Schwarz
  factor `(∑_{α compatible} f α)² ≤ d · ∑ f α²` (`cauchy_compatible_factor`).
* **Layer C (explicit external analytic structure).**  `RestoredTypeIISpectralProvider` with the
  three fields `highH_bound`, `lowH_bound`, `diagonal_bound`.  **No instance is constructed from
  nothing**: `restoredTypeII_of_provider` takes it as a visible hypothesis; the only inhabitant in
  the bank is the zero-error model (`spectralProvider_zero`), and a bad error function is shown not
  to satisfy it (`spectralProvider_not_automatic`).

`caseII_powerSaving_of_provider`: provider + the §10 whole-rectangle margins ⟹ the restored
Type-II error is `≤ 9K · x^{ε − 1/208}` on every actual Case-II box.
-/

namespace Erdos287
namespace ResearchBankV12
namespace RestoredTypeIIEnvelope

open ConcreteParameters TypeIIWholeRectangle CompatibleCellsConcrete

/-! ## Layer A: exact exponent functions -/

/-- `e₁ = 3θ + r + ν − 1/2 − s/2`. -/
def e1 (θ r s ν : ℚ) : ℚ := 3 * θ + r + ν - 1 / 2 - s / 2

/-- `e₂ = (5/2)θ + r/2 + (5/4)ν − 1/2`. -/
def e2 (θ r ν : ℚ) : ℚ := (5 / 2) * θ + r / 2 + (5 / 4) * ν - 1 / 2

/-- `e₃ = (17/8)θ + (3/4)r + ν − 1/2`. -/
def e3 (θ r ν : ℚ) : ℚ := (17 / 8) * θ + (3 / 4) * r + ν - 1 / 2

/-- **The envelope exponents are the negatives of the restored Type-II gaps.** -/
theorem e_eq_neg_g (θ r s ν : ℚ) :
    e1 θ r s ν = -g1 θ r s ν ∧ e2 θ r ν = -g2 θ r ν ∧ e3 θ r ν = -g3 θ r ν := by
  refine ⟨?_, ?_, ?_⟩ <;> simp only [e1, e2, e3, g1, g2, g3] <;> ring

section rpow
variable {x : ℝ} (hx : 0 < x) (θ r s ν : ℝ)
include hx

/-- Term 1: `Q³ R N / √(x S) = x^{3θ + r + ν − 1/2 − s/2}`. -/
theorem term1_eq :
    (x ^ θ) ^ (3 : ℕ) * x ^ r * x ^ ν / Real.sqrt (x * x ^ s) =
      x ^ (3 * θ + r + ν - 1 / 2 - s / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hx.le,
    Real.mul_rpow hx.le (Real.rpow_nonneg hx.le _), ← Real.rpow_mul hx.le,
    ← Real.rpow_add hx, ← Real.rpow_add hx, ← Real.rpow_add hx, ← Real.rpow_sub hx]
  congr 1; push_cast; ring

/-- Term 2: `Q^{5/2} R^{1/2} N^{5/4} / √x = x^{(5/2)θ + r/2 + (5/4)ν − 1/2}`. -/
theorem term2_eq :
    (x ^ θ) ^ (5 / 2 : ℝ) * (x ^ r) ^ (1 / 2 : ℝ) * (x ^ ν) ^ (5 / 4 : ℝ) / Real.sqrt x =
      x ^ ((5 / 2) * θ + r / 2 + (5 / 4) * ν - 1 / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hx.le, ← Real.rpow_mul hx.le, ← Real.rpow_mul hx.le,
    ← Real.rpow_add hx, ← Real.rpow_add hx, ← Real.rpow_sub hx]
  congr 1; ring

/-- Term 3: `Q^{17/8} R^{3/4} N / √x = x^{(17/8)θ + (3/4)r + ν − 1/2}`. -/
theorem term3_eq :
    (x ^ θ) ^ (17 / 8 : ℝ) * (x ^ r) ^ (3 / 4 : ℝ) * x ^ ν / Real.sqrt x =
      x ^ ((17 / 8) * θ + (3 / 4) * r + ν - 1 / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hx.le, ← Real.rpow_mul hx.le,
    ← Real.rpow_add hx, ← Real.rpow_add hx, ← Real.rpow_sub hx]
  congr 1; ring

end rpow

/-- The envelope `x^{e₁} + x^{e₂} + x^{e₃}` (rational exponents cast to `ℝ`). -/
noncomputable def envelope (θ r s ν : ℚ) (x : ℝ) : ℝ :=
  x ^ ((e1 θ r s ν : ℚ) : ℝ) + x ^ ((e2 θ r ν : ℚ) : ℝ) + x ^ ((e3 θ r ν : ℚ) : ℝ)

/-- If all three gaps are `≥ m`, then for `x ≥ 1` the envelope is `≤ 3 x^{−m}`. -/
theorem envelope_le {θ r s ν m : ℚ} (h1 : m ≤ g1 θ r s ν) (h2 : m ≤ g2 θ r ν)
    (h3 : m ≤ g3 θ r ν) {x : ℝ} (hx : 1 ≤ x) :
    envelope θ r s ν x ≤ 3 * x ^ (-(m : ℝ)) := by
  obtain ⟨E1, E2, E3⟩ := e_eq_neg_g θ r s ν
  have k : ∀ e : ℚ, e ≤ -m → x ^ (e : ℝ) ≤ x ^ (-(m : ℝ)) := fun e he =>
    Real.rpow_le_rpow_of_exponent_le hx (by exact_mod_cast he)
  have a := k (e1 θ r s ν) (by rw [E1]; linarith)
  have b := k (e2 θ r ν) (by rw [E2]; linarith)
  have c := k (e3 θ r ν) (by rw [E3]; linarith)
  unfold envelope; linarith

theorem envelope_nonneg (θ r s ν : ℚ) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ envelope θ r s ν x := by
  unfold envelope; positivity

/-! ## Layer B: exact finite compatible-cell / Cauchy factors -/

/-- **Cauchy–Schwarz over the compatible classes**: `(∑ f)² ≤ d · ∑ f²` (the factor is the exact
count `d`, not `|k| d`). -/
theorem cauchy_compatible_factor (I : TypeIIInterface) (hk : I.k ≠ 0) (f : ℕ → ℝ) :
    (∑ α ∈ I.detectorClasses, f α) ^ 2 ≤ I.d * ∑ α ∈ I.detectorClasses, f α ^ 2 := by
  have := sq_sum_le_card_mul_sum_sq (s := I.detectorClasses) (f := f)
  rw [I.detectorClasses_card hk] at this
  exact this

/-! ## Layer C: the explicit external spectral provider -/

/-- **The restored Type-II spectral provider** (external analytic input; never constructed from
nothing).  `Ehigh`, `Elow`, `Ediag` are the high-H, low-H and diagonal contributions to the
normalized error `R11_rest / (x N / S)`; `K` stands for `C^{O(1)}` and `ε` for the `x^ε` loss. -/
structure RestoredTypeIISpectralProvider (Ehigh Elow Ediag : ℝ → ℝ) (θ r s ν : ℚ) (K ε : ℝ) :
    Prop where
  K_nonneg : 0 ≤ K
  highH_bound : ∀ x : ℝ, 1 ≤ x → |Ehigh x| ≤ K * x ^ ε * envelope θ r s ν x
  lowH_bound : ∀ x : ℝ, 1 ≤ x → |Elow x| ≤ K * x ^ ε * envelope θ r s ν x
  diagonal_bound : ∀ x : ℝ, 1 ≤ x → |Ediag x| ≤ K * x ^ ε * envelope θ r s ν x

/-- **Restored Type-II bound from the provider** (visibly depends on it): if all three gaps are
`≥ m`, then `|Ehigh + Elow + Ediag| ≤ 9K · x^{ε − m}` for `x ≥ 1`. -/
theorem restoredTypeII_of_provider {Ehigh Elow Ediag : ℝ → ℝ} {θ r s ν m : ℚ} {K ε : ℝ}
    (hP : RestoredTypeIISpectralProvider Ehigh Elow Ediag θ r s ν K ε)
    (h1 : m ≤ g1 θ r s ν) (h2 : m ≤ g2 θ r ν) (h3 : m ≤ g3 θ r ν) {x : ℝ} (hx : 1 ≤ x) :
    |Ehigh x + Elow x + Ediag x| ≤ 9 * K * x ^ (ε - m) := by
  have hx0 : 0 < x := by linarith
  have henv := envelope_le h1 h2 h3 hx
  have hKx : 0 ≤ K * x ^ ε := mul_nonneg hP.K_nonneg (Real.rpow_nonneg hx0.le _)
  have hb : K * x ^ ε * envelope θ r s ν x ≤ K * x ^ ε * (3 * x ^ (-(m : ℝ))) :=
    mul_le_mul_of_nonneg_left henv hKx
  have hsplit : x ^ (ε - m) = x ^ ε * x ^ (-(m : ℝ)) := by
    rw [sub_eq_add_neg, Real.rpow_add hx0]
  have a := hP.highH_bound x hx
  have b := hP.lowH_bound x hx
  have c := hP.diagonal_bound x hx
  calc |Ehigh x + Elow x + Ediag x| ≤ |Ehigh x| + |Elow x| + |Ediag x| := by
        have := abs_add_le (Ehigh x + Elow x) (Ediag x)
        have := abs_add_le (Ehigh x) (Elow x)
        linarith
    _ ≤ 3 * (K * x ^ ε * (3 * x ^ (-(m : ℝ)))) := by linarith
    _ = 9 * K * x ^ (ε - m) := by rw [hsplit]; ring

/-- **Concrete Case II power saving from the provider**: on every actual Case-II box with
`1/8 ≤ ν ≤ 1/4`, the restored Type-II error is `≤ 9K · x^{ε − 1/208}`. -/
theorem caseII_powerSaving_of_provider {Ehigh Elow Ediag : ℝ → ℝ} {θ r s ν : ℚ} {K ε : ℝ}
    (hbox : CaseIIBox ν θ r s) (hν1 : 1 / 8 ≤ ν) (hν2 : ν ≤ 1 / 4)
    (hP : RestoredTypeIISpectralProvider Ehigh Elow Ediag θ r s ν K ε) {x : ℝ} (hx : 1 ≤ x) :
    |Ehigh x + Elow x + Ediag x| ≤ 9 * K * x ^ (ε - ((1 / 208 : ℚ) : ℝ)) := by
  obtain ⟨a, b, c⟩ := all_gaps_ge hbox hν1 hν2
  exact restoredTypeII_of_provider hP a b c hx

/-- The zero-error model inhabits the provider (non-vacuity only; says nothing about the actual
arithmetic error terms). -/
theorem spectralProvider_zero (θ r s ν : ℚ) (ε : ℝ) :
    RestoredTypeIISpectralProvider (fun _ => 0) (fun _ => 0) (fun _ => 0) θ r s ν 0 ε :=
  ⟨le_rfl, fun _ _ => by simp, fun _ _ => by simp, fun _ _ => by simp⟩

/-- **Firewall: Type-II geometry does not construct the spectral provider.**  At a concrete
Case-II box (where all the §10 margins hold), a large error function violates the provider for
every constant `K` and loss `ε`. -/
theorem spectralProvider_not_automatic :
    CaseIIBox (1 / 4) 0 (rStar (1 / 4)) (sStar (1 / 4)) ∧
    ∀ K ε : ℝ, ¬ RestoredTypeIISpectralProvider
      (fun x => (K + 1) * x ^ ε * envelope 0 (rStar (1 / 4)) (sStar (1 / 4)) (1 / 4) x + 1)
      (fun _ => 0) (fun _ => 0) 0 (rStar (1 / 4)) (sStar (1 / 4)) (1 / 4) K ε := by
  refine ⟨⟨le_rfl, theta0_pos.le, ?_, le_rfl, ?_, le_rfl, ?_⟩, ?_⟩
  · unfold rStar; rw [lam_eq, zeta_eq]; norm_num
  · unfold sStar; rw [zeta_eq]; norm_num
  · unfold smallBV rStar sStar; rw [lam_eq, zeta_eq]; norm_num
  · intro K ε hP
    have h := hP.highH_bound 1 le_rfl
    have hK := hP.K_nonneg
    have he := envelope_nonneg 0 (rStar (1 / 4)) (sStar (1 / 4)) (1 / 4) (x := 1) zero_le_one
    simp only [Real.one_rpow, mul_one] at h
    rw [abs_of_nonneg (by positivity)] at h
    nlinarith

/-! ## §7 High-H / low-H: concrete cost comparison (exact algebra) -/

/-- The Type-II index map `(u, v, w) = (C q₁ n₂ n₂', q₂, a k (h n₂' − h' n₂))` (V10). -/
theorem indexMap_concrete (x : ResearchBankV10.TypeIICoefficient.CoeffVars) :
    ResearchBankV10.TypeIICoefficient.indexMap x =
      (x.C * x.q₁ * x.n₂ * x.n₂', x.q₂, x.a * x.k * (x.h * x.n₂' - x.h' * x.n₂)) := rfl

/-- Low-H collapse `w = a k h (n₂' − n₂)` when `h = h'`. -/
theorem lowH_index (a k h n₂ n₂' : ℤ) : a * k * (h * n₂' - h * n₂) = a * k * h * (n₂' - n₂) :=
  ResearchBankV10.TypeIIHighLow.lowH_w_eq a k h n₂ n₂'

/-- The high-H coefficient-norm skeleton `Q⁻² N² H² + K N H³ + N² H + K N Q² H²`. -/
noncomputable def highHNorm (Q N H K : ℝ) : ℝ :=
  Q⁻¹ ^ 2 * N ^ 2 * H ^ 2 + K * N * H ^ 3 + N ^ 2 * H + K * N * Q ^ 2 * H ^ 2

/-- The low-H coefficient-norm skeleton `H N²`. -/
def lowHNorm (H N : ℝ) : ℝ := H * N ^ 2

/-- The leading high-H term is at most the whole skeleton (all terms nonnegative). -/
theorem leading_le_highHNorm {Q N H K : ℝ} (hN : 0 ≤ N) (hH : 0 ≤ H) (hK : 0 ≤ K) :
    Q⁻¹ ^ 2 * N ^ 2 * H ^ 2 ≤ highHNorm Q N H K := by
  unfold highHNorm; have : 0 ≤ K * N * H ^ 3 := by positivity
  have : 0 ≤ N ^ 2 * H := by positivity
  have : 0 ≤ K * N * Q ^ 2 * H ^ 2 := by positivity
  linarith

/-- **Complete prefactor comparison**: with the prefactor relation `P_lo · C Q² = P_hi · H`,
`(P_lo/P_hi)² · (H N²)/(Q⁻² N² H²) = H/(C² Q²)`. -/
theorem prefactor_comparison {Plo Phi H N Q C : ℝ} (hPhi : Phi ≠ 0) (hH : H ≠ 0) (hN : N ≠ 0)
    (hQ : Q ≠ 0) (hC : C ≠ 0) (hrel : Plo * (C * Q ^ 2) = Phi * H) :
    (Plo / Phi) ^ 2 * (lowHNorm H N / (Q⁻¹ ^ 2 * N ^ 2 * H ^ 2)) = H / (C ^ 2 * Q ^ 2) :=
  ResearchBankV10.TypeIIHighLow.lowH_cost_identity hPhi hH hN hQ hC hrel

/-- Under `H < Q²` and `1 ≤ C`: `H/(C² Q²) < 1`. -/
theorem lowH_cheaper {H Q C : ℝ} (hQ : Q ≠ 0) (hHQ : H < Q ^ 2) (hC : 1 ≤ C) :
    H / (C ^ 2 * Q ^ 2) < 1 :=
  ResearchBankV10.TypeIIHighLow.lowH_cost_lt_one hQ hHQ hC

/-- **Diagonal comparison**: under `H < Q²` and `1 ≤ C`: `H/(C Q²) < 1`. -/
theorem diagonal_cheaper {H Q C : ℝ} (hQ : Q ≠ 0) (hHQ : H < Q ^ 2) (hC : 1 ≤ C) :
    H / (C * Q ^ 2) < 1 := by
  have hQ2 : 0 < Q ^ 2 := by positivity
  rw [div_lt_one (by positivity)]
  nlinarith

/-- **Regression fixture 3**: a smaller coefficient norm without the prefactor does not give a
smaller cost; with the wrong prefactor `P_lo = P_hi` the low-H route would *fail*. -/
theorem lowH_without_prefactor_fails :
    (¬ ∀ Plo Phi nlo nhi : ℝ, 0 < Plo → 0 < Phi → 0 < nlo → nlo < nhi →
      Plo ^ 2 * nlo < Phi ^ 2 * nhi) ∧
    ∀ {P H N Q : ℝ}, P ≠ 0 → 0 < H → N ≠ 0 → Q ≠ 0 → H < Q ^ 2 →
      1 < (P / P) ^ 2 * (lowHNorm H N / (Q⁻¹ ^ 2 * N ^ 2 * H ^ 2)) :=
  ⟨ResearchBankV10.TypeIIHighLow.smaller_norm_insufficient,
    fun hP hH hN hQ hHQ => ResearchBankV10.TypeIIHighLow.wrong_prefactor_fails hP hH hN hQ hHQ⟩

end RestoredTypeIIEnvelope
end ResearchBankV12
end Erdos287
