import RequestProject.Erdos287.ResearchBankV18.ProviderInterfaces

/-!
# Erdős #287 — Research Bank V18 §4: abstract post-centering transfer

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

Kernel-proved algebra (LEAN BANK; the transfer theorems are LEAN CONDITIONAL on the provider
contracts they take as arguments):
* **`multiplier_transfer`** — if a base estimate `B` is stable under arbitrary one-bounded
  coefficient slots, and the colour phase admits a decomposition
  `Ω(m,n) = ∑_λ C_λ f_λ(m) g_λ(n)` with one-bounded `f_λ, g_λ`, then the coloured estimate is
  at most `(∑_λ ‖C_λ‖) · B`;
* `multiplier_transfer_second` — the same for three slots;
* polarization constants: **`polarize_one`** (`4`: one paired complex sequence from nonnegative
  real `[0,1]`-valued sequences), **`polarize_two`** (`16 = 4²`: two paired sequences),
  **`polarize_three`** (`64 = 4³`: three paired sequence groups).

No theorem here asserts that any actual branch instantiates a provider.
-/

namespace Erdos287
namespace ResearchBankV18
namespace PostCenteringTransfer

open ProviderInterfaces

variable {ι κ ρ : Type*} [Fintype ι] [Fintype κ] [Fintype ρ]

theorem bilin_left (K : ι → κ → ℂ) (α : ι → ℂ) (β : κ → ℂ) :
    bilin K α β = ∑ i, α i * ∑ j, β j * K i j := by
  unfold bilin; refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_; ring

theorem bilin_right (K : ι → κ → ℂ) (α : ι → ℂ) (β : κ → ℂ) :
    bilin K α β = ∑ j, β j * ∑ i, α i * K i j := by
  unfold bilin; rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_; ring

theorem trilin_bilin (K : ι → κ → ρ → ℂ) (α : ι → ℂ) (β : κ → ℂ) (γ : ρ → ℂ) :
    trilin K α β γ = bilin (fun i j => ∑ r, γ r * K i j r) α β := by
  unfold trilin bilin; refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun r _ => ?_; ring

theorem trilin_right (K : ι → κ → ρ → ℂ) (α : ι → ℂ) (β : κ → ℂ) (γ : ρ → ℂ) :
    trilin K α β γ = ∑ r, γ r * bilin (fun i j => K i j r) α β := by
  unfold trilin bilin
  calc ∑ i, ∑ j, ∑ r, α i * β j * γ r * K i j r = ∑ i, ∑ r, ∑ j, α i * β j * γ r * K i j r :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ r, ∑ i, ∑ j, α i * β j * γ r * K i j r := Finset.sum_comm
    _ = _ := by
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_; ring

theorem split4 (k : ι → ℂ) (a1 a2 a3 a4 : ι → ℝ) :
    ∑ i, (((a1 i : ℂ) - a2 i) + Complex.I * ((a3 i : ℂ) - a4 i)) * k i =
      (∑ i, (a1 i : ℂ) * k i) - (∑ i, (a2 i : ℂ) * k i) +
        Complex.I * ((∑ i, (a3 i : ℂ) * k i) - (∑ i, (a4 i : ℂ) * k i)) := by
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_; ring

/-- **Multiplier transfer** (two slots). -/
theorem multiplier_transfer {Λ : Type*} [Fintype Λ]
    {K : ι → κ → ℂ} {B : ℝ} (P : MaynardFirstExponentialProvider K B)
    (C : Λ → ℂ) (f : Λ → ι → ℂ) (g : Λ → κ → ℂ) (hf : ∀ l, OneBounded (f l))
    (hg : ∀ l, OneBounded (g l)) (α : ι → ℂ) (β : κ → ℂ) (hα : OneBounded α)
    (hβ : OneBounded β) :
    ‖∑ i, ∑ j, α i * β j * K i j * (∑ l, C l * f l i * g l j)‖ ≤ (∑ l, ‖C l‖) * B := by
  have hsplit : ∑ i, ∑ j, α i * β j * K i j * (∑ l, C l * f l i * g l j) =
      ∑ l, C l * bilin K (fun i => α i * f l i) (fun j => β j * g l j) := by
    unfold bilin
    calc ∑ i, ∑ j, α i * β j * K i j * (∑ l, C l * f l i * g l j)
        = ∑ i, ∑ j, ∑ l, C l * (α i * f l i * (β j * g l j) * K i j) := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun l _ => ?_; ring
      _ = ∑ i, ∑ l, ∑ j, C l * (α i * f l i * (β j * g l j) * K i j) :=
          Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ l, ∑ i, ∑ j, C l * (α i * f l i * (β j * g l j) * K i j) := Finset.sum_comm
      _ = _ := by
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
  rw [hsplit, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
  rw [norm_mul]
  have hαf : OneBounded fun i => α i * f l i := fun i => by
    rw [norm_mul]; exact mul_le_one₀ (hα i) (norm_nonneg _) (hf l i)
  have hβg : OneBounded fun j => β j * g l j := fun j => by
    rw [norm_mul]; exact mul_le_one₀ (hβ j) (norm_nonneg _) (hg l j)
  exact mul_le_mul_of_nonneg_left (P.stable _ _ hαf hβg) (norm_nonneg _)

/-- **Multiplier transfer** (three slots; the phase separates in the first two slots). -/
theorem multiplier_transfer_second {Λ : Type*} [Fintype Λ] {K : ι → κ → ρ → ℂ} {B : ℝ}
    (P : MaynardSecondExponentialProvider K B)
    (C : Λ → ℂ) (f : Λ → ι → ℂ) (g : Λ → κ → ℂ) (hf : ∀ l, OneBounded (f l))
    (hg : ∀ l, OneBounded (g l)) (α : ι → ℂ) (β : κ → ℂ) (γ : ρ → ℂ) (hα : OneBounded α)
    (hβ : OneBounded β) (hγ : OneBounded γ) :
    ‖∑ l, C l * trilin K (fun i => α i * f l i) (fun j => β j * g l j) γ‖ ≤
      (∑ l, ‖C l‖) * B := by
  rw [Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
  rw [norm_mul]
  have hαf : OneBounded fun i => α i * f l i := fun i => by
    rw [norm_mul]; exact mul_le_one₀ (hα i) (norm_nonneg _) (hf l i)
  have hβg : OneBounded fun j => β j * g l j := fun j => by
    rw [norm_mul]; exact mul_le_one₀ (hβ j) (norm_nonneg _) (hg l j)
  exact mul_le_mul_of_nonneg_left (P.stable _ _ _ hαf hβg hγ) (norm_nonneg _)

/-- Nonnegative `[0,1]`-valued real sequences. -/
def UnitInterval (a : ι → ℝ) : Prop := ∀ i, 0 ≤ a i ∧ a i ≤ 1

theorem pos_part_unit {x : ℝ} (h : |x| ≤ 1) : 0 ≤ max x 0 ∧ max x 0 ≤ 1 :=
  ⟨le_max_right _ _, max_le (le_trans (le_abs_self x) h) zero_le_one⟩

theorem neg_part_unit {x : ℝ} (h : |x| ≤ 1) : 0 ≤ max (-x) 0 ∧ max (-x) 0 ≤ 1 :=
  ⟨le_max_right _ _, max_le (le_trans (neg_le_abs x) h) zero_le_one⟩

theorem decomp (z : ℂ) :
    z = ((max z.re 0 : ℝ) : ℂ) - ((max (-z.re) 0 : ℝ) : ℂ) +
      Complex.I * (((max z.im 0 : ℝ) : ℂ) - ((max (-z.im) 0 : ℝ) : ℂ)) := by
  have h1 : max z.re 0 - max (-z.re) 0 = z.re := by
    rcases le_total z.re 0 with h | h
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
  have h2 : max z.im 0 - max (-z.im) 0 = z.im := by
    rcases le_total z.im 0 with h | h
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
  apply Complex.ext <;> simp [h1, h2]

/-- **Polarization, one paired sequence: constant `4`.** -/
theorem polarize_one (k : ι → ℂ) {B : ℝ}
    (h : ∀ a : ι → ℝ, UnitInterval a → ‖∑ i, (a i : ℂ) * k i‖ ≤ B) (z : ι → ℂ)
    (hz : OneBounded z) : ‖∑ i, z i * k i‖ ≤ 4 * B := by
  have hre : ∀ i, |(z i).re| ≤ 1 := fun i => (Complex.abs_re_le_norm _).trans (hz i)
  have him : ∀ i, |(z i).im| ≤ 1 := fun i => (Complex.abs_im_le_norm _).trans (hz i)
  set a1 : ι → ℝ := fun i => max (z i).re 0
  set a2 : ι → ℝ := fun i => max (-(z i).re) 0
  set a3 : ι → ℝ := fun i => max (z i).im 0
  set a4 : ι → ℝ := fun i => max (-(z i).im) 0
  have e : ∑ i, z i * k i = (∑ i, (a1 i : ℂ) * k i) - (∑ i, (a2 i : ℂ) * k i) +
      Complex.I * ((∑ i, (a3 i : ℂ) * k i) - (∑ i, (a4 i : ℂ) * k i)) := by
    rw [← split4]
    refine Finset.sum_congr rfl fun i _ => ?_
    conv_lhs => rw [decomp (z i)]
  have b1 := h a1 fun i => pos_part_unit (hre i)
  have b2 := h a2 fun i => neg_part_unit (hre i)
  have b3 := h a3 fun i => pos_part_unit (him i)
  have b4 := h a4 fun i => neg_part_unit (him i)
  rw [e]
  calc ‖(∑ i, (a1 i : ℂ) * k i) - (∑ i, (a2 i : ℂ) * k i) +
        Complex.I * ((∑ i, (a3 i : ℂ) * k i) - (∑ i, (a4 i : ℂ) * k i))‖
      ≤ ‖(∑ i, (a1 i : ℂ) * k i) - (∑ i, (a2 i : ℂ) * k i)‖ +
        ‖Complex.I * ((∑ i, (a3 i : ℂ) * k i) - (∑ i, (a4 i : ℂ) * k i))‖ := norm_add_le _ _
    _ ≤ (‖∑ i, (a1 i : ℂ) * k i‖ + ‖∑ i, (a2 i : ℂ) * k i‖) +
        (‖∑ i, (a3 i : ℂ) * k i‖ + ‖∑ i, (a4 i : ℂ) * k i‖) := by
        gcongr
        · exact norm_sub_le _ _
        · rw [norm_mul, Complex.norm_I, one_mul]; exact norm_sub_le _ _
    _ ≤ 4 * B := by linarith

/-- **Polarization, two paired sequences: constant `16`.** -/
theorem polarize_two (K : ι → κ → ℂ) {B : ℝ}
    (h : ∀ a : ι → ℝ, ∀ b : κ → ℝ, UnitInterval a → UnitInterval b →
      ‖bilin K (fun i => (a i : ℂ)) (fun j => (b j : ℂ))‖ ≤ B)
    (z : ι → ℂ) (w : κ → ℂ) (hz : OneBounded z) (hw : OneBounded w) :
    ‖bilin K z w‖ ≤ 16 * B := by
  have step1 : ∀ b : κ → ℝ, UnitInterval b → ‖bilin K z (fun j => (b j : ℂ))‖ ≤ 4 * B := by
    intro b hb
    rw [bilin_left]
    exact polarize_one (fun i => ∑ j, (b j : ℂ) * K i j)
      (fun a ha => by rw [← bilin_left]; exact h a b ha hb) z hz
  rw [bilin_right, show (16 : ℝ) * B = 4 * (4 * B) by ring]
  exact polarize_one (fun j => ∑ i, z i * K i j)
    (fun b hb => by rw [← bilin_right]; exact step1 b hb) w hw

/-- **Polarization, three paired sequence groups: constant `64`.** -/
theorem polarize_three (K : ι → κ → ρ → ℂ) {B : ℝ}
    (h : ∀ a : ι → ℝ, ∀ b : κ → ℝ, ∀ c : ρ → ℝ, UnitInterval a → UnitInterval b →
      UnitInterval c →
      ‖trilin K (fun i => (a i : ℂ)) (fun j => (b j : ℂ)) (fun r => (c r : ℂ))‖ ≤ B)
    (z : ι → ℂ) (w : κ → ℂ) (y : ρ → ℂ) (hz : OneBounded z) (hw : OneBounded w)
    (hy : OneBounded y) :
    ‖trilin K z w y‖ ≤ 64 * B := by
  have step : ∀ c : ρ → ℝ, UnitInterval c → ‖trilin K z w (fun r => (c r : ℂ))‖ ≤ 16 * B := by
    intro c hc
    rw [trilin_bilin]
    exact polarize_two _ (fun a b ha hb => by rw [← trilin_bilin]; exact h a b c ha hb hc) z w hz hw
  rw [trilin_right, show (64 : ℝ) * B = 4 * (16 * B) by ring]
  exact polarize_one (fun r => bilin (fun i j => K i j r) z w)
    (fun c hc => by rw [← trilin_right]; exact step c hc) y hy

end PostCenteringTransfer
end ResearchBankV18
end Erdos287
