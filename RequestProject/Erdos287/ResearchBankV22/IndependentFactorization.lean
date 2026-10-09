import RequestProject.Erdos287.ResearchBankV22.CellColouring

/-!
# Erdős #287 — Research Bank V22 §8: independent coefficient factorization

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

The small-prime factor is placed into the FIRST bin:

    Λ_ω = (β_sm^+ ⋆ G_{0,ω}) ⋆ (G_{1,ω} ⋆ G_{2,ω}).

Kernel-proved (LEAN BANK):
* `conv_assoc_disjoint` — associativity of `⋆` for weights on pairwise disjoint universes;
* **`beta_G0_oneBounded`** — `|β_sm^+ ⋆ G_0| ≤ 1` (disjoint smooth/rough support; uses only the
  one-boundedness of `β` from the `SmallPrimeRosserProvider` contract);
* `G1_G2_oneBounded`, `G1_G2_rough` — the second factor is one-bounded and rough-supported;
* **`coloured_weight_source_contract`** — for every colouring `ω`, `Λ_ω = g ⋆ h` with `g`, `h`
  one-bounded, `g` supported on (small ∪ rough) primes and `h` on rough primes: the V16-style
  bilinear source shape `λ(r) = Σ_{uv=r} g(u) h(v)` — proved from the collapse lemma, NOT merely
  from a factorization of the integer support;
* **`colouring_factorization_identity`** — `β ⋆ 1_{cell pattern} = π^{-1} E_ω[Λ_ω]`.

Firewall (FINITE REGRESSION):
* **`literal_cell_convolution_multiplicity_two`** — the literal cell-indicator convolution
  `(1_C ⋆ 1_C)(143) = 2` for the cell `C = {11, 13}`: the old multiplicity-two error;
* `colour_convolution_le_one` — the coloured convolution is always `≤ 1`.
-/

namespace Erdos287
namespace ResearchBankV22
namespace IndependentFactorization

open Finset RoundedRoughSieve CompletedPositiveWeight CellColouring

section Generic

variable {γ : Type*} [DecidableEq γ]

theorem supportedIn_inter {f : Finset γ → ℝ} {U V : Finset γ} (hU : SupportedIn f U)
    (hV : SupportedIn f V) : SupportedIn f (U ∩ V) :=
  fun A hA => subset_inter (hU A hA) (hV A hA)

/-- **Associativity** of `⋆` on pairwise disjoint universes. -/
theorem conv_assoc_disjoint {f g h : Finset γ → ℝ} {U1 U2 U3 : Finset γ}
    (hf : SupportedIn f U1) (hg : SupportedIn g U2) (hh : SupportedIn h U3)
    (d12 : Disjoint U1 U2) (d13 : Disjoint U1 U3) (d23 : Disjoint U2 U3) :
    conv f (conv g h) = conv (conv f g) h := by
  funext A
  rw [conv_collapse hf (conv_supported hg hh) (disjoint_union_right.2 ⟨d12, d13⟩),
    conv_collapse (conv_supported hf hg) hh (disjoint_union_left.2 ⟨d13, d23⟩),
    conv_collapse hg hh d23, conv_collapse hf hg d12]
  rw [if_pos inter_subset_right, if_pos inter_subset_right]
  have e1 : A ∩ (U2 ∪ U3) ∩ U2 = A ∩ (U1 ∪ U2) ∩ U2 := by
    ext p; simp only [mem_inter, mem_union]; tauto
  have e2 : A ∩ (U2 ∪ U3) ∩ U3 = A ∩ U3 := by
    ext p; simp only [mem_inter, mem_union]; tauto
  have e3 : A ∩ U1 = A ∩ (U1 ∪ U2) ∩ U1 := by
    ext p; simp only [mem_inter, mem_union]; tauto
  rw [e1, e2, ← e3, show U1 ∪ (U2 ∪ U3) = U1 ∪ U2 ∪ U3 from (union_assoc _ _ _).symm]
  split_ifs <;> ring

/-- The bilinear source-class coefficient shape `λ = g ⋆ h`, `g, h` one-bounded,
`g` on `Us ∪ Ur`, `h` on the rough universe `Ur`. -/
def SourceFactorization (lam : Finset γ → ℝ) (Us Ur : Finset γ) : Prop :=
  ∃ g h : Finset γ → ℝ, OneBounded g ∧ OneBounded h ∧ SupportedIn g (Us ∪ Ur) ∧
    SupportedIn h Ur ∧ lam = conv g h

end Generic

section Coloured

variable {α J : Type*} [Fintype α] [DecidableEq α] [Fintype J] [DecidableEq J]
  (cell : α → J) (Us Ur : Finset α) (kbin : Fin 3 → J → ℕ) (β : Finset α → ℝ)

/-- The coloured completed coefficient `Λ_ω = (β ⋆ G_0) ⋆ (G_1 ⋆ G_2)`. -/
noncomputable def colouredWeight (ω : α → Fin 3) : Finset α → ℝ :=
  conv (conv β (G cell Ur kbin 0 ω)) (conv (G cell Ur kbin 1 ω) (G cell Ur kbin 2 ω))

variable {Us Ur β}

/-- **`|β ⋆ G_0| ≤ 1`**. -/
theorem beta_G0_oneBounded (hβ : SupportedIn β Us) (hβ1 : OneBounded β) (hd : Disjoint Us Ur)
    (ω : α → Fin 3) : OneBounded (conv β (G cell Ur kbin 0 ω)) :=
  conv_oneBounded_of_disjoint hβ (G_supported_rough cell Ur kbin 0 ω) hd hβ1
    (G_oneBounded cell Ur kbin 0 ω)

theorem G1_G2_oneBounded (ω : α → Fin 3) :
    OneBounded (conv (G cell Ur kbin 1 ω) (G cell Ur kbin 2 ω)) :=
  conv_oneBounded_of_disjoint (G_supported cell Ur kbin 1 ω) (G_supported cell Ur kbin 2 ω)
    (colourClass_disjoint ω (by decide)) (G_oneBounded cell Ur kbin 1 ω)
    (G_oneBounded cell Ur kbin 2 ω)

theorem G1_G2_rough (ω : α → Fin 3) :
    SupportedIn (conv (G cell Ur kbin 1 ω) (G cell Ur kbin 2 ω)) Ur := by
  have := conv_supported (G_supported_rough cell Ur kbin 1 ω)
    (G_supported_rough cell Ur kbin 2 ω)
  rwa [union_self] at this

/-- **The coloured weight has the bilinear source-class shape.** -/
theorem coloured_weight_source_contract (hβ : SupportedIn β Us) (hβ1 : OneBounded β)
    (hd : Disjoint Us Ur) (ω : α → Fin 3) :
    SourceFactorization (colouredWeight cell Ur kbin β ω) Us Ur :=
  ⟨_, _, beta_G0_oneBounded cell kbin hβ hβ1 hd ω, G1_G2_oneBounded cell kbin ω,
    conv_supported hβ (G_supported_rough cell Ur kbin 0 ω), G1_G2_rough cell kbin ω, rfl⟩

theorem colourConv_supported (ω : α → Fin 3) :
    SupportedIn (colourConv cell Ur kbin ω) (Ur ∩ (colourClass ω 0 ∪ (colourClass ω 1 ∪
      colourClass ω 2))) := by
  unfold colourConv
  refine supportedIn_inter ?_ ?_
  · have := conv_supported (G_supported_rough cell Ur kbin 0 ω)
      (conv_supported (G_supported_rough cell Ur kbin 1 ω) (G_supported_rough cell Ur kbin 2 ω))
    simpa using this
  · exact conv_supported (G_supported cell Ur kbin 0 ω)
      (conv_supported (G_supported cell Ur kbin 1 ω) (G_supported cell Ur kbin 2 ω))

/-- `β ⋆ colourConv = (β ⋆ G_0) ⋆ (G_1 ⋆ G_2)` (associativity on disjoint universes). -/
theorem colouredWeight_eq (hβ : SupportedIn β Us) (hd : Disjoint Us Ur) (ω : α → Fin 3) :
    conv β (colourConv cell Ur kbin ω) = colouredWeight cell Ur kbin β ω := by
  unfold colourConv colouredWeight
  refine conv_assoc_disjoint hβ
    (supportedIn_inter (G_supported_rough cell Ur kbin 0 ω) (G_supported cell Ur kbin 0 ω))
    (supportedIn_inter (G1_G2_rough cell kbin ω)
      (conv_supported (G_supported cell Ur kbin 1 ω) (G_supported cell Ur kbin 2 ω))) ?_ ?_ ?_
  · exact disjoint_of_subset_right inter_subset_left hd
  · exact disjoint_of_subset_right inter_subset_left hd
  · rw [disjoint_left]
    intro p hp hp'
    simp only [mem_inter, mem_union, colourClass, mem_filter, mem_univ, true_and] at hp hp'
    rcases hp'.2 with h | h <;> rw [hp.2] at h <;> exact absurd h (by decide)

open Classical in
/-- **Exact factorization identity**: `(β ⋆ 1_{cell pattern})(A) = π^{-1} E_ω[Λ_ω(A)]`. -/
theorem colouring_factorization_identity (hβ : SupportedIn β Us) (hd : Disjoint Us Ur)
    (A : Finset α) :
    conv β (fun B => if CellPattern cell Ur kbin B then (1 : ℝ) else 0) A =
      (piConst kbin)⁻¹ * colourExp (fun ω => colouredWeight cell Ur kbin β ω A) := by
  simp_rw [← colouredWeight_eq cell kbin hβ hd]
  unfold conv colourExp
  simp_rw [exact_colouring_identity cell Ur kbin]
  unfold colourExp
  simp only [Finset.mul_sum, Finset.sum_div]
  rw [Finset.sum_comm (s := (univ : Finset (α → Fin 3)))]
  refine sum_congr rfl fun B _ => sum_congr rfl fun ω _ => ?_
  ring

end Coloured

/-! ### Firewall: the literal cell-indicator convolution -/

/-- The literal indicator of the cell `C = {11, 13}` (primes in `[11, 13]`). -/
def literalCellInd (n : ℕ) : ℕ := if Nat.Prime n ∧ 11 ≤ n ∧ n ≤ 13 then 1 else 0

/-- Literal Dirichlet convolution over `ℕ`. -/
def literalConv (f g : ℕ → ℕ) (n : ℕ) : ℕ := ∑ ab ∈ n.divisorsAntidiagonal, f ab.1 * g ab.2

/-- **Firewall**: the literal cell-indicator convolution counts `143 = 11·13 = 13·11` twice. -/
theorem literal_cell_convolution_multiplicity_two :
    literalConv literalCellInd literalCellInd 143 = 2 := by decide

/-- The coloured convolution never exceeds one. -/
theorem colour_convolution_le_one {α J : Type*} [Fintype α] [DecidableEq α] [Fintype J]
    [DecidableEq J] (cell : α → J) (Ur : Finset α) (kbin : Fin 3 → J → ℕ) (ω : α → Fin 3)
    (A : Finset α) : colourConv cell Ur kbin ω A ≤ 1 := by
  rw [colourConv_eq]; split_ifs <;> norm_num

end IndependentFactorization
end ResearchBankV22
end Erdos287
