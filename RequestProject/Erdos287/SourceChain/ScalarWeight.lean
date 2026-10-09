import Mathlib

/-!
# Erdős #287 — V100R4 source chain: full scalar weight (finite / convolutional content)

**ERDŐS #287 REMAINS OPEN.  TAIL-287 IS NOT BANKED.**

§5 of the request, with referee repairs R1 and R2 (message-level source: the V100R4 text and
the referee report were not supplied; the conventions below are the ones the request fixes).

Arithmetic functions are Mathlib's `ArithmeticFunction ℝ`, whose product is Dirichlet
convolution.

* **Disjoint prime ranges.**  `LowSmooth z a` (all prime factors `≤ z`) and `HighRough z b`
  (all prime factors `> z`).  `lowHigh_unique`: `a₁ b₁ = a₂ b₂` with `aᵢ` low and `bᵢ` high
  forces `a₁ = a₂`, `b₁ = b₂` — uniqueness of the low/high split.
* **Absorption `Γ₁ = λ_sm^{(r)} * γ₁`** and `abs_Gamma1_le_one`: if `|λ_sm| ≤ 1` is supported on
  low-smooth integers and `|γ₁| ≤ 1` on high-rough integers then `|Γ₁(d)| ≤ 1` for every `d`
  (at most one term of the convolution is non-zero).
* **Full three-factor equality** `scalarWeight_eq_sectors`:
  `λ̃⁺ := ∑_D λ_sm^{(r)} * λ_D = ∑_D Γ₁(D) * γ₂(D) * γ₃(D)` when `λ_D = γ₁ * γ₂ * γ₃` —
  an **equality** (associativity of Dirichlet convolution), not a domination.
* **R2 (one box convention).**  Canonical: Pascadi's fixed disjoint geometric grid with
  `γ(D) = 1`.  `labelled_eq_canonical`: a labelled repeated-box family with weights `1/γ(D)`
  (where `γ(D)` is the number of labels of `D`) sums to exactly the canonical disjoint-grid sum;
  `canonical_gamma_one`: for an injective labelling `γ(D) = 1`.  Only the canonical form is
  used downstream.
* **R1 (parity-sensitive fundamental-lemma routing).**  `parityWeight k` is the upper
  fundamental-lemma weight `λ⁺` for even high-box parity `k` and the lower weight `λ⁻` for odd
  `k`; `parity_sign_routing`: `(-1)^k S(n) ≤ (-1)^k ∑_{d∣n} parityWeight k d`, i.e. after the
  outer sign the routed term is a genuine upper majorant.  No "constant-only positive
  completion" is used.
-/

open scoped BigOperators
open Finset ArithmeticFunction

namespace Erdos287.SourceChain

/-! ### Disjoint low/high prime ranges -/

/-- All prime factors `≤ z`. -/
def LowSmooth (z a : ℕ) : Prop := ∀ p ∈ a.primeFactors, p ≤ z

/-- All prime factors `> z`. -/
def HighRough (z b : ℕ) : Prop := ∀ p ∈ b.primeFactors, z < p

theorem coprime_low_high {z a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hla : LowSmooth z a)
    (hhb : HighRough z b) : Nat.Coprime a b := by
  refine Nat.coprime_of_dvd (fun p hp hpa hpb => ?_)
  have h1 := hla p (Nat.mem_primeFactors.2 ⟨hp, hpa, ha⟩)
  have h2 := hhb p (Nat.mem_primeFactors.2 ⟨hp, hpb, hb⟩)
  omega

/-- **Uniqueness of the low/high split.** -/
theorem lowHigh_unique {z a1 b1 a2 b2 : ℕ} (h : a1 * b1 = a2 * b2) (hne : a1 * b1 ≠ 0)
    (hl1 : LowSmooth z a1) (hh1 : HighRough z b1) (hl2 : LowSmooth z a2)
    (hh2 : HighRough z b2) : a1 = a2 ∧ b1 = b2 := by
  have ha1 : a1 ≠ 0 := left_ne_zero_of_mul hne
  have hb1 : b1 ≠ 0 := right_ne_zero_of_mul hne
  have hne2 : a2 * b2 ≠ 0 := h ▸ hne
  have ha2 : a2 ≠ 0 := left_ne_zero_of_mul hne2
  have hb2 : b2 ≠ 0 := right_ne_zero_of_mul hne2
  have d12 : a1 ∣ a2 :=
    (coprime_low_high ha1 hb2 hl1 hh2).dvd_of_dvd_mul_right ⟨b1, by rw [← h]⟩
  have d21 : a2 ∣ a1 :=
    (coprime_low_high ha2 hb1 hl2 hh1).dvd_of_dvd_mul_right ⟨b2, by rw [h]⟩
  have hEq : a1 = a2 := Nat.dvd_antisymm d12 d21
  refine ⟨hEq, ?_⟩
  subst hEq
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero ha1) h

/-! ### Absorption `Γ₁ = λ_sm * γ₁` and `|Γ₁| ≤ 1` -/

/-- Support on low-smooth integers. -/
def SupportedLow (z : ℕ) (f : ArithmeticFunction ℝ) : Prop := ∀ d, f d ≠ 0 → LowSmooth z d

/-- Support on high-rough integers. -/
def SupportedHigh (z : ℕ) (f : ArithmeticFunction ℝ) : Prop := ∀ d, f d ≠ 0 → HighRough z d

/-- **`|Γ₁| ≤ 1`.**  `Γ₁ = λ_sm * γ₁` with `|λ_sm| ≤ 1` low-supported and `|γ₁| ≤ 1`
high-supported. -/
theorem abs_Gamma1_le_one {z : ℕ} {lam gam : ArithmeticFunction ℝ}
    (hlam : SupportedLow z lam) (hgam : SupportedHigh z gam) (hlam1 : ∀ d, |lam d| ≤ 1)
    (hgam1 : ∀ d, |gam d| ≤ 1) (d : ℕ) : |(lam * gam) d| ≤ 1 := by
  rw [mul_apply]
  by_cases hex : ∃ x ∈ d.divisorsAntidiagonal, lam x.1 * gam x.2 ≠ 0
  · obtain ⟨x, hx, hxne⟩ := hex
    rw [Finset.sum_eq_single_of_mem x hx]
    · rw [abs_mul]
      exact mul_le_one₀ (hlam1 _) (abs_nonneg _) (hgam1 _)
    · intro y hy hyx
      by_contra hyne
      have hx' := Nat.mem_divisorsAntidiagonal.1 hx
      have hy' := Nat.mem_divisorsAntidiagonal.1 hy
      have hl1 := hlam x.1 (left_ne_zero_of_mul hxne)
      have hh1 := hgam x.2 (right_ne_zero_of_mul hxne)
      have hl2 := hlam y.1 (left_ne_zero_of_mul hyne)
      have hh2 := hgam y.2 (right_ne_zero_of_mul hyne)
      obtain ⟨e1, e2⟩ := lowHigh_unique (hx'.1.trans hy'.1.symm) (hx'.1 ▸ hx'.2) hl1 hh1 hl2 hh2
      exact hyx (Prod.ext e1.symm e2.symm)
  · push_neg at hex
    rw [Finset.sum_eq_zero hex, abs_zero]
    exact zero_le_one

/-! ### Full three-factor equality (canonical convention `γ(D) = 1`) -/

/-- Sector data on a finite index set of boxes `D` (canonical disjoint grid): the three
factors `γ₁(D), γ₂(D), γ₃(D)` of `λ_D = γ₁ * γ₂ * γ₃`. -/
structure SectorData (β : Type*) where
  boxes : Finset β
  g1 : β → ArithmeticFunction ℝ
  g2 : β → ArithmeticFunction ℝ
  g3 : β → ArithmeticFunction ℝ

/-- `λ_D = γ₁ * γ₂ * γ₃`. -/
noncomputable def SectorData.lamD {β : Type*} (S : SectorData β) (D : β) :
    ArithmeticFunction ℝ := S.g1 D * S.g2 D * S.g3 D

/-- The complete scalar weight `λ̃⁺ = ∑_D λ_sm^{(r)} * λ_D` (canonical grid, `γ(D) = 1`). -/
noncomputable def scalarWeight {β : Type*} (lamSm : ArithmeticFunction ℝ) (S : SectorData β) :
    ArithmeticFunction ℝ := ∑ D ∈ S.boxes, lamSm * S.lamD D

/-- **Full three-factor equality.**  `λ̃⁺ = ∑_D Γ₁(D) * γ₂(D) * γ₃(D)` with
`Γ₁(D) = λ_sm^{(r)} * γ₁(D)`. -/
theorem scalarWeight_eq_sectors {β : Type*} (lamSm : ArithmeticFunction ℝ) (S : SectorData β) :
    scalarWeight lamSm S = ∑ D ∈ S.boxes, (lamSm * S.g1 D) * S.g2 D * S.g3 D := by
  unfold scalarWeight SectorData.lamD
  refine Finset.sum_congr rfl (fun D _ => ?_)
  rw [mul_assoc, mul_assoc, mul_assoc]

/-- The low/high decomposition `λ_D^{(r)} = λ_sm^{(r)} * λ_D` (definition) and the
absorption bound together: every sector's first factor `Γ₁(D)` has `|Γ₁(D)| ≤ 1`. -/
theorem sectors_Gamma1_bounded {β : Type*} {z : ℕ} (lamSm : ArithmeticFunction ℝ)
    (S : SectorData β) (hlam : SupportedLow z lamSm) (hlam1 : ∀ d, |lamSm d| ≤ 1)
    (hg : ∀ D ∈ S.boxes, SupportedHigh z (S.g1 D) ∧ ∀ d, |S.g1 D d| ≤ 1) :
    ∀ D ∈ S.boxes, ∀ d, |(lamSm * S.g1 D) d| ≤ 1 := fun D hD d =>
  abs_Gamma1_le_one hlam (hg D hD).1 hlam1 (hg D hD).2 d

/-! ### R2: one box convention -/

/-- A labelled (possibly repeated) box family: labels `L` and the box of each label. -/
structure LabelledBoxes (κ β : Type*) [DecidableEq β] where
  labels : Finset κ
  box : κ → β

/-- Multiplicity `γ(D)` = number of labels carrying the box `D`. -/
def LabelledBoxes.gamma {κ β : Type*} [DecidableEq β] (F : LabelledBoxes κ β) (D : β) : ℕ :=
  (F.labels.filter (fun k => F.box k = D)).card

/-- The canonical disjoint grid underlying a labelled family. -/
def LabelledBoxes.grid {κ β : Type*} [DecidableEq β] (F : LabelledBoxes κ β) : Finset β :=
  F.labels.image F.box

/-- **Equivalence of the conventions.**  The labelled sum with weights `1/γ(D)` equals the
canonical disjoint-grid sum with `γ(D) = 1`. -/
theorem labelled_eq_canonical {κ β : Type*} [DecidableEq β] (F : LabelledBoxes κ β)
    (w : β → ℝ) :
    ∑ k ∈ F.labels, w (F.box k) / (F.gamma (F.box k) : ℝ) = ∑ D ∈ F.grid, w D := by
  unfold LabelledBoxes.grid
  rw [← Finset.sum_fiberwise_of_maps_to (s := F.labels) (t := F.labels.image F.box)
    (g := F.box) (fun k hk => Finset.mem_image_of_mem _ hk)]
  refine Finset.sum_congr rfl (fun D hD => ?_)
  have hpos : 0 < F.gamma D := by
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hD
    exact Finset.card_pos.2 ⟨k, Finset.mem_filter.2 ⟨hk, rfl⟩⟩
  rw [Finset.sum_congr rfl (fun k hk => by rw [(Finset.mem_filter.1 hk).2]),
    Finset.sum_const, nsmul_eq_mul]
  unfold LabelledBoxes.gamma
  have : ((F.labels.filter (fun k => F.box k = D)).card : ℝ) ≠ 0 := by
    exact_mod_cast hpos.ne'
  field_simp

/-- For an injective labelling (the canonical disjoint grid) every multiplicity is `1`. -/
theorem canonical_gamma_one {κ β : Type*} [DecidableEq β] (F : LabelledBoxes κ β)
    (hinj : Set.InjOn F.box F.labels) {k : κ} (hk : k ∈ F.labels) : F.gamma (F.box k) = 1 := by
  unfold LabelledBoxes.gamma
  rw [Finset.card_eq_one]
  refine ⟨k, Finset.ext (fun j => ?_)⟩
  simp only [Finset.mem_filter, Finset.mem_singleton]
  exact ⟨fun ⟨hj, he⟩ => hinj hj hk he, by rintro rfl; exact ⟨hk, rfl⟩⟩

/-! ### R1: parity-sensitive fundamental-lemma sign routing -/

/-- Fundamental-lemma pair: `∑_{d∣n} λ⁻(d) ≤ S(n) ≤ ∑_{d∣n} λ⁺(d)` for every `n ≥ 1`. -/
structure FundamentalLemmaPair (S : ℕ → ℝ) where
  lower : ℕ → ℝ
  upper : ℕ → ℝ
  lower_le : ∀ n, 0 < n → ∑ d ∈ n.divisors, lower d ≤ S n
  le_upper : ∀ n, 0 < n → S n ≤ ∑ d ∈ n.divisors, upper d

/-- Even high-box parity uses the upper weight, odd parity the lower weight. -/
noncomputable def parityWeight {S : ℕ → ℝ} (P : FundamentalLemmaPair S) (k : ℕ) : ℕ → ℝ :=
  if Even k then P.upper else P.lower

/-- **R1 sign routing.**  `(-1)^k S(n) ≤ (-1)^k ∑_{d∣n} parityWeight k d`. -/
theorem parity_sign_routing {S : ℕ → ℝ} (P : FundamentalLemmaPair S) (k n : ℕ) (hn : 0 < n) :
    (-1 : ℝ) ^ k * S n ≤ (-1 : ℝ) ^ k * ∑ d ∈ n.divisors, parityWeight P k d := by
  unfold parityWeight
  rcases Nat.even_or_odd k with hk | hk
  · rw [if_pos hk, hk.neg_one_pow, one_mul, one_mul]; exact P.le_upper n hn
  · rw [if_neg (Nat.not_even_iff_odd.2 hk), hk.neg_one_pow]
    linarith [P.lower_le n hn]

end Erdos287.SourceChain
