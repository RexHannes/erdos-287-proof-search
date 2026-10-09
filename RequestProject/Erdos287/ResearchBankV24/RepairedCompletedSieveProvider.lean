import RequestProject.Erdos287.ResearchBankV22.IndependentFactorization
import RequestProject.Erdos287.ResearchBankV22.RosserCostProvider
import RequestProject.Erdos287.ResearchBankV22.SmallPrimeUpperSieve
import RequestProject.Erdos287.ResearchBankV23.PrincipalBudget
import RequestProject.Erdos287.ResearchBankV23.HatApproximationProvider

/-!
# Erdős #287 — Research Bank V24 §1: the repaired completed-sieve provider and the V16
# coefficient contract

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

## Part A — the coefficient contract (LEAN BANK)

* `SourceDecomposition λ Us Ur Cm` — `λ` is a finite linear combination `Σ_i c_i g_i` of
  coefficients `g_i` in the V16 bilinear source class (`SourceFactorization`: `g_i = u ⋆ v`,
  `u, v` one-bounded, `u` on `Us ∪ Ur`, `v` on the rough universe `Ur`), with coefficient mass
  `Σ_i |c_i| ≤ Cm`;
* `CountDetermined cell Ur ℓ` — the rough coefficient depends only on the cell-count vector
  (the rounded endpoints are cell endpoints);
* `pattern_representation` — a count-determined rough coefficient is EXACTLY a finite
  combination of cell-pattern indicators;
* `coloured_source_decomposition` — `β ⋆ ℓ` (`β` one-bounded on the smooth side) has an
  explicit source decomposition with mass `≤ (R+1)^{#cells} · 3^R`, built from the exact
  colouring identity and `coloured_weight_source_contract` (small primes in the FIRST bin, two
  independent rough factors);
* `push` / `push_conv` / `push_pull` — transfer from the finite atom type back to integers
  (atom sets `⊆ ℕ`);
* **`new_completed_weight_matches_V16_contract`** — the ACTUAL completed weight
  `Λ_new^+ = μ_E ⋆ β_sm^+ ⋆ ℓ_rd` (on `ℕ`) satisfies the V16 coefficient contract
  `SourceDecomposition Λ_new^+ (E ∪ Psm) Prd ((R+1)^{#cells} 3^R)`, for any count-determined
  rough factor with at most `R` rough atoms.

## Part B — providers

* `SourceClassDistributionProvider` (EXTERNAL PROVIDER; the inherited V16 analytic
  source-class / prime-distribution theorem, NOT re-proved): the distribution error functional
  is linear and uniformly small on the source class;
* `distribution_error_small` (LEAN CONDITIONAL) — the error of any weight with a bounded source
  decomposition is eventually `≤ ε`;
* **`RepairedCompletedSieveProvider`** — the bundle of ONLY the analytic inputs not kernel-proved
  in V21–V23: `RosserScalarProvider`, `PrimeHarmonicTupleProvider`, `PrincipalEulerProvider`,
  `HatReferenceApproximationProvider`, and the inherited source-class provider.  No finite CRT
  or positivity fact is in it; the small-prime Rosser weight needs no provider (it is
  constructed in V22: `rosserSmallProvider`).
-/

namespace Erdos287
namespace ResearchBankV24
namespace RepairedProvider

open Finset
open ResearchBankV22.RoundedRoughSieve ResearchBankV22.CompletedPositiveWeight
open ResearchBankV22.CellColouring ResearchBankV22.IndependentFactorization
open ResearchBankV22.RosserCostProvider ResearchBankV22.SmallPrimeUpperSieve

/-! ## Part A — the coefficient contract -/

section Defs

variable {γ : Type*} [DecidableEq γ]

/-- **The V16 coefficient contract**: a finite combination of bilinear source-class
coefficients with coefficient mass at most `Cm`. -/
def SourceDecomposition (lam : Finset γ → ℝ) (Us Ur : Finset γ) (Cm : ℝ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (c : ι → ℝ) (g : ι → Finset γ → ℝ),
    (∀ i, SourceFactorization (g i) Us Ur) ∧ (∀ A, lam A = ∑ i, c i * g i A) ∧
      ∑ i, |c i| ≤ Cm

/-- The rough coefficient depends only on the cell-count vector. -/
def CountDetermined {J : Type*} [DecidableEq J] (cell : γ → J) (Ur : Finset γ) (ℓ : Finset γ → ℝ) : Prop :=
  ∀ A B, A ⊆ Ur → B ⊆ Ur →
    (∀ j, (A.filter fun p => cell p = j).card = (B.filter fun p => cell p = j).card) → ℓ A = ℓ B

/-- `⋆` is linear in its second argument. -/
theorem conv_sum_right {ι : Type*} (s : Finset ι) (β : Finset γ → ℝ) (c : ι → ℝ)
    (f : ι → Finset γ → ℝ) (A : Finset γ) :
    conv β (fun B => ∑ k ∈ s, c k * f k B) A = ∑ k ∈ s, c k * conv β (f k) A := by
  unfold conv
  simp only [mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun k _ => sum_congr rfl fun B _ => by ring

end Defs

section Pattern

variable {α J : Type} [Fintype α] [DecidableEq α] [Fintype J] [DecidableEq J]
  (cell : α → J) (Ur : Finset α) (ℓ : Finset α → ℝ)

open Classical in
/-- The finite set of count vectors of rough atom sets carrying a nonzero coefficient. -/
noncomputable def patterns : Finset (J → ℕ) := ((Ur.powerset.filter fun A => ℓ A ≠ 0)).image (cnt cell)

open Classical in
/-- A representative atom set of a count vector. -/
noncomputable def rep (κ : J → ℕ) : Finset α :=
  if h : κ ∈ patterns cell Ur ℓ then (mem_image.1 h).choose else ∅

omit [Fintype α] [DecidableEq α] in
theorem rep_spec {κ : J → ℕ} (h : κ ∈ patterns cell Ur ℓ) :
    rep cell Ur ℓ κ ∈ Ur.powerset.filter (fun A => ℓ A ≠ 0) ∧ cnt cell (rep cell Ur ℓ κ) = κ := by
  unfold rep
  rw [dif_pos h]
  exact (mem_image.1 h).choose_spec

omit [Fintype α] [DecidableEq α] [Fintype J] in
theorem cellPattern_iff (alloc : (J → ℕ) → Fin 3 → J → ℕ)
    (halloc : ∀ κ j, ∑ i, alloc κ i j = κ j) (κ : J → ℕ) (A : Finset α) :
    CellPattern cell Ur (alloc κ) A ↔ A ⊆ Ur ∧ cnt cell A = κ := by
  unfold CellPattern PatCond target
  simp only [halloc]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, funext fun j => (h2 j).symm⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun j => by rw [h2]⟩

omit [Fintype α] [DecidableEq α] in
theorem sum_cnt (A : Finset α) : ∑ j, cnt cell A j = A.card := by
  unfold cnt
  exact (card_eq_sum_card_fiberwise (fun p _ => mem_univ (cell p))).symm

variable {cell Ur ℓ}

omit [Fintype α] in
open Classical in
/-- **Pattern representation**: a count-determined rough coefficient is exactly a finite
combination of cell-pattern indicators. -/
theorem pattern_representation (hsupp : SupportedIn ℓ Ur) (hcd : CountDetermined cell Ur ℓ)
    (alloc : (J → ℕ) → Fin 3 → J → ℕ) (halloc : ∀ κ j, ∑ i, alloc κ i j = κ j)
    (A : Finset α) :
    ℓ A = ∑ κ ∈ patterns cell Ur ℓ,
      ℓ (rep cell Ur ℓ κ) * (if CellPattern cell Ur (alloc κ) A then 1 else 0) := by
  unfold CountDetermined at hcd
  simp_rw [cellPattern_iff cell Ur alloc halloc]
  by_cases hA : A ⊆ Ur
  · simp only [hA, true_and]
    by_cases hmem : cnt cell A ∈ patterns cell Ur ℓ
    · rw [sum_eq_single (cnt cell A) (fun κ _ hκ => by rw [if_neg (Ne.symm hκ), mul_zero])
        (fun h => absurd hmem h), if_pos rfl, mul_one]
      obtain ⟨hr, hc⟩ := rep_spec cell Ur ℓ hmem
      refine hcd _ _ hA (mem_powerset.1 (mem_filter.1 hr).1) fun j => ?_
      have := congrFun hc j
      unfold cnt at this
      exact this.symm
    · have h0 : ℓ A = 0 := by
        by_contra hne
        exact hmem (mem_image.2 ⟨A, mem_filter.2 ⟨mem_powerset.2 hA, hne⟩, rfl⟩)
      rw [h0]
      refine (sum_eq_zero fun κ hκ => ?_).symm
      rw [if_neg (fun h : cnt cell A = κ => hmem (h ▸ hκ)), mul_zero]
  · simp only [hA, false_and, if_false, mul_zero, sum_const_zero]
    by_contra hne
    exact hA (hsupp A hne)

omit [Fintype α] [DecidableEq α] in
theorem patterns_card_le {R : ℕ} (hR : ∀ A, A ⊆ Ur → ℓ A ≠ 0 → A.card ≤ R) :
    (patterns cell Ur ℓ).card ≤ (R + 1) ^ Fintype.card J := by
  have hsub : patterns cell Ur ℓ ⊆ Fintype.piFinset fun _ : J => range (R + 1) := by
    intro κ hκ
    obtain ⟨A, hA, rfl⟩ := mem_image.1 hκ
    rw [mem_filter, mem_powerset] at hA
    rw [Fintype.mem_piFinset]
    intro j
    rw [mem_range, Nat.lt_succ_iff]
    calc cnt cell A j ≤ A.card := card_filter_le _ _
      _ ≤ R := hR A hA.1 hA.2
  calc (patterns cell Ur ℓ).card ≤ (Fintype.piFinset fun _ : J => range (R + 1)).card :=
        card_le_card hsub
    _ = (R + 1) ^ Fintype.card J := by simp [Fintype.card_piFinset]

variable {Us : Finset α} {β : Finset α → ℝ}

open Classical in
/-- **Coloured source decomposition** of `β ⋆ ℓ` (LEAN BANK). -/
theorem coloured_source_decomposition (hβ : SupportedIn β Us) (hβ1 : OneBounded β)
    (hd : Disjoint Us Ur) (hsupp : SupportedIn ℓ Ur) (hℓ1 : OneBounded ℓ)
    (hcd : CountDetermined cell Ur ℓ) (alloc : (J → ℕ) → Fin 3 → J → ℕ)
    (halloc : ∀ κ j, ∑ i, alloc κ i j = κ j) {R : ℕ}
    (hR : ∀ A, A ⊆ Ur → ℓ A ≠ 0 → A.card ≤ R) :
    SourceDecomposition (conv β ℓ) Us Ur (((R + 1) ^ Fintype.card J : ℕ) * 3 ^ R) := by
  set K := patterns cell Ur ℓ
  refine ⟨K × (α → Fin 3), inferInstance,
    fun iω => ℓ (rep cell Ur ℓ iω.1) * (piConst (alloc iω.1))⁻¹ / 3 ^ Fintype.card α,
    fun iω => colouredWeight cell Ur (alloc iω.1) β iω.2, ?_, ?_, ?_⟩
  · intro iω
    exact coloured_weight_source_contract cell (alloc iω.1) hβ hβ1 hd iω.2
  · intro A
    have hrep : ℓ = fun B => ∑ κ ∈ K, ℓ (rep cell Ur ℓ κ) *
        (if CellPattern cell Ur (alloc κ) B then 1 else 0) :=
      funext fun B => pattern_representation hsupp hcd alloc halloc B
    conv_lhs => rw [hrep]
    rw [conv_sum_right, Fintype.sum_prod_type, ← sum_coe_sort K]
    refine sum_congr rfl fun κ _ => ?_
    rw [colouring_factorization_identity cell (alloc κ) hβ hd A]
    unfold colourExp
    simp only [sum_div, mul_sum]
    refine sum_congr rfl fun ω _ => ?_
    ring
  · rw [Fintype.sum_prod_type]
    have h3 : (0 : ℝ) < 3 ^ Fintype.card α := by positivity
    have hinner : ∀ κ : K, ∑ ω : α → Fin 3,
        |ℓ (rep cell Ur ℓ κ) * (piConst (alloc κ))⁻¹ / 3 ^ Fintype.card α| =
        |ℓ (rep cell Ur ℓ κ)| * (piConst (alloc κ))⁻¹ := by
      intro κ
      have hp := piConst_pos (J := J) (alloc κ)
      rw [sum_const, card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul, abs_div,
        abs_mul, abs_of_pos (inv_pos.2 hp), abs_of_pos h3]
      push_cast
      field_simp
    simp_rw [hinner]
    have hle : ∀ κ : K, |ℓ (rep cell Ur ℓ κ)| * (piConst (alloc κ))⁻¹ ≤ 3 ^ R := by
      intro κ
      obtain ⟨hr, hc⟩ := rep_spec cell Ur ℓ κ.2
      rw [mem_filter, mem_powerset] at hr
      have hsum : ∑ j, ∑ i, alloc κ i j ≤ R := by
        simp only [halloc]
        rw [← hc, sum_cnt]
        exact hR _ hr.1 hr.2
      have hpi := piProb_inv_le (J := J) (alloc κ) hsum
      have hp := piConst_pos (J := J) (alloc κ)
      calc |ℓ (rep cell Ur ℓ κ)| * (piConst (alloc κ))⁻¹ ≤ 1 * (piConst (alloc κ))⁻¹ :=
            mul_le_mul_of_nonneg_right (hℓ1 _) (inv_pos.2 hp).le
        _ ≤ 3 ^ R := by rw [one_mul]; exact hpi
    calc ∑ κ : K, |ℓ (rep cell Ur ℓ κ)| * (piConst (alloc κ))⁻¹ ≤ ∑ _κ : K, (3 : ℝ) ^ R :=
          sum_le_sum fun κ _ => hle κ
      _ = (K.card : ℝ) * 3 ^ R := by rw [sum_const, card_univ, Fintype.card_coe, nsmul_eq_mul]
      _ ≤ _ := by
          gcongr
          exact_mod_cast patterns_card_le hR

end Pattern

/-! ### Transfer from a finite atom type back to atom sets of integers -/

section Transfer

variable {γ : Type*} [DecidableEq γ] (V : Finset γ)

/-- Atom sets of `V` as atom sets of `γ`. -/
def emb (A : Finset V) : Finset γ := A.map (Function.Embedding.subtype (· ∈ V))

/-- Push a weight on the finite atom type `V` forward to `γ` (zero off `V`). -/
noncomputable def push (g : Finset V → ℝ) : Finset γ → ℝ := fun A =>
  if A ⊆ V then g (A.subtype (· ∈ V)) else 0

theorem emb_subtype {A : Finset γ} (hA : A ⊆ V) : emb V (A.subtype (· ∈ V)) = A := by
  ext x; simp only [emb, mem_map, mem_subtype, Function.Embedding.coe_subtype]
  constructor
  · rintro ⟨y, hy, rfl⟩; exact hy
  · intro hx; exact ⟨⟨x, hA hx⟩, hx, rfl⟩

theorem subtype_emb (A : Finset V) : (emb V A).subtype (· ∈ V) = A := by
  ext x; simp [emb]

omit [DecidableEq γ] in
theorem emb_subset (A : Finset V) : emb V A ⊆ V := by
  intro x hx; obtain ⟨y, -, rfl⟩ := mem_map.1 hx; exact y.2

variable {V}

theorem push_pull {f : Finset γ → ℝ} (hf : SupportedIn f V) : push V (pull V f) = f := by
  funext A
  unfold push pull
  split_ifs with hA
  · change f (emb V _) = f A; rw [emb_subtype V hA]
  · by_contra h; exact hA (hf A (Ne.symm h))

theorem push_oneBounded {g : Finset V → ℝ} (hg : OneBounded g) : OneBounded (push V g) := by
  intro A; unfold push; split_ifs
  · exact hg _
  · simp

theorem push_supported {g : Finset V → ℝ} {U : Finset V} (hg : SupportedIn g U) :
    SupportedIn (push V g) (emb V U) := by
  intro A hA
  unfold push at hA
  split_ifs at hA with hAV
  · rw [← emb_subtype V hAV]
    exact map_subset_map.2 (hg _ hA)
  · exact absurd rfl hA

theorem push_conv (f g : Finset V → ℝ) : push V (conv f g) = conv (push V f) (push V g) := by
  funext A
  unfold push conv
  by_cases hA : A ⊆ V
  · rw [if_pos hA]
    refine sum_nbij' (fun B => emb V B) (fun B => B.subtype (· ∈ V)) ?_ ?_ ?_ ?_ ?_
    · intro B hB
      rw [mem_powerset] at hB ⊢
      rw [← emb_subtype V hA]; exact map_subset_map.2 hB
    · intro B hB
      rw [mem_powerset] at hB ⊢
      intro x hx; rw [mem_subtype] at hx ⊢; exact hB hx
    · intro B _; exact subtype_emb V B
    · intro B hB
      rw [mem_powerset] at hB
      exact emb_subtype V (hB.trans hA)
    · intro B hB
      dsimp only
      rw [mem_powerset] at hB
      have h1 : emb V B ⊆ V := emb_subset V B
      have h2 : A \ emb V B ⊆ V := sdiff_subset.trans hA
      rw [if_pos h1, if_pos h2, subtype_emb]
      congr 2
      ext x
      simp only [mem_sdiff, mem_subtype, emb, mem_map, Function.Embedding.coe_subtype]
      constructor
      · rintro ⟨hx, hnx⟩; exact ⟨hx, fun ⟨y, hy, hyx⟩ => hnx (Subtype.ext hyx ▸ hy)⟩
      · rintro ⟨hx, hnx⟩; exact ⟨hx, fun hy => hnx ⟨x, hy, rfl⟩⟩
  · rw [if_neg hA]
    refine (sum_eq_zero fun B hB => ?_).symm
    dsimp only
    rw [mem_powerset] at hB
    by_cases h1 : B ⊆ V
    · have h2 : ¬ A \ B ⊆ V := by
        intro h2; apply hA; intro x hx
        by_cases hxB : x ∈ B
        · exact h1 hxB
        · exact h2 (mem_sdiff.2 ⟨hx, hxB⟩)
      rw [if_neg h2, mul_zero]
    · rw [if_neg h1, zero_mul]

theorem push_sum {ι : Type*} [Fintype ι] (c : ι → ℝ) (g : ι → Finset V → ℝ) (A : Finset γ) :
    push V (fun B => ∑ i, c i * g i B) A = ∑ i, c i * push V (g i) A := by
  unfold push; split_ifs <;> simp

theorem push_source {g : Finset V → ℝ} {Us Ur : Finset V} (hg : SourceFactorization g Us Ur) :
    SourceFactorization (push V g) (emb V Us) (emb V Ur) := by
  obtain ⟨u, v, hu, hv, hus, hvs, rfl⟩ := hg
  refine ⟨push V u, push V v, push_oneBounded hu, push_oneBounded hv, ?_, push_supported hvs,
    push_conv u v⟩
  have := push_supported hus
  simpa [emb, map_union] using this

/-- **Transfer of the coefficient contract** along `push`. -/
theorem push_sourceDecomposition {lam : Finset V → ℝ} {Us Ur : Finset V} {Cm : ℝ}
    (h : SourceDecomposition lam Us Ur Cm) :
    SourceDecomposition (push V lam) (emb V Us) (emb V Ur) Cm := by
  obtain ⟨ι, hι, c, g, hg, hlam, hmass⟩ := h
  refine ⟨ι, hι, c, fun i => push V (g i), fun i => push_source (hg i), fun A => ?_, hmass⟩
  have : lam = fun B => ∑ i, c i * g i B := funext hlam
  rw [this, push_sum]

theorem pull_supported {f : Finset γ → ℝ} {U : Finset γ} (hf : SupportedIn f U) :
    SupportedIn (pull V f) (U.subtype (· ∈ V)) := by
  intro A hA x hx
  rw [mem_subtype]
  exact hf _ hA (mem_map_of_mem _ hx)

omit [DecidableEq γ] in
theorem pull_oneBounded {f : Finset γ → ℝ} (hf : OneBounded f) : OneBounded (pull V f) :=
  fun _ => hf _

end Transfer


/-! ### Rounded rough weights are determined by their cell counts -/

section Rounded

variable {γ J : Type*} [LinearOrder γ] [LinearOrder J] [Fintype J] (cell : γ → J)
  (wc : J → ℝ) (X : ℝ)

/-- Generalized admissibility with an accumulated prefix product `P` and parity shift `par`. -/
def AdmGen (P : ℝ) (par : ℕ) (A : Finset γ) : Prop :=
  ∀ p ∈ A, Even ((above A p).card + par) →
    P * (∏ q ∈ above A p, wc (cell q)) * wc (cell p) ^ 3 ≤ X

omit [LinearOrder J] [Fintype J] in
theorem adm_iff_admGen (A : Finset γ) :
    Adm (roundedCond (fun p => wc (cell p)) X) A ↔ AdmGen cell wc X 1 0 A := by
  unfold Adm AdmGen roundedCond; simp

omit [Fintype J] in
theorem above_insert_max {A : Finset γ} (hA : A.Nonempty) {p : γ} (hp : p ∈ A)
    (hne : p ≠ A.max' hA) : above A p = insert (A.max' hA) (above (A.erase (A.max' hA)) p) := by
  ext q
  simp only [above, mem_filter, mem_insert, mem_erase]
  constructor
  · rintro ⟨hq, hlt⟩
    by_cases hqa : q = A.max' hA
    · exact Or.inl hqa
    · exact Or.inr ⟨⟨hqa, hq⟩, hlt⟩
  · rintro (rfl | ⟨⟨-, hq⟩, hlt⟩)
    · exact ⟨A.max'_mem hA, lt_of_le_of_ne (A.le_max' p hp) hne⟩
    · exact ⟨hq, hlt⟩

omit [LinearOrder J] [Fintype J] in
theorem admGen_erase_max {A : Finset γ} (hA : A.Nonempty) (P : ℝ) (par : ℕ) :
    AdmGen cell wc X P par A ↔
      (Even par → P * wc (cell (A.max' hA)) ^ 3 ≤ X) ∧
        AdmGen cell wc X (P * wc (cell (A.max' hA))) (par + 1) (A.erase (A.max' hA)) := by
  set a := A.max' hA
  have habove_a : above A a = ∅ := by
    ext q; simp only [above, mem_filter, notMem_empty, iff_false, not_and, not_lt]
    exact fun hq => A.le_max' q hq
  have hnot : ∀ p, a ∉ above (A.erase a) p := by
    intro p h; simp [above] at h
  have hkey : ∀ p ∈ A, p ≠ a →
      ((above A p).card + par = (above (A.erase a) p).card + (par + 1)) ∧
      P * (∏ q ∈ above A p, wc (cell q)) =
        P * wc (cell a) * ∏ q ∈ above (A.erase a) p, wc (cell q) := by
    intro p hp hne
    rw [above_insert_max hA hp hne, card_insert_of_notMem (hnot p), prod_insert (hnot p)]
    constructor <;> ring
  constructor
  · intro h
    refine ⟨fun hpar => ?_, fun p hp hpar => ?_⟩
    · have := h a (A.max'_mem hA) (by rw [habove_a, card_empty, zero_add]; exact hpar)
      rwa [habove_a, prod_empty, mul_one] at this
    · obtain ⟨hne, hpA⟩ := mem_erase.1 hp
      obtain ⟨hc, hprod⟩ := hkey p hpA hne
      have := h p hpA (by rw [hc]; exact hpar)
      rwa [hprod] at this
  · rintro ⟨h1, h2⟩ p hp hpar
    by_cases hpa : p = a
    · subst hpa
      rw [habove_a, prod_empty, mul_one]
      rw [habove_a, card_empty, zero_add] at hpar
      exact h1 hpar
    · obtain ⟨hc, hprod⟩ := hkey p hp hpa
      rw [hprod]
      exact h2 p (mem_erase.2 ⟨hpa, hp⟩) (by rw [← hc]; exact hpar)

variable {cell}

omit [Fintype J] in
theorem cell_max'_le (hmono : Monotone cell) {A B : Finset γ} (hA : A.Nonempty) (hB : B.Nonempty)
    (hcnt : ∀ j, (A.filter fun p => cell p = j).card = (B.filter fun p => cell p = j).card) :
    cell (A.max' hA) ≤ cell (B.max' hB) := by
  have hpos : 0 < (B.filter fun p => cell p = cell (A.max' hA)).card := by
    rw [← hcnt]; exact card_pos.2 ⟨A.max' hA, mem_filter.2 ⟨A.max'_mem hA, rfl⟩⟩
  obtain ⟨y, hy⟩ := card_pos.1 hpos
  rw [mem_filter] at hy
  rw [← hy.2]
  exact hmono (B.le_max' y hy.1)

omit [Fintype J] in
theorem cnt_erase_eq {A B : Finset γ} {a b : γ} (ha : a ∈ A) (hb : b ∈ B) (hab : cell a = cell b)
    (hcnt : ∀ j, (A.filter fun p => cell p = j).card = (B.filter fun p => cell p = j).card)
    (j : J) : ((A.erase a).filter fun p => cell p = j).card =
      ((B.erase b).filter fun p => cell p = j).card := by
  rw [filter_erase, filter_erase]
  by_cases hj : cell a = j
  · rw [card_erase_of_mem (mem_filter.2 ⟨ha, hj⟩), card_erase_of_mem (mem_filter.2 ⟨hb, hab ▸ hj⟩),
      hcnt]
  · have e1 : a ∉ A.filter (fun p => cell p = j) := fun h => hj (mem_filter.1 h).2
    have e2 : b ∉ B.filter (fun p => cell p = j) := fun h => hj (hab ▸ (mem_filter.1 h).2)
    rw [erase_eq_of_notMem e1, erase_eq_of_notMem e2, hcnt]

omit [LinearOrder γ] in
theorem card_eq_sum_cnt (A : Finset γ) :
    A.card = ∑ j, (A.filter fun p => cell p = j).card :=
  card_eq_sum_card_fiberwise (fun p _ => mem_univ (cell p))

theorem admGen_count (hmono : Monotone cell) :
    ∀ n : ℕ, ∀ A B : Finset γ, A.card = n →
      (∀ j, (A.filter fun p => cell p = j).card = (B.filter fun p => cell p = j).card) →
      ∀ P par, (AdmGen cell wc X P par A ↔ AdmGen cell wc X P par B) := by
  intro n
  induction n with
  | zero =>
    intro A B hA hcnt P par
    have hA0 : A = ∅ := card_eq_zero.1 hA
    have hB0 : B = ∅ := by
      apply card_eq_zero.1
      rw [card_eq_sum_cnt (cell := cell) B, ← sum_congr rfl fun j _ => hcnt j,
        ← card_eq_sum_cnt, hA]
    rw [hA0, hB0]
  | succ n ih =>
    intro A B hA hcnt P par
    have hBc : B.card = n + 1 := by
      rw [card_eq_sum_cnt (cell := cell) B, ← sum_congr rfl fun j _ => hcnt j,
        ← card_eq_sum_cnt, hA]
    have hAn : A.Nonempty := card_pos.1 (by omega)
    have hBn : B.Nonempty := card_pos.1 (by omega)
    have hcell : cell (A.max' hAn) = cell (B.max' hBn) :=
      le_antisymm (cell_max'_le hmono hAn hBn hcnt)
        (cell_max'_le hmono hBn hAn fun j => (hcnt j).symm)
    rw [admGen_erase_max cell wc X hAn, admGen_erase_max cell wc X hBn, hcell]
    have hc' := cnt_erase_eq (A.max'_mem hAn) (B.max'_mem hBn) hcell hcnt
    have hcardA : (A.erase (A.max' hAn)).card = n := by
      rw [card_erase_of_mem (A.max'_mem hAn), hA]; rfl
    rw [ih _ _ hcardA hc']

/-- **Rounded rough weights are count-determined** (LEAN BANK): if the rounded endpoints are
cell endpoints (`w = wc ∘ cell`) and cells are monotone intervals, `ℓ_rd` depends only on the
cell-count vector. -/
theorem ellRd_countDetermined (hmono : Monotone cell) (U : Finset γ) :
    CountDetermined cell U (ellRd U (fun p => wc (cell p)) X) := by
  intro A B hA hB hcnt
  unfold ellRd ellW
  rw [if_pos hA, if_pos hB]
  have hcard : A.card = B.card := by
    rw [card_eq_sum_cnt (cell := cell) A, card_eq_sum_cnt (cell := cell) B]
    exact sum_congr rfl fun j _ => hcnt j
  have hadm : Adm (roundedCond (fun p => wc (cell p)) X) A ↔
      Adm (roundedCond (fun p => wc (cell p)) X) B := by
    rw [adm_iff_admGen, adm_iff_admGen]
    exact admGen_count wc X hmono _ A B rfl hcnt 1 0
  rw [hcard]
  split_ifs with ha hb hb
  · rfl
  · exact absurd (hadm.1 ha) hb
  · exact absurd (hadm.2 hb) ha
  · rfl

end Rounded

section Contract

variable {J : Type} [Fintype J] [DecidableEq J]

open Classical in
/-- **The new completed weight satisfies the V16 coefficient contract** (LEAN BANK).
For the actual `Λ_new^+ = μ_E ⋆ β_sm^+ ⋆ ℓ_rd` on `ℕ` (pairwise disjoint `E`, `Psm`, `Prd`),
whose rounded rough factor is determined by its cell counts and has at most `R` atoms,
`Λ_new^+` is an explicit finite combination of V16 bilinear source-class coefficients
(small primes and `E` in the FIRST factor, two independent rough colour factors), with
coefficient mass `≤ (R+1)^{#cells} · 3^R`. -/
theorem new_completed_weight_matches_V16_contract {E Psm Prd : Finset ℕ} {level X : ℝ}
    {w : ℕ → ℝ} (h1 : Disjoint E Psm) (h2 : Disjoint E Prd) (h3 : Disjoint Psm Prd)
    (cell : ℕ → J) (hcd : CountDetermined cell Prd (ellRd Prd w X))
    (alloc : (J → ℕ) → Fin 3 → J → ℕ) (halloc : ∀ κ j, ∑ i, alloc κ i j = κ j) {R : ℕ}
    (hR : ∀ A, A ⊆ Prd → ellRd Prd w X A ≠ 0 → A.card ≤ R) :
    SourceDecomposition (LambdaNewPlus E Psm Prd level w X) (E ∪ Psm) Prd
      (((R + 1) ^ Fintype.card J : ℕ) * 3 ^ R) := by
  set V := E ∪ Psm ∪ Prd
  set β := conv (muE E) (rosserBeta Psm level)
  set ℓ := ellRd Prd w X
  have hβs : SupportedIn β (E ∪ Psm) := conv_supported (muE_supported E) (ellRd_supported _ _ _)
  have hβ1 : OneBounded β := conv_oneBounded_of_disjoint (muE_supported E)
    (ellRd_supported _ _ _) h1 (fun A => by unfold muE; split_ifs <;> simp)
    (ellRd_oneBounded _ _ _)
  have hℓs : SupportedIn ℓ Prd := ellRd_supported _ _ _
  have hd : Disjoint (E ∪ Psm) Prd := disjoint_union_left.2 ⟨h2, h3⟩
  have hEPV : E ∪ Psm ⊆ V := subset_union_left
  have hPV : Prd ⊆ V := subset_union_right
  -- pull back to the finite atom type `V`
  set Us' : Finset V := (E ∪ Psm).subtype (· ∈ V)
  set Ur' : Finset V := Prd.subtype (· ∈ V)
  have hd' : Disjoint Us' Ur' := by
    rw [disjoint_left]; intro x hx hx'
    rw [mem_subtype] at hx hx'
    exact disjoint_left.1 hd hx hx'
  have hcd' : CountDetermined (fun p : V => cell p) Ur' (pull V ℓ) := by
    unfold CountDetermined at hcd ⊢
    intro A B hA hB hcnt
    unfold pull
    refine hcd _ _ ?_ ?_ fun j => ?_
    · intro x hx; obtain ⟨y, hy, rfl⟩ := mem_map.1 hx; have := hA hy; rw [mem_subtype] at this
      exact this
    · intro x hx; obtain ⟨y, hy, rfl⟩ := mem_map.1 hx; have := hB hy; rw [mem_subtype] at this
      exact this
    · have := hcnt j
      rw [filter_map, filter_map, card_map, card_map]
      convert this using 3
  have hR' : ∀ A, A ⊆ Ur' → pull V ℓ A ≠ 0 → A.card ≤ R := by
    intro A hA hne
    have hsub : emb V A ⊆ Prd := by
      intro x hx; obtain ⟨y, hy, rfl⟩ := mem_map.1 hx; have := hA hy; rw [mem_subtype] at this
      exact this
    have := hR _ hsub hne
    rwa [emb, card_map] at this
  have hdec := coloured_source_decomposition (cell := fun p : V => cell p) (Ur := Ur')
    (ℓ := pull V ℓ) (Us := Us') (β := pull V β) (pull_supported hβs) (pull_oneBounded hβ1) hd'
    (pull_supported hℓs) (pull_oneBounded (ellRd_oneBounded _ _ _)) hcd' alloc halloc hR'
  have hpush := push_sourceDecomposition hdec
  rw [push_conv, push_pull (fun A hA => (hβs A hA).trans hEPV),
    push_pull (fun A hA => (hℓs A hA).trans hPV), emb_subtype V hEPV,
    emb_subtype V hPV] at hpush
  have hΛ : LambdaNewPlus E Psm Prd level w X = conv β ℓ := rfl
  rw [hΛ]
  exact hpush

/-- **The ACTUAL rounded completed weight satisfies the V16 coefficient contract** (LEAN BANK):
with cell-endpoint rounding `w = wc ∘ cell` on monotone cells, no count-determinacy hypothesis
is needed. -/
theorem rounded_completed_weight_matches_V16_contract {J : Type} [LinearOrder J] [Fintype J]
    {E Psm Prd : Finset ℕ} {level X : ℝ} (h1 : Disjoint E Psm) (h2 : Disjoint E Prd)
    (h3 : Disjoint Psm Prd) (cell : ℕ → J) (hmono : Monotone cell) (wc : J → ℝ)
    (alloc : (J → ℕ) → Fin 3 → J → ℕ) (halloc : ∀ κ j, ∑ i, alloc κ i j = κ j) {R : ℕ}
    (hR : ∀ A, A ⊆ Prd → ellRd Prd (fun p => wc (cell p)) X A ≠ 0 → A.card ≤ R) :
    SourceDecomposition (LambdaNewPlus E Psm Prd level (fun p => wc (cell p)) X) (E ∪ Psm) Prd
      (((R + 1) ^ Fintype.card J : ℕ) * 3 ^ R) :=
  new_completed_weight_matches_V16_contract h1 h2 h3 cell (ellRd_countDetermined wc X hmono Prd)
    alloc halloc hR

end Contract

/-! ## Part B — providers -/

/-- **The inherited V16 analytic source-class / prime-distribution provider** (EXTERNAL
PROVIDER; never constructed, NOT re-proved).  `DE M λ` is the distribution error of the
coefficient `λ` at scale `M`; it is linear in `λ` and uniformly small on the bilinear source
class with universes `Us S M`, `Ur S M`. -/
structure SourceClassDistributionProvider (Us Ur : ℕ → ℕ → Finset ℕ)
    (DE : ℕ → (Finset ℕ → ℝ) → ℝ) : Prop where
  linear : ∀ M {ι : Type} [Fintype ι] (c : ι → ℝ) (g : ι → Finset ℕ → ℝ),
    DE M (fun A => ∑ i, c i * g i A) = ∑ i, c i * DE M (g i)
  class_bound : ∀ S : ℕ, ∀ ε > 0, ∃ M₀ : ℕ, ∀ M ≥ M₀, ∀ g : Finset ℕ → ℝ,
    SourceFactorization g (Us S M) (Ur S M) → |DE M g| ≤ ε

/-- **Distribution error of a weight with a bounded source decomposition** (LEAN CONDITIONAL
on the inherited source-class provider). -/
theorem distribution_error_small {Us Ur : ℕ → ℕ → Finset ℕ} {DE : ℕ → (Finset ℕ → ℝ) → ℝ}
    (P : SourceClassDistributionProvider Us Ur DE) (S : ℕ) (lam : ℕ → Finset ℕ → ℝ) {Cm : ℝ}
    (hCm : 0 ≤ Cm) (hdec : ∀ M, SourceDecomposition (lam M) (Us S M) (Ur S M) Cm) :
    ∀ ε > 0, ∃ M₀ : ℕ, ∀ M ≥ M₀, |DE M (lam M)| ≤ ε := by
  intro ε hε
  obtain ⟨M₀, hM₀⟩ := P.class_bound S (ε / (Cm + 1)) (by positivity)
  refine ⟨M₀, fun M hM => ?_⟩
  obtain ⟨ι, hι, c, g, hg, hlam, hmass⟩ := hdec M
  have : lam M = fun A => ∑ i, c i * g i A := funext hlam
  rw [this, P.linear]
  calc |∑ i, c i * DE M (g i)| ≤ ∑ i, |c i * DE M (g i)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |c i| * (ε / (Cm + 1)) := by
        refine sum_le_sum fun i _ => ?_
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hM₀ M hM (g i) (hg i)) (abs_nonneg _)
    _ = (∑ i, |c i|) * (ε / (Cm + 1)) := by rw [sum_mul]
    _ ≤ Cm * (ε / (Cm + 1)) := mul_le_mul_of_nonneg_right hmass (by positivity)
    _ ≤ ε := by
        rw [mul_div_assoc', div_le_iff₀ (by positivity)]
        nlinarith

open ResearchBankV23.PrincipalEuler ResearchBankV23.HatApproximationProvider in
/-- **The repaired completed-sieve provider**: ONLY the analytic inputs not kernel-proved in
V21–V23 (EXTERNAL PROVIDER interfaces).  Finite CRT algebra, positivity, the colouring identity,
the coefficient contract and the rational budget are NOT fields: they are kernel theorems.  The
small-prime Rosser weight is constructed (`rosserSmallProvider`), so no small-prime provider is
needed. -/
structure RepairedCompletedSieveProvider (K : ℕ) (h : ℕ → ℝ) (F : ℝ → ℝ)
    (Psm Prd : ℕ → ℝ → Finset ℕ) (lev X : ℝ → ℝ) (wτ : ℝ → ℝ → ℕ → ℝ) (r : ℕ)
    (Sd : ResearchBankV23.SingularFactors.SingularData) (LF I : ℝ) (S0 N Li : ℕ → ℝ) (phiW : ℝ)
    (model : ℕ → ℕ → PrincipalModel h) (Kh : ℕ) (EAB : ℕ → ℝ) (Us Ur : ℕ → ℕ → Finset ℕ)
    (DE : ℕ → (Finset ℕ → ℝ) → ℝ) where
  rosser : RosserScalarProvider K h F Psm Prd lev X
  tuple : PrimeHarmonicTupleProvider h Prd X wτ
  euler : PrincipalEulerProvider h r Sd LF I S0 N Li phiW model
  hat : HatReferenceApproximationProvider Kh EAB
  source : SourceClassDistributionProvider Us Ur DE

/-- The small-prime upper weight needs no provider: it is constructed (LEAN BANK). -/
theorem small_prime_weight_constructed (Psm : Finset ℕ) (level : ℝ) (hlev : 1 ≤ level)
    (hP : ∀ p ∈ Psm, 1 ≤ p) :
    (rosserSmallProvider Psm level hlev hP).beta = rosserBeta Psm level := rfl

end RepairedProvider
end ResearchBankV24
end Erdos287
