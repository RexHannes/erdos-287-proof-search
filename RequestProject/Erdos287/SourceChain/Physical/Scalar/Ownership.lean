import RequestProject.Erdos287.SourceChain.Physical.Scalar.LowSieve

/-!
# Erdős #287 — scalar sieve: box ownership and the labelled-tuple convention

**ERDŐS #287 REMAINS OPEN.  TAIL-287 IS NOT BANKED.**

The key combinatorial identity behind the convention `B_P = T_P/γ(P)` (§14, Lichtman §5):
for every `a`,

`∑_{P ∈ 𝐃_J^+} B_P(a) = 1_{a squarefree, all prime factors high, ω(a) = J, ν(a) ∈ 𝐃_J^+}`

where `ν(a)` is the (unique) box vector of `a` — the boxes of its prime factors in decreasing
order (Lichtman's map `ν`, "each integer `p_1 ⋯ p_r` has a unique vector").  This is
`sum_Bcoef_eq_hw`.  Ingredients:

* `Tcount_eq_card_perm` — for good `a`, `T_P(a)` counts the permutations `π` with `ν ∘ π = P`;
* `Tcount_eq_zero` — `T_P(a) = 0` unless `a` is a squarefree product of `J` high primes;
* `perm_count_eq_gamma` — if `ν ∘ π₀ = P` then `#{π : ν ∘ π = P} = γ(P)` (orbit–stabiliser,
  `DomMulAct.stabilizer_card`);
* `eq_of_antitone_comp` — an antitone `P = ν ∘ π` with `ν` antitone forces `P = ν`
  (uniqueness of the nonincreasing ordering, `Tuple.unique_monotone`);
* `boxAdm_nu_iff` — `ν(a) ∈ 𝐃_J^+` (index form) iff the prime-set form `HighAdm`.
-/

open scoped BigOperators
open Finset

namespace Erdos287.Physical.Sieve

/-- Decreasing enumeration `p_1 > p_2 > ⋯ > p_J` of a finite set of naturals. -/
noncomputable def desc (A : Finset ℕ) {J : ℕ} (h : A.card = J) (i : Fin J) : ℕ :=
  A.orderEmbOfFin h i.rev

theorem desc_mem (A : Finset ℕ) {J : ℕ} (h : A.card = J) (i : Fin J) : desc A h i ∈ A :=
  A.orderEmbOfFin_mem h _

theorem desc_lt_iff (A : Finset ℕ) {J : ℕ} (h : A.card = J) {i j : Fin J} :
    desc A h i < desc A h j ↔ j < i := by
  unfold desc
  rw [(A.orderEmbOfFin h).lt_iff_lt, Fin.rev_lt_rev]

theorem desc_strictAnti (A : Finset ℕ) {J : ℕ} (h : A.card = J) : StrictAnti (desc A h) :=
  fun _ _ hij => (desc_lt_iff A h).2 hij

theorem desc_injective (A : Finset ℕ) {J : ℕ} (h : A.card = J) : Function.Injective (desc A h) :=
  (desc_strictAnti A h).injective

theorem desc_surj (A : Finset ℕ) {J : ℕ} (h : A.card = J) {p : ℕ} (hp : p ∈ A) :
    ∃ i, desc A h i = p := by
  have : p ∈ Set.range (A.orderEmbOfFin h) := by rw [Finset.range_orderEmbOfFin]; exact hp
  obtain ⟨j, hj⟩ := this
  exact ⟨j.rev, by simp [desc, hj]⟩

theorem image_desc (A : Finset ℕ) {J : ℕ} (h : A.card = J) : univ.image (desc A h) = A := by
  ext p
  simp only [mem_image, mem_univ, true_and]
  exact ⟨fun ⟨i, hi⟩ => hi ▸ desc_mem A h i, fun hp => desc_surj A h hp⟩

theorem prod_desc {M : Type*} [CommMonoid M] (A : Finset ℕ) {J : ℕ} (h : A.card = J)
    (f : ℕ → M) : ∏ i, f (desc A h i) = ∏ q ∈ A, f q := by
  conv_rhs => rw [← image_desc A h]
  rw [Finset.prod_image (fun x _ y _ hxy => desc_injective A h hxy)]

theorem above_desc (A : Finset ℕ) {J : ℕ} (h : A.card = J) (i : Fin J) :
    above A (desc A h i) = (univ.filter (· < i)).image (desc A h) := by
  ext q
  simp only [above, mem_filter, mem_image, mem_univ, true_and]
  constructor
  · rintro ⟨hq, hlt⟩
    obtain ⟨j, rfl⟩ := desc_surj A h hq
    exact ⟨j, (desc_lt_iff A h).1 hlt, rfl⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨desc_mem A h j, (desc_lt_iff A h).2 hj⟩

theorem card_above_desc (A : Finset ℕ) {J : ℕ} (h : A.card = J) (i : Fin J) :
    (above A (desc A h i)).card = i := by
  rw [above_desc, card_image_of_injective _ (desc_injective A h),
    show univ.filter (· < i) = Finset.Iio i by ext; simp]
  simp

theorem prod_above_desc {M : Type*} [CommMonoid M] (A : Finset ℕ) {J : ℕ} (h : A.card = J)
    (i : Fin J) (f : ℕ → M) :
    ∏ q ∈ above A (desc A h i), f q = ∏ j ∈ univ.filter (· < i), f (desc A h j) := by
  rw [above_desc, Finset.prod_image (fun x _ y _ hxy => desc_injective A h hxy)]

/-- An antitone `P = ν ∘ π` with `ν` antitone forces `P = ν`. -/
theorem eq_of_antitone_comp {J : ℕ} {β : Type*} [LinearOrder β] {ν P : Fin J → β}
    (hν : Antitone ν) (hP : Antitone P) {π : Equiv.Perm (Fin J)} (h : ν ∘ π = P) : P = ν := by
  have h1 : Monotone ((OrderDual.toDual ∘ ν) ∘ π) := by
    rw [Function.comp_assoc, h]; exact hP
  have h2 : Monotone ((OrderDual.toDual ∘ ν) ∘ (Equiv.refl (Fin J) : Equiv.Perm (Fin J))) := by
    simpa using hν
  have := Tuple.unique_monotone h1 h2
  rw [← h]
  funext i
  have := congrFun this i
  simpa using this

/-- If `ν ∘ π₀ = P` then `#{π : ν ∘ π = P} = γ(P) = ∏_b (#P⁻¹(b))!`. -/
theorem perm_count_eq_gamma {J : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] {ν P : Fin J → ι}
    {π₀ : Equiv.Perm (Fin J)} (h0 : ν ∘ π₀ = P) :
    (univ.filter (fun π : Equiv.Perm (Fin J) => ν ∘ π = P)).card =
      ∏ b : ι, (univ.filter (fun i => P i = b)).card.factorial := by
  have hstab := DomMulAct.stabilizer_card P
  have hfib : ∀ b : ι, Fintype.card {i // P i = b} = (univ.filter (fun i => P i = b)).card :=
    fun b => Fintype.card_subtype _
  simp only [hfib] at hstab
  rw [← hstab, ← Fintype.card_subtype]
  refine Fintype.card_congr
    { toFun := fun π => ⟨π₀⁻¹ * π.1, ?_⟩
      invFun := fun g => ⟨π₀ * g.1, ?_⟩
      left_inv := fun π => by ext; simp
      right_inv := fun g => by ext; simp }
  · funext i
    have h1 := congrFun π.2 i
    have h2 := congrFun h0 (π₀⁻¹ (π.1 i))
    simp only [Function.comp_apply, Equiv.Perm.coe_mul, Equiv.Perm.inv_def, Equiv.apply_symm_apply] at h1 h2 ⊢
    rw [← h2, h1]
  · funext i
    have h1 := congrFun g.2 i
    have h2 := congrFun h0 (g.1 i)
    simp only [Function.comp_apply, Equiv.Perm.coe_mul] at h1 h2 ⊢
    rw [h2, h1]

namespace ScalarParams

variable {S : ScalarParams}

/-- The prime-set form of Lichtman's `𝐃_J^+` for the box vector of a set `A` of high primes. -/
def HighAdm (S : ScalarParams) (A : Finset ℕ) : Prop :=
  ∀ p ∈ A, Even (above A p).card →
    (∏ q ∈ above A p, S.boxEnd (S.boxOf q)) * S.boxEnd (S.boxOf p) ^ 3 < S.threshold A.card

/-- Good arguments for `B_P`: squarefree products of `J` high primes. -/
def GoodHigh (S : ScalarParams) (J a : ℕ) : Prop :=
  Squarefree a ∧ (∀ p ∈ a.primeFactors, S.IsHigh p) ∧ a.primeFactors.card = J

open Classical in
/-- **Set form of the high-prime weight**:
`hw_J(a) = 1_{a = p_1 ⋯ p_J squarefree, all p_i high, ν(a) ∈ 𝐃_J^+}`. -/
noncomputable def hw (S : ScalarParams) (J a : ℕ) : ℝ :=
  if S.GoodHigh J a ∧ S.HighAdm a.primeFactors then 1 else 0

/-- The box vector `ν(A)` of a set of high primes (decreasing order). -/
noncomputable def nu (S : ScalarParams) (A : Finset ℕ) {J : ℕ} (h : A.card = J)
    (hA : ∀ p ∈ A, S.IsHigh p) : Fin J → Fin S.H :=
  fun i => ⟨S.boxOf (desc A h i), (boxOf_spec (hA _ (desc_mem A h i))).1⟩

theorem nu_antitone (hS : S.Good) (A : Finset ℕ) {J : ℕ} (h : A.card = J)
    (hA : ∀ p ∈ A, S.IsHigh p) : Antitone (S.nu A h hA) := by
  intro i j hij
  show S.boxOf (desc A h j) ≤ S.boxOf (desc A h i)
  exact boxOf_mono hS (hA _ (desc_mem A h j)) (hA _ (desc_mem A h i))
    ((desc_strictAnti A h).antitone hij)

theorem boxAdm_nu_iff (hS : S.Good) (A : Finset ℕ) {J : ℕ} (h : A.card = J)
    (hA : ∀ p ∈ A, S.IsHigh p) : S.BoxAdm J (S.nu A h hA) ↔ S.HighAdm A := by
  unfold BoxAdm HighAdm
  constructor
  · rintro ⟨-, hc⟩ p hp hev
    obtain ⟨i, rfl⟩ := desc_surj A h hp
    rw [card_above_desc] at hev
    rw [prod_above_desc, h]
    exact hc i hev
  · intro hc
    refine ⟨nu_antitone hS A h hA, fun i hev => ?_⟩
    have := hc (desc A h i) (desc_mem A h i) (by rw [card_above_desc]; exact hev)
    rw [prod_above_desc, h] at this
    exact this

/-- Structure of a labelled tuple: its entries are distinct primes in the boxes. -/
theorem mem_tuples {J : ℕ} {P : Fin J → Fin S.H} {p : Fin J → ℕ} (hp : p ∈ S.tuples J P) :
    Function.Injective p ∧ ∀ i, (p i).Prime ∧ S.InBox (P i) (p i) := by
  classical
  unfold tuples at hp
  rw [mem_filter, Fintype.mem_piFinset] at hp
  exact ⟨hp.2, fun i => (mem_filter.1 (hp.1 i)).2⟩

theorem tuple_prod {J : ℕ} {P : Fin J → Fin S.H} {p : Fin J → ℕ}
    (hp : p ∈ S.tuples J P) :
    S.GoodHigh J (∏ i, p i) ∧ (∏ i, p i).primeFactors = univ.image p := by
  obtain ⟨hinj, hpr⟩ := mem_tuples hp
  have himg : ∀ q ∈ univ.image p, q.Prime := by
    intro q hq
    obtain ⟨i, -, rfl⟩ := mem_image.1 hq
    exact (hpr i).1
  have hprod : ∏ i, p i = ∏ q ∈ univ.image p, q := by
    rw [Finset.prod_image (fun x _ y _ hxy => hinj hxy)]
  unfold GoodHigh
  rw [hprod, Nat.primeFactors_prod himg]
  refine ⟨⟨squarefree_prod_primes himg, ?_, ?_⟩, rfl⟩
  · intro q hq
    obtain ⟨i, -, rfl⟩ := mem_image.1 hq
    exact ⟨(hpr i).1, P i, (P i).2, (hpr i).2⟩
  · rw [card_image_of_injective _ hinj]; simp

theorem Tcount_eq_zero {J : ℕ} (P : Fin J → Fin S.H) {a : ℕ}
    (ha : ¬ S.GoodHigh J a) : S.Tcount J P a = 0 := by
  unfold Tcount
  rw [card_eq_zero, filter_eq_empty_iff]
  intro p hp hpa
  exact ha (hpa ▸ (tuple_prod hp).1)

/-- For good `a`, `T_P(a) = #{π : ν(a) ∘ π = P}`. -/
theorem Tcount_eq_card_perm (hS : S.Good) {J : ℕ} (P : Fin J → Fin S.H) {a : ℕ}
    (ha : S.GoodHigh J a) :
    S.Tcount J P a = (univ.filter (fun π : Equiv.Perm (Fin J) =>
      S.nu a.primeFactors ha.2.2 ha.2.1 ∘ π = P)).card := by
  classical
  obtain ⟨hsq, hhigh, hcard⟩ := ha
  set A := a.primeFactors with hA
  have hprodA : ∏ q ∈ A, q = a := Nat.prod_primeFactors_of_squarefree hsq
  unfold Tcount
  symm
  refine Finset.card_bij (fun π _ => fun i => desc A hcard (π i)) ?_ ?_ ?_
  · intro π hπ
    have hπ' := (mem_filter.1 hπ).2
    rw [mem_filter]
    refine ⟨?_, ?_⟩
    · unfold tuples
      rw [mem_filter, Fintype.mem_piFinset]
      refine ⟨fun i => ?_, fun i j hij => π.injective (desc_injective A hcard hij)⟩
      have hm := desc_mem A hcard (π i)
      have hhi := hhigh _ hm
      have hbox : S.boxOf (desc A hcard (π i)) = P i := by
        have := congrFun hπ' i
        simp only [Function.comp_apply, nu] at this
        exact congrArg Fin.val this
      have hin := (boxOf_spec hhi).2
      rw [hbox] at hin
      rw [mem_filter, mem_range]
      refine ⟨?_, hhi.1, hin⟩
      exact Nat.lt_succ_of_le (Nat.le_floor hin.2)
    · rw [Equiv.prod_comp π (fun i => desc A hcard i),
        show ∏ i, desc A hcard i = ∏ q ∈ A, q from prod_desc A hcard (fun q => q)]
      exact hprodA
  · intro π₁ _ π₂ _ h
    ext i
    have := congrFun h i
    exact congrArg Fin.val (desc_injective A hcard this)
  · intro p hp
    obtain ⟨hpt, hpa⟩ := mem_filter.1 hp
    obtain ⟨hinj, hpr⟩ := mem_tuples hpt
    have hpA : ∀ i, p i ∈ A := by
      intro i
      rw [hA, Nat.mem_primeFactors]
      refine ⟨(hpr i).1, ?_, hsq.ne_zero⟩
      rw [← hpa]; exact Finset.dvd_prod_of_mem p (mem_univ i)
    -- `p` is a bijection `Fin J → A`
    let p' : Fin J → A := fun i => ⟨p i, hpA i⟩
    have hp'inj : Function.Injective p' := fun i j hij => hinj (congrArg Subtype.val hij)
    have hp'bij : Function.Bijective p' := by
      rw [Fintype.bijective_iff_injective_and_card]
      exact ⟨hp'inj, by simp [hcard]⟩
    let d' : Fin J → A := fun i => ⟨desc A hcard i, desc_mem A hcard i⟩
    have hd'bij : Function.Bijective d' := by
      rw [Fintype.bijective_iff_injective_and_card]
      exact ⟨fun i j hij => desc_injective A hcard (congrArg Subtype.val hij), by simp [hcard]⟩
    let e := Equiv.ofBijective d' hd'bij
    let π : Equiv.Perm (Fin J) := (Equiv.ofBijective p' hp'bij).trans e.symm
    have hπ : ∀ i, desc A hcard (π i) = p i := by
      intro i
      have : d' (π i) = p' i := by
        show e (e.symm (p' i)) = p' i
        exact e.apply_symm_apply _
      exact congrArg Subtype.val this
    refine ⟨π, ?_, funext hπ⟩
    rw [mem_filter]
    refine ⟨mem_univ _, funext fun i => ?_⟩
    apply Fin.ext
    simp only [Function.comp_apply, nu]
    rw [hπ i]
    exact boxOf_eq hS (hhigh _ (hpA i)) (hpr i).2

theorem gammaP_pos {J : ℕ} (P : Fin J → Fin S.H) : 0 < S.gammaP J P :=
  Finset.prod_pos (fun _ _ => Nat.factorial_pos _)

open Classical in
/-- **Ownership identity**: `∑_{P ∈ 𝐃_J^+} B_P(a) = hw_J(a)`. -/
theorem sum_Bcoef_eq_hw (hS : S.Good) (J a : ℕ) :
    (∑ P : Fin J → Fin S.H, if S.BoxAdm J P then S.Bcoef J P a else 0) = S.hw J a := by
  classical
  by_cases ha : S.GoodHigh J a
  · set ν := S.nu a.primeFactors ha.2.2 ha.2.1 with hν
    have hzero : ∀ P : Fin J → Fin S.H, P ≠ ν →
        (if S.BoxAdm J P then S.Bcoef J P a else 0) = 0 := by
      intro P hP
      split_ifs with hadm
      · unfold Bcoef
        rw [Tcount_eq_card_perm hS P ha, card_eq_zero.2, Nat.cast_zero, zero_div]
        rw [filter_eq_empty_iff]
        intro π _ hπ
        exact hP (eq_of_antitone_comp (nu_antitone hS _ _ _) hadm.1 hπ)
      · rfl
    rw [Finset.sum_eq_single ν (fun P _ hP => hzero P hP) (fun h => absurd (mem_univ _) h)]
    unfold hw
    have hiff := boxAdm_nu_iff hS a.primeFactors ha.2.2 ha.2.1
    by_cases hadm : S.BoxAdm J ν
    · rw [if_pos hadm, if_pos ⟨ha, hiff.1 hadm⟩]
      unfold Bcoef
      rw [Tcount_eq_card_perm hS ν ha,
        perm_count_eq_gamma (π₀ := Equiv.refl _) (by rfl)]
      have := gammaP_pos (S := S) ν
      unfold gammaP at this ⊢
      rw [div_self (by exact_mod_cast this.ne')]
    · rw [if_neg hadm, if_neg (fun h => hadm (hiff.2 h.2))]
  · unfold hw
    rw [if_neg (fun h => ha h.1)]
    refine Finset.sum_eq_zero (fun P _ => ?_)
    split_ifs
    · unfold Bcoef; rw [Tcount_eq_zero P ha]; simp
    · rfl

/-- **The complete scalar coefficient in set form** (Lichtman's ownership map `ν`):
`ℓ_X(d) = ∑_{J ≤ ε₀^{-2}} (-1)^J ∑_{ba = d} κ_J(b) hw_J(a)`. -/
theorem ellX_eq_setForm (hS : S.Good) (d : ℕ) :
    S.ellX d = ∑ J ∈ range (S.T ^ 2 + 1),
      (-1 : ℝ) ^ J * ∑ x ∈ d.divisorsAntidiagonal, S.kappa J x.1 * S.hw J x.2 := by
  unfold ellX
  refine Finset.sum_congr rfl (fun J _ => ?_)
  simp_rw [← sum_Bcoef_eq_hw hS J, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun P _ => ?_)
  split_ifs <;> simp

end ScalarParams

end Erdos287.Physical.Sieve
