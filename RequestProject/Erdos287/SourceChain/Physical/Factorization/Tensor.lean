import RequestProject.Erdos287.SourceChain.Physical.Factorization.Support
import RequestProject.Erdos287.SourceChain.Physical.Factorization.Colouring

/-!
# Erdős #287 — exact three-colour tensorization of the high-prime box weights

**ERDŐS #287 REMAINS OPEN.  TAIL-287 IS NOT BANKED.**

Fix a sector `(J, P)` and **any** colouring `c` of the `J` box positions (in the application:
the Pascadi colouring `atomColour`).  Distinctness of the primes across the three colour
classes is decoupled by a uniformly random colouring `χ : Fin K → Fin 3` of all candidate
primes (`K = ⌊z⌋ + 1`): a labelled tuple `q` of distinct primes is kept for `χ` iff
`χ(q_i) = c(i)` for every position `i`, which happens for exactly `3^{K-J}` colourings
(`card_compat_mul`).  For a fixed `χ` the kept tuples are *exactly* the triples of partial
tuples (one per colour class, the primes of class `k` all `χ`-coloured `k`), so the count
becomes a triple Dirichlet convolution.

* `partTuples J P c χ k` — partial labelled tuples on the positions of colour `k`
  (dummy entry `1` elsewhere), distinct within the class, primes `χ`-coloured `k`;
* `colFactor J P c χ k = γ_k⁻¹ · #{partial tuples with product m}` where
  `γ_k = ∏_b (#{i : c i = k, P_i = b})!` is the repeated-box multiplicity of the class;
* `atomWeight J P c = 3^J ∏_k γ_k / (γ(P) 3^K)`;
* **`bcoef_tensor`** — `B_P = atomWeight • ∑_χ colFactor₀ * colFactor₁ * colFactor₂`
  (exact identity of arithmetic functions; `B_P = T_P/γ(P)` is the literal box weight).
-/

open Finset

set_option autoImplicit false

namespace Erdos287.Physical.Sieve.ScalarParams

open Erdos287.Physical.Factor

/-! ### Counting arithmetic functions -/

open Classical in
/-- `m ↦ #{x ∈ A : f x = m}` (and `0` at `m = 0`), as an arithmetic function. -/
noncomputable def cntAF {α : Type*} (A : Finset α) (f : α → ℕ) : ArithmeticFunction ℝ :=
  ⟨fun m => if m = 0 then 0 else ((A.filter (fun x => f x = m)).card : ℝ), by simp⟩

lemma cntAF_apply {α : Type*} (A : Finset α) (f : α → ℕ) {m : ℕ} (hm : m ≠ 0) [DecidableEq ℕ] :
    cntAF A f m = ((A.filter (fun x => f x = m)).card : ℝ) := by
  classical
  simp only [cntAF, ArithmeticFunction.coe_mk, if_neg hm]
  congr

/-- Dirichlet product of counting functions counts pairs. -/
lemma cntAF_mul {α β : Type*} (A : Finset α) (B : Finset β) (f : α → ℕ) (g : β → ℕ) :
    cntAF A f * cntAF B g = cntAF (A ×ˢ B) (fun p => f p.1 * g p.2) := by
  classical
  ext m
  by_cases hm : m = 0
  · subst hm; simp
  rw [ArithmeticFunction.mul_apply, cntAF_apply _ _ hm]
  have h1 : ∀ x ∈ m.divisorsAntidiagonal, cntAF A f x.1 * cntAF B g x.2 =
      ∑ a ∈ A, ∑ b ∈ B, if (f a, g b) = x then (1 : ℝ) else 0 := by
    intro x hx
    obtain ⟨hx1, -⟩ := Nat.mem_divisorsAntidiagonal.1 hx
    have hx1' : x.1 ≠ 0 := fun h => hm (by rw [← hx1, h, zero_mul])
    have hx2' : x.2 ≠ 0 := fun h => hm (by rw [← hx1, h, mul_zero])
    rw [cntAF_apply _ _ hx1', cntAF_apply _ _ hx2', card_filter, card_filter]
    push_cast
    rw [sum_mul_sum]
    refine sum_congr rfl (fun a _ => sum_congr rfl (fun b _ => ?_))
    by_cases ha : f a = x.1 <;> by_cases hb : g b = x.2 <;>
      simp [ha, hb, Prod.ext_iff]
  rw [sum_congr rfl h1, sum_comm]
  rw [card_filter, sum_product]
  push_cast
  refine sum_congr rfl (fun a _ => ?_)
  rw [sum_comm]
  refine sum_congr rfl (fun b _ => ?_)
  rw [sum_ite_eq]
  simp only [Nat.mem_divisorsAntidiagonal]
  by_cases h : f a * g b = m
  · rw [if_pos ⟨h, hm⟩, if_pos h]
  · rw [if_neg (fun h' => h h'.1), if_neg h]

/-- Scalar multiple of an arithmetic function. -/
noncomputable def scaleAF (r : ℝ) (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ :=
  ⟨fun m => r * f m, by simp⟩

@[simp] lemma scaleAF_apply (r : ℝ) (f : ArithmeticFunction ℝ) (m : ℕ) :
    scaleAF r f m = r * f m := rfl

lemma scaleAF_mul (r s : ℝ) (f g : ArithmeticFunction ℝ) :
    scaleAF r f * scaleAF s g = scaleAF (r * s) (f * g) := by
  ext m
  simp only [ArithmeticFunction.mul_apply, scaleAF_apply, mul_sum]
  refine sum_congr rfl (fun x _ => by ring)

lemma af_sum_apply {ι : Type*} (s : Finset ι) (f : ι → ArithmeticFunction ℝ) (a : ℕ) :
    (∑ i ∈ s, f i) a = ∑ i ∈ s, f i a := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih => rw [sum_insert hx, sum_insert hx, ArithmeticFunction.add_apply, ih]

/-! ### Candidate primes, the colouring range, partial tuples -/

variable (S : ScalarParams)

open Classical in
/-- The candidate primes of box `j` (exactly the range used in `tuples`). -/
noncomputable def boxPrimes (j : Fin S.H) : Finset ℕ :=
  (range (⌊S.boxTop j⌋₊ + 1)).filter (fun p => p.Prime ∧ S.InBox j p)

/-- Every candidate prime is `< K = ⌊z⌋ + 1`. -/
noncomputable def Kc : ℕ := ⌊S.ztop⌋₊ + 1

/-- The colour of a natural number under `χ` (`0` outside the colouring range). -/
noncomputable def chiAt (χ : Fin S.Kc → Fin 3) (p : ℕ) : Fin 3 := if h : p < S.Kc then χ ⟨p, h⟩ else 0

open Classical in
/-- Partial labelled tuples of colour class `k` (entry `1` off the class). -/
noncomputable def partTuples (J : ℕ) (P : Fin J → Fin S.H) (c : ℕ → Fin 3)
    (χ : Fin S.Kc → Fin 3) (k : Fin 3) : Finset (Fin J → ℕ) :=
  (Fintype.piFinset fun i => if c i.val = k then
      (S.boxPrimes (P i)).filter (fun p => S.chiAt χ p = k) else {1}).filter
    (fun q => ∀ i j, c i.val = k → c j.val = k → q i = q j → i = j)

/-- Repeated-box multiplicity of colour class `k`: `γ_k = ∏_b (#{i : c i = k, P_i = b})!`. -/
noncomputable def gammaCol (J : ℕ) (P : Fin J → Fin S.H) (c : ℕ → Fin 3) (k : Fin 3) : ℕ :=
  ∏ b : Fin S.H, (univ.filter (fun i : Fin J => c i.val = k ∧ P i = b)).card.factorial

/-- **The colour-`k` factor** `γ_{k,χ}(m) = γ_k⁻¹ #{partial tuples of class k with product m}`. -/
noncomputable def colFactor (J : ℕ) (P : Fin J → Fin S.H) (c : ℕ → Fin 3)
    (χ : Fin S.Kc → Fin 3) (k : Fin 3) : ArithmeticFunction ℝ :=
  scaleAF ((S.gammaCol J P c k : ℝ)⁻¹) (cntAF (S.partTuples J P c χ k) (fun q => ∏ i, q i))

/-- The atom weight `3^J ∏_k γ_k / (γ(P) 3^K)`. -/
noncomputable def atomWeight (J : ℕ) (P : Fin J → Fin S.H) (c : ℕ → Fin 3) : ℝ :=
  (3 : ℝ) ^ J * (∏ k : Fin 3, (S.gammaCol J P c k : ℝ)) / ((S.gammaP J P : ℝ) * 3 ^ S.Kc)

/-- The literal box weight `B_P` as an arithmetic function. -/
noncomputable def bcoefAF (J : ℕ) (P : Fin J → Fin S.H) : ArithmeticFunction ℝ :=
  ⟨fun a => if a = 0 then 0 else S.Bcoef J P a, by simp⟩

/-- The low weight `κ_J` as an arithmetic function. -/
noncomputable def kappaAF (J : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun b => if b = 0 then 0 else S.kappa J b, by simp⟩

variable {S}

lemma fin3_cases (x : Fin 3) : x = 0 ∨ x = 1 ∨ x = 2 := by fin_cases x <;> simp

lemma boxPrimes_lt (hS : S.Good) {j : Fin S.H} {p : ℕ} (hp : p ∈ S.boxPrimes j) : p < S.Kc := by
  classical
  unfold boxPrimes at hp
  obtain ⟨-, -, hbox⟩ := mem_filter.1 hp
  have h1 : (p : ℝ) ≤ S.ztop := by
    refine hbox.2.trans ?_
    rw [boxTop_eq hS, ztop, boxEnd_le_iff hS]
    exact j.2
  have h2 : p ≤ ⌊S.ztop⌋₊ := Nat.le_floor h1
  unfold Kc; omega

lemma mem_tuples_iff {J : ℕ} {P : Fin J → Fin S.H} {q : Fin J → ℕ} :
    q ∈ S.tuples J P ↔ (∀ i, q i ∈ S.boxPrimes (P i)) ∧ Function.Injective q := by
  classical
  unfold tuples boxPrimes
  rw [mem_filter, Fintype.mem_piFinset]

/-! ### Step 1: the random colouring normalisation -/

lemma card_compat_tuple (hS : S.Good) {J : ℕ} {P : Fin J → Fin S.H} {q : Fin J → ℕ}
    (hq : q ∈ S.tuples J P) (c : ℕ → Fin 3) :
    (univ.filter (fun χ : Fin S.Kc → Fin 3 => ∀ i : Fin J, S.chiAt χ (q i) = c i.val)).card *
      3 ^ J = 3 ^ S.Kc := by
  obtain ⟨hmem, hinj⟩ := mem_tuples_iff.1 hq
  have hlt : ∀ i, q i < S.Kc := fun i => boxPrimes_lt hS (hmem i)
  set q' : Fin J → Fin S.Kc := fun i => ⟨q i, hlt i⟩
  have hq' : Function.Injective q' := fun i j h => hinj (congrArg Fin.val h)
  have := card_compat_mul q' hq' (fun i => c i.val)
  convert this using 3
  ext χ
  simp only [mem_filter, mem_univ, true_and, chiAt, q', dif_pos (hlt _)]

open Classical in
lemma Tcount_mul_pow (hS : S.Good) {J : ℕ} (P : Fin J → Fin S.H) (c : ℕ → Fin 3) (a : ℕ) :
    S.Tcount J P a * 3 ^ S.Kc = 3 ^ J * ∑ χ : Fin S.Kc → Fin 3,
      ((S.tuples J P).filter (fun q => ∏ i, q i = a ∧ ∀ i : Fin J,
        S.chiAt χ (q i) = c i.val)).card := by
  unfold Tcount
  rw [card_eq_sum_ones, sum_mul]
  have : ∀ q ∈ (S.tuples J P).filter (fun p => ∏ i, p i = a), 1 * 3 ^ S.Kc =
      3 ^ J * ∑ χ : Fin S.Kc → Fin 3, if (∀ i : Fin J, S.chiAt χ (q i) = c i.val) then 1 else 0 := by
    intro q hq
    rw [one_mul, ← card_compat_tuple hS (mem_filter.1 hq).1 c, mul_comm, card_filter]
  rw [sum_congr rfl this, ← mul_sum, sum_comm]
  congr 1
  refine sum_congr rfl (fun χ _ => ?_)
  rw [card_filter, sum_filter]
  refine sum_congr rfl (fun q _ => ?_)
  by_cases h1 : ∏ i, q i = a <;> simp [h1]

/-! ### Step 2: compatible tuples = triples of partial tuples -/

/-- The colour-`k` part of a tuple. -/
def mask {J : ℕ} (c : ℕ → Fin 3) (k : Fin 3) (q : Fin J → ℕ) : Fin J → ℕ :=
  fun i => if c i.val = k then q i else 1

/-- The `k`-th component of a triple. -/
def comp {J : ℕ} (t : ((Fin J → ℕ) × (Fin J → ℕ)) × (Fin J → ℕ)) (k : Fin 3) : Fin J → ℕ :=
  if k = 0 then t.1.1 else if k = 1 then t.1.2 else t.2

/-- Merge a triple of partial tuples. -/
def merge {J : ℕ} (c : ℕ → Fin 3) (t : ((Fin J → ℕ) × (Fin J → ℕ)) × (Fin J → ℕ)) :
    Fin J → ℕ := fun i => comp t (c i.val) i

lemma prod_mask {J : ℕ} (c : ℕ → Fin 3) (q : Fin J → ℕ) :
    ∏ i, q i = (∏ i, mask c 0 q i) * (∏ i, mask c 1 q i) * (∏ i, mask c 2 q i) := by
  rw [← prod_mul_distrib, ← prod_mul_distrib]
  refine prod_congr rfl (fun i _ => ?_)
  rcases fin3_cases (c i.val) with h | h | h <;> simp [mask, h]

lemma mem_partTuples {J : ℕ} {P : Fin J → Fin S.H} {c : ℕ → Fin 3} {χ : Fin S.Kc → Fin 3}
    {k : Fin 3} {q : Fin J → ℕ} :
    q ∈ S.partTuples J P c χ k ↔
      (∀ i, (c i.val = k → q i ∈ S.boxPrimes (P i) ∧ S.chiAt χ (q i) = k) ∧
        (c i.val ≠ k → q i = 1)) ∧
      ∀ i j, c i.val = k → c j.val = k → q i = q j → i = j := by
  classical
  unfold partTuples
  rw [mem_filter, Fintype.mem_piFinset]
  refine and_congr_left (fun _ => forall_congr' (fun i => ?_))
  by_cases h : c i.val = k
  · simp [h]
  · simp [h]

open Classical in
lemma card_compat_eq_triples {J : ℕ} (P : Fin J → Fin S.H) (c : ℕ → Fin 3)
    (χ : Fin S.Kc → Fin 3) (a : ℕ) :
    ((S.tuples J P).filter (fun q => ∏ i, q i = a ∧ ∀ i : Fin J,
        S.chiAt χ (q i) = c i.val)).card =
      (((S.partTuples J P c χ 0 ×ˢ S.partTuples J P c χ 1) ×ˢ S.partTuples J P c χ 2).filter
        (fun t => (∏ i, t.1.1 i) * (∏ i, t.1.2 i) * (∏ i, t.2 i) = a)).card := by
  refine Finset.card_nbij' (fun q => ((mask c 0 q, mask c 1 q), mask c 2 q)) (merge c) ?_ ?_ ?_ ?_
  · intro q hq
    obtain ⟨hqt, hprod, hcomp⟩ := mem_filter.1 hq
    obtain ⟨hmem, hinj⟩ := mem_tuples_iff.1 hqt
    have hpart : ∀ k, mask c k q ∈ S.partTuples J P c χ k := by
      intro k
      rw [mem_partTuples]
      refine ⟨fun i => ⟨fun hk => ?_, fun hk => ?_⟩, fun i j hi hj hij => ?_⟩
      · simp only [mask, if_pos hk]; exact ⟨hmem i, (hcomp i).trans hk⟩
      · simp [mask, hk]
      · simp only [mask, if_pos hi, if_pos hj] at hij; exact hinj hij
    simp only [coe_filter, Set.mem_setOf_eq, mem_product]
    exact ⟨⟨⟨hpart 0, hpart 1⟩, hpart 2⟩, by rw [← prod_mask, hprod]⟩
  · intro t ht
    simp only [coe_filter, Set.mem_setOf_eq, mem_product] at ht
    obtain ⟨⟨⟨h0, h1⟩, h2⟩, hprod⟩ := ht
    have hk : ∀ k, comp t k ∈ S.partTuples J P c χ k := by
      intro k; rcases fin3_cases k with rfl | rfl | rfl <;> simpa [comp]
    have hval : ∀ i, merge c t i ∈ S.boxPrimes (P i) ∧ S.chiAt χ (merge c t i) = c i.val :=
      fun i => ((mem_partTuples.1 (hk (c i.val))).1 i).1 rfl
    have hmask : ∀ k, mask c k (merge c t) = comp t k := by
      intro k; funext i
      by_cases hi : c i.val = k
      · simp [mask, merge, hi]
      · simp only [mask, if_neg hi]
        exact (((mem_partTuples.1 (hk k)).1 i).2 hi).symm
    refine mem_filter.2 ⟨mem_tuples_iff.2 ⟨fun i => (hval i).1, fun i j hij => ?_⟩, ?_, ?_⟩
    · have hc : c i.val = c j.val := by rw [← (hval i).2, ← (hval j).2, hij]
      have hij' : comp t (c i.val) i = comp t (c i.val) j := by
        have := hij; simp only [merge] at this; rw [← hc] at this; exact this
      exact (mem_partTuples.1 (hk (c i.val))).2 i j rfl hc.symm hij'
    · rw [prod_mask, hmask, hmask, hmask]
      simpa [comp] using hprod
    · exact fun i => (hval i).2
  · intro q hq
    funext i
    rcases fin3_cases (c i.val) with h | h | h <;> simp [merge, comp, mask, h]
  · intro t ht
    simp only [coe_filter, Set.mem_setOf_eq, mem_product] at ht
    obtain ⟨⟨⟨h0, h1⟩, h2⟩, -⟩ := ht
    have hk : ∀ k, comp t k ∈ S.partTuples J P c χ k := by
      intro k; rcases fin3_cases k with rfl | rfl | rfl <;> simpa [comp]
    have hmask : ∀ k, mask c k (merge c t) = comp t k := by
      intro k; funext i
      by_cases hi : c i.val = k
      · simp [mask, merge, hi]
      · simp only [mask, if_neg hi]
        exact (((mem_partTuples.1 (hk k)).1 i).2 hi).symm
    simp only [hmask]
    simp [comp]

/-! ### Step 3: the tensor identity -/

lemma gammaCol_pos (J : ℕ) (P : Fin J → Fin S.H) (c : ℕ → Fin 3) (k : Fin 3) :
    0 < S.gammaCol J P c k :=
  prod_pos (fun _ _ => Nat.factorial_pos _)

/-- **Exact three-colour tensorization of the box weight `B_P`.** -/
theorem bcoef_tensor (hS : S.Good) {J : ℕ} (P : Fin J → Fin S.H) (c : ℕ → Fin 3) :
    S.bcoefAF J P = scaleAF (S.atomWeight J P c) (∑ χ : Fin S.Kc → Fin 3,
      S.colFactor J P c χ 0 * S.colFactor J P c χ 1 * S.colFactor J P c χ 2) := by
  classical
  ext a
  by_cases ha : a = 0
  · subst ha; simp [bcoefAF]
  have hγ : ∀ k, (S.gammaCol J P c k : ℝ) ≠ 0 := fun k => by
    exact_mod_cast (gammaCol_pos J P c k).ne'
  have hcol : ∀ χ, S.colFactor J P c χ 0 * S.colFactor J P c χ 1 * S.colFactor J P c χ 2 =
      scaleAF (∏ k : Fin 3, (S.gammaCol J P c k : ℝ))⁻¹
        (cntAF ((S.partTuples J P c χ 0 ×ˢ S.partTuples J P c χ 1) ×ˢ S.partTuples J P c χ 2)
          (fun t => (∏ i, t.1.1 i) * (∏ i, t.1.2 i) * (∏ i, t.2 i))) := by
    intro χ
    simp only [colFactor, scaleAF_mul, cntAF_mul, Fin.prod_univ_three, mul_inv]
  simp only [hcol, scaleAF_apply]
  rw [af_sum_apply]
  simp only [scaleAF_apply, cntAF_apply _ _ ha, ← mul_sum]
  simp only [bcoefAF, ArithmeticFunction.coe_mk, if_neg ha, Bcoef]
  have hT := Tcount_mul_pow hS P c a
  simp only [card_compat_eq_triples P c] at hT
  have hT' : (S.Tcount J P a : ℝ) = 3 ^ J * (∑ χ : Fin S.Kc → Fin 3,
      ((((S.partTuples J P c χ 0 ×ˢ S.partTuples J P c χ 1) ×ˢ S.partTuples J P c χ 2).filter
        (fun t => (∏ i, t.1.1 i) * (∏ i, t.1.2 i) * (∏ i, t.2 i) = a)).card : ℝ)) / 3 ^ S.Kc := by
    rw [eq_div_iff (by positivity)]
    exact_mod_cast hT
  rw [hT', atomWeight]
  have hγP : (S.gammaP J P : ℝ) ≠ 0 := by exact_mod_cast (gammaP_pos P).ne'
  have hprod : (∏ k : Fin 3, (S.gammaCol J P c k : ℝ)) ≠ 0 :=
    prod_ne_zero_iff.2 (fun k _ => hγ k)
  field_simp

end Erdos287.Physical.Sieve.ScalarParams
