import RequestProject.Erdos287.CurrentTail.ExactSource

/-!
# Erdős #287 — current tail consolidation: the algebraic heart of V100 Relative-BDH

**ERDŐS #287 REMAINS OPEN.  TAIL-287 IS NOT BANKED.**

For a weight `α` on a finite support `S`:

* `ind P = 1` if `P`, else `0`;
* `Delta S α Q b = ∑_{n∈S} α n (1_{n≡b (Q)} - 1_{(n,Q)=1}/φ(Q))`         (ordinary discrepancy);
* `DeltaRel S α f c q a = ∑_{n∈S, n≡c (f)} α n (1_{n≡a (q)} - 1_{(n,q)=1}/φ(q))` (relative);
* `units q = {a < q : (a,q) = 1}`, `crt h c a` the CRT lift (`≡ c (f)`, `≡ a (q)`).

Kernel-proved:

* `modEq_crt_iff` — `n ≡ crt c a (fq) ↔ n ≡ c (f) ∧ n ≡ a (q)`;
* `sum_units_ind_modEq` — **CRT unit-class bijection** at the level of indicators:
  `∑_{a unit mod q} 1_{n≡a(q)} = 1_{(n,q)=1}`;
* `rbdh_crt_identity` — **the V100 CRT identity**
  `Δ^{f,c}(q,a) = Δ(fq,b_{c,a}) - φ(q)⁻¹ ∑*_{a'} Δ(fq,b_{c,a'})`;
* `variance_contraction` and `rbdh_variance_contraction` —
  `∑*_a |Δ^{f,c}(q,a)|² ≤ ∑*_a |Δ(fq,b_{c,a})|²`;
* `crt_mapsTo_units`, `crt_injOn` and `rbdh_full_contraction` —
  `∑*_a |Δ^{f,c}(q,a)|² ≤ ∑*_{b mod fq} |Δ(fq,b)|²` when `(c,f) = 1`;
* `card_factorization_le_tau` — **coprime factorization multiplicity** `≤ τ(Q)`;
* `divisor_weight_transport` — `∑_{(f,q)} G(fq) ≤ ∑_Q τ(Q) G(Q)` for `G ≥ 0`;
* `DeltaRel_eq_Delta_restrict` — the relative discrepancy *is* the ordinary discrepancy of the
  restricted sequence `α · 1_{n ≡ c (f)}` (definitional reduction);
* `relativeSW_of_SW` — SW at modulus `fq` for `α` gives SW at modulus `q` for the restriction;
* `RBDH_of_BDHProvider` — Relative-BDH from an *ordinary* BDH statement (`BDHProvider`) whose
  conclusion speaks only about ordinary discrepancies of arbitrary sequences.
-/

open scoped BigOperators
open Finset

namespace Erdos287.CurrentTail

/-- Indicator of a proposition. -/
noncomputable def ind (P : Prop) [Decidable P] : ℝ := if P then 1 else 0

/-- Reduced residues modulo `q` (so that `(units q).card = φ(q)`). -/
def units (q : ℕ) : Finset ℕ := (range q).filter q.Coprime

theorem card_units (q : ℕ) : (units q).card = Nat.totient q := by
  rw [Nat.totient]; rfl

/-- Ordinary discrepancy `Δ_α(Q,b)`. -/
noncomputable def Delta (S : Finset ℕ) (α : ℕ → ℝ) (Q b : ℕ) : ℝ :=
  ∑ n ∈ S, α n * (ind (n ≡ b [MOD Q]) - ind (Nat.Coprime n Q) / (Nat.totient Q : ℝ))

/-- Relative discrepancy `Δ_α^{f,c}(q,a)`. -/
noncomputable def DeltaRel (S : Finset ℕ) (α : ℕ → ℝ) (f c q a : ℕ) : ℝ :=
  ∑ n ∈ S.filter (fun n => n ≡ c [MOD f]),
    α n * (ind (n ≡ a [MOD q]) - ind (Nat.Coprime n q) / (Nat.totient q : ℝ))

/-- CRT lift `b_{c,a}`. -/
def crt {f q : ℕ} (h : Nat.Coprime f q) (c a : ℕ) : ℕ := (Nat.chineseRemainder h c a).1

theorem modEq_crt_iff {f q : ℕ} (h : Nat.Coprime f q) (c a n : ℕ) :
    n ≡ crt h c a [MOD f * q] ↔ n ≡ c [MOD f] ∧ n ≡ a [MOD q] := by
  have h1 := (Nat.chineseRemainder h c a).2.1
  have h2 := (Nat.chineseRemainder h c a).2.2
  rw [← Nat.modEq_and_modEq_iff_modEq_mul h]
  constructor
  · rintro ⟨u, v⟩; exact ⟨u.trans h1, v.trans h2⟩
  · rintro ⟨u, v⟩; exact ⟨u.trans h1.symm, v.trans h2.symm⟩

theorem ind_congr {P Q : Prop} [Decidable P] [Decidable Q] (h : P ↔ Q) : ind P = ind Q := by
  unfold ind; by_cases hP : P
  · rw [if_pos hP, if_pos (h.1 hP)]
  · rw [if_neg hP, if_neg (fun hQ => hP (h.2 hQ))]

theorem ind_and {P Q : Prop} [Decidable P] [Decidable Q] : ind (P ∧ Q) = ind P * ind Q := by
  unfold ind; by_cases hP : P <;> by_cases hQ : Q <;> simp [hP, hQ]

theorem coprime_mod_iff (q n : ℕ) : Nat.Coprime (n % q) q ↔ Nat.Coprime n q := by
  unfold Nat.Coprime; rw [Nat.ModEq.gcd_eq (Nat.mod_modEq n q)]

theorem mem_units {q a : ℕ} : a ∈ units q ↔ a < q ∧ Nat.Coprime a q := by
  simp only [units, mem_filter, mem_range, Nat.coprime_comm]

/-- **CRT unit-class bijection (indicator form).** -/
theorem sum_units_ind_modEq {q : ℕ} (hq : 0 < q) (n : ℕ) :
    ∑ a ∈ units q, ind (n ≡ a [MOD q]) = ind (Nat.Coprime n q) := by
  unfold ind
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
  have : (units q).filter (fun a => n ≡ a [MOD q]) =
      if Nat.Coprime n q then {n % q} else ∅ := by
    ext a
    rw [mem_filter, mem_units]
    have key : ∀ a, a < q → (n ≡ a [MOD q] ↔ n % q = a) := by
      intro a ha
      unfold Nat.ModEq; rw [Nat.mod_eq_of_lt ha]
    split_ifs with hc
    · rw [mem_singleton]
      constructor
      · rintro ⟨⟨ha, -⟩, hmod⟩
        exact ((key a ha).1 hmod).symm
      · rintro rfl
        exact ⟨⟨Nat.mod_lt _ hq, (coprime_mod_iff q n).2 hc⟩,
          (key _ (Nat.mod_lt _ hq)).2 rfl⟩
    · simp only [Finset.notMem_empty, iff_false, not_and]
      intro ⟨ha, hca⟩ hmod
      apply hc
      rw [← coprime_mod_iff, (key a ha).1 hmod]; exact hca
  rw [this]
  split_ifs <;> simp

theorem DeltaRel_eq_sum (S : Finset ℕ) (α : ℕ → ℝ) (f c q a : ℕ) :
    DeltaRel S α f c q a = ∑ n ∈ S, α n * (ind (n ≡ c [MOD f]) *
      (ind (n ≡ a [MOD q]) - ind (Nat.Coprime n q) / (Nat.totient q : ℝ))) := by
  unfold DeltaRel
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  unfold ind; split_ifs <;> simp

/-- **The V100 CRT identity.**  For coprime `f, q ≥ 1`:
`Δ^{f,c}(q,a) = Δ(fq, b_{c,a}) - φ(q)⁻¹ ∑*_{a'} Δ(fq, b_{c,a'})`. -/
theorem rbdh_crt_identity (S : Finset ℕ) (α : ℕ → ℝ) {f q : ℕ} (hf : 0 < f) (hq : 0 < q)
    (h : Nat.Coprime f q) (c a : ℕ) :
    DeltaRel S α f c q a = Delta S α (f * q) (crt h c a) -
      (1 / (Nat.totient q : ℝ)) * ∑ a' ∈ units q, Delta S α (f * q) (crt h c a') := by
  have hφq := (totient_cast_pos hq).ne'
  have hφfq := (totient_cast_pos (Nat.mul_pos hf hq)).ne'
  have hcop : ∀ n, ind (Nat.Coprime n (f * q)) = ind (Nat.Coprime n f) * ind (Nat.Coprime n q) := by
    intro n; rw [← ind_and]; exact ind_congr Nat.coprime_mul_iff_right
  have hcrt : ∀ n a', ind (n ≡ crt h c a' [MOD f * q]) = ind (n ≡ c [MOD f]) * ind (n ≡ a' [MOD q]) := by
    intro n a'; rw [← ind_and]; exact ind_congr (modEq_crt_iff h c a' n)
  -- coprimality of `n` with `f` follows from `n ≡ c` only when `(c,f)=1`; we do not need it:
  -- the identity is exact in all cases.
  have hsum : ∑ a' ∈ units q, Delta S α (f * q) (crt h c a') =
      ∑ n ∈ S, α n * (ind (n ≡ c [MOD f]) * ind (Nat.Coprime n q) -
        (Nat.totient q : ℝ) * ind (Nat.Coprime n (f * q)) / (Nat.totient (f * q) : ℝ)) := by
    unfold Delta
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [← Finset.mul_sum, Finset.sum_sub_distrib]
    simp_rw [hcrt n]
    rw [← Finset.mul_sum, sum_units_ind_modEq hq, Finset.sum_const, card_units, nsmul_eq_mul]
    ring
  rw [hsum, DeltaRel_eq_sum]
  unfold Delta
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [hcrt n a]
  field_simp
  ring

/-- **Finite-dimensional variance contraction.**  For a finite set `T` of size `k ≥ 1`,
`∑_{a∈T} (x_a - k⁻¹ ∑ x)² ≤ ∑_{a∈T} x_a²`. -/
theorem variance_contraction (T : Finset ℕ) (x : ℕ → ℝ) :
    ∑ a ∈ T, (x a - (1 / (T.card : ℝ)) * ∑ a' ∈ T, x a') ^ 2 ≤ ∑ a ∈ T, x a ^ 2 := by
  rcases T.eq_empty_or_nonempty with rfl | hT
  · simp
  have hk : (0 : ℝ) < T.card := by exact_mod_cast hT.card_pos
  set s := ∑ a' ∈ T, x a'
  have : ∑ a ∈ T, (x a - (1 / (T.card : ℝ)) * s) ^ 2 =
      ∑ a ∈ T, x a ^ 2 - s ^ 2 / T.card := by
    simp_rw [sub_sq]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    have e : ∑ a ∈ T, 2 * x a * (1 / (T.card : ℝ) * s) = 2 * s ^ 2 / T.card := by
      rw [← Finset.sum_mul, ← Finset.mul_sum]; field_simp; ring
    rw [e]; field_simp; ring
  rw [this]
  have : 0 ≤ s ^ 2 / T.card := div_nonneg (sq_nonneg _) hk.le
  linarith

/-- **Relative variance contraction.**
`∑*_a |Δ^{f,c}(q,a)|² ≤ ∑*_a |Δ(fq, b_{c,a})|²`. -/
theorem rbdh_variance_contraction (S : Finset ℕ) (α : ℕ → ℝ) {f q : ℕ} (hf : 0 < f)
    (hq : 0 < q) (h : Nat.Coprime f q) (c : ℕ) :
    ∑ a ∈ units q, DeltaRel S α f c q a ^ 2 ≤
      ∑ a ∈ units q, Delta S α (f * q) (crt h c a) ^ 2 := by
  have := variance_contraction (units q) (fun a => Delta S α (f * q) (crt h c a))
  rw [card_units] at this
  refine le_of_eq_of_le ?_ this
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [rbdh_crt_identity S α hf hq h c a]

theorem crt_lt {f q : ℕ} (hf : 0 < f) (hq : 0 < q) (h : Nat.Coprime f q) (c a : ℕ) :
    crt h c a < f * q :=
  Nat.chineseRemainder_lt_mul h c a hf.ne' hq.ne'

/-- The CRT lift of a unit `a` (with `(c,f)=1`) is a unit modulo `fq`. -/
theorem crt_mapsTo_units {f q : ℕ} (hf : 0 < f) (hq : 0 < q) (h : Nat.Coprime f q) {c : ℕ}
    (hc : Nat.Coprime f c) {a : ℕ} (ha : a ∈ units q) : crt h c a ∈ units (f * q) := by
  rw [mem_units] at ha ⊢
  refine ⟨crt_lt hf hq h c a, ?_⟩
  have h1 : crt h c a ≡ c [MOD f] := (Nat.chineseRemainder h c a).2.1
  have h2 : crt h c a ≡ a [MOD q] := (Nat.chineseRemainder h c a).2.2
  apply Nat.Coprime.mul_right
  · unfold Nat.Coprime; rw [Nat.ModEq.gcd_eq h1, Nat.gcd_comm]; exact hc
  · unfold Nat.Coprime; rw [Nat.ModEq.gcd_eq h2]; exact ha.2

theorem crt_injOn {f q : ℕ} (h : Nat.Coprime f q) (c : ℕ) :
    Set.InjOn (crt h c) (units q : Set ℕ) := by
  intro a ha a' ha' heq
  have h2 : crt h c a ≡ a [MOD q] := (Nat.chineseRemainder h c a).2.2
  have h2' : crt h c a' ≡ a' [MOD q] := (Nat.chineseRemainder h c a').2.2
  have ha1 := (mem_units.1 ha).1
  have ha1' := (mem_units.1 ha').1
  have hm : a ≡ a' [MOD q] := h2.symm.trans (by rw [heq]; exact h2')
  unfold Nat.ModEq at hm
  rwa [Nat.mod_eq_of_lt ha1, Nat.mod_eq_of_lt ha1'] at hm

/-- Ordinary variance `V(Q) = ∑*_{b mod Q} |Δ(Q,b)|²`. -/
noncomputable def V (S : Finset ℕ) (α : ℕ → ℝ) (Q : ℕ) : ℝ :=
  ∑ b ∈ units Q, Delta S α Q b ^ 2

/-- Relative variance `V^{f,c}(q) = ∑*_{a mod q} |Δ^{f,c}(q,a)|²`. -/
noncomputable def Vrel (S : Finset ℕ) (α : ℕ → ℝ) (f c q : ℕ) : ℝ :=
  ∑ a ∈ units q, DeltaRel S α f c q a ^ 2

/-- **Full contraction.**  For `(c,f)=1`: `V^{f,c}(q) ≤ V(fq)`. -/
theorem rbdh_full_contraction (S : Finset ℕ) (α : ℕ → ℝ) {f q : ℕ} (hf : 0 < f) (hq : 0 < q)
    (h : Nat.Coprime f q) {c : ℕ} (hc : Nat.Coprime f c) :
    Vrel S α f c q ≤ V S α (f * q) := by
  refine (rbdh_variance_contraction S α hf hq h c).trans ?_
  rw [← Finset.sum_image (g := crt h c) (f := fun b => Delta S α (f * q) b ^ 2)
    (fun a ha a' ha' heq => crt_injOn h c ha ha' heq)]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => sq_nonneg _)
  intro b hb
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hb
  exact crt_mapsTo_units hf hq h hc ha

/-- **Coprime factorization multiplicity.**  Any finite set of pairs contains at most `τ(Q)`
factorizations `Q = f · q`. -/
theorem card_factorization_le_tau (P : Finset (ℕ × ℕ)) {Q : ℕ} (hQ : 0 < Q) :
    (P.filter (fun x => x.1 * x.2 = Q)).card ≤ (Nat.divisors Q).card := by
  refine Finset.card_le_card_of_injOn Prod.fst ?_ ?_
  · intro x hx
    have hx' := (Finset.mem_filter.1 hx).2
    exact Nat.mem_divisors.2 ⟨⟨x.2, hx'.symm⟩, hQ.ne'⟩
  · intro x hx y hy hxy
    have hx' := (Finset.mem_filter.1 hx).2
    have hy' := (Finset.mem_filter.1 hy).2
    have h1 : 0 < x.1 := Nat.pos_of_ne_zero (fun h0 => by rw [h0, zero_mul] at hx'; omega)
    have hxy' : x.1 = y.1 := hxy
    have : x.2 = y.2 := by
      apply Nat.eq_of_mul_eq_mul_left h1
      rw [hx', hxy', hy']
    exact Prod.ext hxy' this

/-- **Divisor-weight transport.**  For `G ≥ 0`, `∑_{(f,q)∈P} G(fq) ≤ ∑_Q τ(Q) G(Q)`. -/
theorem divisor_weight_transport (P : Finset (ℕ × ℕ)) (G : ℕ → ℝ) (hG : ∀ Q, 0 ≤ G Q)
    (hpos : ∀ x ∈ P, 0 < x.1 * x.2) :
    ∑ x ∈ P, G (x.1 * x.2) ≤
      ∑ Q ∈ P.image (fun x => x.1 * x.2), ((Nat.divisors Q).card : ℝ) * G Q := by
  rw [Finset.sum_comp]
  refine Finset.sum_le_sum (fun Q hQ => ?_)
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hQ
  rw [nsmul_eq_mul]
  refine mul_le_mul_of_nonneg_right ?_ (hG _)
  exact_mod_cast card_factorization_le_tau P (hpos x hx)

/-- **Transported relative variance.**  Summing `V^{f,c_f}(q)` over coprime pairs `(f,q)`
(with `(c_f, f) = 1`) is bounded by the divisor-weighted ordinary variance. -/
theorem rbdh_pairs_le_weighted (S : Finset ℕ) (α : ℕ → ℝ) (P : Finset (ℕ × ℕ)) (c : ℕ → ℕ)
    (hP : ∀ x ∈ P, 0 < x.1 ∧ 0 < x.2 ∧ Nat.Coprime x.1 x.2 ∧ Nat.Coprime x.1 (c x.1)) :
    ∑ x ∈ P, Vrel S α x.1 (c x.1) x.2 ≤
      ∑ Q ∈ P.image (fun x => x.1 * x.2), ((Nat.divisors Q).card : ℝ) * V S α Q := by
  refine (Finset.sum_le_sum (fun x hx => ?_)).trans
    (divisor_weight_transport P (V S α) (fun Q => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
      (fun x hx => Nat.mul_pos (hP x hx).1 (hP x hx).2.1))
  obtain ⟨h1, h2, h3, h4⟩ := hP x hx
  exact rbdh_full_contraction S α h1 h2 h3 h4

/-- The restriction `α · 1_{n ≡ c (f)}`. -/
noncomputable def restrict (α : ℕ → ℝ) (f c : ℕ) (n : ℕ) : ℝ :=
  if n ≡ c [MOD f] then α n else 0

/-- The relative discrepancy is the ordinary discrepancy of the restricted sequence. -/
theorem DeltaRel_eq_Delta_restrict (S : Finset ℕ) (α : ℕ → ℝ) (f c q a : ℕ) :
    DeltaRel S α f c q a = Delta S (restrict α f c) q a := by
  unfold DeltaRel Delta restrict
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  split_ifs <;> simp

theorem restrict_sq_sum (S : Finset ℕ) (α : ℕ → ℝ) (f c : ℕ) :
    ∑ n ∈ S, restrict α f c n ^ 2 = ∑ n ∈ S.filter (fun n => n ≡ c [MOD f]), α n ^ 2 := by
  unfold restrict
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  split_ifs <;> simp

/-- **Relative SW from SW at the lifted modulus.**  If all ordinary discrepancies modulo `fq`
are at most `η`, then all relative discrepancies modulo `q` are at most `2η`. -/
theorem relativeSW_of_SW (S : Finset ℕ) (α : ℕ → ℝ) {f q : ℕ} (hf : 0 < f) (hq : 0 < q)
    (h : Nat.Coprime f q) {η : ℝ} (hη : ∀ b, |Delta S α (f * q) b| ≤ η) (c a : ℕ) :
    |DeltaRel S α f c q a| ≤ 2 * η := by
  rw [rbdh_crt_identity S α hf hq h c a]
  have hφ := totient_cast_pos hq
  have hsum : |∑ a' ∈ units q, Delta S α (f * q) (crt h c a')| ≤ (Nat.totient q : ℝ) * η := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum (fun a' _ => hη (crt h c a'))).trans ?_
    rw [Finset.sum_const, card_units, nsmul_eq_mul]
  have e : |1 / (Nat.totient q : ℝ) * ∑ a' ∈ units q, Delta S α (f * q) (crt h c a')| ≤ η := by
    rw [abs_mul, abs_of_pos (by positivity), one_div, inv_mul_le_iff₀ hφ]
    exact hsum
  calc _ ≤ |Delta S α (f * q) (crt h c a)| +
        |1 / (Nat.totient q : ℝ) * ∑ a' ∈ units q, Delta S α (f * q) (crt h c a')| :=
          abs_sub _ _
    _ ≤ η + η := add_le_add (hη _) e
    _ = 2 * η := by ring

/-- **Ordinary BDH statement (the smallest external analytic interface).**  Over a set of
"good" moduli (e.g. moduli coprime to a fixed tiny base): every weight `β` on `S` whose
ordinary discrepancies at good moduli `q ≤ Q₀` are at most `η` satisfies
`∑_{good q ≤ Q} V_β(q) ≤ B(∑ β², η)`.  The conclusion speaks only about *ordinary*
discrepancies of *arbitrary* sequences; it contains no relative or #287 content. -/
def BDHStatement (S : Finset ℕ) (good : ℕ → Prop) [DecidablePred good] (Q0 Q : ℕ)
    (B : ℝ → ℝ → ℝ) : Prop :=
  ∀ (β : ℕ → ℝ) (η : ℝ), (∀ q ∈ (Finset.Icc 1 Q0).filter good, ∀ b, |Delta S β q b| ≤ η) →
    ∑ q ∈ (Finset.Icc 1 Q).filter good, V S β q ≤ B (∑ n ∈ S, β n ^ 2) η

/-- **Relative-BDH from ordinary BDH (kernel reduction).**  Applying the ordinary BDH statement
over moduli coprime to `f` to the restricted sequence `α · 1_{n≡c(f)}`, with the SW input
supplied at the lifted moduli `fq`, gives
`∑_{q ≤ Q, (q,f)=1} V^{f,c}(q) ≤ B(∑_{n ≡ c (f)} α², 2η)`.
The true `1/f` density is carried by `∑_{n ≡ c(f)} α_n²`. -/
theorem RBDH_of_BDH (S : Finset ℕ) (α : ℕ → ℝ) {f : ℕ} (hf : 0 < f) (c : ℕ) {Q0 Q : ℕ}
    {B : ℝ → ℝ → ℝ} (hBDH : BDHStatement S (fun q => Nat.Coprime f q) Q0 Q B) {η : ℝ}
    (hSW : ∀ q ∈ (Finset.Icc 1 Q0).filter (fun q => Nat.Coprime f q), ∀ b,
      |Delta S α (f * q) b| ≤ η) :
    ∑ q ∈ (Finset.Icc 1 Q).filter (fun q => Nat.Coprime f q), Vrel S α f c q ≤
      B (∑ n ∈ S.filter (fun n => n ≡ c [MOD f]), α n ^ 2) (2 * η) := by
  have := hBDH (restrict α f c) (2 * η) (by
    intro q hq b
    have hq' := Finset.mem_filter.1 hq
    have hq1 : 0 < q := (Finset.mem_Icc.1 hq'.1).1
    rw [← DeltaRel_eq_Delta_restrict]
    exact relativeSW_of_SW S α hf hq1 hq'.2 (hSW q hq) c b)
  rw [restrict_sq_sum] at this
  refine le_of_eq_of_le (Finset.sum_congr rfl (fun q _ => ?_)) this
  unfold Vrel V
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [DeltaRel_eq_Delta_restrict]

/-- **Coprimality insertion/removal (exact).**  For coprime `f, d ≥ 1` and a compatible class
`b ≡ c (mod f)`:
`P(fd,b) - P(f,c)/φ(d) = Δ^{f,c}(d,b) - φ(d)⁻¹ ∑_{n ≡ c (f), (n,d) > 1} α_n`. -/
theorem relative_term_eq_DeltaRel (S : Finset ℕ) (α : ℕ → ℝ) {f d : ℕ} (hd : 0 < d)
    (hfd : Nat.Coprime f d) {b c : ℕ} (hbc : b ≡ c [MOD f]) :
    progSum S α (f * d) b - progSum S α f c / (Nat.totient d : ℝ) =
      DeltaRel S α f c d b - (1 / (Nat.totient d : ℝ)) *
        ∑ n ∈ S.filter (fun n => n ≡ c [MOD f] ∧ ¬ Nat.Coprime n d), α n := by
  have hφ := (totient_cast_pos hd).ne'
  have e1 : progSum S α (f * d) b =
      ∑ n ∈ S, α n * (ind (n ≡ c [MOD f]) * ind (n ≡ b [MOD d])) := by
    unfold progSum; rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [← ind_and]
    have : n ≡ b [MOD f * d] ↔ n ≡ c [MOD f] ∧ n ≡ b [MOD d] := by
      rw [← Nat.modEq_and_modEq_iff_modEq_mul hfd]
      exact ⟨fun ⟨u, v⟩ => ⟨u.trans hbc, v⟩, fun ⟨u, v⟩ => ⟨u.trans hbc.symm, v⟩⟩
    unfold ind; by_cases hh : n ≡ b [MOD f * d]
    · rw [if_pos hh, if_pos (this.1 hh)]; ring
    · rw [if_neg hh, if_neg (fun h' => hh (this.2 h'))]; ring
  have e2 : progSum S α f c = ∑ n ∈ S, α n * ind (n ≡ c [MOD f]) := by
    unfold progSum; rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    unfold ind; split_ifs <;> ring
  have e3 : ∑ n ∈ S.filter (fun n => n ≡ c [MOD f] ∧ ¬ Nat.Coprime n d), α n =
      ∑ n ∈ S, α n * (ind (n ≡ c [MOD f]) * (1 - ind (Nat.Coprime n d))) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    unfold ind; split_ifs <;> simp_all
  rw [e1, e2, e3, DeltaRel_eq_sum, Finset.sum_div, Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  field_simp
  ring

end Erdos287.CurrentTail
