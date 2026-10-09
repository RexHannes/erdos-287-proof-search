import RequestProject.Erdos287.CurrentTail.RelativeBDH

/-!
# Erdős #287 — V100R source chain: exact Type-II split, relative centering, Ordering-B square

**ERDŐS #287 REMAINS OPEN.  TAIL-287 IS NOT BANKED.**  Append-only layer over
`RequestProject/Erdos287/CurrentTail/`; nothing there is modified.

Source level: the formulas of §2.1–§2.4 of the V100R/V100R2 request message (the literal
V100R texts were not present in the repository; see the report).

Kernel-proved here:

* `typeII_split` (§2.1) — for coprime `l, r` and every `v`,
  `I_{lr}(v) - U_{lr}(v) = I_l(v)(I_r(v) - U_r(v)) + (I_l(v) - U_l(v)) U_r(v)`, where
  `I_s(v) = 1_{Av ≡ B (s)}` and `U_s(v) = 1_{(v,s)=1}/φ(s)`;
* `secondTerm_eq_DeltaRel` (§2.2) — the second Type-II term, summed against `α` over the
  physical condition `mn ≡ c (f)`, is exactly `Δ_{α^{(r)}}^{f, c m̄}(l, B·\overline{Am})`, where
  `α^{(r)}_m(n) = α(n) U_r(mn)`.  Both inverses carry explicit unit hypotheses
  (`m · m̄ ≡ 1 (f)`, `(Am) · w ≡ 1 (l)`); `A` is never cancelled modulo `f`;
* `card_fibre_le` / `residueFibre_card_le` (§2.3) — the map `m ↦ (m mod f, m mod l)` on an
  interval of length `L` has fibres of size `≤ L/(fl) + 1` (coprime `f, l`), the genuine
  reciprocal `1/f` density per `l`-class;
* `physical_pair_congr` / `orderingB_physical_square` (§2.4) — the physical congruences
  `m n_i ≡ c (f)`, `A m n_i ≡ B (l)` imply `n₁ ≡ n₂ (mod fl)`; first Cauchy is applied to the
  physical sum *before* any character expansion.
-/

open scoped BigOperators
open Finset

namespace Erdos287.SourceChain

open Erdos287.CurrentTail

/-! ### §2.1 Exact Type-II split -/

/-- `I_s(v) = 1_{A v ≡ B (mod s)}`. -/
noncomputable def Iind (A B s v : ℕ) : ℝ := ind (A * v ≡ B [MOD s])

/-- `U_s(v) = 1_{(v,s)=1} / φ(s)`. -/
noncomputable def Uind (s v : ℕ) : ℝ := ind (Nat.Coprime v s) / (Nat.totient s : ℝ)

theorem ind_and (P Q : Prop) [Decidable P] [Decidable Q] :
    ind (P ∧ Q) = ind P * ind Q := by
  unfold ind; by_cases hP : P <;> by_cases hQ : Q <;> simp [hP, hQ]

theorem ind_congr {P Q : Prop} [Decidable P] [Decidable Q] (h : P ↔ Q) : ind P = ind Q := by
  unfold ind; by_cases hP : P
  · simp [hP, h.1 hP]
  · simp [hP, (not_congr h).1 hP]

/-- `I_{lr} = I_l · I_r` for coprime `l, r` (CRT). -/
theorem Iind_mul {l r : ℕ} (hlr : Nat.Coprime l r) (A B v : ℕ) :
    Iind A B (l * r) v = Iind A B l v * Iind A B r v := by
  unfold Iind
  rw [← ind_and]
  exact ind_congr (Nat.modEq_and_modEq_iff_modEq_mul hlr).symm

/-- `U_{lr} = U_l · U_r` for coprime `l, r`. -/
theorem Uind_mul {l r : ℕ} (hlr : Nat.Coprime l r) (v : ℕ) :
    Uind (l * r) v = Uind l v * Uind r v := by
  unfold Uind
  rw [Nat.totient_mul hlr, Nat.cast_mul, show ind (Nat.Coprime v (l * r)) =
    ind (Nat.Coprime v l) * ind (Nat.Coprime v r) by
      rw [← ind_and]; exact ind_congr Nat.coprime_mul_iff_right]
  ring

/-- **§2.1 Exact Type-II split.**
`I_{lr} - U_{lr} = I_l (I_r - U_r) + (I_l - U_l) U_r` for coprime `l, r`. -/
theorem typeII_split {l r : ℕ} (hlr : Nat.Coprime l r) (A B v : ℕ) :
    Iind A B (l * r) v - Uind (l * r) v =
      Iind A B l v * (Iind A B r v - Uind r v) + (Iind A B l v - Uind l v) * Uind r v := by
  rw [Iind_mul hlr, Uind_mul hlr]; ring

/-- The summed form of the split against any weight. -/
theorem typeII_split_sum {l r : ℕ} (hlr : Nat.Coprime l r) (A B : ℕ) (S : Finset ℕ)
    (w : ℕ → ℝ) :
    ∑ v ∈ S, w v * (Iind A B (l * r) v - Uind (l * r) v) =
      ∑ v ∈ S, w v * (Iind A B l v * (Iind A B r v - Uind r v)) +
        ∑ v ∈ S, w v * ((Iind A B l v - Uind l v) * Uind r v) := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  rw [typeII_split hlr]; ring

/-! ### §2.2 Relative centering source -/

/-- Multiplying by a unit modulo `f` with explicit inverse: `m n ≡ c ↔ n ≡ c m̄`. -/
theorem mul_modEq_iff_of_inv {f m minv n c : ℕ} (hinv : m * minv ≡ 1 [MOD f]) :
    m * n ≡ c [MOD f] ↔ n ≡ c * minv [MOD f] := by
  constructor
  · intro h
    calc n = 1 * n := (one_mul n).symm
      _ ≡ (m * minv) * n [MOD f] := (hinv.symm).mul_right n
      _ = minv * (m * n) := by ring
      _ ≡ minv * c [MOD f] := h.mul_left minv
      _ = c * minv := by ring
  · intro h
    calc m * n ≡ m * (c * minv) [MOD f] := h.mul_left m
      _ = c * (m * minv) := by ring
      _ ≡ c * 1 [MOD f] := hinv.mul_left c
      _ = c := mul_one c

/-- The `l`-condition of the physical sum: `A m n ≡ B (l) ↔ n ≡ B · \overline{Am} (l)`. -/
theorem affine_modEq_iff_of_inv {l A m w n B : ℕ} (hinv : (A * m) * w ≡ 1 [MOD l]) :
    A * (m * n) ≡ B [MOD l] ↔ n ≡ B * w [MOD l] := by
  rw [← mul_assoc]; exact mul_modEq_iff_of_inv hinv

/-- An explicit inverse modulo `l` forces coprimality with `l`. -/
theorem coprime_of_inv {l a w : ℕ} (h : a * w ≡ 1 [MOD l]) : Nat.Coprime a l := by
  have h1 : Nat.Coprime (a * w) l := by
    have := (Nat.ModEq.gcd_eq h)
    rw [Nat.gcd_one_left] at this
    exact this
  exact Nat.Coprime.coprime_dvd_left (dvd_mul_right a w) h1

/-- `α^{(r)}_m(n) = α(n) U_r(mn)` — the coefficient carrying the `r`-mean. -/
noncomputable def alphaR (α : ℕ → ℝ) (r m : ℕ) (n : ℕ) : ℝ := α n * Uind r (m * n)

/-- **§2.2 Relative centering source.**  For fixed `m` with explicit inverses
`m · m̄ ≡ 1 (mod f)` and `(Am) · w ≡ 1 (mod l)`, the second Type-II term summed over the
physical condition `mn ≡ c (mod f)` is the relative discrepancy
`Δ_{α^{(r)}_m}^{f, c m̄}(l, B w)`.  (`A` is not cancelled modulo `f`; only the unit
hypothesis modulo `l` is used for the `l`-condition.) -/
theorem secondTerm_eq_DeltaRel (S : Finset ℕ) (α : ℕ → ℝ) {A B f c l r m minv w : ℕ}
    (hm : m * minv ≡ 1 [MOD f]) (hAm : (A * m) * w ≡ 1 [MOD l]) :
    ∑ n ∈ S.filter (fun n => m * n ≡ c [MOD f]),
        α n * ((Iind A B l (m * n) - Uind l (m * n)) * Uind r (m * n)) =
      DeltaRel S (alphaR α r m) f (c * minv) l (B * w) := by
  have hml : Nat.Coprime m l :=
    Nat.Coprime.coprime_dvd_left (dvd_mul_left m A) (coprime_of_inv hAm)
  unfold DeltaRel
  rw [Finset.filter_congr (fun n _ => mul_modEq_iff_of_inv (n := n) (c := c) hm)]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  unfold alphaR Iind Uind
  rw [ind_congr (affine_modEq_iff_of_inv (n := n) (B := B) hAm),
    ind_congr (show Nat.Coprime (m * n) l ↔ Nat.Coprime n l from
      ⟨fun h => Nat.Coprime.coprime_dvd_left (dvd_mul_left n m) h,
       fun h => Nat.Coprime.mul_left hml h⟩)]
  ring

/-! ### §2.3 Residue-fibre density -/

/-- Pairwise-congruent elements of an interval of length `L` number at most `L/q + 1`. -/
theorem card_fibre_le {q : ℕ} (M0 L : ℕ) (T : Finset ℕ)
    (hT : T ⊆ Finset.Ico M0 (M0 + L)) (hcong : ∀ x ∈ T, ∀ y ∈ T, x ≡ y [MOD q]) :
    T.card ≤ L / q + 1 := by
  have hmaps : ∀ x ∈ T, (x - M0) / q ∈ Finset.range (L / q + 1) := by
    intro x hx
    have := Finset.mem_Ico.1 (hT hx)
    rw [Finset.mem_range]
    have : (x - M0) / q ≤ L / q := Nat.div_le_div_right (by omega)
    omega
  have hinj : Set.InjOn (fun x => (x - M0) / q) T := by
    intro x hx y hy hxy
    have hx' := Finset.mem_Ico.1 (hT hx)
    have hy' := Finset.mem_Ico.1 (hT hy)
    have hc : x - M0 ≡ y - M0 [MOD q] := by
      have h := hcong x hx y hy
      have h2 : (x - M0) + M0 ≡ (y - M0) + M0 [MOD q] := by
        rwa [Nat.sub_add_cancel hx'.1, Nat.sub_add_cancel hy'.1]
      exact Nat.ModEq.add_right_cancel' M0 h2
    have e1 := Nat.div_add_mod (x - M0) q
    have e2 := Nat.div_add_mod (y - M0) q
    simp only at hxy
    unfold Nat.ModEq at hc
    rw [hxy, hc] at e1
    omega
  calc T.card ≤ (Finset.range (L / q + 1)).card := Finset.card_le_card_of_injOn _ hmaps hinj
    _ = L / q + 1 := Finset.card_range _

/-- **§2.3 Residue-fibre density.**  For coprime `f, l` the fibre of
`m ↦ (m mod f, m mod l)` over any pair of classes `(a, b)`, inside an interval of length `L`,
has at most `L/(fl) + 1` elements. -/
theorem residueFibre_card_le {f l : ℕ} (hfl : Nat.Coprime f l)
    (M0 L a b : ℕ) :
    ((Finset.Ico M0 (M0 + L)).filter (fun m => m ≡ a [MOD f] ∧ m ≡ b [MOD l])).card ≤
      L / (f * l) + 1 := by
  refine card_fibre_le M0 L _ (Finset.filter_subset _ _) ?_
  intro x hx y hy
  have hx' := (Finset.mem_filter.1 hx).2
  have hy' := (Finset.mem_filter.1 hy).2
  exact (Nat.modEq_and_modEq_iff_modEq_mul hfl).1
    ⟨hx'.1.trans hy'.1.symm, hx'.2.trans hy'.2.symm⟩

/-- Real-valued form: fibre size `≤ L/(fl) + 1`, i.e. density `1/f` per `l`-class. -/
theorem residueFibre_density {f l : ℕ} (hfl : Nat.Coprime f l)
    (M0 L a b : ℕ) :
    ((((Finset.Ico M0 (M0 + L)).filter
      (fun m => m ≡ a [MOD f] ∧ m ≡ b [MOD l])).card : ℕ) : ℝ) ≤
      (L : ℝ) / ((f : ℝ) * l) + 1 := by
  have h := residueFibre_card_le hfl M0 L a b
  have hdiv : ((L / (f * l) : ℕ) : ℝ) ≤ (L : ℝ) / ((f : ℝ) * l) := by
    rw [← Nat.cast_mul]; exact Nat.cast_div_le
  calc _ ≤ ((L / (f * l) + 1 : ℕ) : ℝ) := by exact_mod_cast h
    _ = ((L / (f * l) : ℕ) : ℝ) + 1 := by push_cast; ring
    _ ≤ _ := by linarith

/-! ### §2.4 Ordering-B square from the physical congruences -/

/-- **Physical congruences ⟹ `n₁ ≡ n₂ (mod fl)`.** -/
theorem physical_pair_congr {f l A B c m n1 n2 : ℕ} (hmf : Nat.Coprime m f)
    (hAml : Nat.Coprime (A * m) l) (hfl : Nat.Coprime f l)
    (h1f : m * n1 ≡ c [MOD f]) (h2f : m * n2 ≡ c [MOD f])
    (h1l : A * m * n1 ≡ B [MOD l]) (h2l : A * m * n2 ≡ B [MOD l]) :
    n1 ≡ n2 [MOD f * l] := by
  refine (Nat.modEq_and_modEq_iff_modEq_mul hfl).1 ⟨?_, ?_⟩
  · exact Nat.ModEq.cancel_left_of_coprime (by rw [Nat.gcd_comm]; exact hmf)
      (h1f.trans h2f.symm)
  · exact Nat.ModEq.cancel_left_of_coprime (by rw [Nat.gcd_comm]; exact hAml)
      (h1l.trans h2l.symm)

/-- The physical condition of the first-Cauchy source. -/
abbrev physCond (f l A B c m n : ℕ) : Prop := m * n ≡ c [MOD f] ∧ A * m * n ≡ B [MOD l]

/-- **§2.4 Ordering-B square.**  First Cauchy applied to the physical sum (no character
expansion), the square opened into pairs, and every pair in the support satisfies
`n₁ ≡ n₂ (mod fl)` (given the unit hypotheses on every `m` in the outer support). -/
theorem orderingB_physical_square (Mset S : Finset ℕ) (β α : ℕ → ℝ) {f l A B c : ℕ}
    (hfl : Nat.Coprime f l) (hunit : ∀ m ∈ Mset, Nat.Coprime m f ∧ Nat.Coprime (A * m) l) :
    (∑ m ∈ Mset, β m * ∑ n ∈ S.filter (fun n => physCond f l A B c m n), α n) ^ 2 ≤
      (∑ m ∈ Mset, β m ^ 2) *
        ∑ m ∈ Mset, ∑ p ∈ S.filter (fun n => physCond f l A B c m n) ×ˢ
          S.filter (fun n => physCond f l A B c m n), α p.1 * α p.2 ∧
    ∀ m ∈ Mset, ∀ p ∈ S.filter (fun n => physCond f l A B c m n) ×ˢ
          S.filter (fun n => physCond f l A B c m n), p.1 ≡ p.2 [MOD f * l] := by
  refine ⟨?_, ?_⟩
  · have h := Finset.sum_mul_sq_le_sq_mul_sq Mset β
      (fun m => ∑ n ∈ S.filter (fun n => physCond f l A B c m n), α n)
    refine h.trans (le_of_eq ?_)
    congr 1
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [sq, Finset.sum_mul_sum, Finset.sum_product]
  · intro m hm p hp
    rw [Finset.mem_product] at hp
    have h1 := (Finset.mem_filter.1 hp.1).2
    have h2 := (Finset.mem_filter.1 hp.2).2
    exact physical_pair_congr (hunit m hm).1 (hunit m hm).2 hfl h1.1 h2.1 h1.2 h2.2

end Erdos287.SourceChain
