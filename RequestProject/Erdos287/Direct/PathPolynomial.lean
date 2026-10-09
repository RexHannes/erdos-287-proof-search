import RequestProject.Erdos287.Direct.LCMCarry

/-!
# Route D — the physical path polynomial

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

Given a set `V` of free positions and integral weights `w`, the *physical path polynomial* is

`P_V(X) = ∑_{J ⊆ V, J has no two consecutive positions} X^{∑_{n ∈ J} w n}`.

The exponents are integral by construction: the intended instantiation is `w n = ℓ / n` for a
common multiple `ℓ` of the positions, so `X^τ` tracks the exact cleared-denominator value of
the reciprocal sum.

Kernel-proved here:

* `pathPoly_coeff` — the `τ`-th coefficient counts the admissible independent sets of weight `τ`;
* `pathPoly_coeff_pos_iff` — positivity of the coefficient is exactly solvability;
* `exact_reciprocal_target` — **the exact target theorem**:
  `∑_{n ∈ P ∪ J} 1/n = 1 ↔ [X^τ] P_V(X)` counts `J`, i.e. the reciprocal equation for a pinned
  set `P` completed by a free independent set `J` is *equivalent* to positivity of the
  coefficient of `X^τ`, where `τ` is the exact residual `ℓ − ∑_{n ∈ P} ℓ/n`;
* `pathPoly_recurrence` — the path (transfer-matrix) recurrence `F_i = F_{i-1} + X^{w_i} F_{i-2}`;
* `pathPoly_mul_of_separated` — the product factorisation across physically separated
  components.
-/

open scoped BigOperators

namespace Erdos287
namespace Direct

/-! ## D.17  Independent (no-two-consecutive) subsets -/

/-- The admissible ("physical") subsets of `V`: no two consecutive positions. -/
def indepSubsets (V : Finset ℕ) : Finset (Finset ℕ) :=
  V.powerset.filter (fun J => ∀ n ∈ J, n + 1 ∉ J)

@[simp] theorem mem_indepSubsets {V J : Finset ℕ} :
    J ∈ indepSubsets V ↔ J ⊆ V ∧ ∀ n ∈ J, n + 1 ∉ J := by
  simp [indepSubsets, Finset.mem_filter, Finset.mem_powerset]

/-- The integral weight of an admissible subset. -/
def weightSum (w : ℕ → ℕ) (J : Finset ℕ) : ℕ := ∑ n ∈ J, w n

/-- The physical path polynomial of the free set `V`. -/
noncomputable def pathPoly (V : Finset ℕ) (w : ℕ → ℕ) : Polynomial ℤ :=
  ∑ J ∈ indepSubsets V, Polynomial.X ^ (weightSum w J)

/-! ## D.18  Coefficients -/

/-- **`pathPoly_coeff`.**  `KERNEL-PROVED`.  The `τ`-th coefficient of the path polynomial is
the number of admissible subsets of weight `τ`. -/
theorem pathPoly_coeff (V : Finset ℕ) (w : ℕ → ℕ) (τ : ℕ) :
    (pathPoly V w).coeff τ =
      (((indepSubsets V).filter (fun J => weightSum w J = τ)).card : ℤ) := by
  rw [pathPoly, Polynomial.finset_sum_coeff]
  simp only [Polynomial.coeff_X_pow]
  rw [Finset.sum_boole]
  congr 1
  refine congrArg Finset.card (Finset.filter_congr fun J _ => ?_)
  exact eq_comm

/-- **`pathPoly_coeff_pos_iff`.**  `KERNEL-PROVED`.  A coefficient is positive exactly when
some admissible subset has that weight; coefficients are never negative. -/
theorem pathPoly_coeff_pos_iff (V : Finset ℕ) (w : ℕ → ℕ) (τ : ℕ) :
    0 < (pathPoly V w).coeff τ ↔ ∃ J ∈ indepSubsets V, weightSum w J = τ := by
  rw [pathPoly_coeff]
  constructor
  · intro h
    have hcard : 0 < ((indepSubsets V).filter (fun J => weightSum w J = τ)).card := by
      exact_mod_cast h
    obtain ⟨J, hJ⟩ := Finset.card_pos.1 hcard
    rw [Finset.mem_filter] at hJ
    exact ⟨J, hJ.1, hJ.2⟩
  · rintro ⟨J, hJ, hw⟩
    have hne : ((indepSubsets V).filter (fun J => weightSum w J = τ)).Nonempty :=
      ⟨J, Finset.mem_filter.2 ⟨hJ, hw⟩⟩
    exact_mod_cast Finset.card_pos.2 hne

/-! ## D.19  The exact reciprocal target -/

/-- **`recipSum_union_eq_one_iff`.**  `KERNEL-PROVED`.  With a common multiple `ℓ` of all
positions, the reciprocal equation for `P ∪ J` is the exact integral weight equation for `J`. -/
theorem recipSum_union_eq_one_iff {P J : Finset ℕ} {ell τ : ℕ} (hell : ell ≠ 0)
    (hdisj : Disjoint P J)
    (hP : ∀ n ∈ P, n ≠ 0 ∧ n ∣ ell) (hJ : ∀ n ∈ J, n ≠ 0 ∧ n ∣ ell)
    (hτ : (∑ n ∈ P, ell / n) + τ = ell) :
    recipSum (P ∪ J) = 1 ↔ weightSum (fun n => ell / n) J = τ := by
  have hmem : ∀ n ∈ P ∪ J, n ≠ 0 ∧ n ∣ ell := by
    intro n hn
    rcases Finset.mem_union.1 hn with h | h
    · exact hP n h
    · exact hJ n h
  have hclear := clearing_identity (A := P ∪ J) (D := ell)
    (fun n hn => (hmem n hn).2) (fun n hn => (hmem n hn).1)
  have hsplit : (∑ n ∈ P ∪ J, ell / n) = (∑ n ∈ P, ell / n) + ∑ n ∈ J, ell / n :=
    Finset.sum_union hdisj
  have hellQ : (ell : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hell
  constructor
  · intro h
    rw [h, mul_one] at hclear
    have : (∑ n ∈ P ∪ J, ell / n) = ell := by exact_mod_cast hclear
    rw [hsplit] at this
    show (∑ n ∈ J, ell / n) = τ
    omega
  · intro h
    have h' : (∑ n ∈ J, ell / n) = τ := h
    have hnat : (∑ n ∈ P ∪ J, ell / n) = ell := by rw [hsplit, h']; omega
    rw [hnat] at hclear
    have : (ell : ℚ) = ell * recipSum (P ∪ J) := by exact_mod_cast hclear
    field_simp at this
    exact this.symm

/-- **`exact_reciprocal_target`.**  `KERNEL-PROVED`.  *The* exact target theorem of Route D:
completing the pinned set `P` by a physical (no-two-consecutive) subset of the free set `V` to
reciprocal sum `1` is **equivalent** to positivity of the coefficient of `X^τ` in the path
polynomial, `τ` being the exact residual `ℓ − ∑_{n∈P} ℓ/n`. -/
theorem exact_reciprocal_target {P V : Finset ℕ} {ell τ : ℕ} (hell : ell ≠ 0)
    (hdisj : Disjoint P V)
    (hP : ∀ n ∈ P, n ≠ 0 ∧ n ∣ ell) (hV : ∀ n ∈ V, n ≠ 0 ∧ n ∣ ell)
    (hτ : (∑ n ∈ P, ell / n) + τ = ell) :
    (∃ J ∈ indepSubsets V, recipSum (P ∪ J) = 1) ↔
      0 < (pathPoly V (fun n => ell / n)).coeff τ := by
  rw [pathPoly_coeff_pos_iff]
  constructor
  · rintro ⟨J, hJ, hsum⟩
    have hJV : J ⊆ V := (mem_indepSubsets.1 hJ).1
    refine ⟨J, hJ, ?_⟩
    exact (recipSum_union_eq_one_iff hell (Finset.disjoint_of_subset_right hJV hdisj) hP
      (fun n hn => hV n (hJV hn)) hτ).1 hsum
  · rintro ⟨J, hJ, hw⟩
    have hJV : J ⊆ V := (mem_indepSubsets.1 hJ).1
    refine ⟨J, hJ, ?_⟩
    exact (recipSum_union_eq_one_iff hell (Finset.disjoint_of_subset_right hJV hdisj) hP
      (fun n hn => hV n (hJV hn)) hτ).2 hw

/-! ## D.20  The path recurrence -/

theorem indepSubsets_filter_notMem (a j : ℕ) :
    (indepSubsets (Finset.Icc a (j + 1))).filter (fun J => (j + 1) ∉ J) =
      indepSubsets (Finset.Icc a j) := by
  ext J
  simp only [Finset.mem_filter, mem_indepSubsets]
  constructor
  · rintro ⟨⟨hsub, hind⟩, hnot⟩
    refine ⟨fun n hn => ?_, hind⟩
    have := hsub hn
    rw [Finset.mem_Icc] at this ⊢
    refine ⟨this.1, ?_⟩
    rcases Nat.lt_or_ge n (j + 1) with h | h
    · omega
    · exact absurd (by omega : n = j + 1) (fun hEq => hnot (hEq ▸ hn))
  · rintro ⟨hsub, hind⟩
    refine ⟨⟨fun n hn => ?_, hind⟩, fun hmem => ?_⟩
    · have := hsub hn
      rw [Finset.mem_Icc] at this ⊢
      omega
    · have := hsub hmem
      rw [Finset.mem_Icc] at this
      omega

/-- **`pathPoly_recurrence`.**  `KERNEL-PROVED`.  The transfer-matrix recurrence along a
physical path: `F_{i} = F_{i-1} + X^{w_i} · F_{i-2}`. -/
theorem pathPoly_recurrence {a j : ℕ} (ha : 1 ≤ a) (haj : a ≤ j) (w : ℕ → ℕ) :
    pathPoly (Finset.Icc a (j + 1)) w =
      pathPoly (Finset.Icc a j) w + Polynomial.X ^ (w (j + 1)) * pathPoly (Finset.Icc a (j - 1)) w := by
  classical
  have hsplit :
      pathPoly (Finset.Icc a (j + 1)) w =
        (∑ J ∈ (indepSubsets (Finset.Icc a (j + 1))).filter (fun J => (j + 1) ∉ J),
          Polynomial.X ^ (weightSum w J)) +
        (∑ J ∈ (indepSubsets (Finset.Icc a (j + 1))).filter (fun J => (j + 1) ∈ J),
          Polynomial.X ^ (weightSum w J)) := by
    rw [pathPoly, ← Finset.sum_filter_add_sum_filter_not _ (fun J => (j + 1) ∉ J)]
    simp
  rw [hsplit, indepSubsets_filter_notMem a j]
  congr 1
  -- the sets containing `j+1` biject with the admissible subsets of `[a, j-1]`
  · rw [pathPoly, Finset.mul_sum]
    refine (Finset.sum_nbij' (fun K => insert (j + 1) K) (fun J => J.erase (j + 1))
      ?_ ?_ ?_ ?_ ?_).symm
    · intro K hK
      show insert (j + 1) K ∈ _
      rw [Finset.mem_filter, mem_indepSubsets]
      simp only [mem_indepSubsets] at hK
      obtain ⟨hsub, hind⟩ := hK
      have hKb : ∀ n ∈ K, a ≤ n ∧ n ≤ j - 1 := by
        intro n hn; have := hsub hn; rw [Finset.mem_Icc] at this; exact this
      refine ⟨⟨fun n hn => ?_, fun n hn => ?_⟩, Finset.mem_insert_self _ _⟩
      · rcases Finset.mem_insert.1 hn with rfl | hn
        · rw [Finset.mem_Icc]; omega
        · have := hKb n hn; rw [Finset.mem_Icc]; omega
      · rcases Finset.mem_insert.1 hn with rfl | hn'
        · intro hmem
          rcases Finset.mem_insert.1 hmem with h | h
          · omega
          · have := hKb _ h; omega
        · have hnb := hKb n hn'
          intro hmem
          rcases Finset.mem_insert.1 hmem with h | h
          · omega
          · exact hind n hn' h
    · intro J hJ
      rw [Finset.mem_filter, mem_indepSubsets] at hJ
      obtain ⟨⟨hsub, hind⟩, hmem⟩ := hJ
      show J.erase (j + 1) ∈ _
      rw [mem_indepSubsets]
      refine ⟨fun n hn => ?_, fun n hn => ?_⟩
      · have hn' : n ∈ J := Finset.mem_of_mem_erase hn
        have hne : n ≠ j + 1 := Finset.ne_of_mem_erase hn
        have hb := hsub hn'
        rw [Finset.mem_Icc] at hb ⊢
        refine ⟨hb.1, ?_⟩
        rcases Nat.lt_or_ge n j with h | h
        · omega
        · exfalso
          have : n = j := by omega
          subst this
          exact hind n hn' (by simpa using hmem)
      · intro hcon
        exact hind n (Finset.mem_of_mem_erase hn) (Finset.mem_of_mem_erase hcon)
    · intro K hK
      simp only [mem_indepSubsets] at hK
      have hKb : ∀ n ∈ K, a ≤ n ∧ n ≤ j - 1 := by
        intro n hn; have := hK.1 hn; rw [Finset.mem_Icc] at this; exact this
      have hnotK : (j + 1) ∉ K := by
        intro hmem; have := hKb _ hmem; omega
      show (insert (j + 1) K).erase (j + 1) = K
      rw [Finset.erase_insert hnotK]
    · intro J hJ
      rw [Finset.mem_filter] at hJ
      show insert (j + 1) (J.erase (j + 1)) = J
      exact Finset.insert_erase hJ.2
    · intro K hK
      simp only [mem_indepSubsets] at hK
      have hKb : ∀ n ∈ K, a ≤ n ∧ n ≤ j - 1 := by
        intro n hn; have := hK.1 hn; rw [Finset.mem_Icc] at this; exact this
      have hnot : (j + 1) ∉ K := by
        intro hmem; have := hKb _ hmem; omega
      show Polynomial.X ^ (w (j + 1)) * Polynomial.X ^ (weightSum w K)
        = Polynomial.X ^ (weightSum w (insert (j + 1) K))
      have hws : weightSum w (insert (j + 1) K) = w (j + 1) + weightSum w K := by
        simp [weightSum, Finset.sum_insert hnot]
      rw [hws, pow_add]

/-! ## D.21  Factorisation across physically separated components -/

/-- Two position sets are *physically separated* when they are disjoint and no position of one
is adjacent to a position of the other. -/
def Separated (V₁ V₂ : Finset ℕ) : Prop :=
  Disjoint V₁ V₂ ∧ ∀ n ∈ V₁, ∀ m ∈ V₂, n + 1 ≠ m ∧ m + 1 ≠ n

/-- **`pathPoly_mul_of_separated`.**  `KERNEL-PROVED`.  The path polynomial factorises across
physically separated components. -/
theorem pathPoly_mul_of_separated {V₁ V₂ : Finset ℕ} (h : Separated V₁ V₂) (w : ℕ → ℕ) :
    pathPoly (V₁ ∪ V₂) w = pathPoly V₁ w * pathPoly V₂ w := by
  classical
  obtain ⟨hdisj, hadj⟩ := h
  rw [pathPoly, pathPoly, pathPoly, Finset.sum_mul_sum, ← Finset.sum_product']
  refine (Finset.sum_nbij' (fun p : Finset ℕ × Finset ℕ => p.1 ∪ p.2)
    (fun J => (J ∩ V₁, J ∩ V₂)) ?_ ?_ ?_ ?_ ?_).symm
  · rintro ⟨J₁, J₂⟩ hp
    rw [Finset.mem_product] at hp
    obtain ⟨hs₁, hi₁⟩ := mem_indepSubsets.1 hp.1
    obtain ⟨hs₂, hi₂⟩ := mem_indepSubsets.1 hp.2
    show J₁ ∪ J₂ ∈ indepSubsets (V₁ ∪ V₂)
    rw [mem_indepSubsets]
    refine ⟨Finset.union_subset (hs₁.trans Finset.subset_union_left)
      (hs₂.trans Finset.subset_union_right), ?_⟩
    intro n hn hcon
    rcases Finset.mem_union.1 hn with hn₁ | hn₂
    · rcases Finset.mem_union.1 hcon with hc₁ | hc₂
      · exact hi₁ n hn₁ hc₁
      · exact (hadj n (hs₁ hn₁) (n + 1) (hs₂ hc₂)).1 rfl
    · rcases Finset.mem_union.1 hcon with hc₁ | hc₂
      · exact (hadj (n + 1) (hs₁ hc₁) n (hs₂ hn₂)).2 rfl
      · exact hi₂ n hn₂ hc₂
  · intro J hJ
    obtain ⟨hsub, hind⟩ := mem_indepSubsets.1 hJ
    show ((J ∩ V₁, J ∩ V₂) : Finset ℕ × Finset ℕ) ∈ indepSubsets V₁ ×ˢ indepSubsets V₂
    rw [Finset.mem_product]
    constructor <;>
      · rw [mem_indepSubsets]
        refine ⟨Finset.inter_subset_right, fun n hn hcon => ?_⟩
        exact hind n (Finset.mem_of_mem_inter_left hn) (Finset.mem_of_mem_inter_left hcon)
  · rintro ⟨J₁, J₂⟩ hp
    rw [Finset.mem_product] at hp
    have hs₁ : J₁ ⊆ V₁ := (mem_indepSubsets.1 hp.1).1
    have hs₂ : J₂ ⊆ V₂ := (mem_indepSubsets.1 hp.2).1
    show ((J₁ ∪ J₂) ∩ V₁, (J₁ ∪ J₂) ∩ V₂) = (J₁, J₂)
    have h1 : (J₁ ∪ J₂) ∩ V₁ = J₁ := by
      ext x
      simp only [Finset.mem_inter, Finset.mem_union]
      constructor
      · rintro ⟨hx | hx, hxV⟩
        · exact hx
        · exact absurd hxV (Finset.disjoint_right.1 hdisj (hs₂ hx))
      · intro hx; exact ⟨Or.inl hx, hs₁ hx⟩
    have h2 : (J₁ ∪ J₂) ∩ V₂ = J₂ := by
      ext x
      simp only [Finset.mem_inter, Finset.mem_union]
      constructor
      · rintro ⟨hx | hx, hxV⟩
        · exact absurd hxV (Finset.disjoint_left.1 hdisj (hs₁ hx))
        · exact hx
      · intro hx; exact ⟨Or.inr hx, hs₂ hx⟩
    rw [h1, h2]
  · intro J hJ
    obtain ⟨hsub, -⟩ := mem_indepSubsets.1 hJ
    show J ∩ V₁ ∪ J ∩ V₂ = J
    rw [← Finset.inter_union_distrib_left]
    exact Finset.inter_eq_left.2 hsub
  · rintro ⟨J₁, J₂⟩ hp
    rw [Finset.mem_product] at hp
    have hs₁ : J₁ ⊆ V₁ := (mem_indepSubsets.1 hp.1).1
    have hs₂ : J₂ ⊆ V₂ := (mem_indepSubsets.1 hp.2).1
    have hdJ : Disjoint J₁ J₂ :=
      Finset.disjoint_of_subset_left hs₁ (Finset.disjoint_of_subset_right hs₂ hdisj)
    show Polynomial.X ^ (weightSum w J₁) * Polynomial.X ^ (weightSum w J₂)
      = Polynomial.X ^ (weightSum w (J₁ ∪ J₂))
    have hws : weightSum w (J₁ ∪ J₂) = weightSum w J₁ + weightSum w J₂ := by
      simp [weightSum, Finset.sum_union hdJ]
    rw [hws, pow_add]

end Direct
end Erdos287
