import RequestProject.Erdos287.Defs

/-!
# Erdős Problem #287 — the numerator bound `C`

`C j` is the largest reduced numerator of `∑_{s∈S} 1/s` over nonempty subsets
`S ⊆ {1,…,j}`.  We:

* bridge the kernel-reducing computation `numOf` to `Rat.num` (`numOf_eq_num`);
* certify the explicit values `C 1 … C 8 = 1,3,11,25,137,137,1019,2143` by `decide`;
* prove `C` is an upper bound for every subset numerator (`num_le_C`), is attained,
  is greatest (`C_spec`), and is monotone (`C_mono`).
-/

open scoped BigOperators

set_option maxHeartbeats 4000000

namespace Erdos287

/-! ## Bridge to `Rat.num` -/

/-
The fold `sumP l` computes the reduced `(numerator, denominator)` of `∑_{s∈l} 1/s`:
the denominator is positive, numerator/denominator are coprime, and the value is correct.
-/
lemma sumP_spec (l : List ℕ) (hpos : ∀ x ∈ l, 0 < x) (hnd : l.Nodup) :
    0 < (sumP l).2 ∧ Nat.Coprime (sumP l).1.natAbs (sumP l).2 ∧
      ((sumP l).1 : ℚ) / ((sumP l).2 : ℚ) = ∑ s ∈ l.toFinset, (1 : ℚ) / s := by
  induction' l with a l ih;
  · simp [sumP]
  · have := ih ( fun x hx => hpos x ( List.mem_cons_of_mem _ hx ) ) ( List.nodup_cons.mp hnd |>.2 );
    simp_all +decide [ Finset.sum_insert, List.toFinset_cons ];
    rw [ ← this.2.2, show sumP ( a :: l ) = addF ( sumP l ) ( 1, a ) from rfl ] ; simp +decide [ addF ] ;
    refine' ⟨ ⟨ Or.inr ⟨ this.1, hpos.1 ⟩, Nat.le_of_dvd ( Nat.mul_pos this.1 hpos.1 ) ( Nat.gcd_dvd_right _ _ ) ⟩, _, _ ⟩;
    · rw [ Int.natAbs_ediv_of_dvd ];
      · convert Nat.coprime_div_gcd_div_gcd _ using 1;
        exact Nat.gcd_pos_of_pos_right _ ( Nat.mul_pos this.1 hpos.1 );
      · exact Int.natCast_dvd.mpr ( Nat.gcd_dvd_left _ _ );
    · rw [ Int.cast_div, Nat.cast_div ] <;> norm_num;
      · rw [ div_div_div_cancel_right₀ ];
        · rw [ inv_eq_one_div, div_add_div ] <;> ring <;> norm_cast <;> aesop;
        · exact ne_of_gt ( Nat.cast_pos.mpr ( Nat.gcd_pos_of_pos_right _ ( Nat.mul_pos this.1 hpos.1 ) ) );
      · exact Nat.gcd_dvd_right _ _;
      · grind;
      · exact Int.natCast_dvd.mpr ( Nat.gcd_dvd_left _ _ );
      · grind

/-
`numOf l` is the numerator of `∑_{s∈l} 1/s` in lowest terms.
-/
lemma numOf_eq_num (l : List ℕ) (hpos : ∀ x ∈ l, 0 < x) (hnd : l.Nodup) :
    (∑ s ∈ l.toFinset, (1 : ℚ) / s).num = numOf l := by
  obtain ⟨a, b, h_denom_pos, h_coprime, hsum⟩ : ∃ a b : ℤ, 0 < b ∧ Int.gcd a b = 1 ∧ (∑ s ∈ l.toFinset, (1 : ℚ) / s) = a / b ∧ (numOf l, denOf l) = (a, b.natAbs) := by
    have := sumP_spec l hpos hnd;
    refine' ⟨ sumP l |>.1, sumP l |>.2, _, _, this.2.2.symm, _ ⟩ <;> aesop;
  rw [ hsum.1, Rat.num_div_eq_of_coprime ] <;> aesop

/-! ## Explicit values (certified by `decide`) -/

set_option maxRecDepth 100000

set_option maxHeartbeats 4000000 in
theorem C_one : C 1 = 1 := by decide

set_option maxHeartbeats 4000000 in
theorem C_two : C 2 = 3 := by decide

set_option maxHeartbeats 4000000 in
theorem C_three : C 3 = 11 := by decide

set_option maxHeartbeats 4000000 in
theorem C_four : C 4 = 25 := by decide

set_option maxHeartbeats 8000000 in
theorem C_five : C 5 = 137 := by decide

set_option maxHeartbeats 8000000 in
theorem C_six : C 6 = 137 := by decide

set_option maxHeartbeats 20000000 in
theorem C_seven : C 7 = 1019 := by decide

set_option maxHeartbeats 80000000 in
theorem C_eight : C 8 = 2143 := by decide

set_option maxHeartbeats 400000000 in
theorem C_nine : C 9 = 7129 := by decide

/-- The tuple `C(1..8) = (1, 3, 11, 25, 137, 137, 1019, 2143)`. -/
theorem C_values :
    C 1 = 1 ∧ C 2 = 3 ∧ C 3 = 11 ∧ C 4 = 25 ∧
      C 5 = 137 ∧ C 6 = 137 ∧ C 7 = 1019 ∧ C 8 = 2143 :=
  ⟨C_one, C_two, C_three, C_four, C_five, C_six, C_seven, C_eight⟩

/-- The witness `S = {1,2,3,4,5,7}` attains `C 7 = 1019`. -/
theorem C_seven_witness :
    (∑ s ∈ ({1, 2, 3, 4, 5, 7} : Finset ℕ), (1 : ℚ) / s).num = 1019 := by
  norm_num

/-! ## Upper bound, attainment, monotonicity -/

/-
Every nonempty subset of `{1,…,j}` has reciprocal-sum numerator at most `C j`.
-/
theorem num_le_C (j : ℕ) (S : Finset ℕ) (hne : S.Nonempty)
    (hsub : S ⊆ Finset.Icc 1 j) :
    (∑ s ∈ S, (1 : ℚ) / s).num ≤ C j := by
  -- Let `l := S.sort (· ≤ ·)`. Then `l.Nodup` (`Finset.sort_nodup`), `l.toFinset = S` (`Finset.sort_toFinset`), and `∀ x ∈ l, 0 < x` (since `x ∈ l → x ∈ S → x ∈ Finset.Icc 1 j → 1 ≤ x`). By `numOf_eq_num` (rewriting `l.toFinset = S`), `(∑ s ∈ S, (1:ℚ)/s).num = numOf l`.
  set l := S.sort (· ≤ ·) with hl
  have h_l_nodup : l.Nodup := by
    exact Finset.sort_nodup _ _
  have h_l_toFinset : l.toFinset = S := by
    aesop
  have h_l_pos : ∀ x ∈ l, 0 < x := by
    exact fun x hx => Finset.mem_Icc.mp ( hsub <| h_l_toFinset ▸ List.mem_toFinset.mpr hx ) |>.1
  have h_sum_eq : (∑ s ∈ S, (1 : ℚ) / s).num = numOf l := by
    rw [ ← h_l_toFinset, numOf_eq_num l h_l_pos h_l_nodup ];
  -- It suffices to show `numOf l` is a member of the list `(((List.range j).map (·+1)).sublists.filter (· ≠ [])).map numOf`.
  have h_mem : l ∈ ((List.range j).map (·+1)).sublists.filter (· ≠ []) := by
    simp +zetaDelta at *;
    refine' ⟨ _, _ ⟩;
    · convert List.sublist_of_subperm_of_sortedLE _ _ _;
      all_goals try infer_instance;
      · refine' List.subperm_of_subset _ _;
        · exact Finset.sort_nodup _ _;
        · intro x hx; have := hsub ( Finset.mem_sort ( α := ℕ ) ( · ≤ · ) |>.1 hx ) ; simp_all +decide [ Finset.subset_iff ] ;
          exact ⟨ x - 1, by linarith [ hsub hx, Nat.sub_add_cancel ( h_l_pos x hx ) ], Nat.succ_pred_eq_of_pos ( h_l_pos x hx ) ⟩;
      · grind +suggestions;
      · intro i j hij; simp +decide ;
        exact hij;
    · exact List.ne_nil_of_mem ( Finset.mem_sort ( α := ℕ ) ( · ≤ · ) |>.2 hne.choose_spec );
  have h_foldr_max : ∀ (a : ℤ) (L : List ℤ), a ∈ L → a ≤ L.foldr max 0 := by
    intro a L ha; induction L <;> aesop;
  exact h_sum_eq.symm ▸ h_foldr_max _ _ ( List.mem_map.mpr ⟨ l, h_mem, rfl ⟩ )

/-
`C j` is attained by some nonempty subset of `{1,…,j}` (for `j ≥ 1`).
-/
theorem C_attained (j : ℕ) (hj : 1 ≤ j) :
    ∃ S : Finset ℕ, S.Nonempty ∧ S ⊆ Finset.Icc 1 j ∧
      (∑ s ∈ S, (1 : ℚ) / s).num = C j := by
  -- Let `base := (List.range j).map (·+1)` (this is `[1,…,j]`, `Nodup`), `Lf := base.sublists.filter (·≠[])`, and `vals := Lf.map numOf`, so `C j = vals.foldr max 0`.
  set base := (List.range j).map (· + 1)
  set Lf := base.sublists.filter (· ≠ [])
  set vals := Lf.map numOf;
  -- Since `C j = vals.foldr max 0`, and `vals` contains `numOf [1] = 1`, we have `C j ≥ 1`.
  have hC_ge_1 : C j ≥ 1 := by
    refine' le_trans _ ( num_le_C j { 1 } _ _ ) <;> norm_num [ hj ];
  -- By `Helper A`, `C j` is in `vals`, i.e., `∃ l₀ ∈ Lf, numOf l₀ = C j`.
  obtain ⟨l₀, hl₀⟩ : ∃ l₀ ∈ Lf, numOf l₀ = C j := by
    have hC_in_vals : C j ∈ vals := by
      have hC_in_vals : ∀ {L : List ℤ}, L ≠ [] → L.foldr max 0 = 0 ∨ L.foldr max 0 ∈ L := by
        intros L hL_nonempty; induction' L with hd tl ih <;> simp_all +decide [ List.foldr ] ;
        grind +splitImp;
      convert hC_in_vals _ |> Or.resolve_left <| ne_of_gt <| hC_ge_1 using 1;
      aesop;
    grind;
  refine' ⟨ l₀.toFinset, _, _, _ ⟩;
  · aesop;
  · intro x hx; simp_all +decide ;
    have := List.mem_sublists.mp ( List.mem_filter.mp hl₀.1 |>.1 ) ; ( have := List.mem_map.mp ( this.subset hx ) ; aesop; );
  · convert numOf_eq_num l₀ _ _;
    · exact hl₀.2.symm;
    · simp +zetaDelta at *;
      exact fun x hx => Nat.pos_of_ne_zero fun h => by have := hl₀.1.1.subset hx; aesop;
    · have h_l₀_sublist : l₀.Sublist base := by
        aesop;
      exact h_l₀_sublist.nodup ( by exact List.Nodup.map ( fun x y hxy => by simpa using hxy ) ( List.nodup_range ) )

/-- `C j` is the greatest reciprocal-sum numerator over nonempty subsets of `{1,…,j}`. -/
theorem C_spec (j : ℕ) (hj : 1 ≤ j) :
    IsGreatest
      ((fun S : Finset ℕ => (∑ s ∈ S, (1 : ℚ) / s).num) ''
        {S : Finset ℕ | S.Nonempty ∧ S ⊆ Finset.Icc 1 j}) (C j) := by
  constructor
  · obtain ⟨S, hne, hsub, hval⟩ := C_attained j hj
    exact ⟨S, ⟨hne, hsub⟩, hval⟩
  · rintro x ⟨S, ⟨hne, hsub⟩, rfl⟩
    exact num_le_C j S hne hsub

/-
`C` is monotone.
-/
theorem C_mono {i j : ℕ} (hij : i ≤ j) : C i ≤ C j := by
  by_cases hi : 1 ≤ i;
  · have := C_attained i hi;
    exact this.choose_spec.2.2 ▸ num_le_C j _ this.choose_spec.1 ( this.choose_spec.2.1.trans ( Finset.Icc_subset_Icc_right hij ) );
  · interval_cases i;
    unfold C;
    induction' ( List.range j ) with j hj <;> simp_all +decide;
    simp_all +decide [ List.sublists_cons ];
    induction ( List.map ( fun x => x + 1 ) hj ).sublists <;> simp_all +decide [ List.flatMap ];
    induction ( List.filter ( fun l => !decide ( l = [] ) ) ( ‹_› :: ( ( j + 1 ) :: ‹_› ) :: ( List.map ( fun x => [ x, ( j + 1 ) :: x ] ) ‹_› ).flatten ) ) <;> simp_all +decide

end Erdos287