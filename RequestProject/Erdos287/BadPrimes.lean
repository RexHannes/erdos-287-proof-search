import RequestProject.Erdos287.Window

/-!
# Erdős Problem #287 — window-restricted bad-prime exclusion (certificate-driven)

For `A ⊆ [N, M]` with `∑ 1/a = 1` and a prime `p`, the *bad-prime check* at exponent `e`
asks whether some nonempty set of cofactors `S ⊆ [⌈N/pᵉ⌉, ⌊M/pᵉ⌋]`, all coprime to `p`,
satisfies `p ∣ num(∑_{s∈S} 1/s)`.  The top `p`-adic layer always supplies such a witness
when `e = topExp A p ≥ 1` (`topLayer_badPrime_witness`).  Consequently, if the check finds
**no** witness at the top exponent (a finite certificate, `BadPrimeWitnessAbsent`), then no
element of `A` is divisible by `p` (`windowRestricted_badPrimes_exclusion`).

Reconstruction note.  The literal reading `q = p^e` with a *fixed* `e` is unsound when the
true top exponent `E = topExp A p` exceeds `e`: the top-layer cofactors `a / p^E` can drop
below `⌈N/p^e⌉`, escaping the window.  The correct window uses the *actual* top exponent
`E = topExp A p`, which is what the argument requires; that is the version certified here.
-/

open scoped BigOperators

set_option maxHeartbeats 4000000

namespace Erdos287

/-- The bad-prime certificate: there is **no** nonempty cofactor set inside the window
`[⌈N/pᵉ⌉, ⌊M/pᵉ⌋]`, coprime to `p`, whose reciprocal-sum numerator is divisible by `p`.
(`⌈N/pᵉ⌉` is written as the natural-number ceiling division `(N + pᵉ - 1) / pᵉ`.) -/
def BadPrimeWitnessAbsent (N M p e : ℕ) : Prop :=
  ¬ ∃ S : Finset ℕ, S.Nonempty ∧
      S ⊆ Finset.Icc ((N + p ^ e - 1) / p ^ e) (M / p ^ e) ∧
      (∀ s ∈ S, ¬ p ∣ s) ∧ (p : ℤ) ∣ (∑ s ∈ S, (1 : ℚ) / s).num

/-
**Top-layer bad-prime witness.**  When the top `p`-adic exponent `E = topExp A p`
is at least `1`, the image of the top layer under `a ↦ a / p^E` is a nonempty cofactor
set inside `[⌈N/p^E⌉, ⌊M/p^E⌋]`, coprime to `p`, whose reciprocal-sum numerator is
divisible by `p`.
-/
theorem topLayer_badPrime_witness
    (A : Finset ℕ) (N M p : ℕ) (hp : p.Prime)
    (hpos : ∀ a ∈ A, 0 < a) (hNa : ∀ a ∈ A, N ≤ a) (hAM : ∀ a ∈ A, a ≤ M)
    (hsum : ∑ a ∈ A, (1 : ℚ) / a = 1)
    (he : 1 ≤ topExp A p) :
    ∃ S : Finset ℕ, S.Nonempty ∧
      S ⊆ Finset.Icc ((N + p ^ (topExp A p) - 1) / p ^ (topExp A p))
        (M / p ^ (topExp A p)) ∧
      (∀ s ∈ S, ¬ p ∣ s) ∧ (p : ℤ) ∣ (∑ s ∈ S, (1 : ℚ) / s).num := by
  refine' ⟨ Finset.image ( fun a => a / p ^ topExp A p ) ( topLayer A p ), _, _, _, _ ⟩;
  · -- Since $A$ is nonempty and $topExp A p \geq 1$, there exists at least one element $a \in A$ such that $Nat.factorization a p = topExp A p$.
    obtain ⟨a, ha⟩ : ∃ a ∈ A, Nat.factorization a p = topExp A p := by
      rcases A.eq_empty_or_nonempty with ( rfl | ⟨ a, ha ⟩ ) <;> simp_all +decide [ topExp ];
      exact Finset.exists_max_image _ _ ⟨ a, ha ⟩ |> fun ⟨ x, hx₁, hx₂ ⟩ => ⟨ x, hx₁, le_antisymm ( Finset.le_sup ( f := fun a => Nat.factorization a p ) hx₁ ) ( Finset.sup_le fun y hy => hx₂ y hy ) ⟩;
    exact ⟨ _, Finset.mem_image_of_mem _ ( Finset.mem_filter.mpr ⟨ ha.1, ha.2 ⟩ ) ⟩;
  · intro;
    simp +zetaDelta at *;
    intro x hx rfl; rw [ Nat.div_le_iff_le_mul_add_pred ] <;> norm_num;
    · constructor;
      · linarith [ hNa x ( Finset.mem_filter.mp hx |>.1 ), Nat.div_mul_cancel ( show p ^ topExp A p ∣ x from Nat.dvd_trans ( pow_dvd_pow _ ( Finset.mem_filter.mp hx |>.2.ge ) ) ( Nat.ordProj_dvd _ _ ) ), Nat.sub_add_cancel ( Nat.one_le_pow ( topExp A p ) p hp.pos ) ];
      · exact Nat.div_le_div_right ( hAM x ( topLayer_subset _ _ hx ) );
    · exact pow_pos hp.pos _;
  · simp +zetaDelta at *;
    intro a ha; rw [ Nat.dvd_div_iff_mul_dvd ];
    · rw [ ← pow_succ ];
      exact Nat.pow_succ_factorization_not_dvd ( ne_of_gt ( hpos a ( Finset.mem_filter.mp ha |>.1 ) ) ) hp |> fun h => fun h' => h ( dvd_trans ( pow_dvd_pow _ ( Nat.succ_le_of_lt ( Finset.mem_filter.mp ha |>.2.symm ▸ Nat.lt_succ_self _ ) ) ) h' );
    · exact Nat.dvd_trans ( pow_dvd_pow _ ( show topExp A p ≤ Nat.factorization a p from by rw [ mem_topLayer ] at ha; aesop ) ) ( Nat.ordProj_dvd _ _ );
  · convert dvd_num_of_sum_inv_zero ( Finset.image ( fun a => a / p ^ topExp A p ) ( topLayer A p ) ) p hp _ _ _ using 1;
    · simp +zetaDelta at *;
      exact fun a ha => ⟨ pow_pos hp.pos _, Nat.le_of_dvd ( hpos a ( topLayer_subset _ _ ha ) ) ( Nat.dvd_trans ( pow_dvd_pow _ ( show topExp A p ≤ Nat.factorization a p from by rw [ mem_topLayer ] at ha; exact ha.2.ge ) ) ( Nat.ordProj_dvd _ _ ) ) ⟩;
    · simp +zetaDelta at *;
      intro a ha; rw [ Nat.dvd_div_iff_mul_dvd ];
      · exact Nat.pow_succ_factorization_not_dvd ( ne_of_gt ( hpos a ( Finset.mem_filter.mp ha |>.1 ) ) ) hp |> fun h => fun h' => h ( dvd_trans ( pow_dvd_pow _ ( Nat.succ_le_of_lt ( show Nat.factorization a p < topExp A p + 1 from Nat.lt_succ_of_le ( Finset.le_sup ( f := fun a => Nat.factorization a p ) ( Finset.mem_filter.mp ha |>.1 ) ) ) ) ) h' );
      · exact Nat.dvd_trans ( pow_dvd_pow _ ( show topExp A p ≤ Nat.factorization a p from by rw [ mem_topLayer ] at ha; aesop ) ) ( Nat.ordProj_dvd _ _ );
    · rw [ Finset.sum_image ];
      · convert topLayer_congruence A p hp hpos hsum he using 1;
        exact Finset.sum_congr rfl fun x hx => by rw [ mem_topLayer.mp hx |>.2 ] ;
      · intro a ha b hb; have := Nat.div_mul_cancel ( Nat.ordProj_dvd a p ) ; have := Nat.div_mul_cancel ( Nat.ordProj_dvd b p ) ; simp_all +decide [ Nat.factorization_eq_zero_iff ] ;
        simp_all +decide [ mem_topLayer ];
        aesop

/-
**Window-restricted bad-prime exclusion.**  If the bad-prime check finds no witness at
the top exponent `E = topExp A p`, then no element of `A` is divisible by `p`.
-/
theorem windowRestricted_badPrimes_exclusion
    (A : Finset ℕ) (N M p : ℕ) (hp : p.Prime)
    (hpos : ∀ a ∈ A, 0 < a) (hNa : ∀ a ∈ A, N ≤ a) (hAM : ∀ a ∈ A, a ≤ M)
    (hsum : ∑ a ∈ A, (1 : ℚ) / a = 1)
    (hcheck : BadPrimeWitnessAbsent N M p (topExp A p)) :
    ∀ a ∈ A, ¬ p ∣ a := by
  contrapose! hcheck; simp_all +decide [ BadPrimeWitnessAbsent ] ;
  convert topLayer_badPrime_witness A N M p hp hpos hNa hAM _ _ using 1;
  · grobner;
  · grind +splitImp;
  · exact Finset.le_sup ( f := fun a => Nat.factorization a p ) hcheck.choose_spec.1 |> le_trans ( Nat.pos_of_ne_zero ( Finsupp.mem_support_iff.mp ( by have := hcheck.choose_spec.2; exact Nat.mem_primeFactors.mpr ⟨ hp, this, by linarith [ hpos _ hcheck.choose_spec.1 ] ⟩ ) ) )

end Erdos287