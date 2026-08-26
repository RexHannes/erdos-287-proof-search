import RequestProject.Erdos287.TopLayer

/-!
# Erdős Problem #287 — symmetric-function congruence and the `√M` fiber dichotomy

Two further certified structural facts:

* `topLayer_symm_congruence` (target 4): the general congruence.  If the top `p`-adic
  layer has cofactors `m₁,…,mₖ`, then `p ∣ e_{k-1}(m₁,…,mₖ)`, where
  `e_{k-1} = ∑ᵢ ∏_{j≠i} mⱼ` is the `(k-1)`-st elementary symmetric polynomial.  This
  unifies the doubleton (`k=2`, `e₁ = m₁+m₂`) and tripleton (`k=3`,
  `e₂ = m₁m₂+m₁m₃+m₂m₃`) obstructions.

* `fiber_dichotomy_sqrtM` (target 5).  If `p² > M` then the `p`-fiber
  `{a ∈ A : p ∣ a}` equals the top layer (when nonempty), and if its size is `k` then
  `p^k ≤ k · M^{k-1}`.  We extract the `k = 1, 2, 3` corollaries.
-/

open scoped BigOperators

set_option maxHeartbeats 4000000

namespace Erdos287

/-! ## Target 4 — the elementary-symmetric congruence -/

/-
**General top-layer congruence.**  With cofactors `m_a = ordCompl[p] a` over the top
`p`-adic layer `L`, the `(k-1)`-st elementary symmetric polynomial
`∑_{a∈L} ∏_{b∈L\{a}} m_b` is divisible by `p`.
-/
theorem topLayer_symm_congruence
    (A : Finset ℕ) (p : ℕ) (hp : p.Prime)
    (hpos : ∀ a ∈ A, 0 < a)
    (hsum : ∑ a ∈ A, (1 : ℚ) / a = 1)
    (he : 1 ≤ topExp A p) :
    (p : ℕ) ∣ ∑ a ∈ topLayer A p, ∏ b ∈ (topLayer A p).erase a, ordCompl[p] b := by
  have h_cong : (∑ a ∈ topLayer A p, (∏ b ∈ (topLayer A p).erase a, (b / p ^ (Nat.factorization b p) : ZMod p))) = 0 := by
    convert congr_arg ( fun x : ZMod p => x * ∏ a ∈ topLayer A p, ( a / p ^ a.factorization p : ZMod p ) ) ( topLayer_congruence A p hp hpos hsum he ) using 1;
    · haveI := Fact.mk hp; rw [ Finset.sum_mul _ _ _ ] ; refine' Finset.sum_congr rfl fun x hx => _ ; rw [ inv_mul_eq_div, eq_div_iff ] ;
      · rw [ Finset.prod_erase_mul _ _ hx ];
      · rw [ Ne.eq_def, ZMod.natCast_eq_zero_iff ];
        exact Nat.not_dvd_ordCompl hp ( ne_of_gt ( hpos x ( Finset.mem_filter.mp hx |>.1 ) ) );
    · ring;
  simp_all +decide [ ← ZMod.natCast_eq_zero_iff ]

/-! ## Target 5 — the `√M` fiber dichotomy -/

/-- The `p`-fiber of `A`: the elements divisible by `p`. -/
def pFiber (A : Finset ℕ) (p : ℕ) : Finset ℕ := A.filter (fun a => p ∣ a)

lemma mem_pFiber {A : Finset ℕ} {p a : ℕ} : a ∈ pFiber A p ↔ a ∈ A ∧ p ∣ a := by
  simp [pFiber]

/-
If `M < p²` and `a ∈ A` with `a ≤ M` is divisible by `p`, then `v_p(a) = 1`.
-/
theorem factorization_eq_one_of_sq {M p a : ℕ} (hp : p.Prime)
    (hpos : 0 < a) (hAM : a ≤ M) (hsq : M < p ^ 2) (hdvd : p ∣ a) :
    Nat.factorization a p = 1 := by
  exact le_antisymm ( Nat.le_of_not_lt fun h => by have := Nat.ordProj_dvd a p; ( have := Nat.dvd_trans ( pow_dvd_pow _ h ) this; nlinarith [ Nat.le_of_dvd ( by positivity ) this ] ) ) ( Nat.pos_of_ne_zero ( Finsupp.mem_support_iff.mp ( by aesop ) ) )

/-
**Fiber dichotomy.**  When `M < p²`, a nonempty `p`-fiber coincides with the top
`p`-adic layer.
-/
theorem pFiber_eq_topLayer_of_sq (A : Finset ℕ) (M p : ℕ) (hp : p.Prime)
    (hpos : ∀ a ∈ A, 0 < a) (hAM : ∀ a ∈ A, a ≤ M) (hsq : M < p ^ 2)
    (hne : (pFiber A p).Nonempty) :
    pFiber A p = topLayer A p := by
  ext a;
  constructor <;> intro ha;
  · have h_topExp : topExp A p = 1 := by
      refine' le_antisymm _ _;
      · refine' Finset.sup_le fun x hx => _;
        exact Nat.le_of_not_lt fun h => by have := Nat.ordProj_dvd x p; exact absurd ( Nat.dvd_trans ( pow_dvd_pow p h ) this ) ( Nat.not_dvd_of_pos_of_lt ( hpos x hx ) ( by nlinarith [ hAM x hx ] ) ) ;
      · refine' le_trans _ ( Finset.le_sup <| Finset.mem_coe.mpr <| Finset.mem_filter.mp ha |>.1 );
        exact Nat.pos_of_ne_zero ( Finsupp.mem_support_iff.mp ( by { exact Nat.mem_primeFactors.mpr ⟨ hp, Finset.mem_filter.mp ha |>.2, by linarith [ hpos a ( Finset.mem_filter.mp ha |>.1 ) ] ⟩ } ) );
    simp_all +decide [ pFiber, topLayer ];
    exact factorization_eq_one_of_sq hp ( hpos a ha.1 ) ( hAM a ha.1 ) hsq ha.2;
  · simp_all +decide [ topLayer, pFiber ];
    contrapose! hne;
    ext x; simp_all +decide [ Nat.factorization_eq_zero_of_not_dvd ] ;
    intro hx; exact fun h => hne <| by have := hpos a ha.1; have := hpos x hx; exact absurd ha.2 <| ne_of_lt <| lt_of_lt_of_le ( Nat.pos_of_ne_zero <| Finsupp.mem_support_iff.mp <| by { exact Nat.mem_primeFactors.mpr ⟨ hp, h, by linarith [ hpos x hx ] ⟩ } ) <| Finset.le_sup ( f := fun a => Nat.factorization a p ) hx;

/-
When `M < p²`, every top-layer element `b` satisfies `p · (ordCompl[p] b) = b`
(its `p`-adic valuation is exactly `1`).
-/
theorem topLayer_ordProj_of_sq (A : Finset ℕ) (M p : ℕ) (hp : p.Prime)
    (hpos : ∀ a ∈ A, 0 < a) (hAM : ∀ a ∈ A, a ≤ M) (hsq : M < p ^ 2)
    (he : 1 ≤ topExp A p) {b : ℕ} (hb : b ∈ topLayer A p) :
    p * ordCompl[p] b = b := by
  have h_factorization : Nat.factorization b p = 1 := by
    apply factorization_eq_one_of_sq hp (hpos b (topLayer_subset _ _ hb)) (hAM b (topLayer_subset _ _ hb)) hsq
    exact hp.dvd_iff_one_le_factorization ( ne_of_gt ( hpos b ( topLayer_subset _ _ hb ) ) ) |>.2 ( by linarith [ show Nat.factorization b p = topExp A p from Finset.mem_filter.mp hb |>.2 ] )
  rw [ h_factorization, pow_one, Nat.mul_div_cancel' ( Nat.dvd_of_mod_eq_zero ( by rw [ Nat.mod_eq_zero_of_dvd ] ; exact hp.dvd_iff_one_le_factorization ( by aesop ) |>.2 ( by aesop ) ) ) ]

/-
**Fiber size bound.**  If `M < p²` and the top `p`-adic layer has size `k`, then
`p^k ≤ k · M^{k-1}`.
-/
theorem fiber_dichotomy_sqrtM
    (A : Finset ℕ) (M p k : ℕ) (hp : p.Prime)
    (hpos : ∀ a ∈ A, 0 < a) (hAM : ∀ a ∈ A, a ≤ M)
    (hsum : ∑ a ∈ A, (1 : ℚ) / a = 1)
    (hsq : M < p ^ 2) (he : 1 ≤ topExp A p)
    (hk : (topLayer A p).card = k) :
    p ^ k ≤ k * M ^ (k - 1) := by
  -- By `topLayer_symm_congruence`, we know that `p ∣ E`.
  have h_div : p ∣ (∑ a ∈ topLayer A p, (∏ b ∈ (topLayer A p).erase a, (ordCompl[p] b))) := by
    convert topLayer_symm_congruence A p hp hpos hsum he using 1;
  -- By `topLayer_ordProj_of_sq`, we know that `p * m b = b` for `b ∈ L`, hence `b ≤ M` gives everything below; also `m b ≥ 1`.
  have h_bound : ∀ a ∈ topLayer A p, (∏ b ∈ (topLayer A p).erase a, (ordCompl[p] b)) * p ^ (k - 1) ≤ M ^ (k - 1) := by
    intros a ha
    have h_erase : ∀ b ∈ (topLayer A p).erase a, b / p ^ (Nat.factorization b p) * p = b := by
      intros b hb
      have h_erase : p * (ordCompl[p] b) = b := by
        apply topLayer_ordProj_of_sq A M p hp hpos hAM hsq he (Finset.mem_of_mem_erase hb);
      grind;
    have h_erase : (∏ b ∈ (topLayer A p).erase a, (ordCompl[p] b)) * p ^ ((topLayer A p).card - 1) = (∏ b ∈ (topLayer A p).erase a, b) := by
      rw [ ← Finset.prod_congr rfl h_erase, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_erase_of_mem ha ];
    exact hk ▸ h_erase.le.trans ( le_trans ( Finset.prod_le_prod' fun x hx => hAM x <| Finset.mem_of_mem_erase hx |> fun hx' => Finset.mem_of_subset ( topLayer_subset _ _ ) hx' ) <| by simp +decide [ Finset.card_erase_of_mem ha ] );
  -- Summing over the `k` elements of `L` gives `≤ k * M ^ (k-1)`.
  have h_sum_bound : (∑ a ∈ topLayer A p, (∏ b ∈ (topLayer A p).erase a, (ordCompl[p] b))) * p ^ (k - 1) ≤ k * M ^ (k - 1) := by
    simpa [ Finset.sum_mul _ _ _, hk ] using Finset.sum_le_sum h_bound;
  rcases k with ( _ | k ) <;> simp_all +decide [ pow_succ' ];
  · simp_all +decide [ topLayer ];
    contrapose! hk;
    exact Exists.elim ( Finset.exists_max_image A ( fun a => Nat.factorization a p ) ( Finset.nonempty_of_ne_empty ( by aesop_cat ) ) ) fun x hx => ⟨ x, hx.1, le_antisymm ( Finset.le_sup ( f := fun a => Nat.factorization a p ) hx.1 ) ( Finset.sup_le fun y hy => hx.2 y hy ) ⟩;
  · refine' le_trans _ h_sum_bound;
    gcongr;
    refine' Nat.le_of_dvd ( Finset.sum_pos _ _ ) h_div;
    · exact fun x hx => Finset.prod_pos fun y hy => Nat.div_pos ( Nat.le_of_dvd ( hpos y ( topLayer_subset _ _ ( Finset.mem_of_mem_erase hy ) ) ) ( Nat.ordProj_dvd _ _ ) ) ( pow_pos hp.pos _ );
    · exact Finset.card_pos.mp ( by linarith )

/-
**`k = 1` corollary.**  Under `M < p²`, the top layer cannot be a singleton
(the bound `p ≤ 1` is impossible).
-/
theorem fiber_card_ne_one_of_sq
    (A : Finset ℕ) (M p : ℕ) (hp : p.Prime)
    (hpos : ∀ a ∈ A, 0 < a) (hAM : ∀ a ∈ A, a ≤ M)
    (hsum : ∑ a ∈ A, (1 : ℚ) / a = 1)
    (hsq : M < p ^ 2) (he : 1 ≤ topExp A p) :
    (topLayer A p).card ≠ 1 := by
  intro hk
  have h := fiber_dichotomy_sqrtM A M p 1 hp hpos hAM hsum hsq he hk
  simp only [pow_one, Nat.sub_self, pow_zero, mul_one] at h
  exact absurd h (by simpa using hp.two_le)

/-
**`k = 2` corollary.**  Under `M < p²`, a doubleton top layer forces `p² ≤ 2M`.
-/
theorem fiber_sq_le_of_card_two
    (A : Finset ℕ) (M p : ℕ) (hp : p.Prime)
    (hpos : ∀ a ∈ A, 0 < a) (hAM : ∀ a ∈ A, a ≤ M)
    (hsum : ∑ a ∈ A, (1 : ℚ) / a = 1)
    (hsq : M < p ^ 2) (he : 1 ≤ topExp A p)
    (hk : (topLayer A p).card = 2) :
    p ^ 2 ≤ 2 * M := by
  convert fiber_dichotomy_sqrtM A M p 2 hp hpos hAM hsum hsq he hk using 1;
  norm_num

/-
**`k = 3` corollary.**  Under `M < p²`, a tripleton top layer forces `p³ ≤ 3M²`.
-/
theorem fiber_cube_le_of_card_three
    (A : Finset ℕ) (M p : ℕ) (hp : p.Prime)
    (hpos : ∀ a ∈ A, 0 < a) (hAM : ∀ a ∈ A, a ≤ M)
    (hsum : ∑ a ∈ A, (1 : ℚ) / a = 1)
    (hsq : M < p ^ 2) (he : 1 ≤ topExp A p)
    (hk : (topLayer A p).card = 3) :
    p ^ 3 ≤ 3 * M ^ 2 := by
  have := Erdos287.fiber_dichotomy_sqrtM A M p 3 hp hpos hAM hsum hsq he hk; norm_num at *; linarith;

end Erdos287