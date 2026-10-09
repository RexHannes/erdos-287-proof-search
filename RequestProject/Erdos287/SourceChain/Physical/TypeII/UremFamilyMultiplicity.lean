import RequestProject.Erdos287.SourceChain.Physical.TypeII.UremFamilyCompose
import RequestProject.Erdos287.SourceChain.Physical.Remainder

/-!
# Erdős #287 — packet multiplicity of the actual physical packets

**ERDŐS #287 REMAINS OPEN.  TAIL-287 IS NOT BANKED.**

The family Urem estimate needs the packet mass at each base, `a_f = ∑_{ξ : f_ξ = f} |Γ_ξ|`, to be
at most `C_a τ(f)^K` for a fixed `K` (report (2.6)).  For the literal packets
`ξ = (j, ℓ, d, d') ∈ Ξ` (`XiAll`), `f_ξ = a_j W q₀`, `Γ_ξ = ω_d ω_{d'}`:

* `abs_omega_le` — `|ω_d| ≤ V · B_f^k` when every tensor factor satisfies `|f'_{i,v}| ≤ B_f`;
* `dvd_f_of_admissible` — every entry `d_i`, `d'_i` of an admissible packet divides `f_ξ`
  (designated entries are `1`; spectator entries divide `q_i ∣ q₀ ∣ f_ξ`);
* `packet_multiplicity` — `a_f ≤ (V B_f^k)² k² τ(f)^{2k}`: a packet with `f_ξ = f` is determined by
  `(j, ℓ, d, d')` with all `2k` entries among the divisors of `f`.  All spectator multiplicities
  are included (no squarefree or pairwise-coprimality saving is used).
-/

open Finset

set_option autoImplicit false

namespace Erdos287.Physical.TypeII.UremFamily

open Erdos287.Physical

/-- `|ω_d| ≤ V B_f^k`. -/
theorem abs_omega_le (P : PhysData) {Bf : ℝ} (hBf : ∀ v i t, |P.fp v i t| ≤ Bf)
    (d : Fin P.k → ℕ) : |P.omega d| ≤ P.V * Bf ^ P.k := by
  have hnn : 0 ≤ (P.V : ℝ) * Bf ^ P.k := by
    rcases Nat.eq_zero_or_pos P.V with h | h
    · rw [h]; simp
    rcases Nat.eq_zero_or_pos P.k with hk | hk
    · rw [hk, pow_zero, mul_one]; positivity
    have := (abs_nonneg _).trans (hBf ⟨0, h⟩ ⟨0, hk⟩ 0)
    positivity
  unfold PhysData.omega
  split_ifs
  · rw [abs_mul]
    have h1 : |∏ i, (ArithmeticFunction.moebius (d i) : ℝ)| ≤ 1 := by
      rw [abs_prod]
      apply prod_le_one (fun i _ => abs_nonneg _)
      intro i _
      have := ArithmeticFunction.abs_moebius_le_one (n := d i)
      have : |((ArithmeticFunction.moebius (d i) : ℤ) : ℝ)| ≤ 1 := by
        rw [← Int.cast_abs]; exact_mod_cast this
      exact this
    have h2 : |∑ v, ∏ i, P.fp v i (Real.log (d i) / Real.log P.X)| ≤ P.V * Bf ^ P.k := by
      refine (abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ v, |∏ i, P.fp v i (Real.log (d i) / Real.log P.X)|
          ≤ ∑ _v : Fin P.V, Bf ^ P.k := by
            refine sum_le_sum (fun v _ => ?_)
            rw [abs_prod]
            calc ∏ i, |P.fp v i (Real.log (d i) / Real.log P.X)| ≤ ∏ _i : Fin P.k, Bf :=
                  prod_le_prod (fun i _ => abs_nonneg _) (fun i _ => hBf v i _)
              _ = Bf ^ P.k := by rw [prod_const, card_univ, Fintype.card_fin]
        _ = P.V * Bf ^ P.k := by rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    calc |∏ i, (ArithmeticFunction.moebius (d i) : ℝ)| *
          |∑ v, ∏ i, P.fp v i (Real.log (d i) / Real.log P.X)| ≤ 1 * (P.V * Bf ^ P.k) :=
          mul_le_mul h1 h2 (abs_nonneg _) zero_le_one
      _ = P.V * Bf ^ P.k := one_mul _
  · simpa using hnn

/-- Every entry of an admissible packet divides `f_ξ`. -/
theorem dvd_f_of_admissible (P : PhysData) {ξ : Packet P.k} (hξ : P.Admissible ξ) (i : Fin P.k) :
    ξ.d i ∣ P.f ξ ∧ ξ.d' i ∣ P.f ξ := by
  obtain ⟨-, hdj, hd'j, hdl, hd'l, -, -, -⟩ := hξ
  have hq0 : P.q0 ξ ∣ P.f ξ := Dvd.intro_left _ rfl
  by_cases hij : i = ξ.j
  · subst hij; rw [hdj, hd'j]; exact ⟨one_dvd _, one_dvd _⟩
  by_cases hil : i = ξ.l
  · subst hil; rw [hdl, hd'l]; exact ⟨one_dvd _, one_dvd _⟩
  have hmem : i ∈ P.spec ξ := by
    simp only [PhysData.spec, mem_filter, mem_univ, true_and]; exact ⟨hij, hil⟩
  have hqi : P.q ξ i ∣ P.q0 ξ := dvd_prod_of_mem _ hmem
  exact ⟨(Nat.dvd_lcm_left _ _).trans (hqi.trans hq0),
    (Nat.dvd_lcm_right _ _).trans (hqi.trans hq0)⟩

/-- **Packet multiplicity** `a_f ≤ (V B_f^k)² k² τ(f)^{2k}` for the actual packets. -/
theorem packet_multiplicity (P : PhysData) (hP : P.WGood) {Bf : ℝ}
    (hBf : ∀ v i t, |P.fp v i t| ≤ Bf) (f0 : ℕ) :
    ∑ ξ ∈ P.XiAll with P.f ξ = f0, |P.Gamma ξ| ≤
      ((P.V * Bf ^ P.k) ^ 2 * (P.k : ℝ) ^ 2) * tau f0 ^ (2 * P.k) := by
  set G : ℝ := P.V * Bf ^ P.k with hG
  have hΓ : ∀ ξ : Packet P.k, |P.Gamma ξ| ≤ G ^ 2 := by
    intro ξ
    unfold PhysData.Gamma
    rw [abs_mul, sq]
    exact mul_le_mul (abs_omega_le P hBf _) (abs_omega_le P hBf _) (abs_nonneg _)
      ((abs_nonneg _).trans (abs_omega_le P hBf ξ.d))
  set T := (univ : Finset (Fin P.k)) ×ˢ (univ : Finset (Fin P.k)) ×ˢ
    (Fintype.piFinset fun _ : Fin P.k => f0.divisors) ×ˢ
    (Fintype.piFinset fun _ : Fin P.k => f0.divisors) with hT
  have hcard : (P.XiAll.filter (fun ξ => P.f ξ = f0)).card ≤ T.card := by
    refine card_le_card_of_injOn (fun ξ => (ξ.j, ξ.l, ξ.d, ξ.d')) ?_ ?_
    · intro ξ hξ
      rw [coe_filter] at hξ
      obtain ⟨hξX, hf⟩ := hξ
      have hadm := PhysData.mem_XiAll hξX
      have hf0 : f0 ≠ 0 := by
        rw [← hf]
        unfold PhysData.f PhysData.q0
        refine Nat.mul_ne_zero (Nat.mul_ne_zero (hP.a_pos _).ne' hP.W_pos.ne') ?_
        rw [prod_ne_zero_iff]
        intro i _
        exact (Nat.lcm_pos (hadm.2.2.2.2.2.1 i).1 (hadm.2.2.2.2.2.1 i).2).ne'
      simp only [hT, coe_product, Set.mem_prod, mem_coe, mem_univ, true_and,
        Fintype.mem_piFinset, Nat.mem_divisors]
      refine ⟨fun i => ⟨?_, hf0⟩, fun i => ⟨?_, hf0⟩⟩
      · rw [← hf]; exact (dvd_f_of_admissible P hadm i).1
      · rw [← hf]; exact (dvd_f_of_admissible P hadm i).2
    · intro ξ _ ξ' _ he
      simp only [Prod.mk.injEq] at he
      obtain ⟨h1, h2, h3, h4⟩ := he
      cases ξ; cases ξ'
      simp_all
  have hTcard : (T.card : ℝ) = (P.k : ℝ) ^ 2 * tau f0 ^ (2 * P.k) := by
    simp only [hT, card_product, card_univ, Fintype.card_fin, Fintype.card_piFinset,
      prod_const, Fintype.card_fin]
    unfold tau
    push_cast
    ring
  calc ∑ ξ ∈ P.XiAll with P.f ξ = f0, |P.Gamma ξ|
      ≤ ∑ ξ ∈ P.XiAll with P.f ξ = f0, G ^ 2 := sum_le_sum (fun ξ _ => hΓ ξ)
    _ = ((P.XiAll.filter (fun ξ => P.f ξ = f0)).card : ℝ) * G ^ 2 := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ (T.card : ℝ) * G ^ 2 := by
        gcongr
    _ = _ := by rw [hTcard]; ring

end Erdos287.Physical.TypeII.UremFamily
