import RequestProject.Erdos287.SourceChain.Physical.TypeII.UremFamilyActual
import RequestProject.Erdos287.SourceChain.Physical.TypeII.UremFamilyMoments
import RequestProject.Erdos287.SourceChain.Physical.TypeII.UremFamilySW

/-!
# Erdős #287 — collapsing the family Urem bound

**ERDŐS #287 REMAINS OPEN.  TAIL-287 IS NOT BANKED.**

* `packet_density_le` — `∑_ξ |Γ_ξ| (M/f_ξ + Q) ≤ C_a (1 + log F)^{2^{2k}} (M + F Q)` from the
  literal packet multiplicity and the divisor moments;
* `atom_total_le` — `∑_{J,P,χ} w_{J,P} ≤ ∑_{J ≤ T²} H^J 3^J`;
* `actual_family_urem_explicit` — the family Urem bound of `actual_family_urem_maynard` with every
  sum evaluated: atom total × reciprocal-divisor moment × number of bands × `√(∑β²)` ×
  `√(packet density)` × `√(C_a C' N'²/(log N')^A)`.
-/

open Finset

set_option autoImplicit false

namespace Erdos287.Physical.TypeII.UremFamily

open Erdos287.Physical Erdos287.Physical.TypeII Erdos287.Physical.Sieve
  Erdos287.Physical.Sieve.ScalarParams Erdos287.Physical.Factor

/-- **Packet density.**  For packets with `1 ≤ f_ξ ≤ F` and multiplicity
`∑_{f_ξ = f₀} |Γ_ξ| ≤ C_a τ(f₀)^{K}`:
`∑_ξ |Γ_ξ| (M/f_ξ + Q) ≤ C_a (1 + log F)^{2^K} (M + F Q)`. -/
theorem packet_density_le {ι : Type} (Ξ : Finset ι) (Γ : ι → ℝ) (f : ι → ℕ) (F K : ℕ)
    (Ca : ℝ) (hCa : 0 ≤ Ca) (hf : ∀ ξ ∈ Ξ, 1 ≤ f ξ ∧ f ξ ≤ F)
    (hmult : ∀ f0, ∑ ξ ∈ Ξ with f ξ = f0, |Γ ξ| ≤ Ca * tau f0 ^ K) (M Q : ℝ) (hM : 0 ≤ M)
    (hQ : 0 ≤ Q) :
    ∑ ξ ∈ Ξ, |Γ ξ| * (M / f ξ + Q) ≤ Ca * (1 + Real.log F) ^ (2 ^ K) * (M + F * Q) := by
  have hmaps : ∀ ξ ∈ Ξ, f ξ ∈ Icc 1 F := fun ξ hξ => mem_Icc.2 (hf ξ hξ)
  rw [← sum_fiberwise_of_maps_to hmaps]
  have hterm : ∀ f0 ∈ Icc 1 F, ∑ ξ ∈ Ξ with f ξ = f0, |Γ ξ| * (M / f ξ + Q) ≤
      Ca * ((f0.divisors.card : ℝ) ^ K / f0) * M + Ca * (f0.divisors.card : ℝ) ^ K * Q := by
    intro f0 _
    have e : ∑ ξ ∈ Ξ with f ξ = f0, |Γ ξ| * (M / f ξ + Q) =
        (∑ ξ ∈ Ξ with f ξ = f0, |Γ ξ|) * (M / f0 + Q) := by
      rw [sum_mul]
      refine sum_congr rfl (fun ξ hξ => ?_)
      rw [(mem_filter.1 hξ).2]
    rw [e]
    have hpos : 0 ≤ M / f0 + Q := by positivity
    refine (mul_le_mul_of_nonneg_right (hmult f0) hpos).trans (le_of_eq ?_)
    unfold tau; ring
  refine (sum_le_sum hterm).trans ?_
  rw [sum_add_distrib, ← sum_mul, ← mul_sum, ← sum_mul, ← mul_sum]
  have h1 := sum_tau_pow_div_le F K
  have h2 := sum_tau_pow_le F K
  have hL : 0 ≤ (1 + Real.log F) ^ (2 ^ K) := pow_nonneg (one_add_log_nonneg F) _
  calc Ca * (∑ i ∈ Icc 1 F, (i.divisors.card : ℝ) ^ K / i) * M +
        Ca * (∑ i ∈ Icc 1 F, (i.divisors.card : ℝ) ^ K) * Q
      ≤ Ca * (1 + Real.log F) ^ (2 ^ K) * M + Ca * (F * (1 + Real.log F) ^ (2 ^ K)) * Q := by
        gcongr
    _ = Ca * (1 + Real.log F) ^ (2 ^ K) * (M + F * Q) := by ring

/-- **Total atom weight**: `∑_{J,P,χ} w_{J,P} ≤ ∑_{J ≤ T²} H^J 3^J`. -/
theorem atom_total_le (S : ScalarParams) (δ N : ℝ) :
    ∑ J ∈ range (S.T ^ 2 + 1), ∑ P : Fin J → Fin S.H, ∑ _χ : Fin S.Kc → Fin 3,
      S.atomWeight J P (S.atomColour δ N J P) ≤ ∑ J ∈ range (S.T ^ 2 + 1), (S.H : ℝ) ^ J * 3 ^ J := by
  refine sum_le_sum (fun J _ => ?_)
  have hcard : ∑ _P : Fin J → Fin S.H, (3 : ℝ) ^ J = (S.H : ℝ) ^ J * 3 ^ J := by
    rw [sum_const, card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
    simp
  rw [← hcard]
  refine sum_le_sum (fun P _ => ?_)
  rw [sum_const, card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  rw [mul_comm]
  exact atomWeight_mul_le P _

/-- One summand of the collapsed bound. -/
lemma urem_summand_le (W sB G Gi CY t : ℝ) (hW : 0 ≤ W) (hsB : 0 ≤ sB) (hGi : Gi ≤ G)
    (ht : 0 ≤ t) (Ca : ℝ) :
    W * sB * Real.sqrt Gi * Real.sqrt (Ca * (t ^ 2 * CY)) ≤
      t * (W * sB * Real.sqrt G * Real.sqrt (Ca * CY)) := by
  have e : Real.sqrt (Ca * (t ^ 2 * CY)) = t * Real.sqrt (Ca * CY) := by
    rw [show Ca * (t ^ 2 * CY) = t ^ 2 * (Ca * CY) by ring, Real.sqrt_mul (sq_nonneg t),
      Real.sqrt_sq ht]
  rw [e]
  have h1 : Real.sqrt Gi ≤ Real.sqrt G := Real.sqrt_le_sqrt hGi
  have h2 : 0 ≤ Real.sqrt (Ca * CY) := Real.sqrt_nonneg _
  calc W * sB * Real.sqrt Gi * (t * Real.sqrt (Ca * CY))
      ≤ W * sB * Real.sqrt G * (t * Real.sqrt (Ca * CY)) := by gcongr
    _ = t * (W * sB * Real.sqrt G * Real.sqrt (Ca * CY)) := by ring

/-- **The explicit family Urem bound on the literal packets.**  From Maynard I, Lemma 13.8
(`MaynardLemma13_8`), the Siegel–Walfisz condition (6.1) and the divisor bound for the common
sequence `α` (divisor exponent `b ∈ ℕ`, `b ≥ 2k+1`), a common `β` supported on `[M, 2M)` with
`∑ β² ≤ B_β`, the base cap `f_ξ ≤ F`, the band cap `l < 2^{n₀}` and the modulus cutoff
`2 F 2^{n₀} ≤ N'/(log N')^C`:
`∑_ξ |physUrem_ξ| ≤ (∑_J H^J 3^J) (1 + log K)^{2^{b+1}} n₀ √B_β
  √(C_a (1 + log F)^{4^k} (M + F 2^{n₀})) √(C_a C' N'²/(log N')^A)`,
`C_a = (V B_f^k)² k²`. -/
theorem actual_family_urem_explicit (hM : MaynardLemma13_8) {b : ℕ} (hb : 0 < b)
    (cSW : ℝ → ℝ) {Aexp : ℝ} (hAexp : 0 < Aexp) :
    ∃ C Cimp : ℝ, ∀ (P : PhysData), P.WGood → ∀ (Bf : ℝ), (∀ v i t, |P.fp v i t| ≤ Bf) →
    (2 * P.k : ℝ) + 1 ≤ b →
    ∀ (Ξ : Finset (Packet P.k)), Ξ ⊆ P.XiAll → ∀ (S : ScalarParams), S.Good →
    ∀ (δ N : ℝ) (K n n0 Nn M K' F : ℕ), K ≤ 2 ^ n →
    ∀ (α β : ArithmeticFunction ℝ),
    (∀ m, α m ≠ 0 → Nn ≤ m ∧ m < 2 * Nn) →
    (∀ m, β m ≠ 0 → M ≤ m ∧ m < 2 * M) → 4 * Nn * M ≤ K' →
    (∀ ξ ∈ Ξ, P.f ξ ≤ F) → ∀ (Bβ : ℝ), (∑ m ∈ Ico M (2 * M), β m ^ 2 ≤ Bβ) →
    (∀ ξ ∈ Ξ, ∀ J (Pb : Fin J → Fin S.H) (χ : Fin S.Kc → Fin 3) l r,
      physCoefCut S δ N (P.Gamma ξ) (P.f ξ) K J Pb χ l r ≠ 0 → l < 2 ^ n0) →
    2 ≤ (Nn : ℝ) - 1 / 2 → SWCondition α ((Nn : ℝ) - 1 / 2) b cSW →
    (∀ m, |α m| ≤ tau m ^ (b : ℝ)) →
    ((2 * F * 2 ^ n0 : ℕ) : ℝ) ≤ ((Nn : ℝ) - 1 / 2) / Real.log ((Nn : ℝ) - 1 / 2) ^ C →
    ∑ ξ ∈ Ξ, |physUrem S δ N (P.Gamma ξ) (P.f ξ) (P.cRes ξ) (P.A ξ) (P.B ξ) K K' α β| ≤
      (∑ J ∈ range (S.T ^ 2 + 1), (S.H : ℝ) ^ J * 3 ^ J) * (1 + Real.log K) ^ (2 ^ (b + 1)) *
        n0 * Real.sqrt Bβ *
        Real.sqrt (((P.V * Bf ^ P.k) ^ 2 * (P.k : ℝ) ^ 2) * (1 + Real.log F) ^ (2 ^ (2 * P.k)) *
          (M + F * (2 ^ n0 : ℕ))) *
        Real.sqrt (((P.V * Bf ^ P.k) ^ 2 * (P.k : ℝ) ^ 2) *
          (Cimp * ((Nn : ℝ) - 1 / 2) ^ 2 / Real.log ((Nn : ℝ) - 1 / 2) ^ Aexp)) := by
  obtain ⟨C, Cimp, hC⟩ := actual_family_urem_maynard hM (B0 := (b : ℝ)) (by exact_mod_cast hb)
    cSW hAexp
  refine ⟨C, Cimp, ?_⟩
  intro P hP Bf hBf hkb Ξ hΞ S hS δ N K n n0 Nn M K' F hKn α β hα hβ hK' hF Bβ hβ2 hl0 hN hsw
    hdiv hcut
  have hmain := hC P hP Bf hBf hkb Ξ hΞ S hS δ N K n n0 Nn M K' F hKn α (fun _ => β) hα
    (fun _ _ => hβ) hK' hF Bβ (fun _ _ => hβ2) hl0 hN hsw hdiv hcut
  refine hmain.trans ?_
  set Ca : ℝ := (P.V * Bf ^ P.k) ^ 2 * (P.k : ℝ) ^ 2
  have hCa0 : 0 ≤ Ca := by positivity
  set Y : ℝ := Cimp * ((Nn : ℝ) - 1 / 2) ^ 2 / Real.log ((Nn : ℝ) - 1 / 2) ^ Aexp
  set G : ℝ := ∑ ξ ∈ Ξ, |P.Gamma ξ| * ((M : ℝ) / P.f ξ + ((2 ^ n0 : ℕ) : ℝ)) with hG
  have hBβ0 : 0 ≤ Bβ := le_trans (sum_nonneg (fun _ _ => sq_nonneg _)) hβ2
  -- Y may have either sign a priori; handle the degenerate case
  by_cases hY0 : Y < 0
  · -- then √(Ca * (t² Y)) = 0 for all terms, RHS of hmain is 0
    have hz : ∀ r : ℕ, Real.sqrt (Ca * ((tau r ^ (b : ℝ)) ^ 2 * Y)) = 0 := by
      intro r
      apply Real.sqrt_eq_zero'.2
      have : 0 ≤ (tau r ^ (b : ℝ)) ^ 2 := sq_nonneg _
      nlinarith [mul_nonneg hCa0 this]
    simp only [hz, mul_zero, sum_const_zero]
    positivity
  push_neg at hY0
  have hGi : ∀ i ∈ range n0, ∑ ξ ∈ Ξ, |P.Gamma ξ| * ((M : ℝ) / P.f ξ + ((2 ^ i : ℕ) : ℝ)) ≤ G := by
    intro i hi
    refine sum_le_sum (fun ξ _ => mul_le_mul_of_nonneg_left ?_ (abs_nonneg _))
    have : 2 ^ i ≤ 2 ^ n0 := Nat.pow_le_pow_right (by norm_num) (mem_range.1 hi).le
    have : ((2 ^ i : ℕ) : ℝ) ≤ ((2 ^ n0 : ℕ) : ℝ) := by exact_mod_cast this
    linarith
  set Z : ℝ := Real.sqrt Bβ * Real.sqrt G * Real.sqrt (Ca * Y) with hZ
  have hZ0 : 0 ≤ Z := by positivity
  -- inner sums
  have hinner : ∀ J (Pb : Fin J → Fin S.H) (_χ : Fin S.Kc → Fin 3),
      ∑ r ∈ Ico 1 K, (1 / (Nat.totient r : ℝ)) * ∑ i ∈ range n0,
          S.atomWeight J Pb (S.atomColour δ N J Pb) * Real.sqrt Bβ *
            Real.sqrt (∑ ξ ∈ Ξ, |P.Gamma ξ| * ((M : ℝ) / P.f ξ + (2 ^ i : ℕ))) *
            Real.sqrt (Ca * ((tau r ^ (b : ℝ)) ^ 2 * Y)) ≤
        S.atomWeight J Pb (S.atomColour δ N J Pb) * ((1 + Real.log K) ^ (2 ^ (b + 1)) * n0 * Z) := by
    intro J Pb _
    set W := S.atomWeight J Pb (S.atomColour δ N J Pb) with hW
    have hW0 : 0 ≤ W := atomWeight_nonneg Pb _
    have hr : ∀ r ∈ Ico 1 K, (1 / (Nat.totient r : ℝ)) * ∑ i ∈ range n0,
          W * Real.sqrt Bβ *
            Real.sqrt (∑ ξ ∈ Ξ, |P.Gamma ξ| * ((M : ℝ) / P.f ξ + (2 ^ i : ℕ))) *
            Real.sqrt (Ca * ((tau r ^ (b : ℝ)) ^ 2 * Y)) ≤
          ((r.divisors.card : ℝ) ^ b / Nat.totient r) * (n0 * (W * Z)) := by
      intro r _
      have ht : tau r ^ (b : ℝ) = (r.divisors.card : ℝ) ^ b := by
        rw [Real.rpow_natCast]; rfl
      have hsum : ∑ i ∈ range n0, W * Real.sqrt Bβ *
            Real.sqrt (∑ ξ ∈ Ξ, |P.Gamma ξ| * ((M : ℝ) / P.f ξ + (2 ^ i : ℕ))) *
            Real.sqrt (Ca * ((tau r ^ (b : ℝ)) ^ 2 * Y)) ≤
          ∑ _i ∈ range n0, (r.divisors.card : ℝ) ^ b * (W * Z) := by
        refine sum_le_sum (fun i hi => ?_)
        rw [ht]
        refine (urem_summand_le W (Real.sqrt Bβ) G _ Y _ hW0 (Real.sqrt_nonneg _) (hGi i hi)
          (by positivity) Ca).trans (le_of_eq ?_)
        rw [hZ]; ring
      rw [sum_const, card_range, nsmul_eq_mul] at hsum
      have hφ : (0 : ℝ) ≤ 1 / (Nat.totient r : ℝ) := by positivity
      calc (1 / (Nat.totient r : ℝ)) * _ ≤ (1 / (Nat.totient r : ℝ)) *
            (n0 * ((r.divisors.card : ℝ) ^ b * (W * Z))) := mul_le_mul_of_nonneg_left hsum hφ
        _ = ((r.divisors.card : ℝ) ^ b / Nat.totient r) * (n0 * (W * Z)) := by ring
    refine (sum_le_sum hr).trans ?_
    rw [← sum_mul]
    have hmom := sum_tau_pow_div_totient_le K b
    have h0 : 0 ≤ (n0 : ℝ) * (W * Z) := by positivity
    calc (∑ r ∈ Ico 1 K, (r.divisors.card : ℝ) ^ b / Nat.totient r) * (n0 * (W * Z))
        ≤ (1 + Real.log K) ^ (2 ^ (b + 1)) * (n0 * (W * Z)) := mul_le_mul_of_nonneg_right hmom h0
      _ = W * ((1 + Real.log K) ^ (2 ^ (b + 1)) * n0 * Z) := by ring
  have hconst0 : 0 ≤ (1 + Real.log K) ^ (2 ^ (b + 1)) * n0 * Z := by
    have := one_add_log_nonneg K; positivity
  calc _ ≤ ∑ J ∈ range (S.T ^ 2 + 1), ∑ Pb : Fin J → Fin S.H, ∑ χ : Fin S.Kc → Fin 3,
          S.atomWeight J Pb (S.atomColour δ N J Pb) * ((1 + Real.log K) ^ (2 ^ (b + 1)) * n0 * Z) :=
        sum_le_sum (fun J _ => sum_le_sum (fun Pb _ => sum_le_sum (fun χ _ => hinner J Pb χ)))
    _ = (∑ J ∈ range (S.T ^ 2 + 1), ∑ Pb : Fin J → Fin S.H, ∑ _χ : Fin S.Kc → Fin 3,
          S.atomWeight J Pb (S.atomColour δ N J Pb)) * ((1 + Real.log K) ^ (2 ^ (b + 1)) * n0 * Z) := by
        simp only [sum_mul]
    _ ≤ (∑ J ∈ range (S.T ^ 2 + 1), (S.H : ℝ) ^ J * 3 ^ J) *
          ((1 + Real.log K) ^ (2 ^ (b + 1)) * n0 * Z) :=
        mul_le_mul_of_nonneg_right (atom_total_le S δ N) hconst0
    _ ≤ _ := by
        have hGle : G ≤ Ca * (1 + Real.log F) ^ (2 ^ (2 * P.k)) * (M + F * (2 ^ n0 : ℕ)) := by
          refine packet_density_le Ξ P.Gamma P.f F (2 * P.k) Ca hCa0
            (fun ξ hξ => ⟨physData_f_pos P hP (PhysData.mem_XiAll (hΞ hξ)), hF ξ hξ⟩) ?_ M _
            (Nat.cast_nonneg _) (Nat.cast_nonneg _)
          intro f0
          refine le_trans ?_ (packet_multiplicity P hP hBf f0)
          exact sum_le_sum_of_subset_of_nonneg (filter_subset_filter _ hΞ)
            (fun _ _ _ => abs_nonneg _)
        have hsG : Real.sqrt G ≤ Real.sqrt (Ca * (1 + Real.log F) ^ (2 ^ (2 * P.k)) *
            (M + F * (2 ^ n0 : ℕ))) := Real.sqrt_le_sqrt hGle
        have hWt : 0 ≤ ∑ J ∈ range (S.T ^ 2 + 1), (S.H : ℝ) ^ J * 3 ^ J := by positivity
        have hlK := one_add_log_nonneg K
        rw [hZ]
        calc (∑ J ∈ range (S.T ^ 2 + 1), (S.H : ℝ) ^ J * 3 ^ J) *
              ((1 + Real.log K) ^ (2 ^ (b + 1)) * n0 *
                (Real.sqrt Bβ * Real.sqrt G * Real.sqrt (Ca * Y)))
            ≤ (∑ J ∈ range (S.T ^ 2 + 1), (S.H : ℝ) ^ J * 3 ^ J) *
              ((1 + Real.log K) ^ (2 ^ (b + 1)) * n0 *
                (Real.sqrt Bβ * Real.sqrt (Ca * (1 + Real.log F) ^ (2 ^ (2 * P.k)) *
                  (M + F * (2 ^ n0 : ℕ))) * Real.sqrt (Ca * Y))) := by gcongr
          _ = _ := by ring

end Erdos287.Physical.TypeII.UremFamily
