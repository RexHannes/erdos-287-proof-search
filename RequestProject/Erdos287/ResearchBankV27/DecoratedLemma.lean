import RequestProject.Erdos287.ResearchBankV27.RepresentationMoment
import RequestProject.Erdos287.ResearchBankV27.DISpectralProvider

/-!
# Erdős #287 — Research Bank V27 §5.10: the master decorated bound

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

A `DecoratedData` bundles one decorated sum: outer set `O`, inner set `I`, outer coefficient `A`
with Cauchy weights `w` (total `mass`), kernel `K(o; i)`, grouping `grp`, and the Kloosterman
form `KD` of the regrouped outer variables, with the exact regrouping hypothesis `hgrp`.

**EXTERNAL PROVIDER.**
* `RepresentationMomentProvider` — the divisor-type representation bounds
  `Σ_{z off-diag} A_z² ≤ Rep` and the diagonal (`ht = ks`) contribution
  `mass · Σ_{z diag} A_z Σ_b |Kl(b;z)| ≤ x^ε N_q² T Δ₁`.

**LEAN CONDITIONAL** (on `DIConclusion`, i.e. on `DISpectralProvider`, and on
`RepresentationMomentProvider`):
* **`decorated_energy_bound`** — for EVERY one-bounded inner decoration `Ψ`:
  `mass · V(Ψ) ≤ x^ε N_q² T Δ₁ + x^{ε_DI} N_q² T (Δ₂+Δ₃)^{1/2}`;
* **`decorated_master_bound`** — `|W(A,Ψ)| ≤ N_q √T [x^{ε/2} √Δ₁ + x^{ε_DI/2} (Δ₂+Δ₃)^{1/4}]`.

**LEAN BANK** (exponent arithmetic, `T ≤ x^{η/4+ε}`, `ε_DI = η/4`, `0 ≤ ε ≤ η`):
* `first_part_saving` — `√T · x^{ε/2} √Δ₁ ≤ x^{ε − 27η/8}`;
* `second_part_saving` — `√T · x^{η/8} (Δ₂+Δ₃)^{1/4} ≤ 2^{1/4} x^{ε/2 − 13η/4}`;
* `energy_instantiation` — `T (x^ε Δ₁ + x^{η/4} (Δ₂+Δ₃)^{1/2}) ≤ 3 x^{−2η}`;
* **`decorated_conservative`** (LEAN CONDITIONAL) — `mass · V(Ψ) ≤ 3 N_q² x^{−2η}` and
  `|W(A,Ψ)| ≤ √3 N_q x^{−η}`.
-/

namespace Erdos287
namespace ResearchBankV27
namespace DecoratedLemma

open Finset CommonCauchy GroupedCoefficient RepresentationMoment DISpectral

/-- One decorated sum together with its Kloosterman form. -/
structure DecoratedData where
  O : Type
  I : Type
  [fO : Fintype O]
  [fI : Fintype I]
  KD : KloostermanData
  A : O → ℂ
  w : O → ℝ
  hA : ∀ o, ‖A o‖ ^ 2 ≤ w o
  hmass : ∑ o, w o = KD.mass
  K : O → I → ℂ
  grp : I → I → KD.Z
  hgrp : ∀ i i', ∑ o, K o i * starRingEnd ℂ (K o i') = ∑ b, KD.Kl b (grp i i')
  Delta1 : ℝ
  eps : ℝ

attribute [instance] DecoratedData.fO DecoratedData.fI

/-- **Representation-moment / diagonal provider** (EXTERNAL PROVIDER; never constructed). -/
structure RepresentationMomentProvider (D : DecoratedData) : Prop where
  rep : ∑ z ∈ D.KD.offDiag, repCount D.grp z ^ 2 ≤ D.KD.Rep
  diag : D.KD.mass * ∑ z ∈ univ.filter (fun z => z ∉ D.KD.offDiag),
      repCount D.grp z * ∑ b, ‖D.KD.Kl b z‖ ≤
    D.KD.x ^ D.eps * D.KD.Nq ^ 2 * D.KD.T * D.Delta1

theorem sqrt_add_le_sqrt_add {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb, Real.sqrt_nonneg a, Real.sqrt_nonneg b,
    mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)]

theorem sqrt_rpow_half {x : ℝ} (hx : 0 ≤ x) (e : ℝ) : Real.sqrt (x ^ e) = x ^ (e / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hx]; ring_nf

theorem mass_nonneg (D : DecoratedData) : 0 ≤ D.KD.mass := by
  rw [← D.hmass]
  exact Finset.sum_nonneg fun o _ => (sq_nonneg _).trans (D.hA o)

/-- **Decorated energy bound** (LEAN CONDITIONAL). -/
theorem decorated_energy_bound (D : DecoratedData) (hx : 0 ≤ D.KD.x) (hDI : DIConclusion D.KD)
    (hRep : RepresentationMomentProvider D) (Ψ : D.I → ℂ) (hΨ : ∀ i, ‖Ψ i‖ ≤ 1) :
    D.KD.mass * energy D.K Ψ ≤
      D.KD.x ^ D.eps * D.KD.Nq ^ 2 * D.KD.T * D.Delta1 +
        D.KD.x ^ D.KD.epsDI * (D.KD.Nq ^ 2 * D.KD.T * Real.sqrt (D.KD.Delta2 + D.KD.Delta3)) := by
  classical
  obtain ⟨hXi, hbil, hcal⟩ := hDI
  set c_off : D.KD.Z → ℂ := fun z => if z ∈ D.KD.offDiag then bPsi D.grp Ψ z else 0
  set c_dg : D.KD.Z → ℂ := fun z => if z ∈ D.KD.offDiag then 0 else bPsi D.grp Ψ z
  have hsplit : ∑ b, ∑ z, bPsi D.grp Ψ z * D.KD.Kl b z =
      bilinear D.KD c_off + ∑ b, ∑ z, c_dg z * D.KD.Kl b z := by
    unfold bilinear
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun z _ => ?_
    simp only [c_off, c_dg]; split_ifs <;> ring
  have hE : energy D.K Ψ ≤ ‖∑ b, ∑ z, bPsi D.grp Ψ z * D.KD.Kl b z‖ := by
    have := grouped_expansion D.K D.grp D.KD.Kl D.hgrp Ψ
    rw [← this, Complex.norm_real]
    exact le_abs_self _
  -- off-diagonal: DI
  have hl2 : l2 c_off ≤ Real.sqrt D.KD.Rep := by
    unfold l2
    refine Real.sqrt_le_sqrt ?_
    calc ∑ z, ‖c_off z‖ ^ 2 = ∑ z ∈ D.KD.offDiag, ‖bPsi D.grp Ψ z‖ ^ 2 := by
          rw [← Finset.sum_filter_add_sum_filter_not univ (fun z => z ∈ D.KD.offDiag)]
          rw [Finset.sum_eq_zero (s := univ.filter fun z => z ∉ D.KD.offDiag)
            (fun z hz => by simp [c_off, (Finset.mem_filter.1 hz).2]), add_zero]
          rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
          exact Finset.sum_congr rfl fun z hz => by simp [c_off, hz]
      _ ≤ ∑ z ∈ D.KD.offDiag, repCount D.grp z ^ 2 := bPsi_L2_le D.grp Ψ hΨ _
      _ ≤ D.KD.Rep := hRep.rep
  have hoff : ‖bilinear D.KD c_off‖ ≤ D.KD.x ^ D.KD.epsDI * D.KD.Xi * Real.sqrt D.KD.Rep := by
    refine (hbil c_off fun z hz => by simp [c_off, hz]).trans ?_
    exact mul_le_mul_of_nonneg_left hl2 (mul_nonneg (Real.rpow_nonneg hx _) hXi)
  -- diagonal
  have hdiag : ‖∑ b, ∑ z, c_dg z * D.KD.Kl b z‖ ≤
      ∑ z ∈ univ.filter (fun z => z ∉ D.KD.offDiag), repCount D.grp z * ∑ b, ‖D.KD.Kl b z‖ := by
    calc ‖∑ b, ∑ z, c_dg z * D.KD.Kl b z‖ ≤ ∑ b, ∑ z, ‖c_dg z‖ * ‖D.KD.Kl b z‖ :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ =>
            (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun z _ => norm_mul _ _)))
      _ = ∑ z, ‖c_dg z‖ * ∑ b, ‖D.KD.Kl b z‖ := by
          rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun z _ => by rw [Finset.mul_sum]
      _ = ∑ z ∈ univ.filter (fun z => z ∉ D.KD.offDiag), ‖bPsi D.grp Ψ z‖ * ∑ b, ‖D.KD.Kl b z‖ := by
          rw [Finset.sum_filter]
          exact Finset.sum_congr rfl fun z _ => by simp only [c_dg]; split_ifs <;> simp
      _ ≤ _ := Finset.sum_le_sum fun z _ =>
          mul_le_mul_of_nonneg_right (bPsi_norm_le D.grp Ψ hΨ z)
            (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  have hm := mass_nonneg D
  calc D.KD.mass * energy D.K Ψ
      ≤ D.KD.mass * (∑ z ∈ univ.filter (fun z => z ∉ D.KD.offDiag),
          repCount D.grp z * ∑ b, ‖D.KD.Kl b z‖ +
          D.KD.x ^ D.KD.epsDI * D.KD.Xi * Real.sqrt D.KD.Rep) := by
        refine mul_le_mul_of_nonneg_left (hE.trans ?_) hm
        rw [hsplit]
        exact (norm_add_le _ _).trans (by linarith)
    _ = D.KD.mass * ∑ z ∈ univ.filter (fun z => z ∉ D.KD.offDiag),
          repCount D.grp z * ∑ b, ‖D.KD.Kl b z‖ +
        D.KD.x ^ D.KD.epsDI * (D.KD.mass * D.KD.Xi * Real.sqrt D.KD.Rep) := by ring
    _ ≤ _ := add_le_add hRep.diag (mul_le_mul_of_nonneg_left hcal (Real.rpow_nonneg hx _))

/-- **Master decorated bound** (LEAN CONDITIONAL). -/
theorem decorated_master_bound (D : DecoratedData) (hx : 0 ≤ D.KD.x) (hDI : DIConclusion D.KD)
    (hRep : RepresentationMomentProvider D) (Ψ : D.I → ℂ) (hΨ : ∀ i, ‖Ψ i‖ ≤ 1)
    (hNq : 0 ≤ D.KD.Nq) (hT : 0 ≤ D.KD.T) (hΔ1 : 0 ≤ D.Delta1) :
    ‖decoratedSum D.A D.K Ψ‖ ≤ D.KD.Nq * Real.sqrt D.KD.T *
      (D.KD.x ^ (D.eps / 2) * Real.sqrt D.Delta1 +
        D.KD.x ^ (D.KD.epsDI / 2) * Real.sqrt (Real.sqrt (D.KD.Delta2 + D.KD.Delta3))) := by
  have hW := decorated_cauchy D.A D.w D.hA D.K Ψ
  rw [D.hmass] at hW
  have hE := decorated_energy_bound D hx hDI hRep Ψ hΨ
  have hsq : ‖decoratedSum D.A D.K Ψ‖ ≤ Real.sqrt
      (D.KD.x ^ D.eps * D.KD.Nq ^ 2 * D.KD.T * D.Delta1 +
        D.KD.x ^ D.KD.epsDI * (D.KD.Nq ^ 2 * D.KD.T * Real.sqrt (D.KD.Delta2 + D.KD.Delta3))) :=
    Real.le_sqrt_of_sq_le (hW.trans hE)
  have hp1 : 0 ≤ D.KD.x ^ D.eps * D.KD.Nq ^ 2 * D.KD.T * D.Delta1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg hx _) (sq_nonneg _)) hT) hΔ1
  have hp2 : 0 ≤ D.KD.x ^ D.KD.epsDI * (D.KD.Nq ^ 2 * D.KD.T * Real.sqrt (D.KD.Delta2 + D.KD.Delta3)) :=
    mul_nonneg (Real.rpow_nonneg hx _) (mul_nonneg (mul_nonneg (sq_nonneg _) hT) (Real.sqrt_nonneg _))
  refine hsq.trans ((sqrt_add_le_sqrt_add hp1 hp2).trans (le_of_eq ?_))
  have e1 : Real.sqrt (D.KD.x ^ D.eps * D.KD.Nq ^ 2 * D.KD.T * D.Delta1) =
      D.KD.Nq * Real.sqrt D.KD.T * (D.KD.x ^ (D.eps / 2) * Real.sqrt D.Delta1) := by
    rw [show D.KD.x ^ D.eps * D.KD.Nq ^ 2 * D.KD.T * D.Delta1 =
      D.KD.Nq ^ 2 * (D.KD.T * (D.KD.x ^ D.eps * D.Delta1)) by ring,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hNq, Real.sqrt_mul hT,
      Real.sqrt_mul (Real.rpow_nonneg hx _), sqrt_rpow_half hx]
    ring
  have e2 : Real.sqrt (D.KD.x ^ D.KD.epsDI *
      (D.KD.Nq ^ 2 * D.KD.T * Real.sqrt (D.KD.Delta2 + D.KD.Delta3))) =
      D.KD.Nq * Real.sqrt D.KD.T *
        (D.KD.x ^ (D.KD.epsDI / 2) * Real.sqrt (Real.sqrt (D.KD.Delta2 + D.KD.Delta3))) := by
    rw [show D.KD.x ^ D.KD.epsDI * (D.KD.Nq ^ 2 * D.KD.T * Real.sqrt (D.KD.Delta2 + D.KD.Delta3))
      = D.KD.Nq ^ 2 * (D.KD.T * (D.KD.x ^ D.KD.epsDI *
        Real.sqrt (D.KD.Delta2 + D.KD.Delta3))) by ring,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hNq, Real.sqrt_mul hT,
      Real.sqrt_mul (Real.rpow_nonneg hx _), sqrt_rpow_half hx]
    ring
  rw [e1, e2]; ring

section Exponent

variable {x η ε T Δ1 Δ2 Δ3 : ℝ}

theorem rpow_mono_exp (hx : 1 ≤ x) {a b : ℝ} (h : a ≤ b) : x ^ a ≤ x ^ b :=
  Real.rpow_le_rpow_of_exponent_le hx h

/-- **First part** `√T · x^{ε/2} √Δ₁ ≤ x^{ε − 27η/8}` (LEAN BANK). -/
theorem first_part_saving (hx : 1 ≤ x) (hT : T ≤ x ^ (η / 4 + ε))
    (hd1 : Δ1 ≤ x ^ (-7 * η)) :
    Real.sqrt T * (x ^ (ε / 2) * Real.sqrt Δ1) ≤ x ^ (ε - 27 * η / 8) := by
  have hx0 : 0 < x := by linarith
  have h1 : Real.sqrt T ≤ x ^ ((η / 4 + ε) / 2) := by
    rw [Real.sqrt_le_left (Real.rpow_nonneg hx0.le _), ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    convert hT using 2; push_cast; ring
  have h2 : Real.sqrt Δ1 ≤ x ^ (-7 * η / 2) := by
    rw [Real.sqrt_le_left (Real.rpow_nonneg hx0.le _), ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    convert hd1 using 2; push_cast; ring
  calc Real.sqrt T * (x ^ (ε / 2) * Real.sqrt Δ1)
      ≤ x ^ ((η / 4 + ε) / 2) * (x ^ (ε / 2) * x ^ (-7 * η / 2)) :=
        mul_le_mul h1 (mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg hx0.le _))
          (mul_nonneg (Real.rpow_nonneg hx0.le _) (Real.sqrt_nonneg _)) (Real.rpow_nonneg hx0.le _)
    _ = x ^ (ε - 27 * η / 8) := by
        rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]; congr 1; ring

/-- **Second part** `√T · x^{η/8} (Δ₂+Δ₃)^{1/4} ≤ 2^{1/4} x^{ε/2 − 13η/4}` (LEAN BANK). -/
theorem second_part_saving (hx : 1 ≤ x) (hT : T ≤ x ^ (η / 4 + ε))
    (hd2 : Δ2 ≤ x ^ (-14 * η)) (hd3 : Δ3 ≤ x ^ (-14 * η)) :
    Real.sqrt T * (x ^ (η / 4 / 2) * Real.sqrt (Real.sqrt (Δ2 + Δ3))) ≤
      Real.sqrt (Real.sqrt 2) * x ^ (ε / 2 - 13 * η / 4) := by
  have hx0 : 0 < x := by linarith
  have h1 : Real.sqrt T ≤ x ^ ((η / 4 + ε) / 2) := by
    rw [Real.sqrt_le_left (Real.rpow_nonneg hx0.le _), ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    convert hT using 2; push_cast; ring
  have hsum : Δ2 + Δ3 ≤ 2 * x ^ (-14 * η) := by linarith
  have h2 : Real.sqrt (Real.sqrt (Δ2 + Δ3)) ≤ Real.sqrt (Real.sqrt 2) * x ^ (-7 * η / 2) := by
    have : Real.sqrt (Real.sqrt (2 * x ^ (-14 * η))) = Real.sqrt (Real.sqrt 2) * x ^ (-7 * η / 2) := by
      rw [Real.sqrt_mul (by norm_num), Real.sqrt_mul (Real.sqrt_nonneg _),
        Real.sqrt_eq_rpow (x ^ (-14 * η)), ← Real.rpow_mul hx0.le, Real.sqrt_eq_rpow (x ^ _),
        ← Real.rpow_mul hx0.le]
      congr 2; ring
    rw [← this]
    exact Real.sqrt_le_sqrt (Real.sqrt_le_sqrt hsum)
  calc Real.sqrt T * (x ^ (η / 4 / 2) * Real.sqrt (Real.sqrt (Δ2 + Δ3)))
      ≤ x ^ ((η / 4 + ε) / 2) * (x ^ (η / 4 / 2) * (Real.sqrt (Real.sqrt 2) * x ^ (-7 * η / 2))) :=
        mul_le_mul h1 (mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg hx0.le _))
          (mul_nonneg (Real.rpow_nonneg hx0.le _) (Real.sqrt_nonneg _)) (Real.rpow_nonneg hx0.le _)
    _ = Real.sqrt (Real.sqrt 2) * (x ^ ((η / 4 + ε) / 2) * x ^ (η / 4 / 2) * x ^ (-7 * η / 2)) := by
        ring
    _ = Real.sqrt (Real.sqrt 2) * x ^ (ε / 2 - 13 * η / 4) := by
        rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]; congr 2; ring

/-- **Energy-level instantiation** (LEAN BANK):
`T (x^ε Δ₁ + x^{η/4} (Δ₂+Δ₃)^{1/2}) ≤ 3 x^{−2η}` for `ε ≤ η`. -/
theorem energy_instantiation (hx : 1 ≤ x) (hη : 0 < η) (hε : ε ≤ η)
    (hT : T ≤ x ^ (η / 4 + ε)) (hΔ1 : 0 ≤ Δ1) (hd1 : Δ1 ≤ x ^ (-7 * η))
    (hd2 : Δ2 ≤ x ^ (-14 * η)) (hd3 : Δ3 ≤ x ^ (-14 * η)) :
    T * (x ^ ε * Δ1 + x ^ (η / 4) * Real.sqrt (Δ2 + Δ3)) ≤ 3 * x ^ (-2 * η) := by
  have hx0 : 0 < x := by linarith
  have hp : ∀ a : ℝ, 0 ≤ x ^ a := fun a => Real.rpow_nonneg hx0.le a
  have hA : T * (x ^ ε * Δ1) ≤ x ^ (-2 * η) := by
    calc T * (x ^ ε * Δ1) ≤ x ^ (η / 4 + ε) * (x ^ ε * x ^ (-7 * η)) :=
          mul_le_mul hT (mul_le_mul_of_nonneg_left hd1 (hp _)) (mul_nonneg (hp _) hΔ1) (hp _)
      _ = x ^ (η / 4 + ε + (ε + -7 * η)) := by rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]
      _ ≤ x ^ (-2 * η) := rpow_mono_exp hx (by linarith)
  have hs : Real.sqrt (Δ2 + Δ3) ≤ Real.sqrt 2 * x ^ (-7 * η) := by
    have : Real.sqrt (2 * x ^ (-14 * η)) = Real.sqrt 2 * x ^ (-7 * η) := by
      rw [Real.sqrt_mul (by norm_num), Real.sqrt_eq_rpow (x ^ _), ← Real.rpow_mul hx0.le]
      congr 2; ring
    rw [← this]; exact Real.sqrt_le_sqrt (by linarith)
  have hB : T * (x ^ (η / 4) * Real.sqrt (Δ2 + Δ3)) ≤ Real.sqrt 2 * x ^ (-2 * η) := by
    calc T * (x ^ (η / 4) * Real.sqrt (Δ2 + Δ3))
        ≤ x ^ (η / 4 + ε) * (x ^ (η / 4) * (Real.sqrt 2 * x ^ (-7 * η))) :=
          mul_le_mul hT (mul_le_mul_of_nonneg_left hs (hp _))
            (mul_nonneg (hp _) (Real.sqrt_nonneg _)) (hp _)
      _ = Real.sqrt 2 * (x ^ (η / 4 + ε) * (x ^ (η / 4) * x ^ (-7 * η))) := by ring
      _ = Real.sqrt 2 * x ^ (η / 4 + ε + (η / 4 + -7 * η)) := by
          rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]
      _ ≤ Real.sqrt 2 * x ^ (-2 * η) :=
          mul_le_mul_of_nonneg_left (rpow_mono_exp hx (by linarith)) (Real.sqrt_nonneg _)
  have h2 : Real.sqrt 2 ≤ 2 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have := hp (-2 * η)
  nlinarith

end Exponent

/-- **Conservative decorated theorem** (LEAN CONDITIONAL on `DIConclusion` and
`RepresentationMomentProvider`): under the exponent ledger `T ≤ x^{η/4+ε}`, `ε_DI = η/4`,
`Δ₁ ≤ x^{−7η}`, `Δ₂, Δ₃ ≤ x^{−14η}`, `ε ≤ η`:
`mass · V(Ψ) ≤ 3 N_q² x^{−2η}` for every one-bounded inner `Ψ`. -/
theorem decorated_conservative (D : DecoratedData) {η : ℝ} (hx : 1 ≤ D.KD.x) (hη : 0 < η)
    (hDI : DIConclusion D.KD) (hRep : RepresentationMomentProvider D)
    (hε : D.eps ≤ η) (hepsDI : D.KD.epsDI = η / 4)
    (hT : D.KD.T ≤ D.KD.x ^ (η / 4 + D.eps)) (hΔ1 : 0 ≤ D.Delta1)
    (hd1 : D.Delta1 ≤ D.KD.x ^ (-7 * η))
    (hd2 : D.KD.Delta2 ≤ D.KD.x ^ (-14 * η))
    (hd3 : D.KD.Delta3 ≤ D.KD.x ^ (-14 * η)) (Ψ : D.I → ℂ) (hΨ : ∀ i, ‖Ψ i‖ ≤ 1) :
    D.KD.mass * energy D.K Ψ ≤ 3 * D.KD.Nq ^ 2 * D.KD.x ^ (-2 * η) := by
  have h := decorated_energy_bound D (by linarith) hDI hRep Ψ hΨ
  have hi := energy_instantiation hx hη hε hT hΔ1 hd1 hd2 hd3
  rw [hepsDI] at h
  have : D.KD.x ^ D.eps * D.KD.Nq ^ 2 * D.KD.T * D.Delta1 +
      D.KD.x ^ (η / 4) * (D.KD.Nq ^ 2 * D.KD.T * Real.sqrt (D.KD.Delta2 + D.KD.Delta3)) =
      D.KD.Nq ^ 2 * (D.KD.T * (D.KD.x ^ D.eps * D.Delta1 +
        D.KD.x ^ (η / 4) * Real.sqrt (D.KD.Delta2 + D.KD.Delta3))) := by ring
  rw [this] at h
  calc D.KD.mass * energy D.K Ψ ≤ _ := h
    _ ≤ D.KD.Nq ^ 2 * (3 * D.KD.x ^ (-2 * η)) := mul_le_mul_of_nonneg_left hi (sq_nonneg _)
    _ = _ := by ring

/-- **Conservative decorated linear bound** (LEAN CONDITIONAL):
`|W(A,Ψ)| ≤ √3 · N_q · x^{−η}`, i.e. `N²/Q · x^{−η+o(1)}` in the normalisation `N_q = N²/Q`. -/
theorem decorated_conservative_linear (D : DecoratedData) {η : ℝ} (hx : 1 ≤ D.KD.x) (hη : 0 < η)
    (hDI : DIConclusion D.KD) (hRep : RepresentationMomentProvider D)
    (hε : D.eps ≤ η) (hepsDI : D.KD.epsDI = η / 4)
    (hT : D.KD.T ≤ D.KD.x ^ (η / 4 + D.eps)) (hΔ1 : 0 ≤ D.Delta1)
    (hd1 : D.Delta1 ≤ D.KD.x ^ (-7 * η))
    (hd2 : D.KD.Delta2 ≤ D.KD.x ^ (-14 * η))
    (hd3 : D.KD.Delta3 ≤ D.KD.x ^ (-14 * η)) (hNq : 0 ≤ D.KD.Nq)
    (Ψ : D.I → ℂ) (hΨ : ∀ i, ‖Ψ i‖ ≤ 1) :
    ‖decoratedSum D.A D.K Ψ‖ ≤ Real.sqrt 3 * D.KD.Nq * D.KD.x ^ (-η) := by
  have hW := decorated_cauchy D.A D.w D.hA D.K Ψ
  rw [D.hmass] at hW
  have hc := decorated_conservative D hx hη hDI hRep hε hepsDI hT hΔ1 hd1 hd2 hd3 Ψ hΨ
  have hx0 : 0 < D.KD.x := by linarith
  have hpos : 0 ≤ Real.sqrt 3 * D.KD.Nq * D.KD.x ^ (-η) :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hNq) (Real.rpow_nonneg hx0.le _)
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) hpos (by norm_num : (2 : ℕ) ≠ 0)).1 ?_
  calc ‖decoratedSum D.A D.K Ψ‖ ^ 2 ≤ 3 * D.KD.Nq ^ 2 * D.KD.x ^ (-2 * η) := hW.trans hc
    _ = (Real.sqrt 3 * D.KD.Nq * D.KD.x ^ (-η)) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num), ← Real.rpow_mul_natCast hx0.le]
      push_cast; ring_nf

end DecoratedLemma
end ResearchBankV27
end Erdos287
