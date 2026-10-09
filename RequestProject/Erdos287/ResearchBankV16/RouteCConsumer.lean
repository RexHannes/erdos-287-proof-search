import RequestProject.Erdos287.ResearchBankV14.RowRigidity
import RequestProject.Erdos287.ResearchBankV9.AffineContact
import RequestProject.Erdos287.ResearchBankV16.MacroGraph26
import RequestProject.Erdos287.ResearchBankV16.Score26
import RequestProject.Erdos287.ResearchBankV16.ContactLocalizationC

/-!
# Erdős #287 — Research Bank V16 §6a: the Route-C deterministic consumer

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

The Route-C analogue of the banked V14 consumer, with **Route-C constants only**: 26 macro-groups,
`G(26,7)`, score `f(v) = v − binom(v,2)/99`, threshold `350`, contact constant `c_C = 46/125`,
contact ratio `R_C`, window buffer `ρ_C = 10001/10000`.

* `FixedTupleC V` — a fixed tuple `a : V → ℕ` with macro-groups in `ZMod 26`, the edge identity
  `gcd(a_u, a_v) = a_v − a_u` on oriented macro-edges, `a_v ≥ 10000`, and the Route-C contact
  ratio `(a_u/d) a_v ≤ R_C (a_{u'}/d') a_{v'}`;
* `window τ M` — the proportional window `t ∈ [X, ρ_C X]`, `X = M/(ρ_C Z)`;
* `window_good` — (contact localization + row rigidity) for all large `M` (LEAN BANK);
* `score_identity` — `∑_t w (S(t) − 350) = S1 − Pair/99 − 350 S0` (LEAN BANK);
* `pair_contradiction`, `no_counterexample_of_good_t` — a window point with `S(t) > 350`
  refutes every counterexample with maximum `M` (occupancy ≥ 8 ⟹ macro-edge ⟹ oriented useful
  identity ⟹ two forced consecutive omissions ⟹ harmonic contradiction at `c_C`) (LEAN BANK).

No Route-C tuple is constructed here; a tuple enters as an explicit argument.
-/

namespace Erdos287
namespace ResearchBankV16
namespace RouteCConsumer

open MacroGraph26 Score26 ContactLocalizationC
open ResearchBankV14.RowRigidity
open ResearchBankV13.FiniteRepresentationModel ResearchBankV9.AffineContact

open Classical in
/-- Oriented macro-edge. -/
def OE {V : Type} (a : V → ℕ) (cell : V → ZMod 26) (u v : V) : Prop :=
  G26.Adj (cell u) (cell v) ∧ a u < a v

/-- The contact cofactor `n_e = a_u / d`, `d = a_v − a_u`. -/
def coeff {V : Type} (a : V → ℕ) (u v : V) : ℕ := a u / (a v - a u)

/-- **A fixed tuple** (kept fixed throughout the asymptotic theorem). -/
structure FixedTupleC (V : Type) [Fintype V] [DecidableEq V] where
  a : V → ℕ
  cell : V → ZMod 26
  a_ge : ∀ v, 10000 ≤ a v
  adj_ne : ∀ u v, G26.Adj (cell u) (cell v) → a u ≠ a v
  edge_gcd : ∀ u v, G26.Adj (cell u) (cell v) → a u < a v → Nat.gcd (a u) (a v) = a v - a u
  ratio : ∀ u v u' v', OE a cell u v → OE a cell u' v' →
    ((coeff a u v : ℚ) * a v) ≤ RC * ((coeff a u' v' : ℚ) * a v')
  has_edge : ∃ u v, OE a cell u v

variable {V : Type} [Fintype V] [DecidableEq V]

section Window

variable (τ : FixedTupleC V)

open Classical in
/-- The oriented edges. -/
noncomputable def edges : Finset (V × V) :=
  (Finset.univ ×ˢ Finset.univ).filter fun p => OE τ.a τ.cell p.1 p.2

theorem mem_edges {p : V × V} : p ∈ edges τ ↔ OE τ.a τ.cell p.1 p.2 := by
  classical
  simp [edges]

/-- `Z = max_e (a_u/d)(a_v + 1)`. -/
noncomputable def Zmax : ℕ := (edges τ).sup fun p => coeff τ.a p.1 p.2 * (τ.a p.2 + 1)

/-- The rigidity height `H = 2 Z`. -/
noncomputable def H : ℕ := 2 * Zmax τ

/-- Scale `X = M / (ρ Z)`, `ρ = ρ_C = 10001/10000`. -/
noncomputable def X (M : ℕ) : ℝ := M / (((rhoC : ℚ) : ℝ) * Zmax τ)

/-- **The fixed proportional interval** `t ∈ [X, ρ X]`. -/
noncomputable def window (M : ℕ) : Finset ℕ :=
  Finset.Icc ⌈X τ M⌉₊ ⌊((rhoC : ℚ) : ℝ) * X τ M⌋₊

theorem coeff_pos {u v : V} (h : OE τ.a τ.cell u v) : 1 ≤ coeff τ.a u v := by
  have hg := τ.edge_gcd u v h.1 h.2
  have hd : (τ.a v - τ.a u) ∣ τ.a u := by rw [← hg]; exact Nat.gcd_dvd_left _ _
  have hu := τ.a_ge u
  have hlt := h.2
  exact Nat.div_pos (Nat.le_of_dvd (by omega) hd) (by omega)

theorem edges_nonempty : (edges τ).Nonempty := by
  obtain ⟨u, v, h⟩ := τ.has_edge
  exact ⟨(u, v), (mem_edges τ).2 h⟩

theorem le_Zmax {u v : V} (h : OE τ.a τ.cell u v) :
    coeff τ.a u v * (τ.a v + 1) ≤ Zmax τ := by
  unfold Zmax
  exact Finset.le_sup (f := fun p : V × V => coeff τ.a p.1 p.2 * (τ.a p.2 + 1))
    ((mem_edges τ (p := (u, v))).2 h)

theorem Zmax_pos : 1 ≤ Zmax τ := by
  obtain ⟨u, v, h⟩ := τ.has_edge
  have h1 := le_Zmax τ h
  have h2 := coeff_pos τ h
  nlinarith

theorem rhoC_real : ((rhoC : ℚ) : ℝ) = 10001 / 10000 := by unfold rhoC; norm_num

/-- **Window theorem** (contact annulus + rigidity on the fixed proportional interval): for every
sufficiently large `M` and every `t` in the window, every `L_v(t)` is rigid at scale `M` with
height `H`, and every useful contact `z = (a_u/d) L_v(t)` lies in `[cM, M]`. -/
theorem window_good : ∃ M₀ : ℕ, ∀ M ≥ M₀, ∀ t ∈ window τ M,
    (∀ v, M < (H τ + 1) * (τ.a v * t + 1) ∧ max (H τ) (NH (H τ)) < τ.a v * t + 1) ∧
    (∀ u v, OE τ.a τ.cell u v →
      ((cC : ℚ) : ℝ) * M ≤ ((coeff τ.a u v * (τ.a v * t + 1) : ℕ) : ℝ) ∧
      coeff τ.a u v * (τ.a v * t + 1) ≤ M) := by
  set Z := Zmax τ with hZdef
  have hZ : 1 ≤ Z := Zmax_pos τ
  set Hh := H τ with hHh
  set B := NH Hh + Hh + 1 with hB
  refine ⟨2 * Z * B, fun M hM t ht => ?_⟩
  set ρ : ℝ := ((rhoC : ℚ) : ℝ) with hρdef
  have hρ : ρ = 10001 / 10000 := rhoC_real
  have hZr : (1 : ℝ) ≤ Z := by exact_mod_cast hZ
  have hρZ : 0 < ρ * Z := by rw [hρ]; positivity
  have hXdef : X τ M * (ρ * Z) = M := by
    unfold X; rw [← hρdef, ← hZdef]; field_simp
  have hMr : ((2 * Z * B : ℕ) : ℝ) ≤ M := by exact_mod_cast hM
  have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast (show 1 ≤ B by omega)
  have hXB : (B : ℝ) ≤ X τ M := by
    unfold X
    rw [le_div_iff₀ hρZ, hρ]
    push_cast at hMr
    nlinarith
  have hX0 : 0 ≤ X τ M := le_trans (by positivity) hXB
  obtain ⟨ht1, ht2⟩ := Finset.mem_Icc.1 ht
  have htX : X τ M ≤ t := Nat.ceil_le.1 ht1
  have htX2 : (t : ℝ) ≤ ρ * X τ M := (Nat.le_floor_iff (by rw [hρ]; positivity)).1 ht2
  have hBt : B ≤ t := by exact_mod_cast hXB.trans htX
  have ht1' : 1 ≤ t := by omega
  have ht0 : (1 : ℝ) ≤ t := by exact_mod_cast ht1'
  have hMle : (M : ℝ) ≤ ρ * Z * t := by
    rw [← hXdef]
    have : X τ M * (ρ * Z) ≤ (t : ℝ) * (ρ * Z) := mul_le_mul_of_nonneg_right htX hρZ.le
    linarith
  refine ⟨fun v => ⟨?_, ?_⟩, fun u v huv => ⟨?_, ?_⟩⟩
  · -- `M < (H + 1) L_v(t)`
    have hav : (10000 : ℝ) ≤ τ.a v := by exact_mod_cast τ.a_ge v
    have hH : (Hh : ℝ) = 2 * Z := by rw [hHh, H]; push_cast; ring
    have : (M : ℝ) < ((Hh + 1) * (τ.a v * t + 1) : ℕ) := by
      push_cast
      rw [hH]
      rw [hρ] at hMle
      have h1 : (0 : ℝ) ≤ (τ.a v : ℝ) * t := by positivity
      nlinarith
    exact_mod_cast this
  · -- `max(H, N_H) < L_v(t)`
    have hav := τ.a_ge v
    have h1 : t ≤ τ.a v * t := Nat.le_mul_of_pos_left t (by omega)
    rw [max_lt_iff]; constructor <;> omega
  · -- lower localization `cM ≤ z`
    obtain ⟨p, hp, hpZ⟩ := Finset.exists_mem_eq_sup (edges τ) (edges_nonempty τ)
      (fun p : V × V => coeff τ.a p.1 p.2 * (τ.a p.2 + 1))
    have hpOE := (mem_edges τ).1 hp
    have hr := τ.ratio p.1 p.2 u v hpOE huv
    have hapge : (10000 : ℝ) ≤ τ.a p.2 := by exact_mod_cast τ.a_ge p.2
    set K1 : ℝ := (coeff τ.a u v : ℝ) * τ.a v with hK1
    have hK1nn : 0 ≤ K1 := by positivity
    have hr' : (coeff τ.a p.1 p.2 : ℝ) * τ.a p.2 ≤ ((RC : ℚ) : ℝ) * K1 := by
      have := (Rat.cast_le (K := ℝ)).2 hr
      push_cast at this
      rw [hK1]; exact this
    have hZle : (Z : ℝ) ≤ ρ * (((RC : ℚ) : ℝ) * K1) := by
      have hZeq : (Z : ℝ) = (coeff τ.a p.1 p.2 : ℝ) * (τ.a p.2 + 1) := by
        rw [hZdef]; unfold Zmax; rw [hpZ]; push_cast; ring
      rw [hZeq]
      have hcp : (0 : ℝ) ≤ coeff τ.a p.1 p.2 := by positivity
      calc (coeff τ.a p.1 p.2 : ℝ) * (τ.a p.2 + 1) ≤ (coeff τ.a p.1 p.2 : ℝ) * (ρ * τ.a p.2) := by
            apply mul_le_mul_of_nonneg_left _ hcp; rw [hρ]; linarith
        _ = ρ * ((coeff τ.a p.1 p.2 : ℝ) * τ.a p.2) := by ring
        _ ≤ ρ * (((RC : ℚ) : ℝ) * K1) := by
            apply mul_le_mul_of_nonneg_left hr'; rw [hρ]; norm_num
    have hbuf : ((cC : ℚ) : ℝ) * ((RC : ℚ) : ℝ) * ρ ^ 2 < 1 := by
      have := cC_mul_RC_buffer_lt_one
      rw [hρdef]; exact_mod_cast this
    have hc0 : (0 : ℝ) ≤ ((cC : ℚ) : ℝ) := by unfold cC; norm_num
    have hR0 : (0 : ℝ) ≤ ((RC : ℚ) : ℝ) := by rw [RC_eq]; norm_num
    have hρ0 : (0 : ℝ) ≤ ρ := by rw [hρ]; norm_num
    calc ((cC : ℚ) : ℝ) * M = ((cC : ℚ) : ℝ) * (X τ M * (ρ * Z)) := by
          rw [hXdef]
      _ ≤ ((cC : ℚ) : ℝ) * (X τ M * (ρ * (ρ * (((RC : ℚ) : ℝ) * K1)))) := by
          gcongr
      _ = (((cC : ℚ) : ℝ) * ((RC : ℚ) : ℝ) * ρ ^ 2) * (K1 * X τ M) := by ring
      _ ≤ 1 * (K1 * X τ M) := by
          apply mul_le_mul_of_nonneg_right hbuf.le (by positivity)
      _ = K1 * X τ M := one_mul _
      _ ≤ K1 * t := mul_le_mul_of_nonneg_left htX hK1nn
      _ ≤ ((coeff τ.a u v * (τ.a v * t + 1) : ℕ) : ℝ) := by
          rw [hK1]; push_cast
          have : (0 : ℝ) ≤ coeff τ.a u v := by positivity
          nlinarith
  · -- upper localization `z ≤ M`
    have h1 : coeff τ.a u v * (τ.a v * t + 1) ≤ coeff τ.a u v * (τ.a v + 1) * t := by
      rw [mul_assoc]
      apply Nat.mul_le_mul_left
      nlinarith
    have h2 := le_Zmax τ huv
    have h3 : coeff τ.a u v * (τ.a v + 1) * t ≤ Z * t := Nat.mul_le_mul_right t h2
    have h4 : ((Z * t : ℕ) : ℝ) ≤ M := by
      push_cast; rw [hρ] at hMle; nlinarith
    have h5 : Z * t ≤ M := by exact_mod_cast h4
    omega

end Window

/-! ## Weights, moments and the score identity -/

section Moments

variable (τ : FixedTupleC V)

/-- A nonnegative physical weight `w(M, t)`. -/
structure WeightSystem (τ : FixedTupleC V) where
  w : ℕ → ℕ → ℝ
  w_nonneg : ∀ M t, 0 ≤ w M t

/-- The vertices with `L_v(t) = a_v t + 1` prime. -/
def primeSet (t : ℕ) : Finset V := Finset.univ.filter fun v => (τ.a v * t + 1).Prime

/-- Cell occupancy `P_r(t)`. -/
def occ (t : ℕ) (r : ZMod 26) : ℕ := ((primeSet τ t).filter fun v => τ.cell v = r).card

theorem sum_occ (t : ℕ) : ∑ r, occ τ t r = (primeSet τ t).card :=
  (Finset.card_eq_sum_card_fiberwise (f := τ.cell) (fun _ _ => by simp)).symm

/-- The score `S(t)` (real). -/
noncomputable def scoreR (t : ℕ) : ℝ := ((score (occ τ t) : ℚ) : ℝ)

variable (W : WeightSystem τ)

/-- Actual zeroth moment over the window. -/
noncomputable def S0 (M : ℕ) : ℝ := ∑ t ∈ window τ M, W.w M t

/-- Actual first moment over the window. -/
noncomputable def S1 (M : ℕ) : ℝ := ∑ t ∈ window τ M, W.w M t * ((primeSet τ t).card : ℝ)

/-- Actual weighted coloured pair count over the window. -/
noncomputable def Pair (M : ℕ) : ℝ :=
  ∑ t ∈ window τ M, W.w M t * ∑ r, (((occ τ t r).choose 2 : ℕ) : ℝ)

theorem scoreR_eq (t : ℕ) :
    scoreR τ t = ((primeSet τ t).card : ℝ) - (∑ r, (((occ τ t r).choose 2 : ℕ) : ℝ)) / 99 := by
  unfold scoreR score f
  push_cast
  rw [Finset.sum_sub_distrib, ← Finset.sum_div, ← sum_occ]
  push_cast; ring

/-- **Score identity**: `∑_t w (S(t) − 350) = S1 − Pair/99 − 350 S0`. -/
theorem score_identity (M : ℕ) :
    ∑ t ∈ window τ M, W.w M t * (scoreR τ t - 350) = S1 τ W M - Pair τ W M / 99 - 350 * S0 τ W M := by
  unfold S1 Pair S0
  rw [Finset.mul_sum, Finset.sum_div, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [scoreR_eq]; ring

end Moments

/-! ## The deterministic endgame -/

/-- **A useful pair at a window point refutes every counterexample with maximum `M`.** -/
theorem pair_contradiction (τ : FixedTupleC V) {M t : ℕ}
    (hrig : ∀ v, M < (H τ + 1) * (τ.a v * t + 1) ∧ max (H τ) (NH (H τ)) < τ.a v * t + 1)
    (hcon : ∀ u v, OE τ.a τ.cell u v →
      ((cC : ℚ) : ℝ) * M ≤ ((coeff τ.a u v * (τ.a v * t + 1) : ℕ) : ℝ) ∧
      coeff τ.a u v * (τ.a v * t + 1) ≤ M)
    {u v : V} (huv : OE τ.a τ.cell u v) (hpu : (τ.a u * t + 1).Prime)
    (hpv : (τ.a v * t + 1).Prime) {A : Finset ℕ} (hA : Erdos287Counterexample A)
    (hAM : A.max' hA.nonempty = M) : False := by
  have hg := τ.edge_gcd u v huv.1 huv.2
  obtain ⟨hz1, -, -⟩ := contact_locations huv.2 hg t
  unfold F at hz1
  set z := coeff τ.a u v * (τ.a v * t + 1) with hz
  have hz1' : z + 1 = τ.a v / (τ.a v - τ.a u) * (τ.a u * t + 1) := by rw [hz]; exact hz1
  obtain ⟨hlow, hup⟩ := hcon u v huv
  have hfloor : ∀ w, A.max' hA.nonempty / (τ.a w * t + 1) ≤ H τ := fun w => by
    rw [hAM, floor_le_iff (by omega)]; exact (hrig w).1
  have hzA : z ∉ A := fun hzA =>
    row_rigidity hA hpv (hfloor v) (hrig v).2 z hzA (by rw [hz]; exact dvd_mul_left _ _)
  have hz1A : z + 1 ∉ A := fun hzA =>
    row_rigidity hA hpu (hfloor u) (hrig u).2 (z + 1) hzA (by rw [hz1']; exact dvd_mul_left _ _)
  exact two_hole_contradiction_cC hA hzA hz1A (by rw [hAM]; exact hup)
    (by rw [hAM]; exact hlow)

/-- **A window point with `S(t) > 350` refutes every counterexample with maximum `M`.** -/
theorem no_counterexample_of_good_t (τ : FixedTupleC V) {M t : ℕ}
    (hrig : ∀ v, M < (H τ + 1) * (τ.a v * t + 1) ∧ max (H τ) (NH (H τ)) < τ.a v * t + 1)
    (hcon : ∀ u v, OE τ.a τ.cell u v →
      ((cC : ℚ) : ℝ) * M ≤ ((coeff τ.a u v * (τ.a v * t + 1) : ℕ) : ℝ) ∧
      coeff τ.a u v * (τ.a v * t + 1) ≤ M)
    (hS : 350 < scoreR τ t) : NoCounterexampleAt M := by
  intro A hA hAM
  have hSq : (350 : ℚ) < score (occ τ t) := by unfold scoreR at hS; exact_mod_cast hS
  obtain ⟨r, hr, s, hs, hrs⟩ :=
    occupied_eight_forces_edge _ (eight_occupied_of_score_gt _ hSq)
  have hne : ∀ q ∈ occupied (occ τ t), ∃ w, w ∈ primeSet τ t ∧ τ.cell w = q := by
    intro q hq
    simp only [occupied, Finset.mem_filter, Finset.mem_univ, true_and] at hq
    obtain ⟨w, hw⟩ := Finset.card_pos.1 (Nat.pos_of_ne_zero hq)
    exact ⟨w, (Finset.mem_filter.1 hw).1, (Finset.mem_filter.1 hw).2⟩
  obtain ⟨u, hu, hcu⟩ := hne r hr
  obtain ⟨v, hv, hcv⟩ := hne s hs
  have hpu : (τ.a u * t + 1).Prime := by simpa [primeSet] using hu
  have hpv : (τ.a v * t + 1).Prime := by simpa [primeSet] using hv
  have hadj : G26.Adj (τ.cell u) (τ.cell v) := by rw [hcu, hcv]; exact hrs
  rcases lt_or_gt_of_ne (τ.adj_ne u v hadj) with hlt | hlt
  · exact pair_contradiction τ hrig hcon ⟨hadj, hlt⟩ hpu hpv hA hAM
  · exact pair_contradiction τ hrig hcon ⟨G26.symm hadj, hlt⟩ hpv hpu hA hAM


end RouteCConsumer
end ResearchBankV16
end Erdos287
