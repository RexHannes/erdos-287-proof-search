import RequestProject.Erdos287.PostV71V87.ReciprocalImage
import RequestProject.Erdos287.PostV71V87.AnalyticToolkit

/-!
# Erdős #287 — V87: `log S_rec(H) ≪ H log log H / log H`

From the block decomposition (`Srec_block_bound`) and Chebyshev's upper bound (imported from
Mathlib, `chebyshev_upper`) we prove, with no further analytic input,

  `log S_rec(H) ≤ C · H · log log H / log H`   for all `H ≥ H0`   (`log_Srec_le`).

Steps:

* `blockSum_le_sum_primeCounting` — `∑_{y<p≤H} ⌊H/p⌋ ≤ ∑_{m ≤ H/(y+1)} π(⌊H/m⌋)`
  (count pairs `(p, m)` with `pm ≤ H`);
* `blockSum_real_le` — `∑_{y<p≤H} ⌊H/p⌋ ≤ C_π H (1 + log ⌊H/(y+1)⌋) / log y`;
* `log_Srec_le_explicit` — `log S_rec(H) ≤ (π(y) + 2) log H + ∑_{y<p≤H} ⌊H/p⌋`;
* `log_Srec_le` — the asymptotic bound, with `y = ⌊H / log H⌋`.
-/

open Real
open scoped BigOperators

namespace Erdos287.PostV71V87

/-- Double counting of the large-prime blocks. -/
theorem blockSum_le_sum_primeCounting (y H : ℕ) :
    blockSum y H ≤ ∑ m ∈ Finset.Icc 1 (H / (y + 1)), Nat.primeCounting (H / m) := by
  classical
  set L := H / (y + 1)
  have h1 : ∀ p ∈ largePrimes y H,
      H / p = ∑ m ∈ Finset.Icc 1 L, if m * p ≤ H then 1 else 0 := by
    intro p hp
    simp only [largePrimes, Finset.mem_filter, Finset.mem_Ioc] at hp
    have hp0 : 0 < p := by omega
    rw [Finset.sum_boole]
    have : (Finset.Icc 1 L).filter (fun m => m * p ≤ H) = Finset.Icc 1 (H / p) := by
      ext m
      simp only [Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, (Nat.le_div_iff_mul_le hp0).2 h3⟩
      · rintro ⟨h1, h2⟩
        refine ⟨⟨h1, le_trans h2 (Nat.div_le_div_left (by omega) (by omega))⟩, ?_⟩
        exact (Nat.le_div_iff_mul_le hp0).1 h2
    rw [this]; simp
  unfold blockSum
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  refine Finset.sum_le_sum (fun m hm => ?_)
  rw [Finset.sum_boole]
  have hm1 : 1 ≤ m := (Finset.mem_Icc.1 hm).1
  have hsub : (largePrimes y H).filter (fun p => m * p ≤ H) ⊆ Nat.primesBelow (H / m + 1) := by
    intro p hp
    simp only [largePrimes, Finset.mem_filter, Finset.mem_Ioc] at hp
    rw [Nat.mem_primesBelow]
    refine ⟨?_, hp.1.2⟩
    have : p ≤ H / m := (Nat.le_div_iff_mul_le (by omega)).2 (by rw [mul_comm]; exact hp.2)
    omega
  have hc : (Nat.primesBelow (H / m + 1)).card = Nat.primeCounting (H / m) := by
    rw [Nat.primesBelow_card_eq_primeCounting']; rfl
  simpa [hc] using Finset.card_le_card hsub

/-- Real form of the block bound. -/
theorem blockSum_real_le {X0 : ℝ} (hX0 : 2 ≤ X0)
    (hcheb : ∀ x : ℝ, X0 ≤ x → (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ Cpi * x / Real.log x)
    {y H : ℕ} (hy : X0 ≤ y) :
    (blockSum y H : ℝ) ≤ Cpi * H * (1 + Real.log ((H / (y + 1) : ℕ) : ℝ)) / Real.log y := by
  have hy2 : (2 : ℝ) ≤ y := le_trans hX0 hy
  have hlogy : 0 < Real.log y := Real.log_pos (by linarith)
  have hCH : 0 ≤ Cpi * (H : ℝ) / Real.log y :=
    div_nonneg (mul_nonneg Cpi_pos.le (Nat.cast_nonneg _)) hlogy.le
  have hstep : ∀ m ∈ Finset.Icc 1 (H / (y + 1)),
      (Nat.primeCounting (H / m) : ℝ) ≤ Cpi * H / Real.log y * (1 / (m : ℝ)) := by
    intro m hm
    obtain ⟨hm1, hmL⟩ := Finset.mem_Icc.1 hm
    have hmy : m * (y + 1) ≤ H := (Nat.le_div_iff_mul_le (by omega)).1 hmL
    have hmpos : (0 : ℝ) < m := by exact_mod_cast hm1
    have hmy' : ((y : ℝ) + 1) * m ≤ H := by
      have : ((m * (y + 1) : ℕ) : ℝ) ≤ H := by exact_mod_cast hmy
      push_cast at this; linarith
    have hx : (y : ℝ) + 1 ≤ (H : ℝ) / m := by rw [le_div_iff₀ hmpos]; exact hmy'
    have hfl : ⌊(H : ℝ) / m⌋₊ = H / m := Nat.floor_div_eq_div H m
    have h1 := hcheb ((H : ℝ) / m) (by linarith)
    rw [hfl] at h1
    have hlog : Real.log y ≤ Real.log ((H : ℝ) / m) := Real.log_le_log (by linarith) (by linarith)
    calc (Nat.primeCounting (H / m) : ℝ) ≤ Cpi * ((H : ℝ) / m) / Real.log ((H : ℝ) / m) := h1
      _ ≤ Cpi * ((H : ℝ) / m) / Real.log y :=
          div_le_div_of_nonneg_left (mul_nonneg Cpi_pos.le (by positivity)) hlogy hlog
      _ = Cpi * H / Real.log y * (1 / (m : ℝ)) := by field_simp
  calc (blockSum y H : ℝ) ≤ ∑ m ∈ Finset.Icc 1 (H / (y + 1)), (Nat.primeCounting (H / m) : ℝ) := by
        exact_mod_cast blockSum_le_sum_primeCounting y H
    _ ≤ ∑ m ∈ Finset.Icc 1 (H / (y + 1)), Cpi * H / Real.log y * (1 / (m : ℝ)) :=
        Finset.sum_le_sum hstep
    _ = Cpi * H / Real.log y * (harmonic (H / (y + 1)) : ℝ) := by
        rw [← Finset.mul_sum, harmonic_eq_sum_Icc]; push_cast; simp [one_div]
    _ ≤ Cpi * H / Real.log y * (1 + Real.log ((H / (y + 1) : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left (harmonic_le_one_add_log _) hCH
    _ = _ := by ring

/-- Explicit form: `log S_rec(H) ≤ (π(y) + 2) log H + ∑_{y<p≤H} ⌊H/p⌋` for `H ≥ 2`. -/
theorem log_Srec_le_explicit (y H : ℕ) (hH : 2 ≤ H) :
    Real.log (Srec H) ≤ ((Nat.primeCounting y : ℝ) + 2) * Real.log H + blockSum y H := by
  have hb := Srec_block_bound y H (by omega)
  have h1 : H * H ^ Nat.primeCounting y + 1 ≤ H ^ (Nat.primeCounting y + 2) := by
    have hp : 1 ≤ H * H ^ Nat.primeCounting y := Nat.one_le_iff_ne_zero.2 (by positivity)
    have : H ^ (Nat.primeCounting y + 2) = H * (H * H ^ Nat.primeCounting y) := by ring
    rw [this]; nlinarith
  have h2 : Srec H ≤ H ^ (Nat.primeCounting y + 2) * 2 ^ blockSum y H :=
    le_trans hb (Nat.mul_le_mul_right _ h1)
  have h3 : (Srec H : ℝ) ≤ (H : ℝ) ^ (Nat.primeCounting y + 2) * 2 ^ blockSum y H := by
    exact_mod_cast h2
  have hS : (0 : ℝ) < Srec H := by exact_mod_cast Srec_pos H
  have hH0 : (0 : ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  have h4 := Real.log_le_log hS h3
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow] at h4
  have hl2 : Real.log 2 ≤ 1 := by
    have := Real.log_two_lt_d9; linarith
  have hB : (blockSum y H : ℝ) * Real.log 2 ≤ blockSum y H := by
    have : (0 : ℝ) ≤ blockSum y H := Nat.cast_nonneg _
    nlinarith
  push_cast at h4
  linarith

set_option maxHeartbeats 1600000 in
/-- **V87 reciprocal-image entropy bound.**
`log S_rec(H) ≤ C · H · log log H / log H` for all `H ≥ H0`. -/
theorem log_Srec_le :
    ∃ C H0 : ℝ, 0 < C ∧ ∀ H : ℕ, H0 ≤ H →
      Real.log (Srec H) ≤ C * H * Real.log (Real.log H) / Real.log H := by
  obtain ⟨X0, hX0, hcheb⟩ := chebyshev_upper
  refine ⟨6 * Cpi + 2, max 4096 (X0 ^ 2), by linarith [Cpi_pos], ?_⟩
  intro H hH
  have h4096 : (4096 : ℝ) ≤ H := le_trans (le_max_left _ _) hH
  have hX : X0 ^ 2 ≤ (H : ℝ) := le_trans (le_max_right _ _) hH
  have hpos : (0 : ℝ) < H := by linarith
  have hH2 : 2 ≤ H := by
    have : (2 : ℝ) ≤ H := by linarith
    exact_mod_cast this
  set s := (H : ℝ) ^ (1 / 4 : ℝ) with hsdef
  have hs4 : s ^ 4 = H := rpow_quarter_pow_four hpos.le
  have hs2 : s ^ 2 = Real.sqrt H := rpow_quarter_sq hpos.le
  have hs0 : 0 ≤ s := Real.rpow_nonneg hpos.le _
  have hs8 : 8 ≤ s := by
    by_contra hc; push_neg at hc
    have : s ^ 4 < 8 ^ 4 := by
      have := pow_lt_pow_left₀ hc hs0 (by norm_num : (4 : ℕ) ≠ 0); exact this
    norm_num at this; linarith
  set lH := Real.log H with hlHdef
  have hlH : lH ≤ 4 * s := log_le_four_rpow hpos.le
  have hexp3 : Real.exp 3 ≤ (H : ℝ) := by
    have h1 : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
    have h2 := Real.exp_one_lt_d9
    have h3 : Real.exp 1 ^ 3 < 2.7182818286 ^ 3 :=
      pow_lt_pow_left₀ h2 (Real.exp_pos 1).le (by norm_num)
    rw [h1]; nlinarith
  have hlH3 : 3 ≤ lH := (Real.le_log_iff_exp_le hpos).2 hexp3
  have hlHpos : 0 < lH := by linarith
  clear_value s lH
  -- the cut `y = ⌊H / log H⌋`
  set y : ℕ := ⌊(H : ℝ) / lH⌋₊ with hydef
  have hy_le : (y : ℝ) ≤ H / lH := Nat.floor_le (by positivity)
  have hy_gt : (H : ℝ) / lH < y + 1 := Nat.lt_floor_add_one _
  clear_value y
  have hhl : 2 * s ^ 2 ≤ (H : ℝ) / lH := by
    rw [le_div_iff₀ hlHpos]
    have : 2 * s ^ 2 * lH ≤ 2 * s ^ 2 * (4 * s) :=
      mul_le_mul_of_nonneg_left hlH (by positivity)
    nlinarith
  have hys : s ^ 2 ≤ y := by nlinarith
  have hsqX : X0 ≤ s ^ 2 := by
    rw [hs2]
    calc X0 = Real.sqrt (X0 ^ 2) := (Real.sqrt_sq (by linarith)).symm
      _ ≤ Real.sqrt H := Real.sqrt_le_sqrt hX
  have hyX : X0 ≤ y := le_trans hsqX hys
  have hy2 : (2 : ℝ) ≤ y := le_trans hX0 hyX
  have hlogy : lH / 2 ≤ Real.log y := by
    have h1 : Real.log (s ^ 2) ≤ Real.log y := Real.log_le_log (by positivity) hys
    have h2 : lH = Real.log (s ^ 4) := by rw [hs4]; exact hlHdef
    rw [Real.log_pow] at h1 h2
    push_cast at h1 h2
    linarith
  have hlogypos : 0 < Real.log y := Real.log_pos (by linarith)
  -- `π(y) log H ≤ 2 C_π H / log H`
  set u := (H : ℝ) / lH with hudef
  have hu0 : 0 ≤ u := by positivity
  have hu_eq : u * lH = H := by rw [hudef]; field_simp
  clear_value u
  have hpi : (Nat.primeCounting y : ℝ) ≤ Cpi * y / Real.log y := by
    have := hcheb y hyX; rwa [Nat.floor_natCast] at this
  have F1 : (Nat.primeCounting y : ℝ) * lH ≤ 2 * Cpi * u := by
    have h1 : Cpi * y / Real.log y ≤ Cpi * u / (lH / 2) := by
      rw [div_le_div_iff₀ hlogypos (by positivity)]
      have := mul_le_mul hy_le hlogy (by positivity) hu0
      nlinarith [Cpi_pos]
    have h2 : Cpi * u / (lH / 2) * lH = 2 * Cpi * u := by field_simp
    nlinarith
  -- block sum
  set L := H / (y + 1) with hLdef
  have hL : (L : ℝ) ≤ lH := by
    have h1 : (L : ℝ) ≤ (H : ℝ) / ((y : ℝ) + 1) := by
      have := Nat.cast_div_le (α := ℝ) (m := H) (n := y + 1); push_cast at this; exact this
    have h2 : (H : ℝ) / ((y : ℝ) + 1) ≤ lH := by
      rw [div_le_iff₀ (by positivity)]
      have := mul_lt_mul_of_pos_right hy_gt hlHpos
      nlinarith
    linarith
  have hlogL : Real.log L ≤ Real.log lH := by
    rcases Nat.eq_zero_or_pos L with h0 | h0
    · rw [h0]; simp; exact Real.log_nonneg (by linarith)
    · exact Real.log_le_log (by exact_mod_cast h0) hL
  set ll := Real.log lH with hlldef
  have hll1 : 1 ≤ ll := by
    rw [hlldef, Real.le_log_iff_exp_le hlHpos]
    have := Real.exp_one_lt_d9; linarith
  clear_value ll L
  have hB := blockSum_real_le hX0 hcheb (y := y) (H := H) hyX
  rw [← hLdef] at hB
  have F2 : (blockSum y H : ℝ) ≤ 2 * Cpi * u * (1 + ll) := by
    have h1 : Cpi * H * (1 + Real.log L) / Real.log y ≤ Cpi * H * (1 + ll) / (lH / 2) := by
      rw [div_le_div_iff₀ hlogypos (by positivity)]
      have hA : 0 ≤ Cpi * (H : ℝ) := mul_nonneg Cpi_pos.le hpos.le
      have := mul_le_mul (mul_le_mul_of_nonneg_left (by linarith : 1 + Real.log L ≤ 1 + ll) hA)
        hlogy (by positivity) (mul_nonneg hA (by linarith))
      linarith
    have h2 : Cpi * H * (1 + ll) / (lH / 2) = 2 * Cpi * u * (1 + ll) := by
      rw [hudef]; field_simp
    linarith
  have F3 : lH ≤ u := by
    have h1 : lH * lH ≤ (4 * s) * (4 * s) := mul_le_mul hlH hlH hlHpos.le (by positivity)
    have h16 : (16 : ℝ) ≤ s ^ 2 := by
      have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 8) hs8 2; norm_num at this; linarith
    have h2 : (4 * s) * (4 * s) ≤ s ^ 4 := by
      have : (4 * s) * (4 * s) = 16 * s ^ 2 := by ring
      rw [this]
      have : s ^ 4 = s ^ 2 * s ^ 2 := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_right h16 (by positivity)
    have hlHH : lH * lH ≤ u * lH := by
      rw [hu_eq]; exact le_trans h1 (le_trans h2 (le_of_eq hs4))
    exact le_of_mul_le_mul_right hlHH hlHpos
  have hE := log_Srec_le_explicit y H hH2
  rw [← hlHdef] at hE
  have hgoal : (6 * Cpi + 2) * H * ll / lH = (6 * Cpi + 2) * (u * ll) := by
    rw [← hu_eq, div_eq_iff hlHpos.ne']; ring
  rw [hgoal]
  have hul : u * 1 ≤ u * ll := mul_le_mul_of_nonneg_left hll1 hu0
  have hc1 : Cpi * (u * 1) ≤ Cpi * (u * ll) := mul_le_mul_of_nonneg_left hul Cpi_pos.le
  have hexp : ((Nat.primeCounting y : ℝ) + 2) * lH = (Nat.primeCounting y : ℝ) * lH + 2 * lH := by
    ring
  have hF2 : 2 * Cpi * u * (1 + ll) = 2 * (Cpi * (u * 1)) + 2 * (Cpi * (u * ll)) := by ring
  have hR : (6 * Cpi + 2) * (u * ll) = 6 * (Cpi * (u * ll)) + 2 * (u * ll) := by ring
  have hF1 : 2 * Cpi * u = 2 * (Cpi * (u * 1)) := by ring
  rw [hR]
  rw [hexp] at hE
  rw [hF2] at F2
  rw [hF1] at F1
  linarith

end Erdos287.PostV71V87
