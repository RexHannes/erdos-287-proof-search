import RequestProject.Erdos287.SourceChain.TypeIISplit
import RequestProject.Erdos287.SourceChain.PoissonRemainder

/-!
# Erdős #287 — V100R/V100R2 source chain: literal nonzero terms and the `F_{AB}` payment

**ERDŐS #287 REMAINS OPEN.  TAIL-287 IS NOT BANKED.**  Source level: `MESSAGE_LEVEL_SOURCE`
(source pack §8 (OB.6)–(OB.10), §9 (Opus repair 1: `k = 1`, `k > 1`, (AB.1), (AB.2))).

* `PF Ψ̂ M q ρ = (M/q) ∑_{h≠0} Ψ̂(hM/q) e(hρ/q)` — the literal (OB.6) Fourier-side
  remainder `𝒫_M(q,ρ)`.
* `PF_scale` — `𝒫_M(kq, kρ̃) = 𝒫_{M/k}(q, ρ̃)` (exact, every `Ψ̂`, `tsum` convention).
* `FABData`, `FABData.FAB` — the literal actual–model term (OB.7), with the actual
  coefficient `C₁₂`, the Möbius sum over `k ∣ r₂`, `(k, r₁) = 1`, and the CRT residues `ρ_k`.
* `FAB_eq_sum_PF` — (OB.7) is exactly `∑ C₁₂/φ(r₂) ∑_k μ(k) 𝒫_M(flr₁k, ρ_k)`.
* `FAB_split` — `F_AB = F_AB^{k=1} + F_AB^{k>1}`.
* `PF_rho_scale` — with `ρ_k ≡ 0 (mod k)` (OB.8): `𝒫_M(flr₁k, ρ_k) = 𝒫_{M/k}(flr₁, ρ̃_k)`.
* `PF_decay_bound` — rapid decay of `Ψ̂` gives `|𝒫_M(q,ρ)| ≤ C_A Z_A (M/q)^{1-A}`.
* `k1_modulus_exponent` — `lr₁ ≤ x^{59/100}`, `M ≥ x^{5/8}`, `f ≤ x^{σ_f}` give
  `flr₁/M ≤ x^{σ_f - 7/200}`; `fiftyNine_minus_fiveEighths` : `59/100 - 5/8 = -7/200`.
* `FAB_kgt1_bound` — the scale-free bound `|𝒫_T(q,a)| ≤ V` gives
  `|F_AB^{k>1}| ≤ V ∑ |C₁₂| τ(r₂)/φ(r₂)`.
* `FAB_kgt1_count` — with `|C₁₂| ≤ 1` supported on `n₁ ≡ n₂ (mod fl)` and `|𝒩| ≤ N`:
  `|F_AB^{k>1}| ≤ V |ℛ₁| (∑_{r₂} τ(r₂)/φ(r₂)) N ∑_l (N/(fl) + 1)` — the (AB.1) shape
  `(log x)^C (RN²/f + LRN)`.
* `AB2_cauchy` — with `𝓑 = ML` and `x = MN`:
  `√(𝓑 (RN²/f + LRN)) ≤ (x/f)(√(fLR/M) + fL√(R/x))` — (AB.2).
-/

open scoped BigOperators
open Finset ArithmeticFunction

namespace Erdos287.SourceChain

/-! ### The literal Fourier-side remainder (OB.6) -/

/-- `e(x) = exp(2πix)` on reals. -/
noncomputable def eR (x : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * (x : ℂ))

theorem norm_eR (x : ℝ) : ‖eR x‖ = 1 := by
  unfold eR; rw [Complex.norm_exp]; simp

/-- (OB.6) `𝒫_M(q,ρ) = (M/q) ∑_{h ≠ 0} Ψ̂(hM/q) e(hρ/q)`. -/
noncomputable def PF (Ψhat : ℝ → ℂ) (M q : ℝ) (ρ : ℤ) : ℂ :=
  ((M / q : ℝ) : ℂ) * ∑' h : ℤ, if h = 0 then 0 else Ψhat (h * M / q) * eR (h * ρ / q)

/-- **Möbius scaling of (OB.6).**  `𝒫_M(kq, kρ̃) = 𝒫_{M/k}(q, ρ̃)` for `k ≠ 0`. -/
theorem PF_scale (Ψhat : ℝ → ℂ) (M q : ℝ) {k : ℤ} (hk : k ≠ 0) (ρt : ℤ) :
    PF Ψhat M (k * q) (k * ρt) = PF Ψhat (M / k) q ρt := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  unfold PF
  by_cases hq : q = 0
  · subst hq; simp
  congr 1
  · congr 1; field_simp
  · refine tsum_congr (fun h => ?_)
    split_ifs
    · rfl
    · congr 2
      · field_simp
      · push_cast; field_simp

/-- **Rapid decay ⟹ arbitrary power saving in the `k = 1` modulus.** -/
theorem PF_decay_bound (Ψhat : ℝ → ℂ) {A C M q : ℝ} (hA : 1 < A) (hM : 0 < M) (hq : 0 < q)
    (hdec : ∀ ξ : ℝ, ξ ≠ 0 → ‖Ψhat ξ‖ ≤ C * |ξ| ^ (-A)) (ρ : ℤ) :
    ‖PF Ψhat M q ρ‖ ≤ (M / q) * (C * (M / q) ^ (-A) * ∑' h : ℤ, |(h : ℝ)| ^ (-A)) := by
  have hs := Real.summable_abs_int_rpow hA
  unfold PF
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  gcongr
  have hbound : ∀ h : ℤ, ‖(if h = 0 then 0 else Ψhat (h * M / q) * eR (h * ρ / q))‖ ≤
      C * (M / q) ^ (-A) * |(h : ℝ)| ^ (-A) := by
    intro h
    split_ifs with h0
    · subst h0
      simp [Real.zero_rpow (by linarith : -A ≠ 0)]
    · rw [norm_mul, norm_eR, mul_one]
      have hh : (h : ℝ) ≠ 0 := by exact_mod_cast h0
      refine (hdec _ (by positivity)).trans (le_of_eq ?_)
      rw [show (h : ℝ) * M / q = h * (M / q) by ring, abs_mul,
        abs_of_pos (by positivity : (0:ℝ) < M / q),
        Real.mul_rpow (abs_nonneg _) (by positivity)]
      ring
  have hsum : HasSum (fun h : ℤ => C * (M / q) ^ (-A) * |(h : ℝ)| ^ (-A))
      (C * (M / q) ^ (-A) * ∑' h : ℤ, |(h : ℝ)| ^ (-A)) := hs.hasSum.mul_left _
  exact tsum_of_norm_bounded hsum hbound

/-! ### Exponent arithmetic of the `k = 1` modulus (Opus repair 1) -/

theorem fiftyNine_minus_fiveEighths : (59 / 100 : ℚ) - 5 / 8 = -(7 / 200) := by norm_num

/-- `f ≤ x^{σ_f}`, `l r₁ ≤ x^{59/100}`, `M ≥ x^{5/8}` ⟹ `f l r₁ / M ≤ x^{σ_f - 7/200}`. -/
theorem k1_modulus_exponent {x f lr1 M σf : ℝ} (hx : 1 < x)
    (hf : f ≤ x ^ σf) (hlr0 : 0 ≤ lr1) (hlr : lr1 ≤ x ^ ((59 : ℝ) / 100))
    (hM : x ^ ((5 : ℝ) / 8) ≤ M) :
    f * lr1 / M ≤ x ^ (σf - 7 / 200) := by
  have hx0 : 0 < x := by linarith
  have hMpos : 0 < M := lt_of_lt_of_le (Real.rpow_pos_of_pos hx0 _) hM
  rw [div_le_iff₀ hMpos]
  calc f * lr1 ≤ x ^ σf * x ^ ((59 : ℝ) / 100) := mul_le_mul hf hlr hlr0 (by positivity)
    _ = x ^ (σf - 7 / 200) * x ^ ((5 : ℝ) / 8) := by
        rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]; congr 1; ring
    _ ≤ x ^ (σf - 7 / 200) * M := mul_le_mul_of_nonneg_left hM (by positivity)

/-- Once `σ_f < 7/200` the `k = 1` modulus is a fixed negative power of `x`. -/
theorem k1_power_saving {σf : ℝ} (h : σf < 7 / 200) : σf - 7 / 200 < 0 := by linarith

/-! ### The literal actual–model term (OB.7) -/

/-- Data of the actual–model term (OB.7).  Indices `l ∈ 𝓛`, `r₁ ∈ ℛ₁`, `r₂ ∈ ℛ₂`,
`n₁, n₂ ∈ 𝒩`; actual coefficient `C₁₂`; CRT residues `ρ_k` (OB.8). -/
structure FABData where
  M : ℝ
  f : ℕ
  Ψhat : ℝ → ℂ
  Ls : Finset ℕ
  R1 : Finset ℕ
  R2 : Finset ℕ
  Ns : Finset ℕ
  C12 : ℕ → ℕ → ℕ → ℕ → ℕ → ℂ
  rho : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℤ

namespace FABData

variable (D : FABData)

/-- The Möbius range `k ∣ r₂`, `(k, r₁) = 1`. -/
def kset (r1 r2 : ℕ) : Finset ℕ := r2.divisors.filter (fun k => Nat.Coprime k r1)

/-- The `h`-sum of (OB.7) at modulus `q`. -/
noncomputable def hsum (q : ℝ) (ρ : ℤ) : ℂ :=
  ∑' h : ℤ, if h = 0 then 0 else D.Ψhat (h * D.M / q) * eR (h * ρ / q)

/-- The modulus `f l r₁ k`. -/
def modulus (l r1 k : ℕ) : ℕ := D.f * l * r1 * k

/-- **(OB.7) literally.** -/
noncomputable def FAB : ℂ :=
  (D.M : ℂ) * ∑ l ∈ D.Ls, ∑ r1 ∈ D.R1, ∑ r2 ∈ D.R2, ∑ n1 ∈ D.Ns, ∑ n2 ∈ D.Ns,
    D.C12 l r1 r2 n1 n2 / (Nat.totient r2 : ℂ) *
      ∑ k ∈ kset r1 r2, ((moebius k : ℤ) : ℂ) / (D.modulus l r1 k : ℂ) *
        D.hsum (D.modulus l r1 k) (D.rho l r1 r2 n1 n2 k)

/-- The Möbius-restricted part of `F_AB` over `k ∈ kset` with `P k`. -/
noncomputable def FABpart (P : ℕ → Prop) [DecidablePred P] : ℂ :=
  ∑ l ∈ D.Ls, ∑ r1 ∈ D.R1, ∑ r2 ∈ D.R2, ∑ n1 ∈ D.Ns, ∑ n2 ∈ D.Ns,
    D.C12 l r1 r2 n1 n2 / (Nat.totient r2 : ℂ) *
      ∑ k ∈ (kset r1 r2).filter P, ((moebius k : ℤ) : ℂ) *
        PF D.Ψhat D.M (D.modulus l r1 k) (D.rho l r1 r2 n1 n2 k)

/-- **(OB.7) = ∑ C₁₂/φ(r₂) ∑_k μ(k) 𝒫_M(flr₁k, ρ_k).** -/
theorem FAB_eq_sum_PF : D.FAB = D.FABpart (fun _ => True) := by
  unfold FAB FABpart
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun l _ => ?_); rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun r1 _ => ?_); rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun r2 _ => ?_); rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun n1 _ => ?_); rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun n2 _ => ?_)
  rw [Finset.filter_true, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  unfold PF hsum
  push_cast
  ring

/-- **`F_AB = F_AB^{k=1} + F_AB^{k>1}`.** -/
theorem FAB_split : D.FAB = D.FABpart (fun k => k = 1) + D.FABpart (fun k => k ≠ 1) := by
  rw [FAB_eq_sum_PF]
  unfold FABpart
  simp only [← Finset.sum_add_distrib, ← mul_add]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  refine Finset.sum_congr rfl (fun r1 _ => ?_)
  refine Finset.sum_congr rfl (fun r2 _ => ?_)
  refine Finset.sum_congr rfl (fun n1 _ => ?_)
  refine Finset.sum_congr rfl (fun n2 _ => ?_)
  rw [Finset.filter_true, Finset.sum_filter_add_sum_filter_not]

/-- **(OB.8) scaling**: if `k ∣ ρ_k` then `𝒫_M(flr₁k, ρ_k) = 𝒫_{M/k}(flr₁, ρ̃_k)`. -/
theorem PF_rho_scale {l r1 k : ℕ} (hk : 0 < k) {ρ : ℤ} (hρ : (k : ℤ) ∣ ρ) :
    ∃ ρt : ℤ, ρ = k * ρt ∧
      PF D.Ψhat D.M (D.modulus l r1 k) ρ = PF D.Ψhat (D.M / k) (D.f * l * r1) ρt := by
  obtain ⟨ρt, rfl⟩ := hρ
  refine ⟨ρt, rfl, ?_⟩
  have := PF_scale D.Ψhat D.M ((D.f * l * r1 : ℕ) : ℝ) (k := (k : ℤ)) (by exact_mod_cast hk.ne')
    ρt
  unfold modulus
  push_cast at this ⊢
  rw [show ((D.f : ℝ) * l * r1 * k) = (k : ℝ) * (D.f * l * r1) by ring]
  exact this

/-- `|kset r₁ r₂| ≤ τ(r₂)`. -/
theorem card_kset_le (r1 r2 : ℕ) : (kset r1 r2).card ≤ (r2.divisors).card :=
  Finset.card_filter_le _ _

/-- **`k > 1` payment from the scale-free bound `|𝒫_T(q,a)| ≤ V`.** -/
theorem FAB_kgt1_bound {V : ℝ} (hV : ∀ (T q : ℝ) (a : ℤ), ‖PF D.Ψhat T q a‖ ≤ V) :
    ‖D.FABpart (fun k => k ≠ 1)‖ ≤
      V * ∑ l ∈ D.Ls, ∑ r1 ∈ D.R1, ∑ r2 ∈ D.R2, ∑ n1 ∈ D.Ns, ∑ n2 ∈ D.Ns,
        ‖D.C12 l r1 r2 n1 n2‖ * ((r2.divisors.card : ℝ) / Nat.totient r2) := by
  have hV0 : 0 ≤ V := le_trans (norm_nonneg _) (hV 0 0 0)
  have inner : ∀ l r1 r2 n1 n2, ‖D.C12 l r1 r2 n1 n2 / (Nat.totient r2 : ℂ) *
      ∑ k ∈ (kset r1 r2).filter (fun k => k ≠ 1), ((moebius k : ℤ) : ℂ) *
        PF D.Ψhat D.M (D.modulus l r1 k) (D.rho l r1 r2 n1 n2 k)‖ ≤
      V * (‖D.C12 l r1 r2 n1 n2‖ * ((r2.divisors.card : ℝ) / Nat.totient r2)) := by
    intro l r1 r2 n1 n2
    rw [norm_mul, norm_div]
    have hk : ‖∑ k ∈ (kset r1 r2).filter (fun k => k ≠ 1), ((moebius k : ℤ) : ℂ) *
        PF D.Ψhat D.M (D.modulus l r1 k) (D.rho l r1 r2 n1 n2 k)‖ ≤
        V * (r2.divisors.card : ℝ) := by
      refine (norm_sum_le _ _).trans ?_
      calc _ ≤ ∑ k ∈ (kset r1 r2).filter (fun k => k ≠ 1), V := by
            refine Finset.sum_le_sum (fun k _ => ?_)
            rw [norm_mul]
            have hmu : ‖((moebius k : ℤ) : ℂ)‖ ≤ 1 := by
              rw [Complex.norm_intCast]; exact_mod_cast abs_moebius_le_one
            calc _ ≤ 1 * V := mul_le_mul hmu (hV _ _ _) (norm_nonneg _) zero_le_one
              _ = V := one_mul V
        _ = V * ((kset r1 r2).filter (fun k => k ≠ 1)).card := by
            rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
        _ ≤ V * (r2.divisors.card : ℝ) := mul_le_mul_of_nonneg_left (by
            exact_mod_cast (Finset.card_filter_le _ _).trans (card_kset_le r1 r2)) hV0
    rw [Complex.norm_natCast]
    calc ‖D.C12 l r1 r2 n1 n2‖ / (Nat.totient r2 : ℝ) * ‖_‖ ≤
        ‖D.C12 l r1 r2 n1 n2‖ / (Nat.totient r2 : ℝ) * (V * (r2.divisors.card : ℝ)) := by
          gcongr
      _ = V * (‖D.C12 l r1 r2 n1 n2‖ * ((r2.divisors.card : ℝ) / Nat.totient r2)) := by ring
  calc ‖D.FABpart (fun k => k ≠ 1)‖ ≤
      ∑ l ∈ D.Ls, ∑ r1 ∈ D.R1, ∑ r2 ∈ D.R2, ∑ n1 ∈ D.Ns, ∑ n2 ∈ D.Ns,
        V * (‖D.C12 l r1 r2 n1 n2‖ * ((r2.divisors.card : ℝ) / Nat.totient r2)) := by
        unfold FABpart
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun l _ => ?_))
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun r1 _ => ?_))
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun r2 _ => ?_))
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun n1 _ => ?_))
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun n2 _ => ?_))
        exact inner l r1 r2 n1 n2
    _ = _ := by simp only [Finset.mul_sum]

/-- Pair count along `n₁ ≡ n₂ (mod q)`: `∑_{n₂ ∈ 𝒩} |C(n₂)| ≤ N/q + 1` when `|C| ≤ 1` is
supported on `n₂ ≡ n₁ (q)` and `𝒩` lies in an interval of length `N`. -/
theorem congr_row_sum_le {q : ℕ} {N0 N : ℕ} (Ns : Finset ℕ)
    (hN : Ns ⊆ Finset.Ico N0 (N0 + N)) (n1 : ℕ) (C : ℕ → ℝ)
    (hC1 : ∀ n, C n ≤ 1) (hsupp : ∀ n, ¬ n ≡ n1 [MOD q] → C n = 0) :
    ∑ n2 ∈ Ns, C n2 ≤ (N : ℝ) / q + 1 := by
  calc ∑ n2 ∈ Ns, C n2 = ∑ n2 ∈ Ns.filter (fun n => n ≡ n1 [MOD q]), C n2 := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl (fun n _ => ?_)
        split_ifs with h
        · rfl
        · exact hsupp n h
    _ ≤ ∑ n2 ∈ Ns.filter (fun n => n ≡ n1 [MOD q]), (1 : ℝ) := Finset.sum_le_sum (fun n _ => hC1 n)
    _ = ((Ns.filter (fun n => n ≡ n1 [MOD q])).card : ℝ) := by simp
    _ ≤ (((N / q : ℕ) + 1 : ℕ) : ℝ) := by
        refine Nat.cast_le.2 (card_fibre_le N0 N _ ((Finset.filter_subset _ _).trans hN) ?_)
        intro x hx y hy
        exact Nat.ModEq.trans (Finset.mem_filter.1 hx).2 (Finset.mem_filter.1 hy).2.symm
    _ ≤ (N : ℝ) / q + 1 := by
        push_cast
        have : ((N / q : ℕ) : ℝ) ≤ (N : ℝ) / q := Nat.cast_div_le
        linarith

/-- **(AB.1) shape.**  With `|C₁₂| ≤ 1` supported on `n₁ ≡ n₂ (mod fl)`, `𝒩` inside an
interval of length `N` with `|𝒩| ≤ N`, and the scale-free bound `|𝒫| ≤ V`:
`|F_AB^{k>1}| ≤ V |ℛ₁| (∑_{r₂∈ℛ₂} τ(r₂)/φ(r₂)) N ∑_{l∈𝓛} (N/(fl) + 1)`. -/
theorem FAB_kgt1_count {V : ℝ} (hV : ∀ (T q : ℝ) (a : ℤ), ‖PF D.Ψhat T q a‖ ≤ V)
    {N0 N : ℕ}
    (hN : D.Ns ⊆ Finset.Ico N0 (N0 + N)) (hNcard : D.Ns.card ≤ N)
    (hC1 : ∀ l r1 r2 n1 n2, ‖D.C12 l r1 r2 n1 n2‖ ≤ 1)
    (hsupp : ∀ l r1 r2 n1 n2, ¬ n2 ≡ n1 [MOD D.f * l] → D.C12 l r1 r2 n1 n2 = 0) :
    ‖D.FABpart (fun k => k ≠ 1)‖ ≤
      V * ((D.R1.card : ℝ) * (∑ r2 ∈ D.R2, (r2.divisors.card : ℝ) / Nat.totient r2) *
        (N * ∑ l ∈ D.Ls, ((N : ℝ) / (D.f * l) + 1))) := by
  have hV0 : 0 ≤ V := le_trans (norm_nonneg _) (hV 0 0 0)
  refine (D.FAB_kgt1_bound hV).trans (mul_le_mul_of_nonneg_left ?_ hV0)
  have hw : ∀ r2 : ℕ, 0 ≤ (r2.divisors.card : ℝ) / Nat.totient r2 := fun _ => by positivity
  calc ∑ l ∈ D.Ls, ∑ r1 ∈ D.R1, ∑ r2 ∈ D.R2, ∑ n1 ∈ D.Ns, ∑ n2 ∈ D.Ns,
        ‖D.C12 l r1 r2 n1 n2‖ * ((r2.divisors.card : ℝ) / Nat.totient r2)
      ≤ ∑ l ∈ D.Ls, ∑ r1 ∈ D.R1, ∑ r2 ∈ D.R2, ∑ n1 ∈ D.Ns,
          ((r2.divisors.card : ℝ) / Nat.totient r2) * ((N : ℝ) / (D.f * l) + 1) := by
        refine Finset.sum_le_sum (fun l hl => Finset.sum_le_sum (fun r1 _ =>
          Finset.sum_le_sum (fun r2 _ => Finset.sum_le_sum (fun n1 _ => ?_))))
        rw [← Finset.sum_mul, mul_comm]
        refine mul_le_mul_of_nonneg_left ?_ (hw r2)
        have := congr_row_sum_le (q := D.f * l) D.Ns hN n1
          (fun n2 => ‖D.C12 l r1 r2 n1 n2‖) (fun n => hC1 _ _ _ _ _)
          (fun n hn => by
            show ‖D.C12 l r1 r2 n1 n‖ = 0
            rw [hsupp l r1 r2 n1 n hn, norm_zero])
        push_cast at this
        exact this
    _ = ∑ l ∈ D.Ls, (D.R1.card : ℝ) * (∑ r2 ∈ D.R2, (r2.divisors.card : ℝ) / Nat.totient r2) *
          (D.Ns.card * ((N : ℝ) / (D.f * l) + 1)) := by
        refine Finset.sum_congr rfl (fun l _ => ?_)
        rw [Finset.sum_const, nsmul_eq_mul]
        simp only [Finset.sum_const, nsmul_eq_mul]
        simp only [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl (fun r2 _ => by ring)
    _ ≤ ∑ l ∈ D.Ls, (D.R1.card : ℝ) * (∑ r2 ∈ D.R2, (r2.divisors.card : ℝ) / Nat.totient r2) *
          (N * ((N : ℝ) / (D.f * l) + 1)) := by
        refine Finset.sum_le_sum (fun l _ => ?_)
        have hS : 0 ≤ ∑ r2 ∈ D.R2, (r2.divisors.card : ℝ) / Nat.totient r2 :=
          Finset.sum_nonneg (fun r2 _ => hw r2)
        gcongr
    _ = _ := by rw [← Finset.mul_sum, ← Finset.mul_sum]

end FABData

/-! ### (AB.2): the Cauchy factor -/

theorem sqrt_add_le_sqrt_add_sqrt {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  have h1 := Real.sq_sqrt ha
  have h2 := Real.sq_sqrt hb
  nlinarith [Real.sqrt_nonneg a, Real.sqrt_nonneg b,
    mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)]

/-- **(AB.2) algebra.**  With `𝓑 = ML` and `x = MN` (all positive):
`√(𝓑 (RN²/f + LRN)) ≤ (x/f)(√(fLR/M) + fL√(R/x))`. -/
theorem AB2_cauchy {M N L R f : ℝ} (hM : 0 < M) (hN : 0 < N) (hL : 0 < L) (hR : 0 < R)
    (hf : 0 < f) :
    Real.sqrt (M * L * (R * N ^ 2 / f + L * R * N)) ≤
      (M * N / f) * (Real.sqrt (f * L * R / M) + f * L * Real.sqrt (R / (M * N))) := by
  have e1 : M * L * (R * N ^ 2 / f) = (M * N / f) ^ 2 * (f * L * R / M) := by
    field_simp
  have e2 : M * L * (L * R * N) = (M * N / f) ^ 2 * ((f * L) ^ 2 * (R / (M * N))) := by
    field_simp
  rw [mul_add, e1, e2]
  have hx : 0 ≤ M * N / f := by positivity
  calc Real.sqrt ((M * N / f) ^ 2 * (f * L * R / M) +
        (M * N / f) ^ 2 * ((f * L) ^ 2 * (R / (M * N))))
      ≤ Real.sqrt ((M * N / f) ^ 2 * (f * L * R / M)) +
          Real.sqrt ((M * N / f) ^ 2 * ((f * L) ^ 2 * (R / (M * N)))) :=
        sqrt_add_le_sqrt_add_sqrt (by positivity) (by positivity)
    _ = _ := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hx,
          Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
        ring

end Erdos287.SourceChain
