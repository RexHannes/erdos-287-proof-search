import RequestProject.Erdos287.SourceChain.Physical.TypeII.UremFamilyPhysical

/-!
# Erdős #287 — the family Urem estimate from Maynard I, Lemma 13.8

**ERDŐS #287 REMAINS OPEN.  TAIL-287 IS NOT BANKED.**

This file states, as a `Prop` (it is **not** proved here and is **not** an axiom), the published
Barban–Davenport–Halberstam-type estimate

> J. Maynard, *Primes in arithmetic progressions to large moduli I: fixed residue classes*,
> arXiv:2006.06572v2, Definition 1 (the Siegel–Walfisz condition (6.1)) and Lemma 13.8,

transcribed from the arXiv text: `n ∼ N` means `N < n ≤ 2N` (`simN`); the Siegel–Walfisz condition
(6.1) is required for every `d ≥ 1`, `q ≥ 1`, `(a,q) = 1` and every `A > 1`, with right-hand side
`≪_A N τ(d)^{B₀} / (log N)^A`; Lemma 13.8 assumes (6.1) and `|α_n| ≤ τ(n)^{B₀}` and gives, for each
`A > 0`, a `C` such that for `Q < N/(log N)^C`
`∑_{q ≤ Q} τ(q)^{B₀} ∑*_{b (q)} |∑_{n∼N} α_n (1_{n≡b (q)} - 1_{(n,q)=1}/φ(q))|² ≪ N²/(log N)^A`.
We use the *weaker* quantifier order in which `C` may also depend on the Siegel–Walfisz constants
(so the hypothesis is implied by the published statement).  The implied constants are uniform
over all sequences with the given Siegel–Walfisz constants, and the range `N ≥ 2` is covered by
enlarging the constant (for bounded `N` both sides are bounded and the right side is positive).

Proved here, from that statement:

* `swCondition_masked` — the coprimality-SW class is preserved by `α ↦ α 1_{(·,r)=1} / τ(r)^{B₀}`
  (a further mask by `d` is a mask by `d r`, and `τ(dr) ≤ τ(d) τ(r)`);
* `bdhEnergy_masked_le` — `bdhEnergy(α^{(r)}) ≤ (τ(r)^{B₀})² C' N²/(log N)^A` for every `r ≥ 1`,
  whenever `Q ≤ N/(log N)^C` and `K + 1 ≤ B₀`;
* `physical_family_urem_maynard` — the physical family Urem estimate: the packet sum of
  `|physUrem_ξ|` over one group is bounded by the explicit expression with
  `C' τ(r)^{2B₀} N²/(log N)^A` in place of the BDH energy.  Hypotheses on the *actual* sequence:
  the Siegel–Walfisz condition (6.1) and the divisor bound.
-/

open Finset

set_option autoImplicit false

namespace Erdos287.Physical.TypeII.UremFamily

open Erdos287.Physical.TypeII Erdos287.Physical.Sieve Erdos287.Physical.Sieve.ScalarParams
  Erdos287.Physical.Factor

/-- `n ∼ N`, i.e. `N < n ≤ 2N` (Maynard's convention). -/
noncomputable def simN (N : ℝ) : Finset ℕ := (range (⌊2 * N⌋₊ + 1)).filter (fun n => N < n)

/-- **Siegel–Walfisz condition (6.1)** of Maynard I, Definition 1, at scale `N` with divisor
exponent `B₀` and constants `cSW A`. -/
def SWCondition (α : ℕ → ℝ) (N B0 : ℝ) (cSW : ℝ → ℝ) : Prop :=
  ∀ d q a : ℕ, 1 ≤ d → 1 ≤ q → Nat.Coprime a q → ∀ A : ℝ, 1 < A →
    |∑ n ∈ simN N with n ≡ a [MOD q] ∧ Nat.Coprime n d, α n -
      (1 / (Nat.totient q : ℝ)) * ∑ n ∈ simN N with Nat.Coprime n (d * q), α n| ≤
    cSW A * N * tau d ^ B0 / Real.log N ^ A

/-- **Maynard I, Lemma 13.8** (Barban–Davenport–Halberstam type estimate), as a statement.
Published theorem; **not formalized here** and only ever used as an explicit hypothesis. -/
def MaynardLemma13_8 : Prop :=
  ∀ B0 : ℝ, 0 < B0 → ∀ cSW : ℝ → ℝ, ∀ A : ℝ, 0 < A → ∃ C Cimp : ℝ,
    ∀ N : ℝ, 2 ≤ N → ∀ α : ℕ → ℝ, SWCondition α N B0 cSW → (∀ n, |α n| ≤ tau n ^ B0) →
    ∀ Q : ℝ, Q < N / Real.log N ^ C →
      ∑ q ∈ Icc 1 ⌊Q⌋₊, tau q ^ B0 * ∑ b ∈ units q, disc (simN N) α q b ^ 2 ≤
        Cimp * N ^ 2 / Real.log N ^ A

lemma one_le_tau {q : ℕ} (hq : 1 ≤ q) : 1 ≤ tau q := by
  unfold tau
  have : 1 ≤ q.divisors.card := Finset.card_pos.2 ⟨1, Nat.one_mem_divisors.2 (by omega)⟩
  exact_mod_cast this

lemma tau_mul_le (d r : ℕ) : tau (d * r) ≤ tau d * tau r := by
  unfold tau
  rw [Nat.divisors_mul]
  exact_mod_cast Finset.card_mul_le

lemma disc_smul (I : Finset ℕ) (ρ : ℕ → ℝ) (w : ℝ) (q b : ℕ) :
    disc I (fun n => w * ρ n) q b = w * disc I ρ q b := by
  unfold disc; rw [mul_sum]; refine sum_congr rfl (fun n _ => ?_); ring

/-- The coprimality-SW class is preserved by masking with `(n, r) = 1` and normalising by
`τ(r)^{B₀}`. -/
theorem swCondition_masked {α : ℕ → ℝ} {N B0 : ℝ} {cSW : ℝ → ℝ} (hN : 2 ≤ N) (hB0 : 0 < B0)
    (h : SWCondition α N B0 cSW) {r : ℕ} (hr : 1 ≤ r) :
    SWCondition (fun n => maskR α r n / tau r ^ B0) N B0 cSW := by
  intro d q a hd hq haq A' hA'
  have hdr : 1 ≤ d * r := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  have hsw := h (d * r) q a hdr hq haq A' hA'
  set w := tau r ^ B0 with hw
  have hw1 : 1 ≤ w := Real.one_le_rpow (one_le_tau hr) hB0.le
  have hw0 : 0 < w := by linarith
  have e1 : ∑ n ∈ simN N with n ≡ a [MOD q] ∧ Nat.Coprime n d, maskR α r n / w =
      (1 / w) * ∑ n ∈ simN N with n ≡ a [MOD q] ∧ Nat.Coprime n (d * r), α n := by
    simp only [sum_filter]
    rw [mul_sum]
    refine sum_congr rfl (fun n _ => ?_)
    unfold maskR
    simp only [Nat.coprime_mul_iff_right]
    split_ifs <;> first | (exfalso; tauto) | ring
  have e2 : ∑ n ∈ simN N with Nat.Coprime n (d * q), maskR α r n / w =
      (1 / w) * ∑ n ∈ simN N with Nat.Coprime n (d * r * q), α n := by
    simp only [sum_filter]
    rw [mul_sum]
    refine sum_congr rfl (fun n _ => ?_)
    unfold maskR
    simp only [Nat.coprime_mul_iff_right]
    split_ifs <;> first | (exfalso; tauto) | ring
  simp only
  rw [e1, e2]
  set X := ∑ n ∈ simN N with n ≡ a [MOD q] ∧ Nat.Coprime n (d * r), α n -
    (1 / (Nat.totient q : ℝ)) * ∑ n ∈ simN N with Nat.Coprime n (d * r * q), α n with hX
  have hfac : 1 / w * ∑ n ∈ simN N with n ≡ a [MOD q] ∧ Nat.Coprime n (d * r), α n -
      1 / (Nat.totient q : ℝ) * (1 / w * ∑ n ∈ simN N with Nat.Coprime n (d * r * q), α n) =
      1 / w * X := by rw [hX]; ring
  rw [hfac, abs_mul, abs_of_pos (by positivity)]
  have hlog : 0 < Real.log N := Real.log_pos (by linarith)
  set T := cSW A' * N / Real.log N ^ A' with hT
  have hrhs : ∀ e : ℕ, cSW A' * N * tau e ^ B0 / Real.log N ^ A' = T * tau e ^ B0 := by
    intro e; rw [hT]; ring
  rw [hrhs] at hsw ⊢
  have htdr : 0 < tau (d * r) ^ B0 := Real.rpow_pos_of_pos
    (lt_of_lt_of_le zero_lt_one (one_le_tau hdr)) _
  have hT0 : 0 ≤ T := by
    have := (abs_nonneg X).trans hsw
    by_contra hneg
    push_neg at hneg
    have : T * tau (d * r) ^ B0 < 0 := mul_neg_of_neg_of_pos hneg htdr
    linarith
  have hmul : tau (d * r) ^ B0 ≤ tau d ^ B0 * w := by
    rw [hw, ← Real.mul_rpow (by unfold tau; positivity) (by unfold tau; positivity)]
    exact Real.rpow_le_rpow (by unfold tau; positivity) (tau_mul_le d r) hB0.le
  calc 1 / w * |X| ≤ 1 / w * (T * tau (d * r) ^ B0) :=
        mul_le_mul_of_nonneg_left hsw (by positivity)
    _ ≤ 1 / w * (T * (tau d ^ B0 * w)) := by gcongr
    _ = T * tau d ^ B0 := by field_simp

/-- **BDH energy of the masked sequences, from Maynard I, Lemma 13.8.** -/
theorem bdhEnergy_masked_le (hM : MaynardLemma13_8) {B0 : ℝ} (hB0 : 0 < B0) (cSW : ℝ → ℝ)
    {A : ℝ} (hA : 0 < A) :
    ∃ C Cimp : ℝ, ∀ N : ℝ, 2 ≤ N → ∀ α : ℕ → ℝ, SWCondition α N B0 cSW →
      (∀ n, |α n| ≤ tau n ^ B0) → ∀ r Qn K : ℕ, 1 ≤ r → (K : ℝ) + 1 ≤ B0 →
      (Qn : ℝ) ≤ N / Real.log N ^ C →
      bdhEnergy (simN N) (maskR α r) Qn K ≤ (tau r ^ B0) ^ 2 * (Cimp * N ^ 2 / Real.log N ^ A) := by
  obtain ⟨C, Cimp, hC⟩ := hM B0 hB0 cSW A hA
  refine ⟨C, Cimp, fun N hN α hsw hdiv r Qn K hr hK hQ => ?_⟩
  set w := tau r ^ B0 with hw
  have hw1 : 1 ≤ w := Real.one_le_rpow (one_le_tau hr) hB0.le
  have hw0 : 0 < w := by linarith
  set ρ : ℕ → ℝ := fun n => maskR α r n / w with hρ
  have hswρ : SWCondition ρ N B0 cSW := swCondition_masked hN hB0 hsw hr
  have hdivρ : ∀ n, |ρ n| ≤ tau n ^ B0 := by
    intro n
    simp only [hρ, maskR, abs_div, abs_of_pos hw0]
    rw [div_le_iff₀ hw0]
    have h1 : |α n * (if Nat.Coprime n r then (1 : ℝ) else 0)| ≤ |α n| := by
      split_ifs <;> simp
    have h2 : 0 ≤ tau n ^ B0 := by unfold tau; positivity
    nlinarith [hdiv n]
  have hmay := hC N hN ρ hswρ hdivρ ((Qn : ℝ) - 1) (by linarith)
  have hmask : ∀ q b, disc (simN N) (maskR α r) q b = w * disc (simN N) ρ q b := by
    intro q b
    rw [← disc_smul]
    congr 1
    funext n
    simp only [hρ]
    field_simp
  unfold bdhEnergy
  simp_rw [hmask, mul_pow]
  set D : ℕ → ℝ := fun q => ∑ b ∈ units q, disc (simN N) ρ q b ^ 2 with hD
  have hD0 : ∀ q, 0 ≤ D q := fun q => sum_nonneg (fun _ _ => sq_nonneg _)
  have e : ∀ q, ∑ b ∈ units q, w ^ 2 * disc (simN N) ρ q b ^ 2 = w ^ 2 * D q := by
    intro q; rw [hD, mul_sum]
  simp_rw [e]
  have key : ∑ q ∈ range Qn, tau q ^ (K + 1) * D q ≤
      ∑ q ∈ Icc 1 ⌊(Qn : ℝ) - 1⌋₊, tau q ^ B0 * D q := by
    have h1 : ∀ q ∈ range Qn, tau q ^ (K + 1) * D q ≤
        if 1 ≤ q then tau q ^ B0 * D q else 0 := by
      intro q _
      split_ifs with hq
      · refine mul_le_mul_of_nonneg_right ?_ (hD0 q)
        rw [← Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_le (one_le_tau hq) (by push_cast; linarith)
      · have : q = 0 := by omega
        subst this
        simp [hD, units]
    refine (sum_le_sum h1).trans ?_
    rw [← sum_filter]
    apply sum_le_sum_of_subset_of_nonneg
    · intro q hq
      rw [mem_filter, mem_range] at hq
      rw [mem_Icc]
      refine ⟨hq.2, Nat.le_floor ?_⟩
      have : (q : ℝ) + 1 ≤ Qn := by exact_mod_cast hq.1
      linarith
    · intro q _ _
      exact mul_nonneg (by unfold tau; positivity) (hD0 q)
  calc ∑ q ∈ range Qn, tau q ^ (K + 1) * (w ^ 2 * D q)
      = w ^ 2 * ∑ q ∈ range Qn, tau q ^ (K + 1) * D q := by
        rw [mul_sum]; refine sum_congr rfl (fun q _ => ?_); ring
    _ ≤ w ^ 2 * (Cimp * N ^ 2 / Real.log N ^ A) :=
        mul_le_mul_of_nonneg_left (key.trans hmay) (by positivity)

/-- `Ico Nn (2 Nn)` is Maynard's `n ∼ N` at `N = Nn - 1/2`. -/
lemma simN_half {Nn : ℕ} (hNn : 1 ≤ Nn) : simN ((Nn : ℝ) - 1 / 2) = Ico Nn (2 * Nn) := by
  have hfl : ⌊2 * ((Nn : ℝ) - 1 / 2)⌋₊ = 2 * Nn - 1 := by
    rw [show 2 * ((Nn : ℝ) - 1 / 2) = ((2 * Nn - 1 : ℕ) : ℝ) by
      rw [Nat.cast_sub (by omega)]; push_cast; ring]
    exact Nat.floor_natCast _
  ext n
  simp only [simN, mem_filter, mem_range, mem_Ico, hfl]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, by omega⟩
    by_contra h
    push_neg at h
    have : (n : ℝ) + 1 ≤ Nn := by exact_mod_cast h
    linarith
  · rintro ⟨h1, h2⟩
    refine ⟨by omega, ?_⟩
    have : (Nn : ℝ) ≤ n := by exact_mod_cast h1
    linarith

/-- **The physical family Urem estimate from Maynard I, Lemma 13.8.**  For one HB/dyadic group
(common `α` supported on `[N_n, 2N_n)`), assuming the Siegel–Walfisz condition (6.1) and the
divisor bound for the *actual* `α` at `N' = N_n - 1/2`, the packet sum of `|physUrem_ξ|` is
bounded by the explicit expression in which each BDH energy is replaced by
`(τ(r)^{B₀})² C' N'²/(log N')^A`.  The cutoff exponent `C` and the constant `C'` depend only on
`B₀`, the SW constants and `A`.  No Urem provider is assumed. -/
theorem physical_family_urem_maynard (hM : MaynardLemma13_8) {B0 : ℝ} (hB0 : 0 < B0)
    (cSW : ℝ → ℝ) {Aexp : ℝ} (hAexp : 0 < Aexp) :
    ∃ C Cimp : ℝ, ∀ {ι : Type} (Ξ : Finset ι) (S : ScalarParams), S.Good →
    ∀ (δ N : ℝ) (Γ : ι → ℝ) (f c A : ι → ℕ) (B : ι → ℤ) (K n n0 Nn M K' F Kexp : ℕ),
    K ≤ 2 ^ n → ∀ (α : ArithmeticFunction ℝ) (β : ι → ArithmeticFunction ℝ),
    (∀ m, α m ≠ 0 → Nn ≤ m ∧ m < 2 * Nn) →
    (∀ ξ ∈ Ξ, ∀ m, β ξ m ≠ 0 → M ≤ m ∧ m < 2 * M) → 4 * Nn * M ≤ K' →
    (∀ ξ ∈ Ξ, 0 < f ξ ∧ f ξ ≤ F) → (∀ ξ ∈ Ξ, Nat.Coprime (c ξ) (f ξ)) →
    (∀ ξ ∈ Ξ, AffinePrimesDivideBase (A ξ) (B ξ) (f ξ)) → ∀ (Bβ Ca : ℝ), 0 ≤ Ca →
    (∀ ξ ∈ Ξ, ∑ m ∈ Ico M (2 * M), β ξ m ^ 2 ≤ Bβ) →
    (∀ f0, ∑ ξ ∈ Ξ with f ξ = f0, |Γ ξ| ≤ Ca * tau f0 ^ Kexp) →
    (∀ ξ ∈ Ξ, ∀ J (P : Fin J → Fin S.H) (χ : Fin S.Kc → Fin 3) l r,
      physCoefCut S δ N (Γ ξ) (f ξ) K J P χ l r ≠ 0 → l < 2 ^ n0) →
    2 ≤ (Nn : ℝ) - 1 / 2 → SWCondition α ((Nn : ℝ) - 1 / 2) B0 cSW →
    (∀ m, |α m| ≤ tau m ^ B0) → (Kexp : ℝ) + 1 ≤ B0 →
    ((2 * F * 2 ^ n0 : ℕ) : ℝ) ≤ ((Nn : ℝ) - 1 / 2) / Real.log ((Nn : ℝ) - 1 / 2) ^ C →
    ∑ ξ ∈ Ξ, |physUrem S δ N (Γ ξ) (f ξ) (c ξ) (A ξ) (B ξ) K K' α (β ξ)| ≤
      ∑ J ∈ range (S.T ^ 2 + 1), ∑ P : Fin J → Fin S.H, ∑ _χ : Fin S.Kc → Fin 3,
        ∑ r ∈ Ico 1 K, (1 / (Nat.totient r : ℝ)) * ∑ i ∈ range n0,
          S.atomWeight J P (S.atomColour δ N J P) * Real.sqrt Bβ *
            Real.sqrt (∑ ξ ∈ Ξ, |Γ ξ| * ((M : ℝ) / f ξ + (2 ^ i : ℕ))) *
            Real.sqrt (Ca * ((tau r ^ B0) ^ 2 * (Cimp * ((Nn : ℝ) - 1 / 2) ^ 2 /
              Real.log ((Nn : ℝ) - 1 / 2) ^ Aexp))) := by
  obtain ⟨C, Cimp, hC⟩ := bdhEnergy_masked_le hM hB0 cSW hAexp
  refine ⟨C, Cimp, ?_⟩
  intro ι Ξ S hS δ N Γ f c A B K n n0 Nn M K' F Kexp hKn α β hα hβ hK' hf hcf hAPB Bβ Ca hCa
    hβ2 hmult hl0 hN hsw hdiv hK hcut
  have hNn : 1 ≤ Nn := by
    by_contra h; push_neg at h
    have : (Nn : ℝ) < 1 := by exact_mod_cast h
    linarith
  refine (physical_family_urem_le Ξ hS δ N Γ f c A B hKn α β hα hβ hK' hf hcf hAPB hCa hβ2
    hmult hl0).trans ?_
  gcongr with J _ P _ χ _ r hr i hi
  · have := atomWeight_nonneg P (S.atomColour δ N J P)
    positivity
  · rw [← simN_half hNn]
    refine hC _ hN α hsw hdiv r _ Kexp (mem_Ico.1 hr).1 hK (le_trans ?_ hcut)
    have : 2 * F * 2 ^ i ≤ 2 * F * 2 ^ n0 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (mem_range.1 hi).le)
    exact_mod_cast this

end Erdos287.Physical.TypeII.UremFamily
