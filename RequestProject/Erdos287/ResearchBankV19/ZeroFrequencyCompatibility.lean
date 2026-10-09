import RequestProject.Erdos287.ResearchBankV18.ColourConductor

/-!
# Erdős #287 — Research Bank V19 §1: zero-frequency compatibility

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

Two simultaneous congruences `n₁ m ≡ a₁ (mod q₁)`, `n₂ m ≡ a₂ (mod q₂)`; `g = gcd(q₁, q₂)`,
`L = lcm(q₁, q₂)`.

Kernel-proved (LEAN BANK):
* `compat_necessary` — any common solution forces `a₁ n₂ ≡ a₂ n₁ (mod g)` (no unit hypothesis);
* `kappa` — the compatibility indicator;
* `crt_exists` — (units `n₁` mod `q₁`, `n₂` mod `q₂`) compatibility gives a common solution;
* `crt_unique` — two common solutions agree modulo `L`;
* **`zero_frequency_count`** — the exact CRT part of the zero-frequency statement: under the unit
  hypotheses, the number of `m ∈ [0, L)` solving both congruences is exactly `κ ∈ {0, 1}`.

REPAIRED / RETIRED: `omega_zero_does_not_fix_main_term` — the implication
"`Ω(0) = 1` ⟹ zero-frequency main term unchanged" is FALSE: at `q₁ = q₂ = 3`, `n₁ = n₂ = 1`,
`a₁ = 1`, `a₂ = 2` the phase at frequency `0` is `1` but the count is `0 ≠ 1`.
-/

namespace Erdos287
namespace ResearchBankV19
namespace ZeroFrequencyCompatibility

open ResearchBankV18.ColourConductor

/-- The compatibility condition `a₁ n₂ ≡ a₂ n₁ (mod gcd(q₁, q₂))`. -/
def Compatible (q₁ q₂ : ℕ) (n₁ n₂ a₁ a₂ : ℤ) : Prop :=
  a₁ * n₂ ≡ a₂ * n₁ [ZMOD (Nat.gcd q₁ q₂ : ℤ)]

instance (q₁ q₂ : ℕ) (n₁ n₂ a₁ a₂ : ℤ) : Decidable (Compatible q₁ q₂ n₁ n₂ a₁ a₂) := by
  unfold Compatible Int.ModEq; infer_instance

/-- The compatibility indicator `κ`. -/
def kappa (q₁ q₂ : ℕ) (n₁ n₂ a₁ a₂ : ℤ) : ℕ := if Compatible q₁ q₂ n₁ n₂ a₁ a₂ then 1 else 0

/-- **Compatibility is necessary.** -/
theorem compat_necessary {q₁ q₂ : ℕ} {n₁ n₂ a₁ a₂ m : ℤ} (h₁ : n₁ * m ≡ a₁ [ZMOD q₁])
    (h₂ : n₂ * m ≡ a₂ [ZMOD q₂]) : Compatible q₁ q₂ n₁ n₂ a₁ a₂ := by
  have g1 : ((Nat.gcd q₁ q₂ : ℕ) : ℤ) ∣ q₁ := Int.natCast_dvd_natCast.2 (Nat.gcd_dvd_left _ _)
  have g2 : ((Nat.gcd q₁ q₂ : ℕ) : ℤ) ∣ q₂ := Int.natCast_dvd_natCast.2 (Nat.gcd_dvd_right _ _)
  have e1 := (h₁.of_dvd g1).mul_right n₂
  have e2 := (h₂.of_dvd g2).mul_right n₁
  unfold Compatible
  calc a₁ * n₂ ≡ n₁ * m * n₂ [ZMOD _] := e1.symm
    _ = n₂ * m * n₁ := by ring
    _ ≡ a₂ * n₁ [ZMOD _] := e2

/-- Cancelling a unit coefficient. -/
theorem cancel_unit {q : ℤ} {n i x y : ℤ} (hi : n * i ≡ 1 [ZMOD q]) (h : n * x ≡ n * y [ZMOD q]) :
    x ≡ y [ZMOD q] := by
  calc x = x * 1 := by ring
    _ ≡ x * (n * i) [ZMOD q] := Int.ModEq.mul_left _ hi.symm
    _ = i * (n * x) := by ring
    _ ≡ i * (n * y) [ZMOD q] := Int.ModEq.mul_left _ h
    _ = y * (n * i) := by ring
    _ ≡ y * 1 [ZMOD q] := Int.ModEq.mul_left _ hi
    _ = y := by ring

/-- **CRT existence** (non-coprime moduli), under unit hypotheses. -/
theorem crt_exists {q₁ q₂ : ℕ} {n₁ n₂ a₁ a₂ i₁ i₂ : ℤ} (hi₁ : n₁ * i₁ ≡ 1 [ZMOD q₁])
    (hi₂ : n₂ * i₂ ≡ 1 [ZMOD q₂]) (hc : Compatible q₁ q₂ n₁ n₂ a₁ a₂) :
    ∃ m : ℤ, n₁ * m ≡ a₁ [ZMOD q₁] ∧ n₂ * m ≡ a₂ [ZMOD q₂] := by
  set g : ℤ := ((Nat.gcd q₁ q₂ : ℕ) : ℤ)
  have g1 : g ∣ q₁ := Int.natCast_dvd_natCast.2 (Nat.gcd_dvd_left _ _)
  have g2 : g ∣ q₂ := Int.natCast_dvd_natCast.2 (Nat.gcd_dvd_right _ _)
  set b₁ := a₁ * i₁
  set b₂ := a₂ * i₂
  have hb : b₁ ≡ b₂ [ZMOD g] := by
    have u1 := hi₁.of_dvd g1
    have u2 := hi₂.of_dvd g2
    calc b₁ = a₁ * i₁ * 1 := by ring
      _ ≡ a₁ * i₁ * (n₂ * i₂) [ZMOD g] := Int.ModEq.mul_left _ u2.symm
      _ = (a₁ * n₂) * (i₁ * i₂) := by ring
      _ ≡ (a₂ * n₁) * (i₁ * i₂) [ZMOD g] := Int.ModEq.mul_right _ hc
      _ = a₂ * i₂ * (n₁ * i₁) := by ring
      _ ≡ a₂ * i₂ * 1 [ZMOD g] := Int.ModEq.mul_left _ u1
      _ = b₂ := by ring
  obtain ⟨t, ht⟩ := (Int.modEq_iff_dvd.1 hb)
  have hbez : g = (q₁ : ℤ) * Int.gcdA q₁ q₂ + (q₂ : ℤ) * Int.gcdB q₁ q₂ := by
    have := Int.gcd_eq_gcd_ab (q₁ : ℤ) (q₂ : ℤ)
    rw [Int.gcd_natCast_natCast] at this
    exact this
  refine ⟨b₁ + (q₁ : ℤ) * Int.gcdA q₁ q₂ * t, ?_, ?_⟩
  · have hm : b₁ + (q₁ : ℤ) * Int.gcdA q₁ q₂ * t ≡ b₁ [ZMOD q₁] :=
      Int.modEq_iff_dvd.2 ⟨-(Int.gcdA q₁ q₂ * t), by ring⟩
    calc n₁ * (b₁ + (q₁ : ℤ) * Int.gcdA q₁ q₂ * t) ≡ n₁ * b₁ [ZMOD q₁] := hm.mul_left _
      _ = a₁ * (n₁ * i₁) := by ring
      _ ≡ a₁ * 1 [ZMOD q₁] := hi₁.mul_left _
      _ = a₁ := by ring
  · have hm : b₁ + (q₁ : ℤ) * Int.gcdA q₁ q₂ * t ≡ b₂ [ZMOD q₂] := by
      apply Int.modEq_iff_dvd.2
      refine ⟨Int.gcdB q₁ q₂ * t, ?_⟩
      have : b₂ - b₁ = g * t := ht
      rw [hbez] at this
      linarith
    calc n₂ * (b₁ + (q₁ : ℤ) * Int.gcdA q₁ q₂ * t) ≡ n₂ * b₂ [ZMOD q₂] := hm.mul_left _
      _ = a₂ * (n₂ * i₂) := by ring
      _ ≡ a₂ * 1 [ZMOD q₂] := hi₂.mul_left _
      _ = a₂ := by ring

/-- **CRT uniqueness modulo `L = lcm(q₁, q₂)`.** -/
theorem crt_unique {q₁ q₂ : ℕ} {n₁ n₂ a₁ a₂ i₁ i₂ m m' : ℤ} (hi₁ : n₁ * i₁ ≡ 1 [ZMOD q₁])
    (hi₂ : n₂ * i₂ ≡ 1 [ZMOD q₂]) (h₁ : n₁ * m ≡ a₁ [ZMOD q₁]) (h₂ : n₂ * m ≡ a₂ [ZMOD q₂])
    (h₁' : n₁ * m' ≡ a₁ [ZMOD q₁]) (h₂' : n₂ * m' ≡ a₂ [ZMOD q₂]) :
    m ≡ m' [ZMOD (Nat.lcm q₁ q₂ : ℕ)] := by
  have c1 := cancel_unit hi₁ (h₁.trans h₁'.symm)
  have c2 := cancel_unit hi₂ (h₂.trans h₂'.symm)
  rw [Int.modEq_iff_dvd] at c1 c2 ⊢
  have d1 : ((q₁ : ℤ).natAbs) ∣ (m' - m).natAbs := Int.natAbs_dvd_natAbs.2 c1
  have d2 : ((q₂ : ℤ).natAbs) ∣ (m' - m).natAbs := Int.natAbs_dvd_natAbs.2 c2
  simp only [Int.natAbs_natCast] at d1 d2
  exact Int.natCast_dvd.2 (Nat.lcm_dvd d1 d2)

/-- The solution set in one period `[0, L)`. -/
def solutions (q₁ q₂ : ℕ) (n₁ n₂ a₁ a₂ : ℤ) : Finset ℕ :=
  (Finset.range (Nat.lcm q₁ q₂)).filter fun m =>
    n₁ * (m : ℤ) ≡ a₁ [ZMOD q₁] ∧ n₂ * (m : ℤ) ≡ a₂ [ZMOD q₂]

/-- **The exact zero-frequency CRT count**: `#{m ∈ [0, L) : both congruences} = κ`. -/
theorem zero_frequency_count {q₁ q₂ : ℕ} (hq₁ : 0 < q₁) (hq₂ : 0 < q₂) {n₁ n₂ a₁ a₂ i₁ i₂ : ℤ}
    (hi₁ : n₁ * i₁ ≡ 1 [ZMOD q₁]) (hi₂ : n₂ * i₂ ≡ 1 [ZMOD q₂]) :
    (solutions q₁ q₂ n₁ n₂ a₁ a₂).card = kappa q₁ q₂ n₁ n₂ a₁ a₂ := by
  unfold kappa
  split_ifs with hc
  · obtain ⟨m₀, h₁, h₂⟩ := crt_exists hi₁ hi₂ hc
    set L := Nat.lcm q₁ q₂
    have hL : 0 < L := Nat.lcm_pos hq₁ hq₂
    have hLz : (0 : ℤ) < L := by exact_mod_cast hL
    set r : ℕ := (m₀ % (L : ℤ)).toNat
    have hr : (r : ℤ) = m₀ % L := Int.toNat_of_nonneg (Int.emod_nonneg _ hLz.ne')
    have hrm : (r : ℤ) ≡ m₀ [ZMOD L] := by rw [hr]; exact Int.mod_modEq _ _
    have d1 : (q₁ : ℤ) ∣ L := Int.natCast_dvd_natCast.2 (Nat.dvd_lcm_left _ _)
    have d2 : (q₂ : ℤ) ∣ L := Int.natCast_dvd_natCast.2 (Nat.dvd_lcm_right _ _)
    have hrsol : n₁ * (r : ℤ) ≡ a₁ [ZMOD q₁] ∧ n₂ * (r : ℤ) ≡ a₂ [ZMOD q₂] :=
      ⟨((hrm.of_dvd d1).mul_left _).trans h₁, ((hrm.of_dvd d2).mul_left _).trans h₂⟩
    have hrL : r < L := by
      have := Int.emod_lt_of_pos m₀ hLz
      omega
    rw [Finset.card_eq_one]
    refine ⟨r, Finset.eq_singleton_iff_unique_mem.2 ⟨?_, fun m hm => ?_⟩⟩
    · exact Finset.mem_filter.2 ⟨Finset.mem_range.2 hrL, hrsol⟩
    · obtain ⟨hmL, hm₁, hm₂⟩ := Finset.mem_filter.1 hm
      have hmr := crt_unique hi₁ hi₂ hm₁ hm₂ hrsol.1 hrsol.2
      have hmL' := Finset.mem_range.1 hmL
      have e := Int.emod_emod_of_dvd (m : ℤ) (dvd_refl (L : ℤ))
      unfold Int.ModEq at hmr
      rw [Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hmL'),
        Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hrL)] at hmr
      exact_mod_cast hmr
  · rw [Finset.card_eq_zero, solutions, Finset.filter_eq_empty_iff]
    intro m _ hm
    exact hc (compat_necessary hm.1 hm.2)

/-- The phase at frequency `0` is always `1`. -/
theorem phase_at_zero (L : ℕ) (Δ : ℤ) : e L (0 * Δ) = 1 := by
  simp [e]

/-- **REPAIRED / RETIRED: `Ω(0) = 1` does not fix the zero-frequency main term.** -/
theorem omega_zero_does_not_fix_main_term :
    ¬ ∀ (q₁ q₂ : ℕ) (n₁ n₂ a₁ a₂ Δ : ℤ),
      e (Nat.lcm q₁ q₂) (0 * Δ) = 1 → (solutions q₁ q₂ n₁ n₂ a₁ a₂).card = 1 := by
  intro h
  have := h 3 3 1 1 1 2 0 (phase_at_zero _ _)
  revert this
  decide

end ZeroFrequencyCompatibility
end ResearchBankV19
end Erdos287
