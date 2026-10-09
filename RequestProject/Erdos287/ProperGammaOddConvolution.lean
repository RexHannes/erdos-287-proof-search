import Mathlib
import RequestProject.Erdos287.BsrcWeights

/-!
# Erdős #287 effectivity — odd convolution algebra and the factor-two error (§38)

```
ODD CONVOLUTION ALGEBRA          : KERNEL-PROVED
EXACT ODD-COUNT ERROR |ρ| ≤ 1/2  : KERNEL-PROVED
FACTOR-TWO ERROR INEQUALITY      : KERNEL-PROVED (finite level)
∑_d h_z(d)/d = 1/B(z)            : CONDITIONAL INTERFACE (hypothesis, not proved)
DIVISOR-MOMENT CONSTANTS         : CERTIFICATE-BACKED
ERDŐS #287                       : OPEN
```

With `g_z(q) = q β(q) 1_{(q,z)=1}` the local factorisation `g_z = 1_odd * h_z` is banked as an
exact finite Dirichlet identity (`oddConvolution_identity`), `h_z` being the Möbius transform
of `g_z` supported on odd arguments.

The exact odd-counting error is `ρ_odd(x) = ⌊(x+1)/2⌋ − x/2`, with the sharp elementary bound
`|ρ_odd(x)| ≤ 1/2` (`abs_rhoOdd_le`), and the factor-two improvement is banked at the finite
level as `oddError_bound` / `factorTwo_Ez`:

    |E_z(x)| ≤ (1/2) · H_{z,α} · x^α,    H_{z,α} = ∑_d |h_z(d)| / d^α.

The Euler-product identity `∑_d h_z(d)/d = 1/B(z)` is **not** proved here: it is carried as an
explicit hypothesis (`OddSeriesClaim`).  The reported divisor-moment constants
`H₀ < 88/5`, `C₁ < 5/4`, `C_{3/5} < 31/10` are `CERTIFICATE-BACKED` typed objects, never
theorems (`divisorMomentCertificate_not_proved`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open Finset ArithmeticFunction

namespace Erdos287
namespace Effectivity

/-! ## §38.1  The local weights -/

/-- `g_z(q) = q β(q) 1_{(q,z)=1}`. -/
def gz (z q : ℕ) : ℚ := (q : ℚ) * beta q * (if Nat.Coprime q z then 1 else 0)

/-- The Möbius transform of `g_z`. -/
def hzRaw (z d : ℕ) : ℚ :=
  ∑ x ∈ d.divisorsAntidiagonal, ((moebius x.1 : ℤ) : ℚ) * gz z x.2

/-- `h_z`, supported on odd arguments. -/
def hz (z d : ℕ) : ℚ := if ¬ 2 ∣ d then hzRaw z d else 0

theorem hz_of_odd {z d : ℕ} (hd : ¬ 2 ∣ d) : hz z d = hzRaw z d := by simp [hz, hd]

theorem hz_of_even {z d : ℕ} (hd : 2 ∣ d) : hz z d = 0 := by simp [hz, hd]

theorem gz_of_even {z q : ℕ} (hq : 2 ∣ q) : gz z q = 0 := by
  simp [gz, beta_eq_zero_of_even hq]

/-- The raw Möbius transform inverts the divisor sum (Mathlib's Möbius inversion). -/
theorem sum_divisors_hzRaw (z : ℕ) {n : ℕ} (hn : 0 < n) :
    ∑ d ∈ n.divisors, hzRaw z d = gz z n := by
  have h := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq (R := ℚ)
    (f := fun d => hzRaw z d) (g := fun n => gz z n)).2
  exact h (fun m _ => rfl) n hn

/-- **`oddConvolution_identity`.**  `KERNEL-PROVED`.  The exact convolution `g_z = 1_odd * h_z`
in Dirichlet form. -/
theorem oddConvolution_identity (z : ℕ) {n : ℕ} (hn : 0 < n) :
    ∑ d ∈ n.divisors, (if ¬ 2 ∣ (n / d) then (1 : ℚ) else 0) * hz z d = gz z n := by
  by_cases hodd : 2 ∣ n
  · rw [gz_of_even hodd]
    refine Finset.sum_eq_zero fun d hd => ?_
    obtain ⟨hdvd, -⟩ := Nat.mem_divisors.1 hd
    by_cases hd2 : 2 ∣ d
    · rw [hz_of_even hd2, mul_zero]
    · have : 2 ∣ n / d := by
        have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdvd hn
        obtain ⟨c, hc⟩ := hdvd
        have hnd : n / d = c := by rw [hc]; exact Nat.mul_div_cancel_left c hd0
        rw [hnd]
        rcases (Nat.Prime.dvd_mul Nat.prime_two).1 (hc ▸ hodd) with h | h
        · exact absurd h hd2
        · exact h
      simp [this]
  · have hall : ∀ d ∈ n.divisors, (if ¬ 2 ∣ (n / d) then (1 : ℚ) else 0) * hz z d = hzRaw z d := by
      intro d hd
      obtain ⟨hdvd, -⟩ := Nat.mem_divisors.1 hd
      have hd2 : ¬ 2 ∣ d := fun h => hodd (h.trans hdvd)
      have hnd : ¬ 2 ∣ (n / d) := fun h => hodd (h.trans (Nat.div_dvd_of_dvd hdvd))
      rw [hz_of_odd hd2]
      simp [hnd]
    rw [Finset.sum_congr rfl hall, sum_divisors_hzRaw z hn]

/-! ## §38.2  The exact odd-count error -/

/-- The exact odd-counting error `ρ_odd(x) = ⌊(x+1)/2⌋ − x/2`. -/
def rhoOdd (x : ℚ) : ℚ := (⌊(x + 1) / 2⌋ : ℚ) - x / 2

/-- **`abs_rhoOdd_le`.**  `KERNEL-PROVED`.  `|ρ_odd(x)| ≤ 1/2`. -/
theorem abs_rhoOdd_le (x : ℚ) : |rhoOdd x| ≤ 1 / 2 := by
  have h1 : ((⌊(x + 1) / 2⌋ : ℤ) : ℚ) ≤ (x + 1) / 2 := Int.floor_le _
  have h2 : (x + 1) / 2 - 1 < ((⌊(x + 1) / 2⌋ : ℤ) : ℚ) := Int.sub_one_lt_floor _
  rw [abs_le, rhoOdd]
  constructor <;> linarith

/-- **`oddCount_exact`.**  `KERNEL-PROVED`.  The exact count of odd integers in `[1, N]`. -/
theorem oddCount_exact (N : ℕ) :
    ((Finset.Icc 1 N).filter (fun n => ¬ 2 ∣ n)).card = (N + 1) / 2 := by
  induction N with
  | zero => decide
  | succ N ih =>
      rw [show Finset.Icc 1 (N + 1) = insert (N + 1) (Finset.Icc 1 N) by
        ext k; simp [Finset.mem_Icc, Finset.mem_insert]; omega]
      rw [Finset.filter_insert]
      by_cases h : ¬ 2 ∣ (N + 1)
      · rw [if_pos h, Finset.card_insert_of_notMem (by simp), ih]
        omega
      · rw [if_neg h, ih]
        omega

/-! ## §38.3  The factor-two error inequality -/

/-- **`oddError_bound`.**  `KERNEL-PROVED`.  The finite-level factor-two inequality: a
coefficient sum against remainders bounded by `1/2` obeys

    |∑_d c_d r_d| ≤ (1/2) (∑_d |c_d| / d^α) x^α         (0 < α, 1 ≤ d ≤ x). -/
theorem oddError_bound {α x : ℝ} (hα : 0 < α) (D : Finset ℕ)
    (hD : ∀ d ∈ D, 1 ≤ d ∧ (d : ℝ) ≤ x) (c r : ℕ → ℝ) (hr : ∀ d ∈ D, |r d| ≤ 1 / 2) :
    |∑ d ∈ D, c d * r d| ≤ 1 / 2 * (∑ d ∈ D, |c d| / (d : ℝ) ^ α) * x ^ α := by
  have hstep : ∀ d ∈ D, |c d * r d| ≤ 1 / 2 * (|c d| / (d : ℝ) ^ α) * x ^ α := by
    intro d hd
    obtain ⟨hd1, hdx⟩ := hD d hd
    have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd1
    have hpow : (d : ℝ) ^ α ≤ x ^ α := Real.rpow_le_rpow hd0.le hdx hα.le
    have hpowpos : (0 : ℝ) < (d : ℝ) ^ α := Real.rpow_pos_of_pos hd0 α
    have hcd : |c d| / (d : ℝ) ^ α * (d : ℝ) ^ α = |c d| :=
      div_mul_cancel₀ _ (ne_of_gt hpowpos)
    calc |c d * r d| = |c d| * |r d| := abs_mul _ _
      _ ≤ |c d| * (1 / 2) := by
          have := hr d hd
          nlinarith [abs_nonneg (c d), abs_nonneg (r d)]
      _ = 1 / 2 * (|c d| / (d : ℝ) ^ α * (d : ℝ) ^ α) := by rw [hcd]; ring
      _ ≤ 1 / 2 * (|c d| / (d : ℝ) ^ α * x ^ α) := by
          have hnn : 0 ≤ |c d| / (d : ℝ) ^ α := by positivity
          nlinarith
      _ = 1 / 2 * (|c d| / (d : ℝ) ^ α) * x ^ α := by ring
  calc |∑ d ∈ D, c d * r d| ≤ ∑ d ∈ D, |c d * r d| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ D, 1 / 2 * (|c d| / (d : ℝ) ^ α) * x ^ α := Finset.sum_le_sum hstep
    _ = 1 / 2 * (∑ d ∈ D, |c d| / (d : ℝ) ^ α) * x ^ α := by
        rw [← Finset.sum_mul, ← Finset.mul_sum]

/-- The finite divisor moment `H_{z,α} = ∑_{d ∈ D} |h_z(d)| / d^α`. -/
noncomputable def HzMoment (z : ℕ) (α : ℝ) (D : Finset ℕ) : ℝ :=
  ∑ d ∈ D, |((hz z d : ℚ) : ℝ)| / (d : ℝ) ^ α

/-- The finite odd-counting error term `E_z(x) = ∑_{d ∈ D} h_z(d) ρ_odd(x/d)`. -/
noncomputable def EzError (z : ℕ) (x : ℚ) (D : Finset ℕ) : ℝ :=
  ∑ d ∈ D, ((hz z d : ℚ) : ℝ) * ((rhoOdd (x / d) : ℚ) : ℝ)

/-- **`factorTwo_Ez`.**  `KERNEL-PROVED`.  The factor-two error improvement for the odd
convolution error, at the finite level. -/
theorem factorTwo_Ez (z : ℕ) {α : ℝ} (hα : 0 < α) (x : ℚ) (D : Finset ℕ) (hD : ∀ d ∈ D, 1 ≤ d ∧ (d : ℝ) ≤ ((x : ℚ) : ℝ)) :
    |EzError z x D| ≤ 1 / 2 * HzMoment z α D * ((x : ℚ) : ℝ) ^ α := by
  refine oddError_bound hα D hD _ _ fun d _ => ?_
  have hcast : |((rhoOdd (x / d) : ℚ) : ℝ)| = ((|rhoOdd (x / d)| : ℚ) : ℝ) :=
    (Rat.cast_abs _).symm
  rw [hcast]
  have hb : ((|rhoOdd (x / d)| : ℚ) : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) := by
    exact_mod_cast abs_rhoOdd_le (x / d)
  simpa using hb

/-! ## §38.4  The Euler-product series: a conditional interface, never a theorem -/

/-- The claim `∑_d h_z(d)/d = 1/B(z)`.  It is **not** proved in this package; it is used only
as an explicit hypothesis. -/
def OddSeriesClaim (B1 : ℚ) (z : ℕ) : Prop :=
  HasSum (fun d : ℕ => ((hz z d : ℚ) : ℝ) / (d : ℝ)) (1 / ((B B1 z : ℚ) : ℝ))

/-- **`oddSeries_hypothesis_used`.**  `KERNEL-PROVED`.  The interface: whoever supplies the
analytic input gets exactly the stated summation, and nothing more is assumed. -/
theorem oddSeries_hypothesis_used (B1 : ℚ) (z : ℕ) (h : OddSeriesClaim B1 z) :
    HasSum (fun d : ℕ => ((hz z d : ℚ) : ℝ) / (d : ℝ)) (1 / ((B B1 z : ℚ) : ℝ)) := h

/-- **`oddSeries_sum_unique`.**  `KERNEL-PROVED`.  Under the hypothesis the value is unique. -/
theorem oddSeries_sum_unique (B1 : ℚ) (z : ℕ) (S : ℝ) (h : OddSeriesClaim B1 z)
    (h' : HasSum (fun d : ℕ => ((hz z d : ℚ) : ℝ) / (d : ℝ)) S) :
    S = 1 / ((B B1 z : ℚ) : ℝ) := h'.unique h

/-! ## §38.5  Divisor-moment numerical certificates -/

/-- A typed numerical certificate for a divisor-moment constant. -/
structure DivisorMomentCertificate where
  /-- A label for the constant (`0` for `H₀`, `1` for `C₁`, `2` for `C_{3/5}`). -/
  label : ℕ
  /-- The claimed value. -/
  value : ℚ
  /-- The certified strict upper bound. -/
  bound : ℚ
  /-- The certificate hypothesis. -/
  value_lt : value < bound

/-- The declared bound `H₀ < 88/5`. -/
def H0Bound : ℚ := 88 / 5

/-- The declared bound `C₁ < 5/4`. -/
def C1Bound : ℚ := 5 / 4

/-- The declared bound `C_{3/5} < 31/10`. -/
def C35Bound : ℚ := 31 / 10

/-- **`divisorMoment_bounds_exact`.**  `KERNEL-PROVED`.  Only the exact rational values of the
declared bounds are kernel content. -/
theorem divisorMoment_bounds_exact :
    H0Bound = 88 / 5 ∧ C1Bound = 5 / 4 ∧ C35Bound = 31 / 10 := ⟨rfl, rfl, rfl⟩

/-- **`divisorMomentCertificate_not_proved`.**  `KERNEL-PROVED`.  Firewall: certificates exist
for every label and bound, so the reported constants are `CERTIFICATE-BACKED`, not proved. -/
theorem divisorMomentCertificate_not_proved (label : ℕ) (bound : ℚ) :
    ∃ C : DivisorMomentCertificate, C.label = label ∧ C.bound = bound :=
  ⟨⟨label, bound - 1, bound, by linarith⟩, rfl, rfl⟩

end Effectivity
end Erdos287
