import Mathlib

/-!
# Erdős #287 — Research Bank V25 §3.1: exact centering identity at a fixed exceptional modulus

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

For a modulus `q`, a residue `a` and an integer `v` put

    δ(q, a, v) = 1_{v ≡ a (mod q)} − 1_{gcd(v, q) = 1} / φ(q).

**LEAN BANK.**

* `full_centering_fixed_modulus_exact` — for coprime `f, q` and any `r` with `r ≡ c (mod f)`,
  `r ≡ a (mod q)` (i.e. `r = CRT(c, a)`), and for EVERY integer `v` (units and non-units alike):

      δ(fq, r, v) = 1_{v ≡ c (f)} δ(q, a, v) + [1_{gcd(v,q)=1}/φ(q)] δ(f, c, v).

  The unit hypotheses `c ∈ (ℤ/f)^×`, `a ∈ (ℤ/q)^×` of the Astra statement are NOT needed: the
  identity is purely a CRT / totient-multiplicativity identity, so it is proved without them.
* `centered_sum_split` — the summed form for an arbitrary finitely supported complex coefficient:
  the full-modulus discrepancy splits into the localized discrepancy plus the correction whose
  reciprocal weight `1/φ(q)` is produced by the identity itself.
* `correction_term_needed` (regression) — deleting the correction term is FALSE.
-/

namespace Erdos287
namespace ResearchBankV25
namespace FixedModulusCentering

open Classical

/-- The indicator `1_{v ≡ a (mod q)}`. -/
noncomputable def indMod (q : ℕ) (a v : ℤ) : ℝ := if v ≡ a [ZMOD (q : ℤ)] then 1 else 0

/-- The indicator `1_{gcd(v, q) = 1}`. -/
noncomputable def indCop (q : ℕ) (v : ℤ) : ℝ := if Int.gcd v q = 1 then 1 else 0

/-- **The centred indicator** `δ(q, a, v) = 1_{v ≡ a (q)} − 1_{gcd(v,q)=1}/φ(q)`. -/
noncomputable def delta (q : ℕ) (a v : ℤ) : ℝ := indMod q a v - indCop q v / (q.totient : ℝ)

theorem indMod_mul {f q : ℕ} (hfq : Nat.Coprime f q) {r v : ℤ} :
    indMod (f * q) r v = indMod f r v * indMod q r v := by
  unfold indMod
  have h := Int.modEq_and_modEq_iff_modEq_mul (a := v) (b := r) (m := (f : ℤ)) (n := (q : ℤ))
    (by simpa using hfq)
  push_cast
  by_cases h1 : v ≡ r [ZMOD (f : ℤ)] <;> by_cases h2 : v ≡ r [ZMOD (q : ℤ)] <;>
    simp_all

theorem indCop_mul (f q : ℕ) (v : ℤ) : indCop (f * q) v = indCop f v * indCop q v := by
  unfold indCop
  have key : Int.gcd v ((f * q : ℕ) : ℤ) = 1 ↔ Int.gcd v f = 1 ∧ Int.gcd v q = 1 := by
    rw [← Int.isCoprime_iff_gcd_eq_one, ← Int.isCoprime_iff_gcd_eq_one,
      ← Int.isCoprime_iff_gcd_eq_one]
    push_cast
    exact IsCoprime.mul_right_iff
  by_cases h1 : Int.gcd v f = 1 <;> by_cases h2 : Int.gcd v q = 1 <;> simp_all

theorem indMod_congr {q : ℕ} {a b v : ℤ} (h : a ≡ b [ZMOD (q : ℤ)]) :
    indMod q a v = indMod q b v := by
  unfold indMod
  by_cases h1 : v ≡ a [ZMOD (q : ℤ)]
  · rw [if_pos h1, if_pos (h1.trans h)]
  · rw [if_neg h1, if_neg (fun h2 => h1 (h2.trans h.symm))]

/-- **Exact full centering identity at a fixed modulus** (LEAN BANK), valid for EVERY integer
`v`, including non-units.  `r` is any CRT lift of `(c mod f, a mod q)`. -/
theorem full_centering_fixed_modulus_exact {f q : ℕ} (hfq : Nat.Coprime f q) {c a r : ℤ}
    (hrc : r ≡ c [ZMOD (f : ℤ)]) (hra : r ≡ a [ZMOD (q : ℤ)]) (v : ℤ) :
    delta (f * q) r v =
      indMod f c v * delta q a v + (indCop q v / (q.totient : ℝ)) * delta f c v := by
  unfold delta
  rw [indMod_mul hfq, indCop_mul, Nat.totient_mul hfq, indMod_congr hrc, indMod_congr hra]
  push_cast
  by_cases hf : (f.totient : ℝ) = 0 <;> by_cases hq : (q.totient : ℝ) = 0
  · simp [hf, hq]
  · simp [hf]; ring
  · simp [hq]
  · field_simp; ring

/-- The identity with the correction term deleted (the historical inference). -/
def CorrectionDeletable : Prop :=
  ∀ (f q : ℕ), Nat.Coprime f q → ∀ c a r : ℤ, r ≡ c [ZMOD (f : ℤ)] → r ≡ a [ZMOD (q : ℤ)] →
    ∀ v : ℤ, delta (f * q) r v = indMod f c v * delta q a v

/-- **Regression: the correction term cannot be deleted.**  Witness `f = 3, q = 2, c = a = r = 1,
v = 1`: `δ(6,1,1) = 1 − 1/2 = 1/2`, whereas `1_{1 ≡ 1 (3)} δ(2,1,1) = 1 − 1/1 = 0`. -/
theorem correction_term_needed : ¬ CorrectionDeletable := by
  intro h
  have := h 3 2 (by norm_num) 1 1 1 (Int.ModEq.refl _) (Int.ModEq.refl _) 1
  unfold delta indMod indCop at this
  have h6 : (Nat.totient (3 * 2) : ℝ) = 2 := by
    rw [Nat.totient_mul (by norm_num), Nat.totient_prime Nat.prime_two,
      Nat.totient_prime Nat.prime_three]; norm_num
  have h2 : (Nat.totient 2 : ℝ) = 1 := by rw [Nat.totient_prime Nat.prime_two]; norm_num
  rw [h6, h2] at this
  norm_num [Int.ModEq] at this

/-- **Summed form** (LEAN BANK): for any finite set of integers and any complex coefficient `α`,
the full-modulus centred sum splits EXACTLY into the localized centred sum and the correction,
whose weight `1/φ(q)` comes out of the identity (it is not a principal-density input). -/
theorem centered_sum_split {f q : ℕ} (hfq : Nat.Coprime f q) {c a r : ℤ}
    (hrc : r ≡ c [ZMOD (f : ℤ)]) (hra : r ≡ a [ZMOD (q : ℤ)]) (S : Finset ℤ) (α : ℤ → ℂ) :
    ∑ v ∈ S, α v * (delta (f * q) r v : ℂ) =
      ∑ v ∈ S, α v * ((indMod f c v * delta q a v : ℝ) : ℂ) +
        (1 / (q.totient : ℂ)) * ∑ v ∈ S, α v * ((indCop q v * delta f c v : ℝ) : ℂ) := by
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [full_centering_fixed_modulus_exact hfq hrc hra v]
  push_cast
  ring

end FixedModulusCentering
end ResearchBankV25
end Erdos287
