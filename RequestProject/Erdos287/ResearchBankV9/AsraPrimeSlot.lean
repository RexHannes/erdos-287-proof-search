import Mathlib.Tactic

/-!
# Erdős #287 — Research Bank V9 §4D–4E: prime-slot truncation and the large-overlap tail

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

**4D. Prime-slot truncation firewall.**  For a Maynard-type weight `λ(d_i, d_j, e)` supported on
`d_i ≤ R`, `d_j ≤ R`, the full divisor sum
`V(t) = ∑_{d_i ∣ L_i(t)} ∑_{d_j ∣ L_j(t)} ∑_{e ∣ W(t)} λ(d_i, d_j, e)` equals the truncated sum
`V_ij(t) = ∑_{e ∣ W(t)} λ(1, 1, e)` **exactly** on the prime-pair locus
`L_i(t), L_j(t)` prime `> R` (`primeSlot_truncation`).  Then only the logical step
"nonnegative physical sequence ⟹ valid upper-sieve majorization" is proved
(`upper_sieve_majorization`); the Iwaniec/Maynard analytic upper-sieve bound is the external
interface `UpperSieveInput`, used only as a hypothesis (`primePair_bound_of_upperSieve`).

**4E. Large-overlap tail.**  The finite divisor decomposition reducing `g ∣ F(t)` to
polynomial-root congruence classes is proved (`dvd_sum_eq_root_classes`); the Shiu /
divisor-moment estimate is the external interface `ShiuAffineDivisorMomentInput`, and
`largeOverlap_tail_bound` proves internally: interface ⟹ tail `≤ ∑_g ρ(g) B(g)`.
-/

open scoped BigOperators

namespace Erdos287
namespace ResearchBankV9
namespace AsraPrimeSlot

/-! ## 4D.  Prime-slot truncation -/

/-- The full (three-slot) divisor sum. -/
def Vfull (lam : ℕ → ℕ → ℕ → ℝ) (Li Lj W : ℕ) : ℝ :=
  ∑ di ∈ Li.divisors, ∑ dj ∈ Lj.divisors, ∑ e ∈ W.divisors, lam di dj e

/-- The truncated divisor sum `V_ij`: only `d_i = d_j = 1`. -/
def Vtrunc (lam : ℕ → ℕ → ℕ → ℝ) (W : ℕ) : ℝ := ∑ e ∈ W.divisors, lam 1 1 e

/-- Support condition of the sieve weight: `λ(d_i, d_j, e) = 0` unless `d_i, d_j ≤ R`. -/
def Supported (lam : ℕ → ℕ → ℕ → ℝ) (R : ℕ) : Prop :=
  ∀ di dj e, (R < di ∨ R < dj) → lam di dj e = 0

/-- **Prime-slot truncation (exact identity on the prime-pair locus).** -/
theorem primeSlot_truncation {lam : ℕ → ℕ → ℕ → ℝ} {R : ℕ} (hsupp : Supported lam R)
    {Li Lj W : ℕ} (hi : Li.Prime) (hj : Lj.Prime) (hiR : R < Li) (hjR : R < Lj) :
    Vfull lam Li Lj W = Vtrunc lam W := by
  unfold Vfull Vtrunc
  rw [hi.divisors, Finset.sum_pair hi.one_lt.ne, hj.divisors, Finset.sum_pair hj.one_lt.ne,
    Finset.sum_pair hj.one_lt.ne]
  have h1 : ∀ e, lam Li 1 e = 0 := fun e => hsupp _ _ _ (Or.inl hiR)
  have h2 : ∀ e, lam Li Lj e = 0 := fun e => hsupp _ _ _ (Or.inl hiR)
  have h3 : ∀ e, lam 1 Lj e = 0 := fun e => hsupp _ _ _ (Or.inr hjR)
  simp [h1, h2, h3]

/-- The squared weights agree as well. -/
theorem primeSlot_truncation_sq {lam : ℕ → ℕ → ℕ → ℝ} {R : ℕ} (hsupp : Supported lam R)
    {Li Lj W : ℕ} (hi : Li.Prime) (hj : Lj.Prime) (hiR : R < Li) (hjR : R < Lj) :
    Vfull lam Li Lj W ^ 2 = Vtrunc lam W ^ 2 := by
  rw [primeSlot_truncation hsupp hi hj hiR hjR]

/-- **Upper-sieve majorization (logical step only).**  For a nonnegative physical sequence `w`,
the prime-pair-restricted weighted sum of `V_ij²` is at most the unrestricted one. -/
theorem upper_sieve_majorization (T : Finset ℕ) (w : ℕ → ℝ) (hw : ∀ t ∈ T, 0 ≤ w t)
    (P : ℕ → Prop) [DecidablePred P] (V : ℕ → ℝ) :
    ∑ t ∈ T.filter P, w t * V t ^ 2 ≤ ∑ t ∈ T, w t * V t ^ 2 :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    fun t ht _ => mul_nonneg (hw t ht) (sq_nonneg _)

/-- **External interface (Iwaniec/Maynard analytic upper sieve) — never inhabited here.** -/
structure UpperSieveInput (T : Finset ℕ) (w : ℕ → ℝ) (V : ℕ → ℝ) (bound : ℝ) : Prop where
  /-- The analytic upper-sieve bound for the truncated weights. -/
  sieve_bound : ∑ t ∈ T, w t * V t ^ 2 ≤ bound

/-- Conditional: the prime-pair weighted count with the full Maynard square is bounded by the
analytic upper-sieve bound for the truncated square. -/
theorem primePair_bound_of_upperSieve {lam : ℕ → ℕ → ℕ → ℝ} {R : ℕ} (hsupp : Supported lam R)
    (T : Finset ℕ) (w : ℕ → ℝ) (hw : ∀ t ∈ T, 0 ≤ w t) (Li Lj W : ℕ → ℕ) (bound : ℝ)
    (hin : UpperSieveInput T w (fun t => Vtrunc lam (W t)) bound) :
    ∑ t ∈ T.filter (fun t => (Li t).Prime ∧ (Lj t).Prime ∧ R < Li t ∧ R < Lj t),
      w t * Vfull lam (Li t) (Lj t) (W t) ^ 2 ≤ bound := by
  have heq : ∑ t ∈ T.filter (fun t => (Li t).Prime ∧ (Lj t).Prime ∧ R < Li t ∧ R < Lj t),
      w t * Vfull lam (Li t) (Lj t) (W t) ^ 2 =
      ∑ t ∈ T.filter (fun t => (Li t).Prime ∧ (Lj t).Prime ∧ R < Li t ∧ R < Lj t),
        w t * Vtrunc lam (W t) ^ 2 := by
    refine Finset.sum_congr rfl fun t ht => ?_
    simp only [Finset.mem_filter] at ht
    rw [primeSlot_truncation_sq hsupp ht.2.1 ht.2.2.1 ht.2.2.2.1 ht.2.2.2.2]
  rw [heq]
  exact (upper_sieve_majorization T w hw _ (fun t => Vtrunc lam (W t))).trans hin.sieve_bound

/-! ## 4E.  Large-overlap tail -/

/-- The polynomial roots modulo `g`, represented in `[0, g)`. -/
def rootClasses (F : Polynomial ℤ) (g : ℕ) : Finset ℤ :=
  (Finset.Ico 0 (g : ℤ)).filter fun b => (g : ℤ) ∣ F.eval b

/-- **Finite divisor decomposition.**  The `g`-divisible part of a weighted sum splits over the
polynomial-root classes modulo `g`. -/
theorem dvd_sum_eq_root_classes (F : Polynomial ℤ) {g : ℕ} (hg : 0 < g) (T : Finset ℤ)
    (w : ℤ → ℝ) :
    ∑ t ∈ T.filter (fun t => (g : ℤ) ∣ F.eval t), w t =
      ∑ b ∈ rootClasses F g, ∑ t ∈ T.filter (fun t => t % g = b), w t := by
  have key : ∀ t : ℤ, ((g : ℤ) ∣ F.eval t ↔ (g : ℤ) ∣ F.eval (t % g)) := by
    intro t
    have h := Polynomial.sub_dvd_eval_sub t (t % g) F
    have hdiv : (g : ℤ) ∣ t - t % g := by
      refine ⟨t / g, ?_⟩; have := Int.emod_add_mul_ediv t g; linarith
    have := hdiv.trans h
    constructor
    · intro h1; have := dvd_sub h1 this; simpa using this
    · intro h1; have := dvd_add h1 this; simpa using this
  have hmaps : ∀ t ∈ T.filter (fun t => (g : ℤ) ∣ F.eval t), t % (g : ℤ) ∈ rootClasses F g := by
    intro t ht
    simp only [Finset.mem_filter] at ht
    simp only [rootClasses, Finset.mem_filter, Finset.mem_Ico]
    exact ⟨⟨Int.emod_nonneg _ (by exact_mod_cast hg.ne'), Int.emod_lt_of_pos _
      (by exact_mod_cast hg)⟩, (key t).1 ht.2⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl fun b hb => ?_
  congr 1
  ext t
  simp only [rootClasses, Finset.mem_filter, Finset.mem_Ico] at hb ⊢
  constructor
  · rintro ⟨⟨ht, -⟩, hb'⟩; exact ⟨ht, hb'⟩
  · rintro ⟨ht, rfl⟩; exact ⟨⟨ht, (key t).2 hb.2⟩, rfl⟩

/-- **External interface (Shiu / affine divisor moment) — never inhabited here.**  Every residue
class modulo `g ∈ G` carries weighted mass at most `B g`. -/
structure ShiuAffineDivisorMomentInput (T : Finset ℤ) (w : ℤ → ℝ) (G : Finset ℕ) (B : ℕ → ℝ) :
    Prop where
  /-- The class-mass bound. -/
  class_bound : ∀ g ∈ G, ∀ b : ℤ, ∑ t ∈ T.filter (fun t => t % g = b), w t ≤ B g

/-- **Large shared-gcd tail bound (internal, given the interface):**
`∑_{g∈G} ∑_{t : g ∣ F(t)} w(t) ≤ ∑_{g∈G} ρ(g) B(g)`, with `ρ(g)` the number of root classes. -/
theorem largeOverlap_tail_bound (F : Polynomial ℤ) (T : Finset ℤ) (w : ℤ → ℝ) (G : Finset ℕ)
    (hG : ∀ g ∈ G, 0 < g) (B : ℕ → ℝ) (hin : ShiuAffineDivisorMomentInput T w G B) :
    ∑ g ∈ G, ∑ t ∈ T.filter (fun t => (g : ℤ) ∣ F.eval t), w t ≤
      ∑ g ∈ G, ((rootClasses F g).card : ℝ) * B g := by
  apply Finset.sum_le_sum
  intro g hg
  rw [dvd_sum_eq_root_classes F (hG g hg)]
  calc ∑ b ∈ rootClasses F g, ∑ t ∈ T.filter (fun t => t % g = b), w t
      ≤ ∑ _b ∈ rootClasses F g, B g := Finset.sum_le_sum fun b _ => hin.class_bound g hg b
    _ = ((rootClasses F g).card : ℝ) * B g := by simp

end AsraPrimeSlot
end ResearchBankV9
end Erdos287
