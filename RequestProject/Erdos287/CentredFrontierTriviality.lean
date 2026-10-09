import Mathlib
import RequestProject.Erdos287.BoundedConductorTargetAudit

/-!
# Erdős #287 effectivity — the centred `k = 1` target is qualitatively trivial (§64)

```
UNIFORM ATOM BOUND FOR K_ell           : KERNEL-PROVED
PERIOD-BLOCK BASE INDEPENDENCE         : KERNEL-PROVED
CENTRED WINDOW BOUND (per conductor)   : KERNEL-PROVED
∃ b, CentredBoundedConductorK1Target b : KERNEL-PROVED
```

§62 refuted the bounded-conductor `k = 1` target as formalised, and proposed the
density-centred replacement `CentredBoundedConductorK1Target`.  This module completes the
audit of that replacement: on ordered windows it is **qualitatively trivial** — *some*
budget always works, for a purely structural reason.  The returned kernel is a finite sum of
`ℓ`-periodic kernels with uniformly bounded atoms, so a window sum differs from its density
term only by the incomplete final period, whose contribution is bounded by
`∑_ℓ ℓ·(sup|K_ℓ| + |mean_ℓ|)` independently of `A`, `B` and `z`.

Consequently *no* qualitative boundedness statement about `returnedKernel` can carry analytic
content: the frontier has to be stated **quantitatively** (a specific admissible budget, as
in the ledger targets) and at the level of the physical `X → ∞` source, not for the finite
periodic kernel alone.  This is recorded as a firewall, not as a closure of any owner: the
`k = 1` analytic owner is *not* closed by this module.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open Finset

namespace Erdos287
namespace Effectivity

/-! ## §64.1  A uniform bound on the local atoms -/

/-- A uniform (in `s` and `z`) bound for the local kernel `K_ℓ`. -/
def Kbound (ell : ℕ) : ℚ := |cEll ell| * (∏ p ∈ ell.primeFactors, ((p : ℚ) + 2) + 1)

lemma prod_add_two_pos (ell : ℕ) : (0 : ℚ) < ∏ p ∈ ell.primeFactors, ((p : ℚ) + 2) := by
  refine Finset.prod_pos fun p hp => ?_
  have := (Nat.prime_of_mem_primeFactors hp).two_le
  have : (2 : ℚ) ≤ (p : ℚ) := by exact_mod_cast this
  linarith

lemma Kbound_nonneg (ell : ℕ) : 0 ≤ Kbound ell := by
  have := prod_add_two_pos ell
  have habs : 0 ≤ |cEll ell| := abs_nonneg _
  have : (0 : ℚ) ≤ ∏ p ∈ ell.primeFactors, ((p : ℚ) + 2) + 1 := by linarith
  exact mul_nonneg habs this

/-- **`abs_Kell_le`.**  `KERNEL-PROVED`.  The local kernel is bounded uniformly in the window
variable `s` and in the outer variable `z`. -/
theorem abs_Kell_le {ell : ℕ} (hell : ell ≠ 0) (s z : ℤ) : |Kell ell s z| ≤ Kbound ell := by
  have hmask : |coprimeMask ell (z - s)| ≤ 1 := by
    rw [coprimeMask_eq_indicator hell]
    by_cases h : Int.gcd (ell : ℤ) (z - s) = 1 <;> simp [h]
  have hsub : gcdFactors ell s ⊆ ell.primeFactors := Finset.filter_subset _ _
  have hbrk : |(∏ p ∈ gcdFactors ell s, (2 - (p : ℚ))) - 1|
      ≤ ∏ p ∈ ell.primeFactors, ((p : ℚ) + 2) + 1 := by
    have h1 : |∏ p ∈ gcdFactors ell s, (2 - (p : ℚ))|
        ≤ ∏ p ∈ ell.primeFactors, ((p : ℚ) + 2) := by
      rw [Finset.abs_prod]
      have hstep : ∏ p ∈ gcdFactors ell s, |2 - (p : ℚ)|
          ≤ ∏ p ∈ gcdFactors ell s, ((p : ℚ) + 2) := by
        refine Finset.prod_le_prod (fun p _ => abs_nonneg _) fun p hp => ?_
        have hpp := Nat.prime_of_mem_primeFactors (hsub hp)
        have : (2 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hpp.two_le
        rw [abs_sub_comm, abs_of_nonneg (by linarith)]
        linarith
      refine hstep.trans ?_
      have hone : (1 : ℚ) ≤ ∏ p ∈ ell.primeFactors \ gcdFactors ell s, ((p : ℚ) + 2) := by
        refine Finset.prod_induction _ (fun x => (1 : ℚ) ≤ x) (fun a b ha hb => by nlinarith)
          le_rfl fun p hp => ?_
        have hpp := Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.1 hp).1
        have : (2 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hpp.two_le
        linarith
      have hnn : (0 : ℚ) ≤ ∏ p ∈ gcdFactors ell s, ((p : ℚ) + 2) := by
        refine Finset.prod_nonneg fun p hp => ?_
        have hpp := Nat.prime_of_mem_primeFactors (hsub hp)
        have : (2 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hpp.two_le
        linarith
      have hsd := Finset.prod_sdiff (f := fun p : ℕ => ((p : ℚ) + 2)) hsub
      nlinarith
    calc |(∏ p ∈ gcdFactors ell s, (2 - (p : ℚ))) - 1|
        ≤ |∏ p ∈ gcdFactors ell s, (2 - (p : ℚ))| + |(1 : ℚ)| := abs_sub _ _
      _ ≤ ∏ p ∈ ell.primeFactors, ((p : ℚ) + 2) + 1 := by
          have : |(1 : ℚ)| = 1 := abs_one
          linarith
  rw [Kell, Kbound, abs_mul, abs_mul]
  have h0 : 0 ≤ |cEll ell| := abs_nonneg _
  have hstep : |cEll ell| * |coprimeMask ell (z - s)| ≤ |cEll ell| * 1 :=
    mul_le_mul_of_nonneg_left hmask h0
  have hbrk0 : 0 ≤ |(∏ p ∈ gcdFactors ell s, (2 - (p : ℚ))) - 1| := abs_nonneg _
  calc |cEll ell| * |coprimeMask ell (z - s)|
          * |(∏ p ∈ gcdFactors ell s, (2 - (p : ℚ))) - 1|
      ≤ (|cEll ell| * 1) * |(∏ p ∈ gcdFactors ell s, (2 - (p : ℚ))) - 1| :=
        mul_le_mul_of_nonneg_right hstep hbrk0
    _ ≤ |cEll ell| * (∏ p ∈ ell.primeFactors, ((p : ℚ) + 2) + 1) := by
        rw [mul_one]
        exact mul_le_mul_of_nonneg_left hbrk h0

/-! ## §64.2  Period blocks do not depend on the base point -/

/-- Splitting an integer window at an interior point. -/
lemma sum_Ico_split {f : ℤ → ℚ} {A C B : ℤ} (hAC : A ≤ C) (hCB : C ≤ B) :
    ∑ s ∈ Finset.Ico A C, f s + ∑ s ∈ Finset.Ico C B, f s = ∑ s ∈ Finset.Ico A B, f s := by
  rw [← Finset.sum_union (Finset.Ico_disjoint_Ico_consecutive A C B),
    Finset.Ico_union_Ico_eq_Ico hAC hCB]

/-- Shifting a one-period window by one step does not change its sum. -/
lemma periodBlock_shift_one {f : ℤ → ℚ} {m : ℕ} (hm : 0 < m) (hper : ∀ s, f (s + m) = f s)
    (A : ℤ) :
    ∑ s ∈ Finset.Ico (A + 1) (A + 1 + (m : ℤ)), f s = ∑ s ∈ Finset.Ico A (A + (m : ℤ)), f s := by
  have hm' : (1 : ℤ) ≤ (m : ℤ) := by exact_mod_cast hm
  have h1 : Finset.Ico A (A + (m : ℤ)) = insert A (Finset.Ico (A + 1) (A + (m : ℤ))) := by
    ext s; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
  have h2 : Finset.Ico (A + 1) (A + 1 + (m : ℤ))
      = insert (A + (m : ℤ)) (Finset.Ico (A + 1) (A + (m : ℤ))) := by
    ext s; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
  have hn1 : A ∉ Finset.Ico (A + 1) (A + (m : ℤ)) := by simp
  have hn2 : A + (m : ℤ) ∉ Finset.Ico (A + 1) (A + (m : ℤ)) := by simp
  rw [h1, h2, Finset.sum_insert hn1, Finset.sum_insert hn2, hper A]

/-- **`periodBlock_base_independent`.**  `KERNEL-PROVED`.  A complete period block has the
same sum wherever it starts. -/
theorem periodBlock_base_independent {f : ℤ → ℚ} {m : ℕ} (hm : 0 < m)
    (hper : ∀ s, f (s + m) = f s) (A : ℤ) :
    ∑ s ∈ Finset.Ico A (A + (m : ℤ)), f s = ∑ s ∈ Finset.Ico (0 : ℤ) (m : ℤ), f s := by
  induction A using Int.induction_on with
  | zero => simp
  | succ n ih =>
      have := periodBlock_shift_one hm hper (n : ℤ)
      rw [show ((n : ℤ) + 1) = ((n : ℤ) + 1) from rfl] at this
      rw [show ((n : ℤ) + 1 + (m : ℤ)) = ((n : ℤ) + 1 + (m : ℤ)) from rfl] at this
      rw [this, ih]
  | pred n ih =>
      have := periodBlock_shift_one hm hper (-(n : ℤ) - 1)
      have heq : (-(n : ℤ) - 1 + 1) = -(n : ℤ) := by ring
      rw [heq] at this
      rw [← this, ih]

/-- **`sum_blocks`.**  `KERNEL-PROVED`.  A window consisting of `q` complete periods. -/
theorem sum_blocks {f : ℤ → ℚ} {m : ℕ} (hm : 0 < m) (hper : ∀ s, f (s + m) = f s)
    (A : ℤ) (q : ℕ) :
    ∑ s ∈ Finset.Ico A (A + (m : ℤ) * (q : ℤ)), f s
      = (q : ℚ) * ∑ s ∈ Finset.Ico (0 : ℤ) (m : ℤ), f s := by
  induction q with
  | zero => simp
  | succ q ih =>
      have hsplit : ∑ s ∈ Finset.Ico A (A + (m : ℤ) * (q : ℤ)), f s
            + ∑ s ∈ Finset.Ico (A + (m : ℤ) * (q : ℤ))
                (A + (m : ℤ) * ((q : ℤ) + 1)), f s
          = ∑ s ∈ Finset.Ico A (A + (m : ℤ) * ((q : ℤ) + 1)), f s := by
        refine sum_Ico_split ?_ ?_ <;>
          nlinarith [Int.natCast_nonneg m, Int.natCast_nonneg q,
            (by exact_mod_cast hm : (1:ℤ) ≤ (m:ℤ))]
      have hblock : ∑ s ∈ Finset.Ico (A + (m : ℤ) * (q : ℤ))
            (A + (m : ℤ) * ((q : ℤ) + 1)), f s
          = ∑ s ∈ Finset.Ico (0 : ℤ) (m : ℤ), f s := by
        have hrw : A + (m : ℤ) * ((q : ℤ) + 1) = (A + (m : ℤ) * (q : ℤ)) + (m : ℤ) := by ring
        rw [hrw, periodBlock_base_independent hm hper]
      push_cast
      rw [← hsplit, hblock, ih]
      ring

/-! ## §64.3  The incomplete final period is uniformly bounded -/

lemma abs_sum_Ico_le {f : ℤ → ℚ} {C B : ℤ} {c : ℚ} (hCB : C ≤ B) (hc : ∀ s, |f s| ≤ c) :
    |∑ s ∈ Finset.Ico C B, f s| ≤ ((B - C : ℤ) : ℚ) * c := by
  have hcard : ((Finset.Ico C B).card : ℤ) = B - C := by
    rw [Int.card_Ico]; omega
  have h1 : |∑ s ∈ Finset.Ico C B, f s| ≤ ∑ _s ∈ Finset.Ico C B, c :=
    (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun s _ => hc s)
  rw [Finset.sum_const, nsmul_eq_mul] at h1
  have hcast : ((Finset.Ico C B).card : ℚ) = ((B - C : ℤ) : ℚ) := by exact_mod_cast hcard
  rwa [hcast] at h1

/-- **`perSum_eq_mul_perMean`.**  `KERNEL-PROVED`. -/
theorem perSum_eq_mul_perMean {ell : ℕ} (hell : 0 < ell) (z : ℤ) :
    perSum ell z = (ell : ℚ) * perMean ell z := by
  have hne : (ell : ℚ) ≠ 0 := by positivity
  rw [perMean, mul_div_cancel₀ _ hne]

/-- **`windowSum_centred_bound`.**  `KERNEL-PROVED`.  For each internal conductor, the
window sum differs from its density term by at most one incomplete period. -/
theorem windowSum_centred_bound {ell : ℕ} (hellpos : 0 < ell) (A B z : ℤ) (hAB : A ≤ B) :
    |∑ s ∈ Finset.Ico A B, Kell ell s z - ((B - A : ℤ) : ℚ) * perMean ell z|
      ≤ (ell : ℚ) * (Kbound ell + |perMean ell z|) := by
  have hper : ∀ s : ℤ, Kell ell (s + ell) z = Kell ell s z := fun s => Kell_periodic ell s z
  set L : ℕ := (B - A).toNat with hL
  set q : ℕ := L / ell with hq
  set r : ℕ := L % ell with hr
  have hLqr : L = ell * q + r := (Nat.div_add_mod L ell).symm
  have hrlt : r < ell := Nat.mod_lt _ hellpos
  have hLz : (L : ℤ) = B - A := by omega
  have hz : (L : ℤ) = (ell : ℤ) * (q : ℤ) + (r : ℤ) := by
    exact_mod_cast congrArg (fun n : ℕ => (n : ℤ)) hLqr
  set C : ℤ := A + (ell : ℤ) * (q : ℤ) with hC
  have hAC : A ≤ C := by
    have : (0 : ℤ) ≤ (ell : ℤ) * (q : ℤ) := by positivity
    omega
  have hCB : C ≤ B := by omega
  have hsplit : ∑ s ∈ Finset.Ico A C, Kell ell s z + ∑ s ∈ Finset.Ico C B, Kell ell s z
      = ∑ s ∈ Finset.Ico A B, Kell ell s z :=
    sum_Ico_split hAC hCB
  have hblocks : ∑ s ∈ Finset.Ico A C, Kell ell s z = (q : ℚ) * ((ell : ℚ) * perMean ell z) := by
    rw [hC, sum_blocks hellpos hper A q, sum_Ico_eq_sum_range (fun s : ℤ => Kell ell s z) ell]
    have hps : ∑ i ∈ Finset.range ell, Kell ell (i : ℤ) z = perSum ell z := rfl
    rw [hps, perSum_eq_mul_perMean hellpos]
  have hrem : |∑ s ∈ Finset.Ico C B, Kell ell s z| ≤ ((B - C : ℤ) : ℚ) * Kbound ell :=
    abs_sum_Ico_le hCB (fun s => abs_Kell_le (by omega) s z)
  have hBC : ((B - C : ℤ) : ℚ) = (r : ℚ) := by
    have : B - C = (r : ℤ) := by omega
    rw [this]; norm_num
  have hBA : ((B - A : ℤ) : ℚ) = (ell : ℚ) * (q : ℚ) + (r : ℚ) := by
    have hBA' : B - A = (ell : ℤ) * (q : ℤ) + (r : ℤ) := by omega
    rw [hBA']; push_cast; ring
  have hdiff : ∑ s ∈ Finset.Ico A B, Kell ell s z - ((B - A : ℤ) : ℚ) * perMean ell z
      = ∑ s ∈ Finset.Ico C B, Kell ell s z - (r : ℚ) * perMean ell z := by
    rw [← hsplit, hblocks, hBA]
    ring
  rw [hBC] at hrem
  rw [hdiff]
  have hrle : (r : ℚ) ≤ (ell : ℚ) := by exact_mod_cast hrlt.le
  have hr0 : (0 : ℚ) ≤ (r : ℚ) := by positivity
  have hK0 : 0 ≤ Kbound ell := Kbound_nonneg ell
  have hm0 : (0 : ℚ) ≤ |perMean ell z| := abs_nonneg _
  have habs2 : |(r : ℚ) * perMean ell z| = (r : ℚ) * |perMean ell z| := by
    rw [abs_mul, abs_of_nonneg hr0]
  have hstep : |∑ s ∈ Finset.Ico C B, Kell ell s z - (r : ℚ) * perMean ell z|
      ≤ (r : ℚ) * Kbound ell + (r : ℚ) * |perMean ell z| := by
    refine (abs_sub _ _).trans ?_
    linarith [hrem, habs2.le, habs2.ge]
  have hfin : (r : ℚ) * Kbound ell + (r : ℚ) * |perMean ell z|
      ≤ (ell : ℚ) * (Kbound ell + |perMean ell z|) := by nlinarith
  linarith

/-! ## §64.4  Qualitative triviality of the centred target -/

/-- The explicit qualitative budget. -/
def centredBudget : ℚ := ∑ ell ∈ conductorRange, (ell : ℚ) * (Kbound ell + Kbound ell)

/-- The `z`-uniform bound on the complete-period mean. -/
lemma abs_perMean_le {ell : ℕ} (hell : 0 < ell) (z : ℤ) : |perMean ell z| ≤ Kbound ell := by
  have hne : (0 : ℚ) < (ell : ℚ) := by positivity
  have h1 : |perSum ell z| ≤ (ell : ℚ) * Kbound ell := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have : ∑ s ∈ Finset.range ell, |Kell ell (s : ℤ) z| ≤ ∑ _s ∈ Finset.range ell, Kbound ell :=
      Finset.sum_le_sum fun s _ => abs_Kell_le (by omega) _ _
    simpa [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using this
  rw [perMean, abs_div, abs_of_nonneg hne.le, div_le_iff₀ hne]
  linarith [h1]

/-- **`centred_target_satisfiable`.**  `KERNEL-PROVED`.  The density-centred `k = 1` target is
satisfied by an explicit budget: *qualitative* boundedness of the returned finite-conductor
kernel carries no analytic content, because the kernel is a finite sum of periodic kernels
with uniformly bounded atoms.  A *quantitative* budget (as demanded by the ledger) is a
different, still open, question. -/
theorem centred_target_satisfiable : CentredBoundedConductorK1Target centredBudget := by
  intro A B z hAB
  rw [centredBudget]
  have hterm : ∀ ell ∈ conductorRange,
      |∑ s ∈ Finset.Ico A B, Kell ell s z - ((B - A : ℤ) : ℚ) * perMean ell z|
        ≤ (ell : ℚ) * (Kbound ell + Kbound ell) := by
    intro ell hell
    rw [conductorRange, Finset.mem_Icc] at hell
    have hpos : 0 < ell := by omega
    refine (windowSum_centred_bound hpos A B z hAB).trans ?_
    have hle := abs_perMean_le hpos z
    have : (0 : ℚ) ≤ (ell : ℚ) := by positivity
    nlinarith
  have hrw : returnedKernel A B z - ((B - A : ℤ) : ℚ) * meanSumAt z
      = ∑ ell ∈ conductorRange,
          (∑ s ∈ Finset.Ico A B, Kell ell s z - ((B - A : ℤ) : ℚ) * perMean ell z) := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← meanSumAt, returnedKernel,
      show Finset.Icc 1001 5000 = conductorRange from rfl]
    refine congrArg₂ _ (Finset.sum_congr rfl fun ell hell => ?_) rfl
    rw [conductorRange, Finset.mem_Icc] at hell
    exact (Qell_compiler (by omega : 0 < ell) A B z).symm
  rw [hrw]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hterm)

/-- **`centred_target_exists_budget`.**  `KERNEL-PROVED`. -/
theorem centred_target_exists_budget : ∃ b : ℚ, CentredBoundedConductorK1Target b :=
  ⟨centredBudget, centred_target_satisfiable⟩

/-- **`qualitative_boundedness_has_no_analytic_content`.**  `KERNEL-PROVED` firewall.  The
uncentred target is false for every budget while the centred target holds for some budget:
neither statement is an analytic theorem about the source.  The `k = 1` owner is therefore
**not** closed by this module; what remains is the *quantitative* budget question. -/
theorem qualitative_boundedness_has_no_analytic_content :
    (∀ b : ℚ, ¬ BoundedConductorK1Target b) ∧ (∃ b : ℚ, CentredBoundedConductorK1Target b) :=
  ⟨boundedConductorK1Target_unsatisfiable, centred_target_exists_budget⟩

end Effectivity
end Erdos287
