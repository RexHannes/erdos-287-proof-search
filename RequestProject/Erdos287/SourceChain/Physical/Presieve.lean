import RequestProject.Erdos287.SourceChain.Physical.PairIdentity

/-!
# Erdős #287 — physical source: the presieve `W = ∏_{p ≤ log log log X} p` and truncation

**ERDŐS #287 REMAINS OPEN.  TAIL-287 IS NOT BANKED.**  `sources/physical_spec.md` §6.

* `physW X = primorial ⌊log log log X⌋` — the actual presieve modulus `W`.
* `wgood_eventually` — for fixed positive, pairwise distinct slopes, the presieve hypotheses
  `PhysData.WGood` hold with `W = physW X` for all sufficiently large `X` ("all prime divisors of
  the fixed slopes and their non-zero differences eventually divide `W`").  This discharges the
  hypothesis `hP` of every packet theorem at the physical `W`.
* `maynardInner_eq_divisors` — the divisor-vector range used in `MaynardInner` is lossless:
  it equals the sum over all `d` with `d_i ∣ L_i(t)` (`d_j = d_ℓ = 1`).
-/

open scoped BigOperators
open Finset

namespace Erdos287.Physical

/-- **The physical presieve modulus** `W = ∏_{p ≤ w} p`, `w = log log log X`. -/
noncomputable def physW (X : ℝ) : ℕ := primorial ⌊Real.log (Real.log (Real.log X))⌋₊

theorem dvd_physW {X : ℝ} {p : ℕ} (hp : p.Prime)
    (hle : (p : ℝ) ≤ Real.log (Real.log (Real.log X))) : p ∣ physW X := by
  unfold physW primorial
  apply Finset.dvd_prod_of_mem
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨Nat.lt_succ_of_le (Nat.le_floor hle), hp⟩

theorem le_logLogLog (B : ℝ) :
    ∀ X ≥ Real.exp (Real.exp (Real.exp B)), B ≤ Real.log (Real.log (Real.log X)) := by
  intro X hX
  have h1 : Real.exp (Real.exp B) ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le (lt_of_lt_of_le (Real.exp_pos _) hX)]; exact hX
  have h2 : Real.exp B ≤ Real.log (Real.log X) := by
    rw [Real.le_log_iff_exp_le (lt_of_lt_of_le (Real.exp_pos _) h1)]; exact h1
  rw [Real.le_log_iff_exp_le (lt_of_lt_of_le (Real.exp_pos _) h2)]; exact h2

/-- **Eventual presieve property**: for positive, pairwise distinct slopes, `W = physW X`
satisfies `WGood` for every `X ≥ exp(exp(exp(∑ a_i)))`. -/
theorem wgood_eventually (P : PhysData) (ha : ∀ i, 0 < P.a i) (hinj : Function.Injective P.a) :
    ∃ X0 : ℝ, ∀ X ≥ X0, ({ P with W := physW X } : PhysData).WGood := by
  set B : ℕ := ∑ i, P.a i
  refine ⟨Real.exp (Real.exp (Real.exp B)), fun X hX => ?_⟩
  have hB := le_logLogLog (B : ℝ) X hX
  have hle : ∀ i, P.a i ≤ B := fun i =>
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  refine ⟨ha, primorial_pos _, ?_, ?_⟩
  · intro i p hp hpi
    apply dvd_physW hp
    have := Nat.le_of_dvd (ha i) hpi
    have : (p : ℝ) ≤ B := by exact_mod_cast this.trans (hle i)
    linarith
  · intro i i' hii p hp hpd
    apply dvd_physW hp
    have hne : (P.a i : ℤ) - P.a i' ≠ 0 := by
      intro h; apply hii; apply hinj; exact_mod_cast (sub_eq_zero.1 h)
    have h1 : p ∣ ((P.a i : ℤ) - P.a i').natAbs := Int.natCast_dvd.mp hpd
    have h2 := Nat.le_of_dvd (Int.natAbs_pos.2 hne) h1
    have h3 : ((P.a i : ℤ) - P.a i').natAbs ≤ B := by
      have := hle i; have := hle i'; omega
    have : (p : ℝ) ≤ B := by exact_mod_cast h2.trans h3
    linarith

namespace PhysData

variable {P : PhysData}

/-- The truncation `d_i ≤ Dmax` in `MaynardInner` is lossless. -/
theorem maynardInner_eq_divisors (j l : Fin P.k) {t : ℕ} (ht : t ∈ P.Tset) :
    P.MaynardInner j l t = ∑ d ∈ (Fintype.piFinset fun i => (P.L i t).divisors).filter
      (fun d => d j = 1 ∧ d l = 1), P.omega d := by
  classical
  unfold MaynardInner
  have htm : t ≤ P.tMax := by
    have := (Finset.mem_filter.1 ht).1; rw [Finset.mem_range] at this; omega
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext d
  simp only [Dvec, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_Icc, Nat.mem_divisors]
  have hL0 : ∀ i, P.L i t ≠ 0 := fun i => by unfold L; omega
  have hLle : ∀ i, P.L i t ≤ P.Dmax := by
    intro i
    unfold L Dmax
    have h1 : P.a i ≤ ∑ i, P.a i :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    have := Nat.mul_le_mul h1 htm
    omega
  constructor
  · rintro ⟨⟨-, hj, hl⟩, hd⟩
    exact ⟨fun i => ⟨hd i, hL0 i⟩, hj, hl⟩
  · rintro ⟨hd, hj, hl⟩
    refine ⟨⟨fun i => ⟨Nat.pos_of_ne_zero (fun h => hL0 i (by
      have := (hd i).1; rw [h] at this; exact zero_dvd_iff.1 this)), (Nat.le_of_dvd
        (Nat.pos_of_ne_zero (hL0 i)) (hd i).1).trans (hLle i)⟩, hj, hl⟩, fun i => (hd i).1⟩

end PhysData

end Erdos287.Physical
