import RequestProject.Defs

/-!
# A cheap sufficient criterion for `ForbiddenPP`

`ForbiddenPP M p a w L` asks, among other things, that every nonempty subset sum
`∑_{j ∈ J} L / j` with `J ⊆ {1, …, w}` be prime to `p`.  Enumerating the `2 ^ w` subsets is out of
the question for `w = 40`.

Taking `L = w !` makes this trivial: every such sum is at least `1` and at most `w * w !`, so as
soon as `w * w ! < p` it lies strictly between `0` and `p` and cannot be divisible by `p`.
-/

namespace Erdos287

open Finset

/--
If `p` is a prime with `w * w ! < p`, and the multiplier window at `M` for `p ^ a` is at most
`w`, then `p ^ a` is a forbidden prime power at `M`, certified with `L = w !`.
-/
theorem forbiddenPP_of_factorial_bound {M p a w : ℕ} (hp : p.Prime) (ha : 0 < a)
    (hw : 1 ≤ w) (hM : M < (w + 1) * p ^ a) (hbig : w * Nat.factorial w < p) :
    ForbiddenPP M p a w (Nat.factorial w) := by
  have hfac0 : 0 < Nat.factorial w := Nat.factorial_pos w
  have hfacle : Nat.factorial w ≤ w * Nat.factorial w := Nat.le_mul_of_pos_left _ (by omega)
  have hpfac : ¬ p ∣ Nat.factorial w := by
    intro hdvd
    have := Nat.le_of_dvd hfac0 hdvd
    omega
  refine ⟨hp, ha, hM, hfac0, ?_, hpfac, ?_⟩
  · intro j hj
    rw [Finset.mem_Icc] at hj
    exact Nat.dvd_factorial (by omega) hj.2
  · intro J hJ hJne
    rw [Finset.mem_powerset] at hJ
    -- the subset sum is positive
    have hpos : 0 < ∑ j ∈ J, Nat.factorial w / j := by
      refine Finset.sum_pos (fun j hj => ?_) hJne
      have hj' := Finset.mem_Icc.1 (hJ hj)
      exact Nat.div_pos (Nat.le_of_dvd hfac0 (Nat.dvd_factorial (by omega) hj'.2)) (by omega)
    -- and it is smaller than `p`
    have hterm : ∀ j ∈ J, Nat.factorial w / j ≤ Nat.factorial w := fun j _ =>
      Nat.div_le_self _ _
    have hcard : J.card ≤ w := by
      have := Finset.card_le_card hJ
      simpa [Nat.card_Icc] using this
    have hsum : ∑ j ∈ J, Nat.factorial w / j ≤ w * Nat.factorial w := by
      calc ∑ j ∈ J, Nat.factorial w / j ≤ ∑ _j ∈ J, Nat.factorial w := Finset.sum_le_sum hterm
        _ = J.card * Nat.factorial w := by rw [Finset.sum_const, smul_eq_mul]
        _ ≤ w * Nat.factorial w := Nat.mul_le_mul_right _ hcard
    intro hdvd
    have := Nat.le_of_dvd hpos hdvd
    omega

end Erdos287
