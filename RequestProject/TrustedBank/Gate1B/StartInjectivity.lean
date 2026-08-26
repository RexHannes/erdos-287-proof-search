import Mathlib

/-!
# Gate 1B — same-start injectivity (live) versus mixed-start (dead)

Two facts are banked, and their difference is the whole point.

* `sameStart_injective`: if the interval length `T` is at most the modulus `u`, then
  `n ↦ n + θ (mod u)` is injective on an interval of length `T` **for a fixed shift θ**.
  This proves `SAME_START_SD45_DIAGONAL` and nothing more.

* `mixedStart_not_diagonal`: with **two different shifts** the same hypothesis `T < u`
  does *not* force `n = n'`.  Consequently `MIXED_START_SD45_DEAD` is **not** a
  consequence of same-start injectivity, and the mixed-start problem stays **OPEN**.
-/

namespace TrustedBank
namespace Gate1B

/-- **Same-start injectivity.**  For a fixed shift `θ` and an interval `[a, a+T)` with
`T ≤ u`, the residues `n + θ (mod u)` are pairwise distinct. -/
theorem sameStart_injective {u T a theta n n' : ℕ} (hT : T ≤ u)
    (hn : n ∈ Finset.Ico a (a + T)) (hn' : n' ∈ Finset.Ico a (a + T))
    (h : Nat.ModEq u (n + theta) (n' + theta)) : n = n' := by
  simp only [Finset.mem_Ico] at hn hn'
  have hmod : Nat.ModEq u n n' := Nat.ModEq.add_right_cancel' theta h
  rcases le_total n n' with hle | hle
  · have hdvd : u ∣ n' - n := (Nat.modEq_iff_dvd' hle).mp hmod
    have hlt : n' - n < u := by omega
    have := Nat.eq_zero_of_dvd_of_lt hdvd
    rcases Nat.eq_zero_or_pos (n' - n) with h0 | hpos
    · omega
    · exact absurd (this hlt) (by omega)
  · have hdvd : u ∣ n - n' := (Nat.modEq_iff_dvd' hle).mp hmod.symm
    have hlt : n - n' < u := by omega
    rcases Nat.eq_zero_or_pos (n - n') with h0 | hpos
    · omega
    · exact absurd (Nat.eq_zero_of_dvd_of_lt hdvd hlt) (by omega)

/-- The same statement in the `%`-form used in the source bookkeeping. -/
theorem sameStart_injective_mod {u T a theta n n' : ℕ} (hT : T ≤ u)
    (hn : n ∈ Finset.Ico a (a + T)) (hn' : n' ∈ Finset.Ico a (a + T))
    (h : (n + theta) % u = (n' + theta) % u) : n = n' :=
  sameStart_injective hT hn hn' h

/-- **Mixed-start is not diagonal.**  With `u = 10`, `T = 3`, interval `[0,3)` and the
two *different* shifts `θ = 5`, `θ' = 4`, the points `n = 0 ≠ 1 = n'` collide modulo
`u`.  So `T < u` alone does **not** force a cross-start diagonal. -/
theorem mixedStart_not_diagonal :
    ∃ u T a theta theta' n n' : ℕ,
      T < u ∧ n ∈ Finset.Ico a (a + T) ∧ n' ∈ Finset.Ico a (a + T) ∧ n ≠ n' ∧
        (n + theta) % u = (n' + theta') % u := by
  refine ⟨10, 3, 0, 5, 4, 0, 1, by norm_num, by decide, by decide, by decide, by decide⟩

/-- A second mixed-start collision, at distance `2` inside the window. -/
theorem mixedStart_not_diagonal' :
    ∃ u T a theta theta' n n' : ℕ,
      T < u ∧ n ∈ Finset.Ico a (a + T) ∧ n' ∈ Finset.Ico a (a + T) ∧ n ≠ n' ∧
        (n + theta) % u = (n' + theta') % u :=
  ⟨7, 3, 2, 1, 6, 2, 4, by norm_num, by decide, by decide, by decide, by decide⟩

end Gate1B
end TrustedBank
