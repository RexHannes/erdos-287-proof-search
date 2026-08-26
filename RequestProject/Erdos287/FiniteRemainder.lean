import RequestProject.Erdos287.Blocker
import RequestProject.Erdos287.V2SophieFinite
import RequestProject.Erdos287.ProblemStatement

/-!
# Erdős Problem #287 — the finite-remainder certificate engine

A *window certificate* consists of a position `x` and two prime powers
`pu ^ au ∣ x`, `pv ^ av ∣ x + 1` whose windows at the top endpoint `U` are at most `9`
and whose bases exceed the corresponding certified numerator bound `C j`
(`j = ⌊U / p^e⌋`, `C 1 … C 9 = 1, 3, 11, 25, 137, 137, 1019, 7129`).

Such a certificate excludes **an entire interval** `[L, U]` of maxima at once
(`Gap2CE.blocker_window`): for every `M ∈ [L, U]`,

* `⌊M/p^e⌋ ≤ ⌊U/p^e⌋`, so `C ⌊M/p^e⌋ ≤ C ⌊U/p^e⌋ < p` and `primePower_window_exclusion`
  makes both `x` and `x + 1` holes;
* `M ≤ 2x` gives `N ≤ ⌊M/2⌋ ≤ x`, so the two holes lie inside the window `[N, M]`;
* two adjacent holes contradict `holes_isolated`.

This is what turns the per-`M` finite sweep into an *interval* mechanism: a chain of
certificates covers a range of maxima whose length grows geometrically, since each
certificate reaches from `L ≈ x` up to `U = 2x`.
-/

open scoped BigOperators

namespace Erdos287

/-- The certified values of the numerator bound `C` on windows `0 … 9`
(`C 0 ≤ C 1 = 1`, then `1, 3, 11, 25, 137, 137, 1019, 2143, 7129`).  Outside that range
the value is `0`, which makes every threshold test fail — windows `> 9` are never used. -/
def CVal (j : ℕ) : ℕ :=
  if j ≤ 1 then 1
  else if j = 2 then 3
  else if j = 3 then 11
  else if j = 4 then 25
  else if j ≤ 6 then 137
  else if j = 7 then 1019
  else if j = 8 then 2143
  else if j = 9 then 7129
  else 0

/-- `CVal` dominates `C` on windows `≤ 9`. -/
theorem C_le_CVal {j : ℕ} (hj : j ≤ 9) : C j ≤ (CVal j : ℤ) := by
  interval_cases j
  · exact le_trans (C_mono (by norm_num)) (by rw [C_one]; norm_num [CVal])
  · rw [C_one]; norm_num [CVal]
  · rw [C_two]; norm_num [CVal]
  · rw [C_three]; norm_num [CVal]
  · rw [C_four]; norm_num [CVal]
  · rw [C_five]; norm_num [CVal]
  · rw [C_six]; norm_num [CVal]
  · rw [C_seven]; norm_num [CVal]
  · rw [C_eight]; norm_num [CVal]
  · rw [C_nine]; norm_num [CVal]

/-- **Window exclusion from a top endpoint.**  If the window of `p ^ e` at `U` is at most
`9` and `CVal` of that window is below `p`, then `p ^ e` is an excluded prime power for
*every* `M ≤ U`. -/
theorem excludedPP_of_window_le {M U p e : ℕ} (hp : p.Prime) (he : 1 ≤ e) (hMU : M ≤ U)
    (hw : U / p ^ e ≤ 9) (hC : CVal (U / p ^ e) < p) : ExcludedPP M (p ^ e) :=
  ⟨p, e, hp, he, rfl,
    lt_of_le_of_lt (le_trans (C_mono (Nat.div_le_div_right hMU)) (C_le_CVal hw))
      (by exact_mod_cast hC)⟩

namespace Gap2CE

variable (ce : Gap2CE)

/-- **Interval blocker.**  A window certificate `(x, pu^au, pv^av, L, U)` refutes every
gap-`≤2` counterexample whose maximum lies in `[L, U]`. -/
theorem blocker_window {x pu au pv av L U : ℕ}
    (hpu : pu.Prime) (hpv : pv.Prime) (hau : 1 ≤ au) (hav : 1 ≤ av)
    (hdu : pu ^ au ∣ x) (hdv : pv ^ av ∣ (x + 1))
    (hwu : U / pu ^ au ≤ 9) (hcu : CVal (U / pu ^ au) < pu)
    (hwv : U / pv ^ av ≤ 9) (hcv : CVal (U / pv ^ av) < pv)
    (hUx : U ≤ 2 * x) (hxL : x + 1 ≤ L)
    (h1 : L ≤ ce.M) (h2 : ce.M ≤ U) : False := by
  have hexcu : ExcludedPP ce.M (pu ^ au) := excludedPP_of_window_le hpu hau h2 hwu hcu
  have hexcv : ExcludedPP ce.M (pv ^ av) := excludedPP_of_window_le hpv hav h2 hwv hcv
  have hM2 : 2 ≤ ce.M := by omega
  have hN : ce.N ≤ ce.M / 2 := ce.halfRange_min_le hM2
  have hNx : ce.N ≤ x := by omega
  exact ce.excludedPP_blockerPair hNx (by omega) hexcu hexcv hdu hdv

end Gap2CE

end Erdos287
