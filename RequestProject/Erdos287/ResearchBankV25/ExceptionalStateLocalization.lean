import RequestProject.Erdos287.ResearchBankV25.FixedModulusCentering
import RequestProject.Erdos287.ResearchBankV25.FixedResidueEnergy

/-!
# Erdős #287 — Research Bank V25 §3.4: exceptional-state localization

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

The fixed exceptional modulus `f` stays on the original variable.  The localized pieces are
`α_u(n) = α(n) 1_{n ≡ u (f)}`, `u ∈ (ℤ/f)^×`.

**LEAN BANK.**

* `alphaLoc_partition` — `Σ_{u ∈ G_f} α_u(n) = 1_{(n,f)=1} α(n)`: the localized pieces partition
  the `f`-unit part of `α` exactly;
* `indMod_natCast` / `indCop_natCast` — the integer indicators of §3.1 agree with the `ZMod`
  indicators used in §3.3;
* `sum_delta_eq_Disc` — `Σ_n γ(n) δ(q, a, n) = Δ_γ(q, a)`;
* `sum_localized_delta_eq_Disc` — for `c ≡ u (f)` with `u` a unit,
  `Σ_n γ(n) 1_{n ≡ c (f)} δ(q, a, n) = Δ_{γ_u}(q, a)`.  This is the bridge from the centering
  identity to the conditioned residue energy.

**Firewall.**  No statement here asserts that `α_u` is globally Siegel–Walfisz.
-/

namespace Erdos287
namespace ResearchBankV25
namespace ExceptionalStateLocalization

open Finset FixedModulusCentering FixedResidueEnergy

/-- **The localized pieces partition the `f`-unit part** (LEAN BANK). -/
theorem alphaLoc_partition {f : ℕ} [NeZero f] (α : ℕ → ℂ) (n : ℕ) :
    ∑ u : (ZMod f)ˣ, alphaLoc α u n = if Nat.Coprime n f then α n else 0 := by
  unfold alphaLoc
  simp only [coprime_iff_isUnit (q := f)]
  exact sum_units_ite (n : ZMod f) (α n)

theorem indMod_natCast (q : ℕ) (a : ℤ) (n : ℕ) :
    indMod q a n = if (n : ZMod q) = (a : ZMod q) then 1 else 0 := by
  unfold indMod
  have : ((n : ℤ) : ZMod q) = (a : ZMod q) ↔ (n : ℤ) ≡ a [ZMOD (q : ℤ)] :=
    ZMod.intCast_eq_intCast_iff _ _ _
  push_cast at this
  by_cases h : (n : ZMod q) = (a : ZMod q)
  · rw [if_pos (this.1 h), if_pos h]
  · rw [if_neg (fun h' => h (this.2 h')), if_neg h]

theorem indCop_natCast (q n : ℕ) : indCop q n = if Nat.Coprime n q then 1 else 0 := by
  unfold indCop
  rw [Int.gcd_natCast_natCast]

/-- **Summed centred indicator = literal discrepancy** (LEAN BANK). -/
theorem sum_delta_eq_Disc (q : ℕ) (a : ℤ) (Ns : Finset ℕ) (γ : ℕ → ℂ) :
    ∑ n ∈ Ns, γ n * ((delta q a n : ℝ) : ℂ) = Disc q Ns γ (a : ZMod q) := by
  unfold delta Disc
  simp only [indMod_natCast, indCop_natCast]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  split_ifs <;> push_cast <;> ring

/-- **Localized summed centred indicator = localized discrepancy** (LEAN BANK). -/
theorem sum_localized_delta_eq_Disc {f : ℕ} (q : ℕ) (c a : ℤ) (u : (ZMod f)ˣ)
    (hcu : (c : ZMod f) = u) (Ns : Finset ℕ) (γ : ℕ → ℂ) :
    ∑ n ∈ Ns, γ n * ((indMod f c n * delta q a n : ℝ) : ℂ) =
      Disc q Ns (alphaLoc γ u) (a : ZMod q) := by
  rw [← sum_delta_eq_Disc]
  refine Finset.sum_congr rfl fun n _ => ?_
  unfold alphaLoc
  rw [indMod_natCast, hcu]
  split_ifs <;> push_cast <;> ring

end ExceptionalStateLocalization
end ResearchBankV25
end Erdos287
