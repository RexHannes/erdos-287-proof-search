import RequestProject.Erdos287.ResearchBankV14.CompilerApplication

/-!
# Erdős #287 — Research Bank V15 §B1: the fixed actual affine source

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

The source is the fixed admissible affine system `L_i(t) = a_i t + 1`, `i ∈ Fin K`,
`K = 2^4170`, produced by V14: `a = CompilerApplication.compilerTuple.a`.  It is a single
constant (`fixedSlopes`); every V15 theorem is about this one tuple — nothing is quantified
uniformly over compiler outputs.

* `L i t = a_i t + 1`;
* `Admissible` — for every prime `p` some `t` makes every `L_i(t)` prime to `p`;
  `fixed_admissible` (take `t ≡ 0 (mod p)`, where every `L_i ≡ 1`);
* `fixed_slopes_ge` — `a_i ≥ 1000`;
* `fixed_edge_identity` — the V14 edge identity `gcd(a_u, a_v) = a_v − a_u` on oriented edges.
-/

namespace Erdos287
namespace ResearchBankV15
namespace FixedAffineSource

open ResearchBankV14 ResearchBankV14.BalancedKernelParameters
open ResearchBankV14.ConditionalAsymptoticImplication ResearchBankV14.CompilerApplication

/-- The fixed tuple (from V14). -/
noncomputable abbrev tuple : FixedTuple (Fin K) := compilerTuple

/-- The fixed slopes `a_i`. -/
noncomputable def fixedSlopes (i : Fin K) : ℕ := tuple.a i

/-- The affine forms `L_i(t) = a_i t + 1`. -/
noncomputable def L (i : Fin K) (t : ℕ) : ℕ := fixedSlopes i * t + 1

/-- Admissibility of an affine system `a_i t + 1`. -/
def Admissible {ι : Type*} (a : ι → ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ t : ℕ, ∀ i, ¬ p ∣ a i * t + 1

/-- Every system `a_i t + 1` is admissible (`t = 0`). -/
theorem admissible_of_affine_one {ι : Type*} (a : ι → ℕ) : Admissible a := by
  intro p hp
  refine ⟨0, fun i h => ?_⟩
  simp only [mul_zero, zero_add, Nat.dvd_one] at h
  exact hp.one_lt.ne' h

/-- **The fixed source is admissible.** -/
theorem fixed_admissible : Admissible fixedSlopes := admissible_of_affine_one _

theorem fixed_slopes_ge (i : Fin K) : 1000 ≤ fixedSlopes i := tuple.a_ge i

theorem fixed_edge_identity {u v : Fin K} (h : OE fixedSlopes tuple.cell u v) :
    Nat.gcd (fixedSlopes u) (fixedSlopes v) = fixedSlopes v - fixedSlopes u :=
  tuple.edge_gcd u v h.1 h.2

theorem L_pos (i : Fin K) (t : ℕ) : 0 < L i t := Nat.succ_pos _

end FixedAffineSource
end ResearchBankV15
end Erdos287
