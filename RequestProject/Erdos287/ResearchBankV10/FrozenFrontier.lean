import RequestProject.Erdos287.ResearchBankV9

/-!
# Erdős #287 — Research Bank V10 §B: the frozen input firewall

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

V10 imports the complete V9 bank and freezes it.  Nothing is reproved: the frozen inputs whose
exact theorems exist in V9 are **re-used directly** (`frozenV9Bank_holds` is a tuple of V9 proof
terms); the others are recorded as frozen research-record rows in the V10 ledger.

`FrozenV9Bank` bundles the exact statements of the following V9 theorems:

* `Gates.gate_margin` — `7/13 − 78/145 = 1/1885` (frozen gate arithmetic);
* `AsraCRT.clean_main_modulus` — rough gcd/lcm algebra (`lcm(B, lcm(D, d)) = BDd` and
  multiplicativity of `φ` under the coprimality hypotheses);
* `AsraZeroMode.centred_kernel_sum_zero` — paired zero-mode algebra (centred kernel sums to `0`);
* `Gates.gate_145_38` — V8/V9 finite graph facts (`α(G(145, 38)) = 39`, `χ_f = 145/39`);
* `Splice.splice` — V9 effective finite-splice logic.

Frozen as **research-record rows only** (no exact theorem of that name exists in V2–V9, so nothing
is claimed as kernel-proved): raw/cut exact joining identities, physical pruning interfaces,
elementary `R10/R00` estimates, and the small-total-modulus BV interface (whose V9 counterpart is
the uninhabited `AsraInterfaces.ExternalRatioBVInput`).

`Erdos287Closed` — the full statement "no Erdős #287 counterexample exists".  It is **never**
proved or assumed in V10/V11.
-/

namespace Erdos287
namespace ResearchBankV10
namespace FrozenFrontier

open ResearchBankV9

/-- The full Erdős #287 statement (never proved or assumed in V10/V11). -/
def Erdos287Closed : Prop := ∀ A : Finset ℕ, ¬ Erdos287Counterexample A

/-- **The frozen V9 bank**: exact statements of re-used V9 theorems. -/
def FrozenV9Bank : Prop :=
  ((7 : ℚ) / 13 - 78 / 145 = 1 / 1885) ∧
  (∀ {B D d : ℕ}, Nat.Coprime B (D * d) → Nat.Coprime D d →
    Nat.lcm B (Nat.lcm D d) = B * D * d ∧
      Nat.totient (B * D * d) = Nat.totient B * Nat.totient D * Nat.totient d) ∧
  (∀ (L g : ℕ) [NeZero g] (w : (ZMod g)ˣ),
    ∑ v : (ZMod g)ˣ, AsraZeroMode.centredKernel L g (if v = w then 1 else 0) = 0) ∧
  (Gates.AlphaEq 145 38 ∧ Gates.ChiFEq 145 38 (145 / 39)) ∧
  (∀ {U M₀ : ℕ}, Splice.FiniteVerifiedThrough U → M₀ ≤ U + 1 →
    Splice.EventualNoCounterexampleFrom M₀ → Erdos287Closed)

/-- **The frozen bank holds**, by direct re-use of the V9 proofs (nothing reproved). -/
theorem frozenV9Bank_holds : FrozenV9Bank :=
  ⟨Gates.gate_margin.1, fun h1 h2 => AsraCRT.clean_main_modulus h1 h2,
    fun L g _ w => AsraZeroMode.centred_kernel_sum_zero L g w, Gates.gate_145_38,
    fun hfin hU hev => Splice.splice hfin hU hev⟩

/-- The frozen splice logic: `Erdos287Closed` is equivalent to the V9 effective finite splice. -/
theorem erdos287Closed_iff_effectiveSplice : Erdos287Closed ↔ Splice.EffectiveFiniteSplice :=
  Splice.effectiveSplice_iff_no_counterexample.symm

end FrozenFrontier
end ResearchBankV10
end Erdos287
