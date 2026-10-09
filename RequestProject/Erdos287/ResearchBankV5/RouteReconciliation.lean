import RequestProject.Erdos287.AnchoredV4
import RequestProject.Erdos287.ResearchBankV5.Routes

/-!
# Research Bank V5 — route reconciliation (proved implications only)

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

This file contains **only proved implications** relating the two routes to the original problem.
It does **not** claim route equivalence, and it does not relate an Anchored V4 `ENTRY` to a
contact-core bad forest in either direction: no such theorem exists.

* `anchoredV4_bridge` — re-export (unchanged) of the Anchored V4 bridge: a final V4 configuration
  (interval word, non-adjacent omissions, selected endpoints, reciprocal sum exactly `1`) is
  literally an Erdős #287 counterexample;
* `contactCore_gateD_bridge` — the **separate** contact-core Gate D bridge: a final contact-core
  configuration (a Boolean selection word on `[N, M]` with isolated holes and both endpoints
  selected, of reciprocal value exactly `1`) is an Erdős #287 counterexample;
* the contrapositives of both;
* `routes_not_claimed_equivalent` — the firewall statement.

Both bridges discharge a bridge obligation **in their own route**.  They coexist; neither implies
the other.
-/

namespace Erdos287
namespace ResearchBankV5
namespace Reconciliation

open Erdos287.AnchoredV4

/-! ## 1.  Anchored V4 bridge (re-exported unchanged) -/

/-- **Anchored V4 bridge.**  Re-export of `Erdos287.AnchoredV4.final_configuration_is_counterexample`;
the V4 layer itself is untouched. -/
theorem anchoredV4_bridge {aM M : ℕ} {Zf : Finset ℕ}
    (haM : 1 < aM) (hZ : Zf ⊆ Finset.Ioo aM M) (hna : NoAdjacent Zf)
    (hval : wordSum (Finset.Icc aM M) Zf = 1) : Erdos287.AnchoredV4.Erdos287Counterexample :=
  final_configuration_is_counterexample haM hZ hna hval

/-- Contrapositive of the V4 bridge. -/
theorem anchoredV4_bridge_contrapositive (hno : ¬ Erdos287.AnchoredV4.Erdos287Counterexample) {aM M : ℕ}
    {Zf : Finset ℕ} (haM : 1 < aM) (hZ : Zf ⊆ Finset.Ioo aM M) (hna : NoAdjacent Zf) :
    wordSum (Finset.Icc aM M) Zf ≠ 1 := fun hval => hno (anchoredV4_bridge haM hZ hna hval)

/-! ## 2.  Contact-core Gate D bridge -/

/-- The denominator set selected by a contact-core Boolean word on the window `[N, M]`. -/
def contactSelection (N M : ℕ) (ε : ℕ → Bool) : Finset ℕ :=
  (Finset.Icc N M).filter (fun n => ε n)

/-- **Contact-core Gate D bridge.**  A final contact-core configuration — a Boolean selection word
on `[N, M]` whose holes are isolated and whose right endpoint is selected — of reciprocal value
exactly `1` is literally an Erdős #287 counterexample.

This is the contact-core route's *own* bridge; it is **not** the Anchored V4 bridge, and neither
implies the other. -/
theorem contactCore_gateD_bridge {N M : ℕ} (hN : 1 < N) (ε : ℕ → Bool)
    (hholes : ∀ n, N ≤ n → n < M → ε n = false → ε (n + 1) = true)
    (hright : ε M = true)
    (hval : recipSum (contactSelection N M ε) = 1) :
    Erdos287.AnchoredV4.Erdos287Counterexample := by
  classical
  refine ⟨contactSelection N M ε, ?_, hval, ?_⟩
  · intro n hn
    have hmem := (Finset.mem_filter.1 hn).1
    have := (Finset.mem_Icc.1 hmem).1
    omega
  · intro n hn
    have hmem := (Finset.mem_filter.1 hn).1
    obtain ⟨hNn, hnM⟩ := Finset.mem_Icc.1 hmem
    rcases eq_or_lt_of_le hnM with heq | hlt
    · left
      intro m hm
      have := (Finset.mem_Icc.1 (Finset.mem_filter.1 hm).1).2
      omega
    · right
      by_cases h1 : ε (n + 1) = true
      · refine ⟨n + 1, ?_, by omega, by omega⟩
        exact Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨by omega, by omega⟩, by simpa using h1⟩
      · have hfalse : ε (n + 1) = false := by
          cases h : ε (n + 1) with
          | false => rfl
          | true => exact absurd h h1
        have hne : n + 1 ≠ M := by
          intro hEq
          rw [hEq, hright] at hfalse
          exact Bool.noConfusion hfalse
        have hlt' : n + 1 < M := by omega
        have h2 : ε (n + 2) = true := hholes (n + 1) (by omega) hlt' hfalse
        refine ⟨n + 2, ?_, by omega, by omega⟩
        exact Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨by omega, by omega⟩, by simpa using h2⟩

/-- The full contact-core final configuration, as the route states it: a window `[N, M]` with
`1 < N ≤ M`, a Boolean selection word with isolated holes, **both** endpoints selected, and
reciprocal value exactly `1`.  (The proof of the bridge does not need the left endpoint
condition; it is retained because it is part of the configuration produced by the route.) -/
structure ContactFinalConfig where
  /-- Left endpoint of the window. -/
  N : ℕ
  /-- Right endpoint of the window. -/
  M : ℕ
  /-- The selection word. -/
  sel : ℕ → Bool
  /-- The window starts above `1`. -/
  hN : 1 < N
  /-- The window is nonempty. -/
  hNM : N ≤ M
  /-- Holes are isolated. -/
  hholes : ∀ n, N ≤ n → n < M → sel n = false → sel (n + 1) = true
  /-- The left endpoint is selected. -/
  hleft : sel N = true
  /-- The right endpoint is selected. -/
  hright : sel M = true
  /-- The configuration has reciprocal value exactly `1`. -/
  hval : recipSum (contactSelection N M sel) = 1

/-- **Gate D, packaged form.**  Every contact-core final configuration yields an Erdős #287
counterexample. -/
theorem ContactFinalConfig.toCounterexample (cfg : ContactFinalConfig) :
    Erdos287.AnchoredV4.Erdos287Counterexample :=
  contactCore_gateD_bridge cfg.hN cfg.sel cfg.hholes cfg.hright cfg.hval

/-- Contrapositive of the contact-core Gate D bridge. -/
theorem contactCore_gateD_bridge_contrapositive
    (hno : ¬ Erdos287.AnchoredV4.Erdos287Counterexample) (cfg : ContactFinalConfig) : False :=
  hno cfg.toCounterexample

/-! ## 3.  Firewall -/

/-- **No route equivalence is asserted.**  Both routes possess a proved bridge to the original
problem; this is the *only* relation between them recorded in this project.  No implication
between an Anchored V4 `ENTRY` and a contact-core bad forest is proved in either direction, and
nothing here lets a status statement in one route move a status in the other. -/
theorem routes_not_claimed_equivalent :
    (∀ (aM M : ℕ) (Zf : Finset ℕ), 1 < aM → Zf ⊆ Finset.Ioo aM M → NoAdjacent Zf →
        wordSum (Finset.Icc aM M) Zf = 1 → Erdos287.AnchoredV4.Erdos287Counterexample) ∧
      (ContactFinalConfig → Erdos287.AnchoredV4.Erdos287Counterexample) :=
  ⟨fun _ _ _ h1 h2 h3 h4 => anchoredV4_bridge h1 h2 h3 h4,
   fun cfg => cfg.toCounterexample⟩

end Reconciliation
end ResearchBankV5
end Erdos287
