import Mathlib.Tactic
import RequestProject.Erdos287.ResearchBankV15.ZerothMomentContract
import RequestProject.Erdos287.ResearchBankV15.BombieriVinogradovProvider

/-!
# Erdős #287 — Research Bank V15 §B10(b): the first-moment contract

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

Exact finite algebra (proved):

* `card_primeSet` — `#{i : L_i(t) prime} = ∑_i 1[L_i(t) prime]`;
* `S1_expansion` — `S1 = ∑_i ∑_{d,e} λ_d λ_e · countPrime(i, d, e)`;
* `L_modEq` — **complete AP modulus**: `t ≡ r (mod W0 q)` implies
  `L_i(t) ≡ L_i(r) (mod a_i · W0 · q)`; the modulus is `firstMomentModulus = a_i W0 q`, not `q`;
* `mainS1` — the main term, with `φ(a_i W0 q)` and the number of reduced hitting residues;
* `S1_split` — `S1 = mainS1 + errS1` (exact).

Analytic inputs (explicit, never constructed):

* `BVTransfer` — **visibly a function of `OrdinaryBVProvider`**: from the ordinary
  Bombieri–Vinogradov estimate, eventually `|errS1 / N_X| ≤ η`;
* `S1MainTermProvider` — eventually `μ_F − η ≤ mainS1 / N_X`.

`s1_contract` takes the `OrdinaryBVProvider` as an explicit argument.
-/

namespace Erdos287
namespace ResearchBankV15
namespace FirstMomentContract

open Finset
open ResearchBankV14 ResearchBankV14.BalancedKernelParameters
open ResearchBankV14.ConditionalAsymptoticImplication ResearchBankV14.ContactAnnulus
open FixedAffineSource MobiusCoefficients CompleteLCMModulus Normalization ZerothMomentContract
open BombieriVinogradovProvider

variable (src : SourceData)

open Classical in
theorem card_primeSet (t : ℕ) :
    ((primeSet tuple t).card : ℝ) = ∑ i, if (L i t).Prime then (1 : ℝ) else 0 := by
  unfold primeSet
  rw [Finset.card_filter]
  push_cast
  rfl

open Classical in
/-- `#{t ∈ window : Hit d e t, L_i(t) prime}`. -/
noncomputable def countPrime (i : Fin K) (M : ℕ) (d e : Fin K → ℕ) : ℕ :=
  ((window tuple M).filter fun t => Hit src d e t ∧ (L i t).Prime).card

/-- **`S1` square expansion.** -/
theorem S1_expansion (M : ℕ) :
    S1 tuple (weightSystem src) M =
      ∑ i, ∑ d ∈ src.D M, ∑ e ∈ src.D M,
        lamM src M d * lamM src M e * (countPrime src i M d e : ℝ) := by
  classical
  unfold S1
  have : ∀ t, (weightSystem src).w M t * ((primeSet tuple t).card : ℝ) =
      ∑ i, weight src M t * (if (L i t).Prime then (1 : ℝ) else 0) := fun t => by
    rw [card_primeSet, Finset.mul_sum]; rfl
  simp_rw [this]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [weighted_expansion]
  refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun e _ => ?_
  congr 1
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one, Finset.filter_filter]
  rfl

/-- **Complete AP modulus**: congruence mod `W0 q` lifts to congruence of `L_i` mod `a_i W0 q`. -/
theorem L_modEq (i : Fin K) (d e : Fin K → ℕ) {t r : ℕ}
    (h : t ≡ r [MOD src.W0 * completeModulus d e]) :
    L i t ≡ L i r [MOD firstMomentModulus fixedSlopes src.W0 d e i] := by
  unfold L firstMomentModulus
  rw [mul_assoc]
  exact (Nat.ModEq.mul_left' (fixedSlopes i) h).add_right 1

open Classical in
/-- Hitting residues `r < W0 q` whose AP `L_i(r) (mod a_i W0 q)` is reduced. -/
noncomputable def reducedResidueCount (i : Fin K) (d e : Fin K → ℕ) : ℕ :=
  Nat.count (fun r => Hit src d e r ∧ Nat.Coprime (L i r) (firstMomentModulus fixedSlopes src.W0 d e i))
    (src.W0 * completeModulus d e)

/-- Primes in `[L_i(lo), L_i(hi)]`. -/
noncomputable def primeWindowCount (i : Fin K) (M : ℕ) : ℝ :=
  (primeCount (L i ⌊((rho : ℚ) : ℝ) * X tuple M⌋₊) : ℝ) - primeCount (L i ⌈X tuple M⌉₊ - 1)

/-- The main term of the `i`-th first moment for the pair `(d, e)`. -/
noncomputable def mainPrime (i : Fin K) (M : ℕ) (d e : Fin K → ℕ) : ℝ :=
  (reducedResidueCount src i d e : ℝ) * primeWindowCount i M /
    (Nat.totient (firstMomentModulus fixedSlopes src.W0 d e i) : ℝ)

/-- The main term of `S1`. -/
noncomputable def mainS1 (M : ℕ) : ℝ :=
  ∑ i, ∑ d ∈ src.D M, ∑ e ∈ src.D M, lamM src M d * lamM src M e * mainPrime src i M d e

/-- The error term of `S1`. -/
noncomputable def errS1 (M : ℕ) : ℝ :=
  ∑ i, ∑ d ∈ src.D M, ∑ e ∈ src.D M,
    lamM src M d * lamM src M e * ((countPrime src i M d e : ℝ) - mainPrime src i M d e)

/-- **`S1 = mainS1 + errS1`** (exact). -/
theorem S1_split (M : ℕ) : S1 tuple (weightSystem src) M = mainS1 src M + errS1 src M := by
  rw [S1_expansion]
  unfold mainS1 errS1
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  ring

/-- **BV transfer** (explicit analytic input, never constructed): *given* the ordinary
Bombieri–Vinogradov provider, the actual first-moment error is eventually `o(N_X)`.  (This is
where BV — uniform over the moving reduced CRT residues modulo `a_i W0 q` — and the divisor
moment enter.) -/
structure BVTransfer : Prop where
  transfer : OrdinaryBVProvider →
    ∀ η > 0, ∃ M₀ : ℕ, ∀ M ≥ M₀, |errS1 src M / NX src M| ≤ η

/-- **Main-term provider for `S1`** (explicit; never constructed). -/
structure S1MainTermProvider (muF : ℝ) : Prop where
  eventual : ∀ η > 0, ∃ M₀ : ℕ, ∀ M ≥ M₀, muF - η ≤ mainS1 src M / NX src M

/-- **The first-moment contract**, visibly conditional on `OrdinaryBVProvider`. -/
theorem s1_contract (bv : OrdinaryBVProvider) (tr : BVTransfer src) {muF : ℝ}
    (hm : S1MainTermProvider src muF) :
    S1Contract (S1 tuple (weightSystem src)) (NX src) muF := by
  intro η hη
  obtain ⟨M1, h1⟩ := hm.eventual (η / 2) (by positivity)
  obtain ⟨M2, h2⟩ := tr.transfer bv (η / 2) (by positivity)
  refine ⟨max M1 M2, fun M hM => ?_⟩
  have e1 := h1 M (le_trans (le_max_left _ _) hM)
  have e2 := (abs_le.1 (h2 M (le_trans (le_max_right _ _) hM))).1
  rw [S1_split, add_div]
  linarith

end FirstMomentContract
end ResearchBankV15
end Erdos287
