import RequestProject.Erdos287.AnchoredV4.EntryColumns

/-!
# Anchored V4 — the finite global transition system

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

A `TransitionSystem` is the finite global constraint system attached to the ENTRY transition
problem: a finite set of physical positions, a finite set of active prime-power components with
their moduli, the exact integer effect of each position on each component, and the exact target
correction of each component.  A *solution* is a set of positions whose total effect hits every
component target simultaneously — the system is treated globally and is **never** split into
independently repaired rows unless the split is proved (see `solves_of_independent_repairs`, which
states exactly when a split is legitimate).

Proved here:

* `solves_of_independent_repairs` — a sufficient condition (disjoint, single-component repairs);
* `unsolvable_of_common_divisor` — the exact dual/congruence obstruction certificate;
* `subsetSum_gcd_one_unsolvable` — a finite witness that `gcd = 1` (full lattice) does **not**
  imply a `0/1` solution, so global column surjectivity fails in the general model.
-/

open scoped BigOperators

namespace Erdos287
namespace AnchoredV4

/-- The finite global transition system. -/
structure TransitionSystem where
  /-- candidate physical positions -/
  positions : Finset ℕ
  /-- active prime-power components -/
  components : Finset ℕ
  /-- the modulus of each active component -/
  modulus : ℕ → ℕ
  /-- the exact integer effect of a position on a component -/
  effect : ℕ → ℕ → ℤ
  /-- the exact required correction of each component -/
  target : ℕ → ℤ

namespace TransitionSystem

variable (T : TransitionSystem)

/-- A set of positions solves the system when every component equation holds exactly. -/
def Solves (S : Finset ℕ) : Prop :=
  S ⊆ T.positions ∧
    ∀ c ∈ T.components, (T.modulus c : ℤ) ∣ (∑ n ∈ S, T.effect n c) - T.target c

/-- The system is solvable. -/
def Solvable : Prop := ∃ S, T.Solves S

variable {T}

/-- **Legitimate split.**  If every component has its own repair block, the blocks are pairwise
disjoint, and a block has no effect on the other components, then their union solves the whole
system.  This is the *only* rowwise reduction used in V4; the V3 firewall against assuming rowwise
neutrality is respected because the hypotheses here are explicit. -/
theorem solves_of_independent_repairs (rep : ℕ → Finset ℕ)
    (hsub : ∀ c ∈ T.components, rep c ⊆ T.positions)
    (hdisj : ∀ c ∈ T.components, ∀ c' ∈ T.components, c ≠ c' → Disjoint (rep c) (rep c'))
    (hzero : ∀ c ∈ T.components, ∀ c' ∈ T.components, c ≠ c' → ∀ n ∈ rep c', T.effect n c = 0)
    (hhit : ∀ c ∈ T.components,
      (T.modulus c : ℤ) ∣ (∑ n ∈ rep c, T.effect n c) - T.target c) :
    T.Solves (T.components.biUnion rep) := by
  classical
  refine ⟨Finset.biUnion_subset.2 hsub, ?_⟩
  intro c hc
  have hsum : ∑ n ∈ T.components.biUnion rep, T.effect n c = ∑ n ∈ rep c, T.effect n c := by
    rw [Finset.sum_biUnion (fun a ha b hb hab => hdisj a ha b hb hab)]
    rw [Finset.sum_eq_single c]
    · intro c' hc' hne
      refine Finset.sum_eq_zero ?_
      intro n hn
      exact hzero c hc c' hc' (Ne.symm hne) n hn
    · intro hcc
      exact absurd hc hcc
  rw [hsum]
  exact hhit c hc

/-- **Dual obstruction certificate.**  If some divisor `d` of a component modulus divides every
position effect on that component but not the target, the whole system is unsolvable.  This is the
exact form of a "nontrivial dual character / resonance" obstruction. -/
theorem unsolvable_of_common_divisor {c d : ℕ} (hc : c ∈ T.components)
    (hdm : (d : ℤ) ∣ (T.modulus c : ℤ))
    (hdeff : ∀ n ∈ T.positions, (d : ℤ) ∣ T.effect n c)
    (hdt : ¬ ((d : ℤ) ∣ T.target c)) : ¬ T.Solvable := by
  rintro ⟨S, hS, hsolve⟩
  have h1 : (d : ℤ) ∣ ∑ n ∈ S, T.effect n c :=
    Finset.dvd_sum fun n hn => hdeff n (hS hn)
  have h2 : (d : ℤ) ∣ (∑ n ∈ S, T.effect n c) - T.target c :=
    dvd_trans hdm (hsolve c hc)
  exact hdt (by simpa using h1.sub h2)

end TransitionSystem

/-! ## Route A obstruction: full lattice does not mean `0/1` surjectivity -/

/-- The two-position system with effects `2` and `3` modulo `7`, target `1`. -/
def gcdWitnessSystem : TransitionSystem where
  positions := {1, 2}
  components := {0}
  modulus := fun _ => 7
  effect := fun n _ => if n = 1 then 2 else 3
  target := fun _ => 1

/-- **Firewall (Route A).**  The column effects `2, 3` generate the full lattice modulo `7`
(`gcd (2,3) = 1`), yet no set of positions solves the system: the image of the `0/1` column map is
a proper subset of the lattice coset.  Global column surjectivity is therefore **false** in the
general model, and must not be assumed for ENTRY. -/
theorem gcdWitnessSystem_unsolvable : ¬ gcdWitnessSystem.Solvable := by
  rintro ⟨S, hS, hsolve⟩
  have hmem : S ∈ ({1, 2} : Finset ℕ).powerset := Finset.mem_powerset.2 hS
  have h := hsolve 0 (by decide)
  fin_cases hmem <;> revert h <;> decide

/-- The gcd of the two columns really is `1`: the obstruction is not a gcd obstruction. -/
theorem gcdWitnessSystem_gcd_one : Nat.gcd 2 3 = 1 := by decide


/-! ## Reduction of the descent supply to an exact congruence

The descent supply owner is not an independent analytic mystery: a descent move exists as soon as
a guarded, fresh, even set of positions solves the exact integer congruence produced by
`descent_congruence_iff`.  This is the precise sense in which `SAFE_DESCENT_SUPPLY` is a
subset-sum problem over the guarded reservoir, and it is the theorem that connects the absorber
technology of `FourierAbsorber.lean` to the descent of `PrimePowerDescent.lean`. -/

/-- **Descent supply from a congruence solution.**  All hypotheses are explicit finite data. -/
theorem descentStep_of_congruence {aM M Q : ℕ} {mask : Finset ℕ} (s : DescentState aM M Q mask)
    {h' : ℕ} (hh' : h' < s.height) (E : Finset ℕ)
    (hEsub : E ⊆ Finset.Ioo aM M) (hEfresh : Disjoint E s.Z)
    (hEeven : ∀ c ∈ E, Even c)
    (hEnb : ∀ c ∈ E, ∀ j, (j = c + 1 ∨ j + 1 = c) → normHeight j ≤ Q)
    (hEdvd : ∀ n ∈ E, n ≠ 0 ∧ n ∣ 2 * L s.height)
    (hcong : ((2 * L s.height) / (2 * L h') : ℕ) ∣
      (numeratorAt (2 * L s.height) s.value - ∑ n ∈ E, (weight (2 * L s.height) n : ℤ)).natAbs) :
    Nonempty (DescentStep aM M Q mask s) := by
  set P := 2 * L s.height with hPdef
  set P' := 2 * L h' with hP'def
  have hP'P : P' ∣ P := mul_dvd_mul_left 2 (L_dvd_L (le_of_lt hh'))
  have hP'pos : 0 < P' := by
    have := L_pos h'
    omega
  have hPpos : 0 < P := by
    have := L_pos s.height
    omega
  have hr : P = (P / P') * P' := (Nat.div_mul_cancel hP'P).symm
  have hrpos : 0 < P / P' := Nat.div_pos (Nat.le_of_dvd hPpos hP'P) hP'pos
  have hcongZ : ((P / P' : ℕ) : ℤ) ∣
      numeratorAt P s.value - ∑ n ∈ E, (weight P n : ℤ) := by
    rcases Int.natAbs_eq (numeratorAt P s.value - ∑ n ∈ E, (weight P n : ℤ)) with heq | heq
    · rw [heq]; exact_mod_cast Int.natCast_dvd_natCast.2 hcong
    · rw [heq]
      exact dvd_neg.2 (by exact_mod_cast Int.natCast_dvd_natCast.2 hcong)
  have hhit : (wordSum (Finset.Icc aM M) (s.Z ∪ E)).den ∣ P' := by
    have hval : wordSum (Finset.Icc aM M) (s.Z ∪ E) = s.value - recipSum E :=
      wordSum_union (hEsub.trans Finset.Ioo_subset_Icc_self) hEfresh
    rw [hval]
    exact (descent_congruence_iff hrpos hr s.den_ok hEdvd (by omega)).2 hcongZ
  exact ⟨{ centers := E
           newHeight := h'
           centers_subset := hEsub
           centers_fresh := hEfresh
           centers_even := hEeven
           centers_nb_low := hEnb
           newHeight_lt := hh'
           component_hit := hhit }⟩

end AnchoredV4
end Erdos287
