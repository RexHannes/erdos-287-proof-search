import RequestProject.Erdos287.PostQSigma.PrimeResonance

/-!
# Erdős #287 — post-`Q_Σ` bank, §30–§32 (V64): the SC-287 firewall

**Status of SC-287: RETIRED.**  This file defines the prime-conductor "Module A" of SC-287
*only* in order to refute it; nothing downstream may use it as a closure hypothesis (and no
downstream file imports it as a hypothesis — see `Ledger.lean`).

## Prime case (fully proved in Lean, no external input)

`PrimeModuleA θ C` asserts `‖A_p(T)‖ ≤ C · p^θ · P` on the V64 physical family
`M = 2p - 1`, `a = ⌊M/4⌋`, `p ≥ 3` prime.  Any universal prime-conductor square-root module
(`θ = 1/2 + ε`) specialises to it.  We prove:

* `abs_A_p_lower` — on the family, `(p/8 - 1) · P ≤ ‖A_p(T)‖`
  (from `A_p = p·#{p ∈ E} - P` and `P ≤ 8 #{p ∈ E}`);
* `prime_moduleA_false` — **for every `θ < 1` and every `C`, `PrimeModuleA θ C` is false.**

In particular the prime-conductor `p^{1/2+o(1)}` module is false on physical sources, and so is
every exponent `θ < 1` (a fortiori every `θ < 2/3`).

## Composite / aggregate case (§32) — NOT formalised here

The V64 composite short-row construction refuting *aggregate absolute-conductor* SC-287 needs
external analytic input (PNT / `θ(x)` asymptotics and a fixed affine-form Selberg upper bound
for `p, 2p ± 1`), which is **not** formalised locally.  It is recorded as
**EXTERNAL MATHEMATICAL INPUT NOT FORMALISED LOCALLY / PAPER-LEVEL**.  Its retirement verdict is
nevertheless already forced for the *prime* module by the theorem below, and the aggregate
SC-287 is marked RETIRED in the ledger on the authority of the V64 audit.
-/

open scoped BigOperators

namespace Erdos287.PostQSigma.SC287

open Erdos287.ExactSource Erdos287.PostQSigma

/-- The V64 family: `a(p) = ⌊(2p-1)/4⌋`. -/
def aP (p : ℕ) : ℕ := (2 * p - 1) / 4
/-- The V64 family: `M(p) = 2p - 1`. -/
def MP (p : ℕ) : ℕ := 2 * p - 1

/-- The prime-conductor block `A_p(T)` of the physical source `(a(p), M(p))`. -/
noncomputable def Ap (p : ℕ) : ℂ :=
  Acond (Omega (aP p) (MP p)) (Bz (aP p) (MP p)) (T (aP p) (MP p) ∅) (W (aP p) (MP p) ∅) p

/-- **RETIRED** prime-conductor Module A of SC-287, restricted to the V64 family.
Defined only to be refuted. -/
def PrimeModuleA (θ C : ℝ) : Prop :=
  ∀ p : ℕ, p.Prime → 3 ≤ p → ‖Ap p‖ ≤ C * (p : ℝ) ^ θ * (Ptot (aP p) (MP p) : ℝ)

lemma Ptot_pos (a M : ℕ) : 0 < Ptot a M := by
  classical
  rw [Ptot]
  apply Finset.card_pos.2
  exact ⟨∅, mem_Omega.2 ⟨Finset.empty_subset _, fun x hx => absurd hx (Finset.notMem_empty x)⟩⟩

/-- **Resonance lower bound** on the V64 family. -/
theorem abs_A_p_lower {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) :
    ((p : ℝ) / 8 - 1) * (Ptot (aP p) (MP p) : ℝ) ≤ ‖Ap p‖ := by
  classical
  obtain ⟨h1, h2, h3, h4⟩ := v64_family_hyp hp3
  have hA := physical_prime_resonance hp h1 h2 h3 h4
  have h8 := Ptot_le_eight_forced (a := aP p) (M := MP p) h2 h3
  set N := ((Omega (aP p) (MP p)).filter (fun E => p ∈ E)).card
  set P := Ptot (aP p) (MP p)
  have hAr : Ap p = (((p : ℝ) * N - P : ℝ) : ℂ) := by
    rw [Ap, show aP p = (2 * p - 1) / 4 from rfl, show MP p = 2 * p - 1 from rfl, hA]
    push_cast; rfl
  rw [hAr, Complex.norm_real, Real.norm_eq_abs]
  have h8' : (P : ℝ) ≤ 8 * N := by exact_mod_cast h8
  have hp0 : (0 : ℝ) ≤ p := by positivity
  calc ((p : ℝ) / 8 - 1) * P = (p : ℝ) * (P / 8) - P := by ring
    _ ≤ (p : ℝ) * N - P := by nlinarith
    _ ≤ |(p : ℝ) * N - P| := le_abs_self _

/-- Large primes beat `C p^θ` for `θ < 1`. -/
lemma exists_large_prime (θ C : ℝ) (hθ : θ < 1) :
    ∃ p : ℕ, p.Prime ∧ 3 ≤ p ∧ C * (p : ℝ) ^ θ < (p : ℝ) / 8 - 1 := by
  have ht := tendsto_rpow_atTop (show 0 < 1 - θ by linarith)
  obtain ⟨X, hX⟩ := Filter.eventually_atTop.1
    (ht.eventually (Filter.eventually_ge_atTop (16 * (|C| + 1))))
  obtain ⟨p, hpge, hp⟩ := Nat.exists_infinite_primes (⌈max X 32⌉₊)
  have hpX : max X 32 ≤ (p : ℝ) := (Nat.ceil_le.1 hpge)
  have hp32 : (32 : ℝ) ≤ p := le_trans (le_max_right _ _) hpX
  have hpos : (0 : ℝ) < p := by linarith
  refine ⟨p, hp, by exact_mod_cast (show (3 : ℝ) ≤ p by linarith), ?_⟩
  have hbig := hX p (le_trans (le_max_left _ _) hpX)
  have hsplit : (p : ℝ) ^ θ * (p : ℝ) ^ (1 - θ) = p := by
    rw [← Real.rpow_add hpos]; simp
  have hθpos : 0 < (p : ℝ) ^ θ := Real.rpow_pos_of_pos hpos θ
  have hC : C * (p : ℝ) ^ θ ≤ |C| * (p : ℝ) ^ θ :=
    mul_le_mul_of_nonneg_right (le_abs_self C) hθpos.le
  have : 16 * ((|C| + 1) * (p : ℝ) ^ θ) ≤ p := by
    calc 16 * ((|C| + 1) * (p : ℝ) ^ θ) = (p : ℝ) ^ θ * (16 * (|C| + 1)) := by ring
      _ ≤ (p : ℝ) ^ θ * (p : ℝ) ^ (1 - θ) := mul_le_mul_of_nonneg_left hbig hθpos.le
      _ = p := hsplit
  nlinarith

/-- **SC-287 prime Module A is false** for every exponent `θ < 1` and every constant `C`. -/
theorem prime_moduleA_false (θ C : ℝ) (hθ : θ < 1) : ¬ PrimeModuleA θ C := by
  intro h
  obtain ⟨p, hp, hp3, hlt⟩ := exists_large_prime θ C hθ
  have hup := h p hp hp3
  have hlow := abs_A_p_lower hp hp3
  have hP : (0 : ℝ) < Ptot (aP p) (MP p) := by exact_mod_cast Ptot_pos _ _
  have : ((p : ℝ) / 8 - 1) * Ptot (aP p) (MP p) ≤ C * (p : ℝ) ^ θ * Ptot (aP p) (MP p) :=
    hlow.trans hup
  nlinarith

/-- The square-root instance: `θ = 1/2 + ε` with `ε < 1/2`. -/
theorem prime_sqrt_moduleA_false (ε C : ℝ) (hε : ε < 1 / 2) : ¬ PrimeModuleA (1 / 2 + ε) C :=
  prime_moduleA_false _ C (by linarith)

/-- Exponents below `2/3` cannot repair the prime module either. -/
theorem prime_two_thirds_moduleA_false (θ C : ℝ) (hθ : θ < 2 / 3) : ¬ PrimeModuleA θ C :=
  prime_moduleA_false θ C (by linarith)

end Erdos287.PostQSigma.SC287
