import RequestProject.Erdos287.ResearchBankV22.FirstForbiddenPrefix
import RequestProject.Erdos287.ResearchBankV22.ExceptionalPrimeSet

/-!
# Erdős #287 — Research Bank V22 §5: the small-prime upper sieve

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

* `smallUniverse E u` — the primes `< u` outside the exceptional set `E`;
* `SmallPrimeRosserProvider Psm level` — the FINITE / ALGEBRAIC contract of an upper weight
  `β_sm^+` on the small primes with level `level = x^rho`:
  support in `Psm`, one-bounded, `β(1) = 1`, support below the level, and
  `S_β(n) ≥ 1(no relevant small prime divides n)` (hence `S_β(n) ≥ 0`, `dsum_beta_nonneg`);
* `rosserBeta Psm level` — the ACTUAL ordinary Rosser upper weight of dimension one
  (β = 2): `μ(d) · 1(∀ odd j, p₁⋯p_{j-1} p_j³ ≤ level)`;
* **`rosserSmallProvider`** — the Rosser weight satisfies the contract, kernel-proved from
  first-forbidden-prefix positivity (§4).  So the small-prime upper weight is an actual object,
  constructed without any axiom.

The ANALYTIC input — the normalized cost `F(S) + error` of this weight — is NOT part of this
contract; it is the `RosserScalarProvider` of §10 (EXTERNAL PROVIDER).
-/

namespace Erdos287
namespace ResearchBankV22
namespace SmallPrimeUpperSieve

open Finset RoundedRoughSieve FirstForbiddenPrefix

/-- The small-prime universe: primes `< u` outside `E`. -/
def smallUniverse (E : Finset ℕ) (u : ℕ) : Finset ℕ :=
  (range u).filter fun p => p.Prime ∧ p ∉ E

theorem smallUniverse_disjoint (E : Finset ℕ) (u : ℕ) : Disjoint (smallUniverse E u) E := by
  rw [disjoint_left]; intro p hp; exact (mem_filter.1 hp).2.2

/-- **Finite contract of the small-prime Rosser upper weight** (level `level = x^rho`). -/
structure SmallPrimeRosserProvider (Psm : Finset ℕ) (level : ℝ) where
  beta : Finset ℕ → ℝ
  supported : SupportedIn beta Psm
  oneBounded : OneBounded beta
  beta_empty : beta ∅ = 1
  level_supp : ∀ A, beta A ≠ 0 → (∏ p ∈ A, (p : ℝ)) ≤ level
  upper : ∀ D, (if D ∩ Psm = ∅ then 1 else 0) ≤ dsum beta D

theorem SmallPrimeRosserProvider.dsum_beta_nonneg {Psm : Finset ℕ} {level : ℝ}
    (B : SmallPrimeRosserProvider Psm level) (D : Finset ℕ) : 0 ≤ dsum B.beta D :=
  le_trans (by split_ifs <;> norm_num) (B.upper D)

/-- The ordinary dimension-one Rosser upper weight (β = 2) on `Psm` at level `level`. -/
noncomputable def rosserBeta (Psm : Finset ℕ) (level : ℝ) : Finset ℕ → ℝ :=
  ellRd Psm (fun p => (p : ℝ)) level

/-- **The Rosser weight satisfies the small-prime contract** (kernel-proved). -/
noncomputable def rosserSmallProvider (Psm : Finset ℕ) (level : ℝ) (hlev : 1 ≤ level)
    (hP : ∀ p ∈ Psm, 1 ≤ p) : SmallPrimeRosserProvider Psm level where
  beta := rosserBeta Psm level
  supported := ellRd_supported _ _ _
  oneBounded := ellRd_oneBounded _ _ _
  beta_empty := by simp [rosserBeta, ellRd, ellW_empty]
  level_supp A hA := by
    unfold rosserBeta ellRd at hA
    split_ifs at hA with hsub
    unfold ellW at hA
    split_ifs at hA with hadm
    · exact ellW_support_prod_le hlev (fun p hp => by exact_mod_cast hP p (hsub hp))
        (fun p _ q _ h => by exact_mod_cast h) hadm
    all_goals exact absurd rfl hA
  upper D := dsum_ellRd_ge Psm _ level D

end SmallPrimeUpperSieve
end ResearchBankV22
end Erdos287
