import Mathlib.Tactic

/-!
# Contact-core route — external analytic inputs and their conditional consequences

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

**Nothing in this file is inhabited.**  Each external analytic input is a named `Prop` with all of
its parameters visible; every theorem here is an implication that *consumes* such a `Prop` as a
hypothesis.  Recording a statement in this file is **not** a proof of it: the evidence kind of
every `Prop` below is `externalAnalyticBank` (or `conditionalInterface` for the derived
implications), never `kernelProof`.

Contents:

* `CrootGeneralModulus` — reciprocal subset sums of a large supply of small primes hit every
  residue modulo a general large modulus (external analytic input);
* `CrootPrimePowerModulus` — its prime-power corollary;
* `OneDemandInterface` / `valTrans_of_raw_terminal` — (VAL-TRANS): a raw terminal must violate the
  one-demand threshold;
* `FPInterfaceGen`, `FPInterface` — (FP-INTERFACE-GEN), (FP-INTERFACE): a non-full-cube projection
  of a Croot-long first-power row language consumes linearly many interface coordinates;
* `fullCube_no_restriction`, `fullCube_elimination` — the exact logical consequence of a full-cube
  projection: such a row can be eliminated and can never act as anchor, switch or
  forcing-message carrier;
* `linear_charge` — (LINEAR-CHARGE): the combinatorial handshake consequence, kernel-proved
  *conditional* on the FP interface bound.
-/

namespace Erdos287
namespace ResearchBankV5
namespace ContactCore

open Finset

/-! ## 1.  Croot's general-modulus reciprocal coverage (external) -/

/-- **(CROOT-GEN), external analytic input.**  For every sufficiently large modulus `n`, any
sufficiently large supply `S` of distinct primes not dividing `n` has reciprocal subset sums
hitting every residue modulo `n`.

`externalAnalyticBank`.  Not proved in this project. -/
def CrootGeneralModulus : Prop :=
  ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ S : Finset ℕ,
    (∀ s ∈ S, s.Prime ∧ ¬ s ∣ n) → (Nat.log 2 n) ^ 4 ≤ S.card →
      ∀ r : ZMod n, ∃ T ⊆ S, (∑ s ∈ T, ((s : ZMod n))⁻¹) = r

/-- **(CROOT-PP), external analytic input.**  The prime-power corollary of `CrootGeneralModulus`.

`externalAnalyticBank`.  Not proved in this project. -/
def CrootPrimePowerModulus : Prop :=
  ∃ n₀ : ℕ, ∀ (ℓ k : ℕ), ℓ.Prime → n₀ ≤ ℓ ^ k → ∀ S : Finset ℕ,
    (∀ s ∈ S, s.Prime ∧ s ≠ ℓ) → (Nat.log 2 (ℓ ^ k)) ^ 4 ≤ S.card →
      ∀ r : ZMod (ℓ ^ k), ∃ T ⊆ S, (∑ s ∈ T, ((s : ZMod (ℓ ^ k)))⁻¹) = r

/-- The prime-power statement is a *specialization request*, not a theorem of this layer: it is
recorded separately and is equally uninhabited here. -/
theorem crootPrimePower_is_separate_input :
    (CrootGeneralModulus → CrootGeneralModulus) ∧ (CrootPrimePowerModulus → CrootPrimePowerModulus) :=
  ⟨id, id⟩

/-! ## 2.  (VAL-TRANS): valuation-layer one-demand -/

/-- **One-demand interface.**  `Sel d` says the parent port of the terminal cofactor `d` can be
selected inside a complete legal row; `U d` is the available supply `⌊N/ℓ^v⌋` at the layer of `d`,
and `bound d = C_η ((v+1) log ℓ)^{3+η}` is the Croot threshold.

This `Prop` is exactly the conditional consumption of `CrootPrimePowerModulus`;
`conditionalInterface`. -/
def OneDemandInterface (Sel : ℕ → Prop) (U : ℕ → ℕ) (bound : ℕ → ℝ) : Prop :=
  ∀ d : ℕ, bound d ≤ (U d : ℝ) → Sel d

/-- **(VAL-TRANS).**  Under the one-demand interface, a *raw* terminal — one whose parent port is
not selectable — must fall below the Croot threshold: `U_ℓ(d) < C_η ((v+1) log ℓ)^{3+η}`. -/
theorem valTrans_of_raw_terminal {Sel : ℕ → Prop} {U : ℕ → ℕ} {bound : ℕ → ℝ}
    (h : OneDemandInterface Sel U bound) {d : ℕ} (hraw : ¬ Sel d) : (U d : ℝ) < bound d := by
  by_contra hcon
  exact hraw (h d (le_of_not_gt hcon))

/-! ## 3.  First-power row languages and the FP interface -/

/-- The cofactor interval `C_p = [⌈a/p⌉, ⌊M/p⌋]` of a first-power owner `p`. -/
def cofactorSetFP (p a M : ℕ) : Finset ℕ := Finset.Icc ((a + p - 1) / p) (M / p)

/-- The complete row language `ℒ_p = {ε : ∑_c ε_c c⁻¹ ≡ 0 mod p}`. -/
def InLanguage (p a M : ℕ) (ε : ℕ → Bool) : Prop :=
  (∑ c ∈ cofactorSetFP p a M, if ε c then ((c : ZMod p))⁻¹ else 0) = 0

/-- `proj_T(ℒ_p) = {0,1}^T`: every Boolean pattern on the interface coordinates `T` extends to a
word of the row language. -/
def ProjSurjective (p a M : ℕ) (T : Finset ℕ) : Prop :=
  ∀ β : ℕ → Bool, ∃ ε : ℕ → Bool, InLanguage p a M ε ∧ ∀ c ∈ T, ε c = β c

/-- **(FP-INTERFACE-GEN), external analytic input.**  If the projection of a Croot-long first-power
row language to an external Boolean interface `T` is not the full cube, then
`|T| ≫_δ N · log log p / log N`.  The implied constant is carried by `κ`, and `N` is the size of
the cofactor interval.

`externalAnalyticBank`.  Uses the multiscale Croot/PNT incidence argument; not proved here. -/
def FPInterfaceGen (κ : ℝ) : Prop :=
  ∀ (p a M : ℕ) (T : Finset ℕ), T ⊆ cofactorSetFP p a M → ¬ ProjSurjective p a M T →
    κ * ((cofactorSetFP p a M).card : ℝ) * Real.log (Real.log p)
        / Real.log ((cofactorSetFP p a M).card : ℝ) ≤ (T.card : ℝ)

/-- **(FP-INTERFACE), external analytic input.**  In the intended range `N ≤ (log p)^B` the
general bound becomes linear: a non-full-cube projection consumes `≥ κ N` interface coordinates.

`externalAnalyticBank`.  Not proved here; consumed as a hypothesis by `linear_charge`. -/
def FPInterface (κ : ℚ) : Prop :=
  ∀ (p a M : ℕ) (T : Finset ℕ), T ⊆ cofactorSetFP p a M → ¬ ProjSurjective p a M T →
    κ * ((cofactorSetFP p a M).card : ℚ) ≤ (T.card : ℚ)

/-! ## 4.  Full-cube removability — exact conditional consequence -/

/-- **Full-cube rows impose no Boolean restriction.**  If `proj_T(ℒ_p)` is the full cube, then
every external pattern on `T` is realized inside the row language: the row can serve neither as
anchor, nor as switch, nor as a forcing-message carrier. -/
theorem fullCube_no_restriction {p a M : ℕ} {T : Finset ℕ} (h : ProjSurjective p a M T)
    (β : ℕ → Bool) : ∃ ε : ℕ → Bool, InLanguage p a M ε ∧ ∀ c ∈ T, ε c = β c := h β

/-- **Exact elimination.**  For any external constraint `R` depending only on the interface
coordinates `T`, adjoining a full-cube row changes nothing: the system with the row is satisfiable
exactly when the external system alone is. -/
theorem fullCube_elimination {p a M : ℕ} {T : Finset ℕ} (h : ProjSurjective p a M T)
    (R : (ℕ → Bool) → Prop)
    (hR : ∀ ε ε' : ℕ → Bool, (∀ c ∈ T, ε c = ε' c) → (R ε ↔ R ε')) :
    (∃ ε : ℕ → Bool, InLanguage p a M ε ∧ R ε) ↔ ∃ ε : ℕ → Bool, R ε := by
  constructor
  · rintro ⟨ε, -, hRε⟩
    exact ⟨ε, hRε⟩
  · rintro ⟨β, hRβ⟩
    obtain ⟨ε, hmem, hagree⟩ := h β
    exact ⟨ε, hmem, (hR ε β hagree).2 hRβ⟩

/-! ## 5.  (LINEAR-CHARGE) -/

/-- **(LINEAR-CHARGE).**  Conditional on the FP interface bound `κ N_p ≤ |T_p|` for every surviving
long first-power owner, and on the combinatorial handshake `∑_p |T_p| ≤ 2|E(K)| + F_K`, the total
interface demand is linearly bounded:

`κ ∑_{p ∈ K_long} N_p ≤ 2|E(K)| + F_K`.

The implication is kernel-proved; its premises are the external analytic input and the handshake
count of the exact branch-eliminated CONTACT core. -/
theorem linear_charge {κ : ℚ} (Klong : Finset ℕ) (Np Tcard : ℕ → ℕ) (E F : ℕ)
    (hFP : ∀ p ∈ Klong, κ * (Np p : ℚ) ≤ (Tcard p : ℚ))
    (hhand : ∑ p ∈ Klong, Tcard p ≤ 2 * E + F) :
    κ * ∑ p ∈ Klong, (Np p : ℚ) ≤ (2 * E + F : ℚ) := by
  have h1 : κ * ∑ p ∈ Klong, (Np p : ℚ) = ∑ p ∈ Klong, κ * (Np p : ℚ) := by
    rw [Finset.mul_sum]
  have h2 : ∑ p ∈ Klong, κ * (Np p : ℚ) ≤ ∑ p ∈ Klong, (Tcard p : ℚ) :=
    Finset.sum_le_sum hFP
  have h3 : ∑ p ∈ Klong, (Tcard p : ℚ) = ((∑ p ∈ Klong, Tcard p : ℕ) : ℚ) := by push_cast; ring
  have h4 : ((∑ p ∈ Klong, Tcard p : ℕ) : ℚ) ≤ ((2 * E + F : ℕ) : ℚ) := by exact_mod_cast hhand
  rw [h1]
  refine le_trans h2 ?_
  rw [h3]
  push_cast at h4 ⊢
  linarith

/-- The older schematic charge `∑ N_p / log N_p ≲ |E| + F` is *superseded*: the linear form above
is stronger by one logarithmic factor whenever `log N_p ≥ 1`.  This is the exact comparison of the
two right-hand sides at fixed data. -/
theorem linear_charge_supersedes_log_form (x L : ℚ) (hx : 0 ≤ x) (hL : 1 ≤ L) : x / L ≤ x := by
  rw [div_le_iff₀ (by linarith)]
  nlinarith

end ContactCore
end ResearchBankV5
end Erdos287
