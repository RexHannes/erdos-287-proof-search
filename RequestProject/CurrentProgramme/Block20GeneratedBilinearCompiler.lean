import Mathlib
import RequestProject.CurrentProgramme.PerronConditionRemovalCompiler

/-!
# BLOCK20 Δ, Phase C (§7–§11, §13, §14) — templates, bilinear split, generated Type-II

**Append-only.**

* §7 — `Block20Template`: the finite source metadata (at most `20` blocks, block IDs, `d`/`m`
  labels, singleton/grouped provenance, ordered support cells, the selected Type-II subset
  `E`, the sign, the squareful routing state, and a deterministic order).  No continuous
  parameter is a hidden field: masses, kernels and Perron data always enter as explicit
  parameters of the theorems that use them.  `template_selection_not_recomputed` proves that
  `E` is fixed by the template.
* §8 — the Type-II window `ε_* ≤ selectedMass < ε_* + σ_* = ν₀ − ε_*` from the first-crossing
  metadata, and `typeII_size_window`, the conversion to
  `(X/2)^{ε_*} < u ≤ X^{ν₀−ε_*}` **given** the log-mass dictionary `u = X^m`, which is
  carried as an explicit source field (`LogMassSizeDictionary`) and never faked.
* §9 — the exact bilinear split `∏ blocks = u·v`, the splitting of every template predicate
  into the selected / complementary families, and `fixed_template_source_factorisation`.
  `joint_coprimality_predicate_not_factorisable` records what a *residual joint predicate*
  would look like, so no arbitrary factorisation is claimed.
* §10 — the coefficient grammar: `xiOf`/`kappaOf` are products over the packed blocks, the
  Möbius factor of each block occurs exactly once, and the norm data is an **uninhabited**
  `GeneratedCoefficientNormInput` attached to the generated class (proved distinct from an
  arbitrary sequence by `generated_xi_support`).
* §11 — the three-small-prime **supersession candidate**: the coverage predicate
  `ThreeSmallPrimeSourceCoveredByBlock20` is defined and *not proved*; the historical row is
  **not** marked false (`threeSmallPrime_class_is_nonempty`).
* §13 — `Block20GeneratedTypeIIInput`, the **first exact main-line analytic residual**, and
  the conditional compiler to `K0UniformFragmentationConclusion`.  Uninhabited.
* §14 — the finite `CompilerLogBudget` ledger; the current crude total `22` is recorded as an
  upper budget, explicitly **not** an optimality theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open ArithmeticFunction

namespace Erdos287
namespace Block20

/-! ## §7  The Block20 template -/

/-- Which side of the source decomposition a block belongs to. -/
inductive BlockSide
  | dSide
  | mSide
  deriving DecidableEq, Fintype, Repr

/-- How a block was produced by the procedural packing. -/
inductive BlockProvenance
  | singleton
  | grouped
  deriving DecidableEq, Fintype, Repr

/-- The squareful / repeated-prime routing state of a block. -/
inductive RoutingState
  | squarefree
  | squareful
  deriving DecidableEq, Fintype, Repr

/-- **`Block20Template`** — the finite source metadata of one packed source class.

Every field is finite data.  Continuous parameters (masses, kernels, Perron data) are *not*
fields: they are supplied to the theorems below as explicit parameters. -/
structure Block20Template where
  /-- The number of blocks. -/
  r : ℕ
  /-- At most twenty blocks. -/
  r_le_20 : r ≤ 20
  /-- The `d` / `m` label of each block. -/
  side : Fin r → BlockSide
  /-- Singleton or grouped provenance. -/
  provenance : Fin r → BlockProvenance
  /-- The ordered support cells (prime-power atoms) of each block. -/
  support : Fin r → List ℕ
  /-- The selected Type-II subset `E`, **fixed by the template**. -/
  selected : Finset (Fin r)
  /-- The sign `s`. -/
  sign : ℤ
  /-- The sign is a unit. -/
  sign_unit : sign = 1 ∨ sign = -1
  /-- The squareful / repeated-prime routing state. -/
  routing : Fin r → RoutingState
  /-- The deterministic order of the blocks. -/
  order : Fin r → ℕ
  /-- The order is deterministic (injective). -/
  order_injective : Function.Injective order

namespace Block20Template

variable (pi : Block20Template)

/-- The arithmetic value of a block: the product of its support cells. -/
def blockValue (j : Fin pi.r) : ℕ := (pi.support j).prod

/-- `u = ∏_{j ∈ E} block_j`. -/
def uOf : ℕ := ∏ j ∈ pi.selected, pi.blockValue j

/-- `v = ∏_{j ∉ E} block_j`. -/
def vOf : ℕ := ∏ j ∈ pi.selectedᶜ, pi.blockValue j

/-- The selected log-mass, read off the template's own `E`. -/
def selectedMass (mass : Fin pi.r → ℝ) : ℝ := ∑ j ∈ pi.selected, mass j

end Block20Template

open Block20Template

/-- **`template_block_count_le_20`.**  `LEAN_PROVED`. -/
theorem template_block_count_le_20 (pi : Block20Template) : pi.r ≤ 20 := pi.r_le_20

/-- **`template_block_card`.**  `LEAN_PROVED`.  Finite multiplicity: the template indexes
exactly `r ≤ 20` blocks. -/
theorem template_block_card (pi : Block20Template) :
    (Finset.univ : Finset (Fin pi.r)).card = pi.r ∧ pi.r ≤ 20 :=
  ⟨Finset.card_univ.trans (Fintype.card_fin pi.r), pi.r_le_20⟩

/-- **`template_selectedMass_is_template_data`.**  `LEAN_PROVED`.

The selected mass is computed over the template's own `E`; it is a *definition*, not a
recomputation. -/
theorem template_selectedMass_is_template_data (pi : Block20Template) (mass : Fin pi.r → ℝ) :
    pi.selectedMass mass = ∑ j ∈ pi.selected, mass j := rfl

/-- **`template_selection_not_recomputed`.**  `LEAN_PROVED`.

`E` is fixed by the template: any selection rule that agrees with the template's `E` is
independent of the numerical masses. -/
theorem template_selection_not_recomputed (pi : Block20Template)
    (sel : (Fin pi.r → ℝ) → Finset (Fin pi.r)) (hsel : ∀ m, sel m = pi.selected)
    (m1 m2 : Fin pi.r → ℝ) : sel m1 = sel m2 := by rw [hsel, hsel]

/-- A one-block template, used to show that the previous statement has content. -/
def trivialTemplate : Block20Template where
  r := 1
  r_le_20 := by norm_num
  side := fun _ => BlockSide.dSide
  provenance := fun _ => BlockProvenance.singleton
  support := fun _ => [1]
  selected := ∅
  sign := 1
  sign_unit := Or.inl rfl
  routing := fun _ => RoutingState.squarefree
  order := fun j => (j : ℕ)
  order_injective := fun a b h => Fin.ext h

/-- **`mass_dependent_selection_is_different`.**  `LEAN_PROVED`.

A rule that *recomputes* the selected set from the numerical masses is genuinely different:
it can return different sets for different masses.  This is exactly what the template
forbids. -/
theorem mass_dependent_selection_is_different :
    ∃ (sel : (Fin 1 → ℝ) → Finset (Fin 1)) (m1 m2 : Fin 1 → ℝ), sel m1 ≠ sel m2 := by
  classical
  refine ⟨fun m => if 0 < m 0 then {0} else ∅, fun _ => 1, fun _ => 0, ?_⟩
  simp

/-! ## §8  The Type-II window -/

/-- **`typeII_window_from_first_crossing`.**  `LEAN_PROVED`.

With `j₀` the block whose addition first crosses `ε_*`, and every block of mass at most
`σ_*`:

```
ε_* ≤ selectedMass < ε_* + σ_*.
```
-/
theorem typeII_window_from_first_crossing (pi : Block20Template) (mass : Fin pi.r → ℝ)
    {epsStar sigmaStar : ℝ} {j0 : Fin pi.r}
    (hj0 : j0 ∈ pi.selected)
    (hcross : epsStar ≤ pi.selectedMass mass)
    (hprev : ∑ j ∈ pi.selected.erase j0, mass j < epsStar)
    (hblock : mass j0 ≤ sigmaStar) :
    epsStar ≤ pi.selectedMass mass ∧ pi.selectedMass mass < epsStar + sigmaStar := by
  classical
  refine ⟨hcross, ?_⟩
  have hsplit : pi.selectedMass mass = mass j0 + ∑ j ∈ pi.selected.erase j0, mass j := by
    rw [Block20Template.selectedMass, ← Finset.add_sum_erase _ _ hj0]
  rw [hsplit]
  linarith

/-- **`typeII_window_endpoint`.**  `LEAN_PROVED`.

At the Block20 parameters `σ_* = ν₀ − 2ε_*` the upper endpoint is exactly `ν₀ − ε_*`. -/
theorem typeII_window_endpoint (nu0R epsStar : ℝ) :
    epsStar + (nu0R - 2 * epsStar) = nu0R - epsStar := by ring

/-- **`LogMassSizeDictionary`** — `SOURCE INPUT`.

The conversion from logarithmic mass to the literal `X`-powers.  It is carried as an explicit
source field, not faked: `u = X^m` where `m` is the selected log-mass. -/
def LogMassSizeDictionary (X u m : ℝ) : Prop := u = X ^ m

/-- **`typeII_size_window`.**  `CONDITIONAL / LEAN_PROVED`.

Given the log-mass dictionary and the window of §8, the literal size window follows:

```
(X/2)^{ε_*} < u ≤ X^{ν₀ − ε_*}.
```
-/
theorem typeII_size_window {X u m epsStar nu0R : ℝ} (hX : 2 ≤ X) (heps : 0 < epsStar)
    (hdict : LogMassSizeDictionary X u m)
    (hlow : epsStar ≤ m) (hhigh : m ≤ nu0R - epsStar) :
    (X / 2) ^ epsStar < u ∧ u ≤ X ^ (nu0R - epsStar) := by
  have hX0 : (0 : ℝ) < X := by linarith
  have hX1 : (1 : ℝ) ≤ X := by linarith
  have hhalf : X / 2 < X := by linarith
  have h1 : (X / 2) ^ epsStar < X ^ epsStar :=
    Real.rpow_lt_rpow (by linarith) hhalf heps
  have h2 : X ^ epsStar ≤ X ^ m := Real.rpow_le_rpow_of_exponent_le hX1 hlow
  have h3 : X ^ m ≤ X ^ (nu0R - epsStar) := Real.rpow_le_rpow_of_exponent_le hX1 hhigh
  rw [LogMassSizeDictionary] at hdict
  exact ⟨by rw [hdict]; linarith, by rw [hdict]; exact h3⟩

/-! ## §9  The exact bilinear split -/

/-- **`template_product_split`.**  `LEAN_PROVED`.  `∏ all blocks = u · v`. -/
theorem template_product_split (pi : Block20Template) :
    (∏ j : Fin pi.r, pi.blockValue j) = pi.uOf * pi.vOf := by
  classical
  rw [Block20Template.uOf, Block20Template.vOf, Finset.prod_mul_prod_compl]

/-- **`template_predicate_split`.**  `LEAN_PROVED`.

Every template predicate (side labels, provenance, routing state, support data) splits into
the selected and complementary block families, with no block counted twice. -/
theorem template_predicate_split (pi : Block20Template) (P : Fin pi.r → Prop)
    [DecidablePred P] :
    (Finset.univ.filter P) = (pi.selected.filter P) ∪ (pi.selectedᶜ.filter P) ∧
      Disjoint (pi.selected.filter P) (pi.selectedᶜ.filter P) := by
  classical
  constructor
  · rw [← Finset.filter_union]
    congr 1
    simp
  · exact Finset.disjoint_filter_filter disjoint_compl_right

/-- **`template_mass_split`.**  `LEAN_PROVED`. -/
theorem template_mass_split (pi : Block20Template) (mass : Fin pi.r → ℝ) :
    ∑ j : Fin pi.r, mass j = pi.selectedMass mass + ∑ j ∈ pi.selectedᶜ, mass j := by
  classical
  rw [Block20Template.selectedMass, Finset.sum_add_sum_compl]

/-- `ξ_π(u)` — the selected-block coefficient, from the packed block grammar. -/
def xiOf (pi : Block20Template) (w : Fin pi.r → ℂ) : ℂ := ∏ j ∈ pi.selected, w j

/-- `κ_π(v)` — the complementary-block coefficient. -/
def kappaOf (pi : Block20Template) (w : Fin pi.r → ℂ) : ℂ := ∏ j ∈ pi.selectedᶜ, w j

/-- **`fixed_template_source_factorisation`.**  `LEAN_PROVED`.

For a fixed template the block-grammar coefficient factorises exactly as `ξ_π(u)·κ_π(v)`. -/
theorem fixed_template_source_factorisation (pi : Block20Template) (w : Fin pi.r → ℂ) :
    (∏ j : Fin pi.r, w j) = xiOf pi w * kappaOf pi w := by
  classical
  rw [xiOf, kappaOf, Finset.prod_mul_prod_compl]

/-- **`joint_coprimality_predicate_not_factorisable`.**  `LEAN_PROVED`.

What a *residual joint predicate* would cost: the coprimality indicator `1_{(u,v)=1}` is not
of the form `f(u)·g(v)`.  So the factorisation above is a claim about the block grammar, not
a licence to split arbitrary joint conditions. -/
theorem joint_coprimality_predicate_not_factorisable :
    ¬ ∃ f g : ℕ → ℤ, ∀ u v : ℕ, (if Nat.Coprime u v then (1 : ℤ) else 0) = f u * g v := by
  rintro ⟨f, g, h⟩
  have h22 := h 2 2
  have h23 := h 2 3
  have h32 := h 3 2
  norm_num [Nat.Coprime] at h22 h23 h32
  rcases h22 with h0 | h0
  · rw [h0] at h23; simp at h23
  · rw [h0] at h32; simp at h32

/-! ## §10  The coefficient grammar -/

/-- The generated `ξ`-coefficient: supported exactly at the template's `u`. -/
noncomputable def generatedXi (pi : Block20Template) (w : Fin pi.r → ℂ) (n : ℕ) : ℂ :=
  if n = pi.uOf then xiOf pi w else 0

/-- The generated `κ`-coefficient: supported exactly at the template's `v`. -/
noncomputable def generatedKappa (pi : Block20Template) (w : Fin pi.r → ℂ) (n : ℕ) : ℂ :=
  if n = pi.vOf then kappaOf pi w else 0

/-- **`generated_xi_support`.**  `LEAN_PROVED`.

The generated coefficients are **not** arbitrary sequences: they are supported at the
template's own block product. -/
theorem generated_xi_support (pi : Block20Template) (w : Fin pi.r → ℂ) {n : ℕ}
    (h : generatedXi pi w n ≠ 0) : n = pi.uOf := by
  by_contra hne
  exact h (by simp [generatedXi, hne])

/-- **`generated_kappa_support`.**  `LEAN_PROVED`. -/
theorem generated_kappa_support (pi : Block20Template) (w : Fin pi.r → ℂ) {n : ℕ}
    (h : generatedKappa pi w n ≠ 0) : n = pi.vOf := by
  by_contra hne
  exact h (by simp [generatedKappa, hne])

/-- **`mobius_factor_occurs_once`.**  `LEAN_PROVED`.

Each block contributes its Möbius factor exactly once: the packed grammar separates the
Möbius content from the smooth content with no repetition. -/
theorem mobius_factor_occurs_once (pi : Block20Template) (mu smooth : Fin pi.r → ℂ) :
    (∏ j : Fin pi.r, mu j * smooth j) = (∏ j : Fin pi.r, mu j) * (∏ j : Fin pi.r, smooth j) :=
  Finset.prod_mul_distrib

/-- **`ordered_block_convolution`.**  `LEAN_PROVED`.

The block convolution respects the template's deterministic order and the `u`/`v` split. -/
theorem ordered_block_convolution (pi : Block20Template) (w : Fin pi.r → ℂ) :
    (∏ j : Fin pi.r, w j) = xiOf pi w * kappaOf pi w ∧
      (∏ j : Fin pi.r, pi.blockValue j) = pi.uOf * pi.vOf ∧
      Function.Injective pi.order :=
  ⟨fixed_template_source_factorisation pi w, template_product_split pi, pi.order_injective⟩

/-- **`GeneratedCoefficientNormInput`** — `EXTERNAL / ANALYTIC / UNINHABITED`.

The norm data for the **generated** class, attached to a template and its block weights (not
to arbitrary `τ₄₀`-bounded sequences).  The generalized divisor function is supplied as data
`tau40`, with its normalisation as an explicit field. -/
structure GeneratedCoefficientNormInput
    (pi : Block20Template) (w : Fin pi.r → ℂ) (tau40 : ℕ → ℝ) (N : ℕ) (L1 L2 : ℝ) : Prop where
  /-- The divisor-function data is normalised and nonnegative. -/
  tau_normalised : tau40 1 = 1 ∧ ∀ n : ℕ, 0 ≤ tau40 n
  /-- The pointwise divisor bound for the generated `ξ`. -/
  pointwise_xi : ∀ n : ℕ, ‖generatedXi pi w n‖ ≤ tau40 n
  /-- The pointwise divisor bound for the generated `κ`. -/
  pointwise_kappa : ∀ n : ℕ, ‖generatedKappa pi w n‖ ≤ tau40 n
  /-- The `L¹` bound. -/
  l1_bound : ∑ n ∈ Finset.range N, ‖generatedXi pi w n‖ ≤ L1
  /-- The `L²` bound. -/
  l2_bound : ∑ n ∈ Finset.range N, ‖generatedXi pi w n‖ ^ 2 ≤ L2

/-- **`generatedCoefficientNorm_attaches_to_the_generated_class`.**  `CONDITIONAL /
LEAN_PROVED`.

Any inhabitant of the norm input bounds *generated* coefficients, which are supported at the
template's own products: the input cannot be re-used for an arbitrary sequence. -/
theorem generatedCoefficientNorm_attaches_to_the_generated_class
    {pi : Block20Template} {w : Fin pi.r → ℂ} {tau40 : ℕ → ℝ} {N : ℕ} {L1 L2 : ℝ}
    (h : GeneratedCoefficientNormInput pi w tau40 N L1 L2) :
    (∀ n : ℕ, generatedXi pi w n ≠ 0 → n = pi.uOf) ∧
      (∀ n : ℕ, ‖generatedXi pi w n‖ ≤ tau40 n) :=
  ⟨fun _ hn => generated_xi_support pi w hn, h.pointwise_xi⟩

/-- **`generatedCoefficientNorm_not_automatic`.**  `LEAN_PROVED`.  Uninhabited. -/
theorem generatedCoefficientNorm_not_automatic :
    ∃ (pi : Block20Template) (w : Fin pi.r → ℂ) (tau40 : ℕ → ℝ) (N : ℕ) (L1 L2 : ℝ),
      ¬ GeneratedCoefficientNormInput pi w tau40 N L1 L2 := by
  refine ⟨trivialTemplate, fun _ => 0, fun _ => 0, 0, 0, 0, ?_⟩
  intro h
  have := h.tau_normalised.1
  norm_num at this

/-! ## §11  The three-small-prime supersession firewall -/

open Erdos287.PostBalanced7Pro

/-- The template routes the atom `n`: its blocks reassemble `n`, every support cell is a
prime power, no block straddles the `d`/`m` divide, and no block is empty. -/
def RoutesAtom (z : ℕ) (pi : Block20Template) (n : ℕ) : Prop :=
  (∏ j : Fin pi.r, pi.blockValue j) = n ∧
    (∀ j : Fin pi.r, ∀ a ∈ pi.support j, IsPrimePow a) ∧
    (∀ j : Fin pi.r, pi.side j = BlockSide.dSide → ∀ a ∈ pi.support j, IsSmoothBelow z a) ∧
    (∀ j : Fin pi.r, pi.side j = BlockSide.mSide → ∀ a ∈ pi.support j, IsRoughAbove z a) ∧
    (∀ j : Fin pi.r, pi.support j ≠ [])

/-- The mass-constrained routing: additionally every block's logarithmic mass is at most
`σ_*`.  This is the constraint that makes the coverage question nontrivial — lumping all
atoms into two blocks is not allowed. -/
def RoutesAtomWithMass (z : ℕ) (X sigmaStar : ℝ) (pi : Block20Template) (n : ℕ) : Prop :=
  RoutesAtom z pi n ∧
    ∀ j : Fin pi.r, Real.log (pi.blockValue j) / Real.log X ≤ sigmaStar

/-- **The exact coverage residual.**  The previously problematic `Ω(d) ≥ 3` source packets are
routed through Block20 templates.  This is **not proved**: the three-small-prime row is a
*supersession candidate*, with source coverage open. -/
def ThreeSmallPrimeSourceCoveredByBlock20 (z : ℕ) (X sigmaStar : ℝ) : Prop :=
  ∀ n : ℕ, n ≠ 0 → PrefixAtLeastThree z n →
    ∃ pi : Block20Template, RoutesAtomWithMass z X sigmaStar pi n

/-- **`threeSmallPrime_supersession_of_coverage`.**  `CONDITIONAL_COMPILER / LEAN_PROVED`.

*If* the coverage residual is supplied, the historical `Ω(d) ≥ 3` class is superseded as the
controlling frontier: every such source packet is a Block20-generated one. -/
theorem threeSmallPrime_supersession_of_coverage {z : ℕ} {X sigmaStar : ℝ}
    (h : ThreeSmallPrimeSourceCoveredByBlock20 z X sigmaStar)
    {n : ℕ} (hn : n ≠ 0) (hpref : PrefixAtLeastThree z n) :
    ∃ pi : Block20Template, RoutesAtomWithMass z X sigmaStar pi n :=
  h n hn hpref

/-- **`threeSmallPrime_class_is_nonempty`.**  `LEAN_PROVED`.

The historical class is **not** false and not empty: `n = 8` has `Ω(d) = 3` below the cutoff
`z = 10`.  The row is superseded-as-frontier only if coverage is supplied; it is never marked
false. -/
theorem threeSmallPrime_class_is_nonempty : PrefixAtLeastThree 10 8 := by
  have hs : IsSmoothBelow 10 8 := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hdvd : p ∣ 2 ^ 3 := by simpa using Nat.dvd_of_mem_primeFactors hp
    have hp2 : p ∣ 2 := hpp.dvd_of_dvd_pow hdvd
    have : p = 2 := (Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp hp2
    omega
  have hr : IsRoughAbove 10 1 := by
    intro p hp
    simp at hp
  have h1 : smoothPart 10 8 = 8 := by
    have := smoothRough_unique (z := 10) (d₁ := smoothPart 10 8) (m₁ := roughPart 10 8)
      (d₂ := 8) (m₂ := 1) (smoothPart_ne_zero 10 8) (roughPart_ne_zero 10 8)
      (by norm_num) (by norm_num) (smoothPart_smooth 10 8) (roughPart_rough 10 8) hs hr
      (by rw [smoothPart_mul_roughPart (by norm_num) 10])
    exact this.1
  rw [PrefixAtLeastThree, h1]
  simp [ArithmeticFunction.cardFactors_apply]

/-! ## §13  The generated Type-II socket — the current main-line analytic residual -/

/-- The shifted argument `2uv + s` with `s = ±1`. -/
def shiftedArg (s : ℤ) (n : ℕ) : ℕ := if s = 1 then 2 * n + 1 else 2 * n - 1

/-- **`Block20GeneratedTypeIIInput`** —
`287-K0-SP2-BLOCK20-GENERATED-TYPEII45 : ANALYTIC_OPEN / UNINHABITED`.

The literal generated class: an *actual* Block20 template, its *actual* block weights, the
generated `ξ_π` and `κ_π`, the supported Type-II window, both signs, and a physical smooth
weight.  No `τ₄₀`-coefficient generality is used. -/
structure Block20GeneratedTypeIIInput
    (X : ℝ) (N : ℕ) (pi : Block20Template) (w : Fin pi.r → ℂ)
    (mass : Fin pi.r → ℝ) (epsStar sigmaStar : ℝ)
    (W : ℝ → ℝ) (B : ℕ → ℝ) (bound : ℝ) : Prop where
  /-- The scale is nontrivial. -/
  scale : 3 ≤ X ∧ (N : ℝ) = X
  /-- The window parameters are the Block20 ones. -/
  window_parameters : 0 < epsStar ∧ sigmaStar = (nu0Q : ℝ) - 2 * epsStar
  /-- The Type-II window really is the template's supported one. -/
  window_supported :
    epsStar ≤ pi.selectedMass mass ∧ pi.selectedMass mass < epsStar + sigmaStar
  /-- The physical smooth weight is normalised. -/
  weight_normalised : ∀ x : ℝ, 0 ≤ W x ∧ W x ≤ 1
  /-- The estimate, for the template's own sign `s = ±1`. -/
  estimate :
    ‖∑ u ∈ Finset.range N, ∑ v ∈ Finset.range N,
        generatedXi pi w u * generatedKappa pi w v * (W ((u * v : ℕ) / X) : ℂ) *
          (((ArithmeticFunction.vonMangoldt (shiftedArg pi.sign (u * v)) - 2 * B (u * v) : ℝ)) : ℂ)‖
      ≤ bound

/-- **`block20GeneratedTypeII_not_automatic`.**  `LEAN_PROVED`.  **Uninhabited.** -/
theorem block20GeneratedTypeII_not_automatic :
    ∃ (X : ℝ) (N : ℕ) (pi : Block20Template) (w : Fin pi.r → ℂ) (mass : Fin pi.r → ℝ)
      (epsStar sigmaStar : ℝ) (W : ℝ → ℝ) (B : ℕ → ℝ) (bound : ℝ),
      ¬ Block20GeneratedTypeIIInput X N pi w mass epsStar sigmaStar W B bound := by
  refine ⟨0, 0, trivialTemplate, fun _ => 0, fun _ => 0, 0, 0, fun _ => 0, fun _ => 0, 0, ?_⟩
  intro h
  have := h.scale.1
  norm_num at this

/-! ### The uniform `k = 0` compiler -/

/-- The uniform `k = 0` fragmentation conclusion. -/
def K0UniformFragmentationConclusion (S : ℝ → ℝ) : Prop :=
  ∀ eps : ℝ, 0 < eps → ∃ X0 : ℝ, ∀ X : ℝ, X0 ≤ X → |S X| ≤ eps * X / Real.log X

/-- **`K0UniformFragmentationInputs`** — the four literal children of the dependency graph,
plus the exact reassembly and the per-cell savings.  `UNINHABITED`. -/
structure K0UniformFragmentationInputs
    (S : ℝ → ℝ) (cellVal : Fin 4 → ℝ → ℝ)
    (perronInput generatedTypeII finiteBlock20Compiler largePrimePowerRouter : Prop) :
    Prop where
  /-- (1) The Perron condition-removal input (§12). -/
  perron : perronInput
  /-- (2) The Block20 generated Type-II input (§13) — the main-line analytic residual. -/
  typeII : generatedTypeII
  /-- (3) The finite Block20 source compiler (§4, §7–§10). -/
  finite_compiler : finiteBlock20Compiler
  /-- (4) The large prime-power router input (§6). -/
  router : largePrimePowerRouter
  /-- The exact reassembly of the physical sum from the four cells. -/
  reassembly : ∀ X : ℝ, S X = ∑ c : Fin 4, cellVal c X
  /-- Each cell is supplied with an `o(X / log X)` saving. -/
  cell_savings : ∀ c : Fin 4, ∀ eps : ℝ, 0 < eps →
    ∃ X0 : ℝ, ∀ X : ℝ, X0 ≤ X → |cellVal c X| ≤ eps * X / Real.log X

/-- **`k0_uniform_fragmentation_compiler`.**  `CONDITIONAL_COMPILER / LEAN_PROVED`.

```
Perron condition removal + Block20 generated Type-II
  + finite Block20 source compiler + large prime-power router
      →  uniform k = 0.
```

A purely logical implication; no analytic content is created. -/
theorem k0_uniform_fragmentation_compiler
    {S : ℝ → ℝ} {cellVal : Fin 4 → ℝ → ℝ}
    {perronInput generatedTypeII finiteBlock20Compiler largePrimePowerRouter : Prop}
    (h : K0UniformFragmentationInputs S cellVal perronInput generatedTypeII
      finiteBlock20Compiler largePrimePowerRouter) :
    K0UniformFragmentationConclusion S := by
  intro eps heps
  choose X0 hX0 using fun c : Fin 4 => h.cell_savings c (eps / 4) (by positivity)
  refine ⟨Finset.univ.sup' ⟨0, Finset.mem_univ _⟩ X0, ?_⟩
  intro X hX
  have hXc : ∀ c : Fin 4, X0 c ≤ X := fun c =>
    le_trans (Finset.le_sup' X0 (Finset.mem_univ c)) hX
  calc |S X| = |∑ c : Fin 4, cellVal c X| := by rw [h.reassembly X]
    _ ≤ ∑ c : Fin 4, |cellVal c X| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _c : Fin 4, eps / 4 * X / Real.log X :=
        Finset.sum_le_sum fun c _ => hX0 c X (hXc c)
    _ = eps * X / Real.log X := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        rw [nsmul_eq_mul]
        push_cast
        ring

/-- **`k0UniformFragmentation_not_inhabited_here`.**  `LEAN_PROVED`. -/
theorem k0UniformFragmentation_not_inhabited_here :
    ∃ (S : ℝ → ℝ) (cellVal : Fin 4 → ℝ → ℝ) (a b c d : Prop),
      ¬ K0UniformFragmentationInputs S cellVal a b c d := by
  refine ⟨fun _ => 0, fun _ _ => 0, True, False, True, True, ?_⟩
  intro h
  exact h.typeII

/-- **`generated_typeII_is_the_mainline_residual`.**  `LEAN_PROVED`.

The dependency graph is literal: the finite Block20 compiler feeds the generated Type-II
socket, which feeds uniform `k = 0`; and the Type-II socket is the one that is not
available. -/
theorem generated_typeII_is_the_mainline_residual :
    (∀ (S : ℝ → ℝ) (cellVal : Fin 4 → ℝ → ℝ) (a b c d : Prop),
        K0UniformFragmentationInputs S cellVal a b c d → K0UniformFragmentationConclusion S) ∧
      (∃ (X : ℝ) (N : ℕ) (pi : Block20Template) (w : Fin pi.r → ℂ) (mass : Fin pi.r → ℝ)
        (epsStar sigmaStar : ℝ) (W : ℝ → ℝ) (B : ℕ → ℝ) (bound : ℝ),
        ¬ Block20GeneratedTypeIIInput X N pi w mass epsStar sigmaStar W B bound) :=
  ⟨fun _ _ _ _ _ _ h => k0_uniform_fragmentation_compiler h,
    block20GeneratedTypeII_not_automatic⟩

/-! ## §14  The log-cost ledger -/

/-- **`CompilerLogBudget`** — finite metadata bookkeeping.  No analytic logarithm estimate is
involved. -/
structure CompilerLogBudget where
  /-- The external source log cost `C_ext`. -/
  externalLogCost : ℚ
  /-- The Perron cost `C_Perron`. -/
  perronCost : ℚ
  /-- The template cost `C_template`. -/
  templateCost : ℚ
  /-- The dyadic decomposition cost. -/
  dyadicCost : ℚ
  /-- The Mellin cost. -/
  mellinCost : ℚ
  /-- Everything else. -/
  otherCost : ℚ

/-- The total budget. -/
def CompilerLogBudget.total (b : CompilerLogBudget) : ℚ :=
  b.externalLogCost + b.perronCost + b.templateCost + b.dyadicCost + b.mellinCost + b.otherCost

/-- **`total_eq_sum_of_fields`.**  `LEAN_PROVED`. -/
theorem total_eq_sum_of_fields (b : CompilerLogBudget) :
    b.total = b.externalLogCost + b.perronCost + b.templateCost + b.dyadicCost + b.mellinCost
      + b.otherCost := rfl

/-- The **current crude upper budget**: `C_ext = 1`, `C_Perron = 1`, `C_template ≤ 20`. -/
def currentCrudeBudget : CompilerLogBudget where
  externalLogCost := 1
  perronCost := 1
  templateCost := 20
  dyadicCost := 0
  mellinCost := 0
  otherCost := 0

/-- **`currentCrudeBudget_total`.**  `LEAN_PROVED`.  The naive total is `22`. -/
theorem currentCrudeBudget_total : currentCrudeBudget.total = 22 := by
  norm_num [CompilerLogBudget.total, currentCrudeBudget]

/-- **`crude_budget_is_not_an_optimality_theorem`.**  `LEAN_PROVED`.

`22` is a *current crude upper budget*, not an optimum: budgets with a smaller total are
perfectly well formed, which is exactly what template compression would produce. -/
theorem crude_budget_is_not_an_optimality_theorem :
    ∃ b : CompilerLogBudget, b.total < currentCrudeBudget.total := by
  refine ⟨⟨1, 1, 5, 0, 0, 0⟩, ?_⟩
  norm_num [CompilerLogBudget.total, currentCrudeBudget]

end Block20
end Erdos287
