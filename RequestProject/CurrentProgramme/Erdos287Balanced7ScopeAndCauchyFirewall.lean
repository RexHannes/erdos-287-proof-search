import RequestProject.CurrentProgramme.Erdos287RegularTemplateReassembly
import RequestProject.CurrentProgramme.Erdos287RepeatedBalanced7FiniteArithmetic

/-!
# Two firewalls: Balanced7 owner scope, and the first-Cauchy sign consumption

```
BALANCED7 OWNER SCOPE FIREWALL : KERNEL-PROVED (typing / finite)
FIRST-CAUCHY FIREWALL          : KERNEL-PROVED (algebraic identities only)
```

This module is **append-only**.

**§1 — owner scope.**  `SourceScope` distinguishes `directBalanced7` from
`regularPerron`.  The direct Balanced7 owner may be invoked **only** through an
explicit adapter that constructs its seven singleton prime-box fields:
`directBalanced7_of_adapter`.  Shape agreement is *not* enough —
`same_shape_does_not_determine_row` exhibits two distinct rows of identical
Balanced7 shape, and `shape_only_boxes_impossible` shows that no box map
depending on the shape alone can reconstruct the row.  The generic
regular-template-to-Balanced7 identification is carried as an explicitly
uninhabited adapter.

**§2 — first Cauchy.**  The proposed regular-parent factorisation carries a
*linear* small-prefix Möbius/Perron coefficient; this is recorded structurally.
Only the **algebraic** sign-consumption identities are proved: the modulus is
sign-blind, so a `+1 / −1` pair that cancels exactly before Cauchy contributes
`2` after squaring.  The claim that the post-Cauchy object is *analytically*
insufficient is recorded as research-status **metadata**, not as a theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open Finset

namespace Erdos287
namespace OwnerScope

open Erdos287.K0SP2Source
open Erdos287.RepeatedBalanced7

/-! ## §1.  The source-scope classifier -/

/-- The two mutually exclusive source scopes. -/
inductive SourceScope
  /-- A row presented with its seven singleton prime boxes. -/
  | directBalanced7
  /-- A row presented only as a member of the regular Perron support. -/
  | regularPerron
  deriving DecidableEq, Repr

/-- The two scopes are different objects: a classifier value can never be both. -/
theorem scopes_distinct : SourceScope.directBalanced7 ≠ SourceScope.regularPerron := by
  decide

/-- **`DirectBalanced7Source`** — the *only* legitimate input shape for the banked direct
Balanced7 owner: seven explicit, pairwise distinct singleton prime boxes whose product is
the row. -/
structure DirectBalanced7Source where
  /-- The row. -/
  row : ℕ
  /-- The seven singleton prime boxes. -/
  boxes : Fin 7 → ℕ
  /-- Each box carries a prime. -/
  boxes_prime : ∀ i, (boxes i).Prime
  /-- The boxes are pairwise distinct. -/
  boxes_inj : Function.Injective boxes
  /-- The row factors as the product of the seven boxes. -/
  row_eq : row = ∏ i, boxes i

/-- Its scope. -/
def DirectBalanced7Source.scope (_ : DirectBalanced7Source) : SourceScope :=
  SourceScope.directBalanced7

/-- **`RegularPerronSource`** — a row presented only through the regular Perron support.
It carries **no** box data. -/
structure RegularPerronSource where
  /-- The coefficient interface. -/
  coeffs : Erdos287.RegularPerron.RegularPerronCoefficients
  /-- The row. -/
  row : ℕ
  /-- The row lies in the regular support. -/
  mem_reg : coeffs.Reg row

/-- Its scope. -/
def RegularPerronSource.scope (_ : RegularPerronSource) : SourceScope :=
  SourceScope.regularPerron

/-- **Scope separation.**  A direct Balanced7 source and a regular Perron source never
carry the same scope tag, whatever their rows. -/
theorem scope_separation (d : DirectBalanced7Source) (r : RegularPerronSource) :
    d.scope ≠ r.scope := by
  simp [DirectBalanced7Source.scope, RegularPerronSource.scope]

/-! ### The explicit adapter -/

/-- **`Balanced7BoxAdapter`** — the explicit adapter a regular-Perron row must pass
through before the direct Balanced7 owner may be invoked.  It literally supplies the
seven singleton prime-box fields. -/
structure Balanced7BoxAdapter (r : RegularPerronSource) where
  /-- The seven boxes. -/
  boxes : Fin 7 → ℕ
  /-- Each box carries a prime. -/
  boxes_prime : ∀ i, (boxes i).Prime
  /-- The boxes are pairwise distinct. -/
  boxes_inj : Function.Injective boxes
  /-- The boxes reconstruct the row. -/
  row_eq : r.row = ∏ i, boxes i

/-- **`directBalanced7_of_adapter`.**  `KERNEL-PROVED`.

The direct Balanced7 owner is reachable from a regular-Perron row **only** through the
adapter, and then only with all seven box fields present. -/
def directBalanced7_of_adapter {r : RegularPerronSource} (a : Balanced7BoxAdapter r) :
    DirectBalanced7Source :=
  ⟨r.row, a.boxes, a.boxes_prime, a.boxes_inj, a.row_eq⟩

/-- **`GenericRegularTemplateToBalanced7Adapter`** — `UNINHABITED`.

The forbidden shortcut: an adapter claiming to produce the box data for *every* regular
row from the row alone.  It is deliberately over-specified (it must also work for rows
that are not Balanced7 at all) and is never constructed. -/
structure GenericRegularTemplateToBalanced7Adapter where
  /-- A purported universal box map. -/
  boxes : ℕ → Fin 7 → ℕ
  /-- It would have to reconstruct **every** natural number. -/
  universal : ∀ n : ℕ, n = ∏ i, boxes n i
  /-- …with prime boxes. -/
  prime : ∀ n i, (boxes n i).Prime

/-- **`genericAdapter_uninhabited`.**  `KERNEL-PROVED`.

The generic identification is impossible: `1` is not a product of seven primes. -/
theorem genericAdapter_uninhabited : ¬ Nonempty GenericRegularTemplateToBalanced7Adapter := by
  rintro ⟨a⟩
  have h1 : (1 : ℕ) = ∏ i, a.boxes 1 i := a.universal 1
  have h2 : 2 ≤ a.boxes 1 0 := (a.prime 1 0).two_le
  have hdvd : a.boxes 1 0 ∣ ∏ i, a.boxes 1 i := Finset.dvd_prod_of_mem _ (by simp)
  rw [← h1] at hdvd
  have := Nat.le_of_dvd one_pos hdvd
  omega

/-! ### Shape agreement is not ownership -/

/-- Two distinct rows with the same Balanced7 shape. -/
theorem same_shape_does_not_determine_row :
    ∃ n m : ℕ, n ≠ m ∧ Balanced7Shape n ∧ Balanced7Shape m := by
  refine ⟨510510, 570570, by norm_num, ?_, ?_⟩
  · have h : (510510 : ℕ) = ∏ p ∈ ({2, 3, 5, 7, 11, 13, 17} : Finset ℕ), p := by decide
    show (510510 : ℕ).primeFactors.card = 7
    rw [h, Nat.primeFactors_prod (by decide)]
    decide
  · have h : (570570 : ℕ) = ∏ p ∈ ({2, 3, 5, 7, 11, 13, 19} : Finset ℕ), p := by decide
    show (570570 : ℕ).primeFactors.card = 7
    rw [h, Nat.primeFactors_prod (by decide)]
    decide

/-- **`shape_only_boxes_impossible`.**  `KERNEL-PROVED`.

No box map depending on the *shape* alone (here: on `ω(n)`) can reconstruct the row.
Hence `same_shape → owner` is refuted. -/
theorem shape_only_boxes_impossible :
    ¬ ∃ f : ℕ → Fin 7 → ℕ, ∀ n : ℕ, Balanced7Shape n → n = ∏ i, f n.primeFactors.card i := by
  rintro ⟨f, hf⟩
  obtain ⟨n, m, hnm, hn, hm⟩ := same_shape_does_not_determine_row
  have h1 := hf n hn
  have h2 := hf m hm
  rw [show n.primeFactors.card = 7 from hn] at h1
  rw [show m.primeFactors.card = 7 from hm] at h2
  exact hnm (h1.trans h2.symm)

end OwnerScope

/-! ## §2.  The first-Cauchy firewall -/

namespace FirstCauchy

/-- The two positions of the argument relative to the first Cauchy–Schwarz step. -/
inductive CauchyStatus
  /-- Before Cauchy: the coefficient still carries its sign. -/
  | preCauchySigned
  /-- After Cauchy: only the squared modulus survives. -/
  | postCauchySquared
  deriving DecidableEq, Repr

theorem cauchyStatus_distinct :
    CauchyStatus.preCauchySigned ≠ CauchyStatus.postCauchySquared := by decide

/-- **`LinearSmallPrefixFactorisation`** — the structural record that the proposed regular
parent factorisation contains a **linear** small-prefix Möbius/Perron coefficient: the
parent coefficient is the prefix coefficient times a remaining factor, with no square. -/
structure LinearSmallPrefixFactorisation where
  /-- The parent coefficient. -/
  parent : ℕ → ℂ
  /-- The linear small-prefix Möbius/Perron coefficient. -/
  prefixCoeff : ℕ → ℂ
  /-- The remaining factor. -/
  rest : ℕ → ℂ
  /-- The factorisation is linear in the prefix coefficient. -/
  factor : ∀ n, parent n = prefixCoeff n * rest n

/-- Pre-Cauchy, the prefix sign is visible in the parent coefficient. -/
theorem prefix_sign_visible (f : LinearSmallPrefixFactorisation) (n : ℕ) :
    f.parent n = f.prefixCoeff n * f.rest n := f.factor n

/-- **`sign_consumed_by_modulus`.**  `KERNEL-PROVED`.

The algebraic sign-consumption identity: the squared modulus is blind to the prefix sign. -/
theorem sign_consumed_by_modulus (c : ℂ) : ‖-c‖ ^ 2 = ‖c‖ ^ 2 := by
  rw [norm_neg]

/-- **`cancellation_lost_after_cauchy`.**  `KERNEL-PROVED`.

Two prefix coefficients that cancel exactly before Cauchy contribute the full mass after
squaring.  This is the *algebraic* content of the first-Cauchy firewall. -/
theorem cancellation_lost_after_cauchy :
    ∃ a b : ℂ, ‖a + b‖ = 0 ∧ ‖a‖ ^ 2 + ‖b‖ ^ 2 = 2 := by
  refine ⟨1, -1, by norm_num, by norm_num⟩

/-- Status of the analytic insufficiency claim: **research metadata only**. -/
inductive ClaimStatus
  /-- Backed by a kernel theorem of this repository. -/
  | kernelTheorem
  /-- Recorded from the research audit; **no mathematical force**. -/
  | researchMetadata
  deriving DecidableEq, Repr

/-- The algebraic sign-consumption identity is a kernel theorem. -/
def signConsumptionStatus : ClaimStatus := ClaimStatus.kernelTheorem

/-- The claim "post-Cauchy is analytically insufficient" is **metadata**, not a theorem
of this repository. -/
def postCauchyInsufficiencyStatus : ClaimStatus := ClaimStatus.researchMetadata

theorem postCauchyInsufficiency_is_metadata :
    postCauchyInsufficiencyStatus ≠ ClaimStatus.kernelTheorem := by decide

end FirstCauchy
end Erdos287
