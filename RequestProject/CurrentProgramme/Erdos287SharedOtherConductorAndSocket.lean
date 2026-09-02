import RequestProject.CurrentProgramme.Erdos287SharedOtherRawArchitecture

/-!
# The 287A / shared-other45 conductor data, Δ-router and Ford-7.22 source socket

```
PROOF-LOCAL CONDUCTOR / SHARED-gcd DATA (two copies only) : KERNEL-PROVED
Δ-ROUTER (routing only)                                   : KERNEL-PROVED
Ford722OtherParentGeneratedUniformityInput                : OPEN EXTERNAL / UNINHABITED
GENERATED (A_η, B_η) CONTRACT, NOT THE k = 0 β_g PROFILE  : KERNEL-PROVED FIREWALL
NEWEST SOURCE CENSUS METADATA                             : represented, never proved
```

This module is **append-only**.  The analytic covariance theorem is **not** proved and
**not** inhabited: it is carried as an explicit structure, and §4 records a counterguard
showing that the structure is a genuine constraint rather than a decoration.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Erdos287
namespace SharedOtherParent

open Erdos287.SharedOtherRaw
open Erdos287.TwoLaneRawSource

/-! ## §0  Two concrete `U` data used as counterguard witnesses -/

/-- **`selectedE_singleton`.**  `KERNEL-PROVED`. -/
theorem selectedE_singleton (E : Finset Leaf)
    (h : ({E} : Finset (Finset Leaf)).Nonempty) : selectedE {E} h = E :=
  Finset.mem_singleton.1 (selectedE_mem _ h)

/-- A concrete `U` datum with the empty selected `E`. -/
noncomputable def sampleU : RawDataU 1 :=
  ⟨0, 0, [], {∅}, ⟨∅, Finset.mem_singleton_self _⟩, ∅,
    (selectedE_singleton _ ⟨∅, Finset.mem_singleton_self _⟩).symm,
    1, 1, le_rfl, ⟨0, 0, false⟩, true, true⟩

/-- A concrete `U` datum whose selected `E` is `{1}`. -/
noncomputable def sampleU' : RawDataU 1 :=
  ⟨0, 0, [], {{1}}, ⟨{1}, Finset.mem_singleton_self _⟩, {1},
    (selectedE_singleton _ ⟨{1}, Finset.mem_singleton_self _⟩).symm,
    1, 1, le_rfl, ⟨0, 0, false⟩, true, true⟩

/-! ## §1  Proof-local conductor and shared-gcd data

These objects exist **only after two copies exist**: the type is indexed by an ordered pair
of `U` data, and no field of a single `RawDataU` mentions `g`, `d`, `t`, `e`, `n` or `Δ`. -/

/-- **`SharedConductorData`** — the proof-local conductor decomposition of a *pair* of `U`
copies:

```
    q_i = g_i · d_i ,   h_i = d_i · t_i ,   e = gcd(g₁, g₂) ,   g_i = e · n_i .
```
-/
structure SharedConductorData {X : ℕ} (p₁ p₂ : RawDataU X) where
  /-- The first conductor. -/
  q₁ : ℕ
  /-- The second conductor. -/
  q₂ : ℕ
  /-- The first `g` factor. -/
  g₁ : ℕ
  /-- The second `g` factor. -/
  g₂ : ℕ
  /-- The first `d` factor. -/
  d₁ : ℕ
  /-- The second `d` factor. -/
  d₂ : ℕ
  /-- The first `h` datum. -/
  h₁ : ℕ
  /-- The second `h` datum. -/
  h₂ : ℕ
  /-- The first `t` factor. -/
  t₁ : ℕ
  /-- The second `t` factor. -/
  t₂ : ℕ
  /-- The shared gcd. -/
  e : ℕ
  /-- The first reduced factor. -/
  n₁ : ℕ
  /-- The second reduced factor. -/
  n₂ : ℕ
  /-- `q₁ = g₁ · d₁`. -/
  q₁_def : q₁ = g₁ * d₁
  /-- `q₂ = g₂ · d₂`. -/
  q₂_def : q₂ = g₂ * d₂
  /-- `h₁ = d₁ · t₁`. -/
  h₁_def : h₁ = d₁ * t₁
  /-- `h₂ = d₂ · t₂`. -/
  h₂_def : h₂ = d₂ * t₂
  /-- `e = gcd(g₁, g₂)`. -/
  e_def : e = Nat.gcd g₁ g₂
  /-- `g₁ = e · n₁`. -/
  g₁_def : g₁ = e * n₁
  /-- `g₂ = e · n₂`. -/
  g₂_def : g₂ = e * n₂
  /-- The shared gcd is positive. -/
  e_pos : 0 < e

namespace SharedConductorData

variable {X : ℕ} {p₁ p₂ : RawDataU X}

/-- **`Delta`** — the two-copy determinant `Δ = t₁·n₂ − t₂·n₁`. -/
def Delta (D : SharedConductorData p₁ p₂) : ℤ := (D.t₁ : ℤ) * D.n₂ - (D.t₂ : ℤ) * D.n₁

/-- **`e_dvd_g₁`.**  `KERNEL-PROVED`. -/
theorem e_dvd_g₁ (D : SharedConductorData p₁ p₂) : D.e ∣ D.g₁ := ⟨D.n₁, D.g₁_def⟩

/-- **`e_dvd_g₂`.**  `KERNEL-PROVED`. -/
theorem e_dvd_g₂ (D : SharedConductorData p₁ p₂) : D.e ∣ D.g₂ := ⟨D.n₂, D.g₂_def⟩

/-- **`n₁_eq_div`.**  `KERNEL-PROVED`.  `n₁` is the reduced first factor. -/
theorem n₁_eq_div (D : SharedConductorData p₁ p₂) : D.n₁ = D.g₁ / Nat.gcd D.g₁ D.g₂ := by
  rw [← D.e_def, D.g₁_def, Nat.mul_div_cancel_left _ D.e_pos]

/-- **`n₂_eq_div`.**  `KERNEL-PROVED`. -/
theorem n₂_eq_div (D : SharedConductorData p₁ p₂) : D.n₂ = D.g₂ / Nat.gcd D.g₁ D.g₂ := by
  rw [← D.e_def, D.g₂_def, Nat.mul_div_cancel_left _ D.e_pos]

/-- **`reduced_factors_coprime`.**  `KERNEL-PROVED`.

The reduced factors `n₁, n₂` obtained by dividing out the shared gcd are coprime. -/
theorem reduced_factors_coprime (D : SharedConductorData p₁ p₂) :
    Nat.Coprime D.n₁ D.n₂ := by
  have hg : 0 < Nat.gcd D.g₁ D.g₂ := D.e_def ▸ D.e_pos
  rw [D.n₁_eq_div, D.n₂_eq_div]
  exact Nat.coprime_div_gcd_div_gcd hg

/-- **`q_factorisations`.**  `KERNEL-PROVED`.  The literal conductor factorisations. -/
theorem q_factorisations (D : SharedConductorData p₁ p₂) :
    D.q₁ = D.g₁ * D.d₁ ∧ D.q₂ = D.g₂ * D.d₂ ∧ D.h₁ = D.d₁ * D.t₁ ∧ D.h₂ = D.d₂ * D.t₂ :=
  ⟨D.q₁_def, D.q₂_def, D.h₁_def, D.h₂_def⟩

/-- **`Delta_zero_iff_proportional`.**  `KERNEL-PROVED`.

`Δ = 0` exactly when the two `(t, n)` rows are proportional. -/
theorem Delta_zero_iff_proportional (D : SharedConductorData p₁ p₂) :
    D.Delta = 0 ↔ (D.t₁ : ℤ) * D.n₂ = (D.t₂ : ℤ) * D.n₁ := by
  rw [Delta, sub_eq_zero]

end SharedConductorData

/-- **`Delta_is_a_genuine_two_copy_object`.**  `KERNEL-PROVED`.

`Δ` is not a coordinate of a single copy: the same ordered pair of copies carries conductor
data with different `Δ`. -/
theorem Delta_is_a_genuine_two_copy_object :
    ∃ (p : RawDataU 1) (D₁ D₂ : SharedConductorData p p), D₁.Delta ≠ D₂.Delta := by
  refine ⟨sampleU, ?_⟩
  refine ⟨⟨1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      Nat.one_pos⟩,
    ⟨1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      Nat.one_pos⟩, ?_⟩
  norm_num [SharedConductorData.Delta]

/-! ## §2  The Δ-router — routing only -/

/-- **`OtherOwner`** — the three routed classes of the shared-other architecture. -/
inductive OtherOwner
  /-- The `Δ = 0` class. -/
  | c0
  /-- The transverse class. -/
  | transverse
  /-- The `b`-diagonal class. -/
  | bDiagonal
  deriving DecidableEq, Fintype, Repr

/-- **`deltaRoute`** — the router.  It performs **routing only**: it inspects `Δ` and the two
`b` coordinates and returns a class label, and carries no estimate. -/
def deltaRoute (Delta b₁ b₂ : ℤ) : OtherOwner :=
  if Delta = 0 then OtherOwner.c0
  else if b₁ ≠ b₂ then OtherOwner.transverse
  else OtherOwner.bDiagonal

/-- **`deltaRoute_c0_iff`.**  `KERNEL-PROVED`. -/
theorem deltaRoute_c0_iff (Delta b₁ b₂ : ℤ) :
    deltaRoute Delta b₁ b₂ = OtherOwner.c0 ↔ Delta = 0 := by
  unfold deltaRoute
  split_ifs with h1 h2 <;> simp_all

/-- **`deltaRoute_transverse_iff`.**  `KERNEL-PROVED`. -/
theorem deltaRoute_transverse_iff (Delta b₁ b₂ : ℤ) :
    deltaRoute Delta b₁ b₂ = OtherOwner.transverse ↔ Delta ≠ 0 ∧ b₁ ≠ b₂ := by
  unfold deltaRoute
  split_ifs with h1 h2 <;> simp_all

/-- **`deltaRoute_bDiagonal_iff`.**  `KERNEL-PROVED`. -/
theorem deltaRoute_bDiagonal_iff (Delta b₁ b₂ : ℤ) :
    deltaRoute Delta b₁ b₂ = OtherOwner.bDiagonal ↔ Delta ≠ 0 ∧ b₁ = b₂ := by
  unfold deltaRoute
  split_ifs with h1 h2 <;> simp_all

/-- **`deltaRoute_exists_unique`.**  `KERNEL-PROVED`.  Every input is routed to exactly one
class. -/
theorem deltaRoute_exists_unique (Delta b₁ b₂ : ℤ) :
    ∃! o : OtherOwner, deltaRoute Delta b₁ b₂ = o :=
  ⟨deltaRoute Delta b₁ b₂, rfl, fun _ h => h.symm⟩

/-- **`deltaRoute_is_routing_only`.**  `KERNEL-PROVED`.

The router carries no analytic content: two inputs routed to the same class can carry
arbitrarily different data. -/
theorem deltaRoute_is_routing_only :
    ∃ D₁ D₂ b : ℤ, D₁ ≠ D₂ ∧ deltaRoute D₁ b b = deltaRoute D₂ b b := by
  refine ⟨1, 2, 0, by norm_num, ?_⟩
  norm_num [deltaRoute]

/-! ## §3  The Ford-7.22 other-parent generated-uniformity socket -/

/-- **`Ford722OtherParentGeneratedUniformityInput`** — `OPEN EXTERNAL / UNINHABITED`.

The exact source contract of the shared other-parent covariance estimate, stated in the
**generated** coefficients `A_η(a;τ)`, `B_η(b;τ)` of the selected `E` — *never* in the old
`k = 0` `β_g` profile — and carrying the newest source census metadata:

* selected-`E` prime extraction `m = π·z` with `π` prime;
* complement opening `n = y·c`;
* the census determinant `ℓ·q − (π·z·y)·c = 2`;
* the `d ≥ 3` two-atom `4/9` router;
* residual coarse depth exactly `2`;
* two surviving complement atoms that are *distinct linear* HB `f`-leaves;
* a coefficient pattern drawn from `1×1`, `log x ×1`, `log x × log`.

The final field is the analytic covariance conclusion.  **This structure is never
inhabited.** -/
structure Ford722OtherParentGeneratedUniformityInput {X : ℕ} (p : RawDataU X)
    (eta : ℕ → ℝ) (chi : ℕ → ℤ → ℝ) (S T : Finset ℕ) (kernel : ℕ → ℕ → ℤ → ℝ)
    (tau : ℤ) (bound : ℝ) where
  /-- The packet is a genuine `k ≥ 1` leaf, not a `k = 0` profile. -/
  k_at_least_one : 1 ≤ p.k
  /-- The extracted selected-`E` prime. -/
  piPrime : ℕ
  /-- It is prime. -/
  piPrime_prime : Nat.Prime piPrime
  /-- The cofactor of the extraction. -/
  z : ℕ
  /-- The extracted modulus. -/
  m : ℕ
  /-- The prime extraction `m = π·z`. -/
  m_def : m = piPrime * z
  /-- The first complement factor. -/
  y : ℕ
  /-- The second complement factor. -/
  c : ℕ
  /-- The opened complement. -/
  n : ℕ
  /-- The complement opening `n = y·c`. -/
  n_def : n = y * c
  /-- The determinant parameter. -/
  ell : ℤ
  /-- The determinant conductor. -/
  q : ℤ
  /-- The census determinant `ℓ·q − (π·z·y)·c = 2`. -/
  census_determinant : ell * q - ((piPrime : ℤ) * z * y) * c = 2
  /-- The router depth. -/
  d : ℕ
  /-- The two-atom weight. -/
  twoAtomWeight : ℝ
  /-- The `d ≥ 3` two-atom `4/9` router. -/
  two_atom_router : 3 ≤ d → twoAtomWeight ≤ 4 / 9
  /-- The residual coarse depth. -/
  coarseDepth : ℕ
  /-- The residual coarse depth is exactly `2`. -/
  coarseDepth_eq_two : coarseDepth = 2
  /-- The first surviving complement atom. -/
  atom₁ : HBLeaf
  /-- The second surviving complement atom. -/
  atom₂ : HBLeaf
  /-- The two surviving atoms are distinct. -/
  atoms_distinct : atom₁ ≠ atom₂
  /-- The first surviving atom is a linear HB `f`-leaf. -/
  atom₁_linear : atom₁.kind = HBLeafKind.linear
  /-- The second surviving atom is a linear HB `f`-leaf. -/
  atom₂_linear : atom₂.kind = HBLeafKind.linear
  /-- Both surviving atoms belong to the packet's literal HB grammar. -/
  atoms_in_grammar : atom₁ ∈ p.hbGrammar ∧ atom₂ ∈ p.hbGrammar
  /-- The coefficient pattern of the row. -/
  pattern : CoefficientPattern
  /-- **The analytic covariance conclusion**, in the generated coefficients. -/
  generated_uniformity :
    |∑ a ∈ S, ∑ b ∈ T, A_eta p eta chi a tau * B_eta p eta chi b tau * kernel a b tau|
      ≤ bound

/-- **`coefficientPattern_is_exactly_the_three_source_patterns`.**  `KERNEL-PROVED`.

The coefficient-pattern type has exactly the three source patterns `1×1`, `log x ×1`,
`log x × log`. -/
theorem coefficientPattern_is_exactly_the_three_source_patterns :
    Fintype.card CoefficientPattern = 3 := by decide

/-- **`ford722_census_metadata`.**  `KERNEL-PROVED CONDITIONAL`.

Read-out of the census metadata carried by any inhabitant.  It is *conditional*: no
inhabitant is constructed. -/
theorem ford722_census_metadata {X : ℕ} {p : RawDataU X} {eta : ℕ → ℝ} {chi : ℕ → ℤ → ℝ}
    {S T : Finset ℕ} {kernel : ℕ → ℕ → ℤ → ℝ} {tau : ℤ} {bound : ℝ}
    (I : Ford722OtherParentGeneratedUniformityInput p eta chi S T kernel tau bound) :
    I.m = I.piPrime * I.z ∧ Nat.Prime I.piPrime ∧ I.n = I.y * I.c ∧
    I.ell * I.q - ((I.piPrime : ℤ) * I.z * I.y) * I.c = 2 ∧
    I.coarseDepth = 2 ∧ I.atom₁ ≠ I.atom₂ ∧
    I.atom₁.kind = HBLeafKind.linear ∧ I.atom₂.kind = HBLeafKind.linear ∧
    (3 ≤ I.d → I.twoAtomWeight ≤ 4 / 9) ∧ 1 ≤ p.k :=
  ⟨I.m_def, I.piPrime_prime, I.n_def, I.census_determinant, I.coarseDepth_eq_two,
    I.atoms_distinct, I.atom₁_linear, I.atom₂_linear, I.two_atom_router, I.k_at_least_one⟩

/-! ## §4  Counterguards: the socket is a genuine, uninhabited constraint -/

/-- **`ford722_socket_is_a_genuine_constraint`.**  `KERNEL-PROVED`.

The socket is refutable at explicit data: a negative bound makes the covariance conclusion
impossible, so the structure carries real mathematical content and is not a decoration. -/
theorem ford722_socket_is_a_genuine_constraint :
    IsEmpty (Ford722OtherParentGeneratedUniformityInput sampleU (fun _ => 1)
      (fun _ _ => 1) ∅ ∅ (fun _ _ _ => 1) 0 (-1)) := by
  constructor
  intro I
  have h := I.generated_uniformity
  simp only [Finset.sum_empty, abs_zero] at h
  linarith

/-- **`ford722_socket_needs_k_at_least_one`.**  `KERNEL-PROVED`.

The socket is not satisfiable by a `k = 0` leaf: the `k ≥ 1` field excludes it. -/
theorem ford722_socket_needs_k_at_least_one {X : ℕ} {p : RawDataU X} {eta : ℕ → ℝ}
    {chi : ℕ → ℤ → ℝ} {S T : Finset ℕ} {kernel : ℕ → ℕ → ℤ → ℝ} {tau : ℤ} {bound : ℝ}
    (hk : p.k = 0) :
    IsEmpty (Ford722OtherParentGeneratedUniformityInput p eta chi S T kernel tau bound) := by
  constructor
  intro I
  have := I.k_at_least_one
  omega

/-! ## §5  The `k = 0` `β_g` profile firewall -/

/-- **`betaGProfile`** — the *old* `k = 0` profile of a packet: the bare `u`/`v` slots. -/
def betaGProfile {X : ℕ} (p : RawDataU X) : ℕ × ℕ := (p.u, p.v)

/-- **`betaG_profile_does_not_determine_the_generated_coefficients`.**  `KERNEL-PROVED`.

The source contract may **not** be phrased in the old `k = 0` `β_g` profile: two packets
with the same profile generate different `A_η`. -/
theorem betaG_profile_does_not_determine_the_generated_coefficients :
    betaGProfile sampleU = betaGProfile sampleU' ∧
    A_eta sampleU (fun _ => 1) (fun _ _ => 1) 1 0
      ≠ A_eta sampleU' (fun _ => 1) (fun _ _ => 1) 1 0 := by
  refine ⟨rfl, ?_⟩
  have e1 : A_eta sampleU (fun _ => 1) (fun _ _ => 1) 1 0 = 0 := by
    simp [A_eta, sampleU]
  have e2 : A_eta sampleU' (fun _ => 1) (fun _ _ => 1) 1 0 = 1 := by
    simp [A_eta, sampleU']
    decide
  rw [e1, e2]
  norm_num

end SharedOtherParent
end Erdos287
