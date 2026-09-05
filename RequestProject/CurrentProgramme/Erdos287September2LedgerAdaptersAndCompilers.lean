import RequestProject.CurrentProgramme.Erdos287N2EffectiveConstantsBank

/-!
# Erdős #287 — September-2 bank, §6–§13: the typed Perron/nuclear ledger pin, the hard-`U`
adapter socket, the b-diagonal bypass, the `E_L` compiler, the `N2` bank and the four-error
interface

```
TYPED PERRON / NUCLEAR LEDGER SOCKET      : DEFINED, UNINHABITED here
HARD-U → SHARED-FORD SOURCE SOCKET        : DEFINED, UNINHABITED here
b-DIAGONAL BYPASS                         : KERNEL-PROVED CONDITIONAL (antecedent not asserted)
E_L COMPILER                              : KERNEL-PROVED CONDITIONAL
PRIME-PAIR-SIEVE-SURVIVAL45 (finite form) : KERNEL-PROVED from its finite inequalities
2·X_N2 > 4·10⁹                            : KERNEL-PROVED  ⇒ current finite splice FAILS
FOUR-ERROR ALGEBRAIC INTERFACE            : KERNEL-PROVED (algebra only)
```

Nothing here proves an analytic estimate, no socket is inhabited, and Erdős #287 is **not**
claimed.  This module is **append-only**.

**§6.**  `Erdos287TypedPerronNuclearLedgerInput` bundles the full physical obligation (piece
census, coefficients `c_a`, derivative norms, exact polytope constraint count, the
Lemma-7.11 kernel mass, the Lemma-7.14 box/reassembly mass, the Mellin masses and
owner-preserving reassembly).  **No term of this type is constructed anywhere.**  It is
kernel-checked that the record is a genuine constraint (data violating it exist) and that it
does **not** contain its intended conclusion as a field: ledger data satisfying the contract
need not give a small total Perron mass.

**§7.**  `Erdos287HardUToSharedFordSourceInput` demands *index-wise equality* of the #287
physical hard-`U` source and the neutral shared Ford source, in all of: determinant,
orientation, coefficient, support, selected-`E` data, model subtraction, Perron/Mellin
kernel.  **Uninhabited here.**  Kernel-proved: equality of six of the seven components does
not imply row equality, so the selected-`E` clause (say) cannot be dropped.

**§8.**  The direct one-copy provider bypass is proved *only* as a logical dependency: if the
adapter lands in the neutral `d₀·wp` provider before any Cauchy step in the outer variables,
then the two-copy `bDiagonal / rectangle / Ω_H` package is not consumed on that route.  The
antecedent is **not** asserted.

**§9.**  The `E_L` compiler is conditional on the (uninhabited) hard-`U` source equality, so
`E_L` remains `OPEN / CONDITIONAL`.

**§11–§12.**  The `N2` constants are recorded as metadata; the elementary survival inequality
is proved from finite hypotheses only; and the effectivity firewall `2·X_N2 > 4·10⁹` shows
the current `N2`-based finite splice fails.  This is *not* an `N2` analytic failure.

**§13.**  The four-error interface `PrimeMass ≥ m_ε B_X − E_T − E_L − E_2 − E_M` is used only
as algebra: no analytic error bound is inhabited in order to obtain positivity.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos287
namespace September2Ledger

/-! ## §6  The complete typed Perron / nuclear ledger pin -/

/-- The physical data a complete typed Perron/nuclear ledger must supply. -/
structure LedgerData where
  /-- The physical `g_ε` piece census. -/
  pieceCensus : ℕ
  /-- The coefficients `c_a` of the pieces. -/
  coeff : ℕ → ℝ
  /-- The derivative norms of the pieces. -/
  derivativeNorm : ℕ → ℝ
  /-- The exact polytope constraint count. -/
  polytopeConstraints : ℕ
  /-- The Lemma-7.11 kernel mass. -/
  kernelMass711 : ℝ
  /-- The Lemma-7.14 box / reassembly mass. -/
  boxMass714 : ℝ
  /-- The Mellin masses. -/
  mellinMass : ℝ
  /-- Whether the packet reassembly is owner-preserving. -/
  ownerPreservingReassembly : Bool

/-- The contract a ledger must satisfy.  It is a constraint on the supplied physical data;
it does **not** contain the desired total-mass conclusion. -/
def LedgerContract (d : LedgerData) : Prop :=
  0 < d.pieceCensus ∧ 0 < d.polytopeConstraints ∧
    (∀ a, a < d.pieceCensus → |d.coeff a| ≤ 1) ∧
    (∀ a, a < d.pieceCensus → 0 ≤ d.derivativeNorm a) ∧
    d.ownerPreservingReassembly = true

/-- **`Erdos287TypedPerronNuclearLedgerInput`** — the complete typed Perron / nuclear ledger
obligation.  `LEFT UNINHABITED`: no term of this type is constructed in this development. -/
structure Erdos287TypedPerronNuclearLedgerInput where
  /-- The supplied physical ledger data. -/
  data : LedgerData
  /-- The ledger contract holds for the supplied data. -/
  contract : LedgerContract data

/-- **`ledger_contract_is_a_genuine_constraint`.**  `KERNEL-PROVED`.  The contract is not
vacuous: explicit data violate it. -/
theorem ledger_contract_is_a_genuine_constraint :
    ∃ d : LedgerData, ¬ LedgerContract d := by
  refine ⟨⟨0, fun _ => 0, fun _ => 0, 0, 0, 0, 0, false⟩, ?_⟩
  rintro ⟨h, -⟩
  exact absurd h (by norm_num)

/-- The total Perron mass carried by ledger data. -/
def totalPerronMass (d : LedgerData) : ℝ :=
  d.kernelMass711 + d.boxMass714 + d.mellinMass

/-- **`ledger_contract_does_not_bound_the_mass`.**  `KERNEL-PROVED`.  The desired conclusion
is **not** stored inside the source record: ledger data may satisfy the contract and still
have arbitrarily large total Perron mass. -/
theorem ledger_contract_does_not_bound_the_mass (B : ℝ) :
    ∃ d : LedgerData, LedgerContract d ∧ B < totalPerronMass d := by
  refine ⟨⟨1, fun _ => 0, fun _ => 0, 1, |B| + 1, 0, 0, true⟩, ⟨?_, ?_, ?_, ?_, rfl⟩, ?_⟩
  · norm_num
  · norm_num
  · intro a _; norm_num
  · intro a _; norm_num
  · have : B ≤ |B| := le_abs_self B
    simp only [totalPerronMass]
    linarith

/-! ## §7  The hard-`U` → shared-Ford source adapter socket -/

/-- One physical source row, with every attribute the adapter certificate must match. -/
structure SourceRow where
  /-- The determinant line value. -/
  det : ℤ
  /-- The contour orientation. -/
  orientation : Bool
  /-- The generated coefficient. -/
  coefficient : ℤ
  /-- The physical support. -/
  support : Finset ℕ
  /-- The selected-`E` data. -/
  selectedE : Finset ℕ
  /-- The model subtraction. -/
  modelSubtraction : ℤ
  /-- The Perron/Mellin kernel label. -/
  perronMellinKernel : ℕ
  deriving DecidableEq

/-- **`Erdos287HardUToSharedFordSourceInput`** — the literal index-wise source-equality
certificate between the #287 physical hard-`U` source and the neutral shared Ford source.
`LEFT UNINHABITED`: no term of this type is constructed in this development, and in
particular no Twin/HSTAR theorem inhabits it. -/
structure Erdos287HardUToSharedFordSourceInput where
  /-- The common index type of the two sources. -/
  Idx : Type
  /-- The #287 physical hard-`U` source. -/
  hardU : Idx → SourceRow
  /-- The neutral shared Ford source. -/
  sharedFord : Idx → SourceRow
  /-- Literal index-wise equality of the two sources. -/
  rowwise_eq : ∀ i, hardU i = sharedFord i

/-- **`adapter_gives_componentwise_equality`.**  `KERNEL-PROVED`.  An inhabitant of the socket
yields equality of all seven certified components. -/
theorem adapter_gives_componentwise_equality
    (A : Erdos287HardUToSharedFordSourceInput) (i : A.Idx) :
    (A.hardU i).det = (A.sharedFord i).det ∧
    (A.hardU i).orientation = (A.sharedFord i).orientation ∧
    (A.hardU i).coefficient = (A.sharedFord i).coefficient ∧
    (A.hardU i).support = (A.sharedFord i).support ∧
    (A.hardU i).selectedE = (A.sharedFord i).selectedE ∧
    (A.hardU i).modelSubtraction = (A.sharedFord i).modelSubtraction ∧
    (A.hardU i).perronMellinKernel = (A.sharedFord i).perronMellinKernel := by
  have h := A.rowwise_eq i
  rw [h]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **`selectedE_clause_cannot_be_dropped`.**  `KERNEL-PROVED`.  Six of the seven components
may agree while the rows differ: the selected-`E` clause is load-bearing in the certificate. -/
theorem selectedE_clause_cannot_be_dropped :
    ∃ r s : SourceRow,
      r.det = s.det ∧ r.orientation = s.orientation ∧ r.coefficient = s.coefficient ∧
      r.support = s.support ∧ r.modelSubtraction = s.modelSubtraction ∧
      r.perronMellinKernel = s.perronMellinKernel ∧ r ≠ s := by
  refine ⟨⟨0, false, 0, ∅, ∅, 0, 0⟩, ⟨0, false, 0, ∅, {0}, 0, 0⟩, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  intro h
  have : (∅ : Finset ℕ) = ({0} : Finset ℕ) := congrArg SourceRow.selectedE h
  simp at this

/-! ## §8  The direct provider / b-diagonal firewall -/

/-- **`DirectOneCopyProviderBypassesBDiagonalInput`** — the *conditional* proposition: if the
hard-`U` source adapter lands directly in the neutral `d₀·wp` provider before any Cauchy step
in the outer variables, then the old two-copy `bDiagonal / rectangle / Ω_H` package is not
consumed on that route.  Only the logical dependency is proved; the antecedent is **not**
asserted. -/
structure DirectOneCopyProviderBypassesBDiagonalInput where
  /-- The adapter lands directly in the neutral `d₀·wp` provider. -/
  landsInDirectProvider : Prop
  /-- A Cauchy step is taken in the outer variables. -/
  cauchyStepInOuterVariables : Prop
  /-- The two-copy `bDiagonal / rectangle / Ω_H` package is consumed. -/
  consumesBDiagonalPackage : Prop
  /-- The route implication. -/
  bypass : landsInDirectProvider → ¬ cauchyStepInOuterVariables → ¬ consumesBDiagonalPackage

/-- **`bDiagonal_bypassed_conditionally`.**  `KERNEL-PROVED`, conditional. -/
theorem bDiagonal_bypassed_conditionally (R : DirectOneCopyProviderBypassesBDiagonalInput)
    (h₁ : R.landsInDirectProvider) (h₂ : ¬ R.cauchyStepInOuterVariables) :
    ¬ R.consumesBDiagonalPackage :=
  R.bypass h₁ h₂

/-- **`bypass_antecedent_is_not_asserted`.**  `KERNEL-PROVED`.  The record exists with a false
antecedent, so its existence asserts nothing about the actual route. -/
theorem bypass_antecedent_is_not_asserted :
    ∃ R : DirectOneCopyProviderBypassesBDiagonalInput, ¬ R.landsInDirectProvider := by
  refine ⟨⟨False, True, True, ?_⟩, ?_⟩
  · intro h _
    exact absurd h (by simp)
  · simp

/-! ## §9  The conditional `E_L` compiler -/

/-- **`E_L_conditional_bound`.**  `KERNEL-PROVED`, conditional.  From
(i) the hard-`U` source equality certificate, (ii) a neutral `d₀·wp` analytic bound
`E_L ≤ δ · B_X`, and (iii) a fixed/polylog source-mass input `δ ≤ δ₀`, the `E_L` conclusion
`E_L ≤ δ₀ · B_X` follows.  Since the socket of (i) is uninhabited here, `E_L` stays
`OPEN / CONDITIONAL`. -/
theorem E_L_conditional_bound
    (_A : Erdos287HardUToSharedFordSourceInput)
    {E_L delta delta0 B_X : ℝ}
    (hprovider : E_L ≤ delta * B_X) (hmass : delta ≤ delta0) (hB : 0 ≤ B_X) :
    E_L ≤ delta0 * B_X := by
  have : delta * B_X ≤ delta0 * B_X := by
    exact mul_le_mul_of_nonneg_right hmass hB
  linarith

/-! ## §11  The `N2` bank and the elementary survival inequality -/

/-- `C_pair = 11`. -/
def C_pair : ℕ := 11

/-- **`Cpair_C2LF_below_collar`.**  `KERNEL-PROVED`.  A recorded arithmetic relation between
the banked constants. -/
theorem Cpair_C2LF_below_collar :
    C_pair * N2ConstantsBank.C_2LF < N2ConstantsBank.K_collar_bound := by
  unfold C_pair N2ConstantsBank.C_2LF N2ConstantsBank.K_collar_bound
  norm_num

/-- **`fourLossSurvivalPositivity`.**  `KERNEL-PROVED` from its finite inequalities only.
Generic four-loss positivity: if a main term dominates the pair and two-linear-form losses
together with the collar loss, then the surviving count is positive.

This is **not** the Bordignon–Lee sieve-survival bridge and must not be read as one: it is a
named piece of real arithmetic with all three loss bounds as hypotheses.  The genuine
elementary survival/inclusion bridge is `PrimePairSieve.primePairSieveSurvival45` below. -/
theorem fourLossSurvivalPositivity
    {mainTerm pairLoss twoLFLoss collarLoss survival : ℝ}
    (hsurv : survival ≥ mainTerm - pairLoss - twoLFLoss - collarLoss)
    (hpair : pairLoss ≤ mainTerm / 4)
    (h2lf : twoLFLoss ≤ mainTerm / 4)
    (hcollar : collarLoss ≤ mainTerm / 5)
    (hmain : 0 < mainTerm) :
    0 < survival := by
  have : mainTerm - pairLoss - twoLFLoss - collarLoss ≥ mainTerm * (1 - 1/4 - 1/4 - 1/5) := by
    have h1 : mainTerm / 4 = mainTerm * (1/4) := by ring
    have h2 : mainTerm / 5 = mainTerm * (1/5) := by ring
    rw [h1] at hpair h2lf
    rw [h2] at hcollar
    nlinarith
  nlinarith

/-! ### §11.1  The genuine elementary prime-pair sieve-survival bridge -/

namespace PrimePairSieve

/-- The banked physical data of the prime-pair window.

```
Q = X / (2M),   I(M) ⊆ (Q, 2Q],   H = |I(M) ∩ ℤ| ≤ Q + 1,   z = H^(49/100),
long sector:  H ≥ H_BL  with  H − 1 > H^(49/100).
```

Only the finite inequalities are recorded; no analytic sieve statement is part of this
record. -/
structure WindowData where
  /-- The global parameter `X`. -/
  X : ℝ
  /-- The modulus parameter `M ≥ 1`. -/
  M : ℕ
  /-- `M ≥ 1`. -/
  hM : 1 ≤ M
  /-- The window scale `Q = X / (2M)`. -/
  Q : ℝ
  /-- The definition of `Q`. -/
  hQ : Q = X / (2 * M)
  /-- The integer count `H = |I(M) ∩ ℤ|` of the sector. -/
  H : ℕ
  /-- `H ≥ 1`. -/
  hH1 : 1 ≤ H
  /-- The window bound `H ≤ Q + 1`. -/
  hHQ : (H : ℝ) ≤ Q + 1
  /-- The sieve level `z = H^(49/100)`. -/
  z : ℝ
  /-- The definition of `z`. -/
  hz : z = (H : ℝ) ^ ((49 : ℝ) / 100)
  /-- The long-sector hypothesis `H − 1 > H^(49/100)`. -/
  hlong : z < (H : ℝ) - 1

/-- **`windowData_inhabited`.**  `KERNEL-PROVED`.  The banked window hypotheses are
consistent (`X = 8`, `M = 1`, `Q = 4`, `H = 4`, `z = 4^(49/100) < 3`), so the survival bridge
below is not vacuous. -/
theorem windowData_inhabited : Nonempty WindowData := by
  have hsqrt : (4:ℝ) ^ ((1:ℝ)/2) = 2 := by
    rw [← Real.sqrt_eq_rpow, show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hz3 : (4:ℝ) ^ ((49:ℝ)/100) < 3 := by
    have hle : (4:ℝ) ^ ((49:ℝ)/100) ≤ (4:ℝ) ^ ((1:ℝ)/2) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    rw [hsqrt] at hle
    linarith
  refine ⟨⟨8, 1, le_refl 1, 4, by norm_num, 4, by norm_num, by norm_num,
    (4:ℝ) ^ ((49:ℝ)/100), by norm_num, ?_⟩⟩
  norm_num
  linarith

variable (d : WindowData)

/-- **`one_le_z`.**  `KERNEL-PROVED`.  `z = H^(49/100) ≥ 1`. -/
theorem one_le_z : 1 ≤ d.z := by
  rw [d.hz]
  exact Real.one_le_rpow (by exact_mod_cast d.hH1) (by norm_num)

/-- **`z_lt_Q`.**  `KERNEL-PROVED`.  `Q ≥ H − 1 > z`. -/
theorem z_lt_Q : d.z < d.Q := by
  have h := d.hHQ
  have := d.hlong
  linarith

/-- **`sector_element_exceeds_z`.**  `KERNEL-PROVED`.  Every `q ∈ I(M)` satisfies
`q > Q ≥ H − 1 > z`. -/
theorem sector_element_exceeds_z {q : ℕ} (hq : d.Q < (q : ℝ)) : d.z < (q : ℝ) :=
  lt_trans (z_lt_Q d) hq

/-- **`two_le_sector_element`.**  `KERNEL-PROVED`.  A sector element is at least `2`. -/
theorem two_le_sector_element {q : ℕ} (hq : d.Q < (q : ℝ)) : 2 ≤ q := by
  have h1 : (1 : ℝ) < (q : ℝ) := lt_of_le_of_lt (one_le_z d) (sector_element_exceeds_z d hq)
  have : (1 : ℕ) < q := by exact_mod_cast h1
  omega

/-- **`shifted_element_exceeds_z`.**  `KERNEL-PROVED`.  For `s ∈ {−1, +1}` and `M ≥ 1`,

```
    2 M q + s ≥ 2 M q − 1 > q > z .
```
-/
theorem shifted_element_exceeds_z {q : ℕ} (hq : d.Q < (q : ℝ)) {s : ℤ}
    (hs : s = 1 ∨ s = -1) :
    d.z < ((2 * (d.M : ℤ) * (q : ℤ) + s : ℤ) : ℝ) := by
  have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast two_le_sector_element d hq
  have hM1 : (1 : ℝ) ≤ (d.M : ℝ) := by exact_mod_cast d.hM
  have hs' : ((s : ℝ)) = 1 ∨ ((s : ℝ)) = -1 := by
    rcases hs with h | h <;> rw [h] <;> norm_num
  have hzq : d.z < (q : ℝ) := sector_element_exceeds_z d hq
  have hkey : (q : ℝ) < 2 * (d.M : ℝ) * (q : ℝ) - 1 := by nlinarith
  have hcast : ((2 * (d.M : ℤ) * (q : ℤ) + s : ℤ) : ℝ)
      = 2 * (d.M : ℝ) * (q : ℝ) + (s : ℝ) := by push_cast; ring
  rw [hcast]
  rcases hs' with h | h <;> rw [h] <;> linarith

/-- **`no_small_prime_divisor`.**  `KERNEL-PROVED`.  A prime `m` above the sieve level has no
prime divisor below the sieve level. -/
theorem no_small_prime_divisor {m : ℕ} (hm : m.Prime) {p : ℕ} (hp : p.Prime)
    (hpz : (p : ℝ) < d.z) (hzm : d.z < (m : ℝ)) : ¬ p ∣ m := by
  intro hdvd
  have hpm : p = m := (Nat.prime_dvd_prime_iff_eq hp hm).mp hdvd
  have : (p : ℝ) < (m : ℝ) := lt_trans hpz hzm
  rw [hpm] at this
  exact lt_irrefl _ this

/-- **`primePairSieveSurvival45`.**  `KERNEL-PROVED`.  The genuine elementary
survival/inclusion bridge for the prime-pair window.

If `q` lies in the sector `I(M) ⊆ (Q, 2Q]`, and both coordinates

```
    q          and          n = 2 M q + s        (s = ±1)
```

are prime, then **neither coordinate is divisible by any prime `p < z`**; that is, every
simultaneous-prime pair of the window survives the `z`-sieve.

This is an inclusion statement obtained from the finite inequalities
`q > Q ≥ H − 1 > z` and `2 M q + s ≥ 2 M q − 1 > q > z` only.  **No Bordignon–Lee analytic
sieve theorem is used or asserted here.** -/
theorem primePairSieveSurvival45 {q : ℕ} (hq : d.Q < (q : ℝ)) (hqp : q.Prime)
    {s : ℤ} (hs : s = 1 ∨ s = -1) {n : ℕ} (hn : (n : ℤ) = 2 * (d.M : ℤ) * (q : ℤ) + s)
    (hnp : n.Prime) :
    ∀ p : ℕ, p.Prime → (p : ℝ) < d.z → ¬ p ∣ q ∧ ¬ p ∣ n := by
  intro p hp hpz
  have hqz : d.z < (q : ℝ) := sector_element_exceeds_z d hq
  have hnz : d.z < (n : ℝ) := by
    have h := shifted_element_exceeds_z d hq hs
    have hcast : ((n : ℤ) : ℝ) = (n : ℝ) := by push_cast; ring
    rw [hn] at hcast
    rw [← hcast]
    exact h
  exact ⟨no_small_prime_divisor d hqp hp hpz hqz, no_small_prime_divisor d hnp hp hpz hnz⟩

/-- **`survival_bridge_is_not_the_analytic_sieve`.**  `KERNEL-PROVED`.  Surviving the
`z`-sieve is strictly weaker than primality: an integer can avoid every prime factor below
the level and still be composite.  The bridge is therefore an *inclusion* statement only, and
no lower bound for the number of prime pairs follows from it. -/
theorem survival_bridge_is_not_the_analytic_sieve :
    ∃ m : ℕ, ¬ m.Prime ∧ ∀ p : ℕ, p.Prime → (p : ℝ) < 3 → ¬ p ∣ m := by
  refine ⟨25, by decide, ?_⟩
  intro p hp hlt
  have hp2 : 2 ≤ p := hp.two_le
  have hp3 : p < 3 := by exact_mod_cast hlt
  have : p = 2 := by omega
  subst this
  decide

end PrimePairSieve

/-! ## §12  The effectivity firewall -/

/-- **`two_XN2_exceeds_four_billion`.**  `KERNEL-PROVED`.  `2·X_N2 > 4·10⁹`, hence the current
`N2`-based finite splice **fails**.  This is an effectivity statement, not an analytic
failure of `N2`. -/
theorem two_XN2_exceeds_four_billion :
    N2ConstantsBank.finiteBankCeiling < 2 * N2ConstantsBank.XN2 := by
  have h := N2ConstantsBank.n2_finite_splice_fails
  omega

/-! ## §13  The four-error algebraic interface -/

/-- **`fourErrorLowerBound`.**  `KERNEL-PROVED`, algebra only. -/
theorem fourErrorLowerBound {primeMass m_eps B_X E_T E_L E_2 E_M : ℝ}
    (h : primeMass ≥ m_eps * B_X - E_T - E_L - E_2 - E_M) :
    primeMass ≥ m_eps * B_X - (E_T + E_L + E_2 + E_M) := by
  linarith

/-- **`fourError_positivity_needs_all_four`.**  `KERNEL-PROVED`, conditional.  Positivity
follows only once *all four* error terms are supplied below the margin; no analytic bound is
inhabited here. -/
theorem fourError_positivity_needs_all_four {primeMass m_eps B_X E_T E_L E_2 E_M : ℝ}
    (h : primeMass ≥ m_eps * B_X - E_T - E_L - E_2 - E_M)
    (hbudget : E_T + E_L + E_2 + E_M < m_eps * B_X) :
    0 < primeMass := by
  linarith

/-- **`fourError_budget_is_an_input`.**  `KERNEL-PROVED`.  The budget hypothesis is a genuine
input: explicit data refute it. -/
theorem fourError_budget_is_an_input :
    ∃ m_eps B_X E_T E_L E_2 E_M : ℝ,
      ¬ (E_T + E_L + E_2 + E_M < m_eps * B_X) := by
  refine ⟨0, 0, 1, 0, 0, 0, ?_⟩
  norm_num

end September2Ledger
end Erdos287
