import Mathlib
import RequestProject.CurrentProgramme.ConductorSplitLargeSieve

/-!
# Hostile-audit safe bank §3 — general-modulus induced-character algebra

The corrected definition-level identity of the general-modulus conductor split.

For `f ∣ r`, `j = r / f`, and a primitive character `χ*` modulo `f`, the induced character
modulo `r` satisfies **pointwise**

```
χ_r(n) = χ*(n) · 1_{gcd(n, j) = 1}.
```

No hypothesis `r` squarefree and no hypothesis `gcd(f, j) = 1` is needed; this is the exact
point at which the earlier `SMALLR-GENERAL-MODULUS-DEATH-CERTIFICATE` was wrong, and it is
recorded here as banked algebra (see `induced_character_pointwise`,
`inducedSpec_holds_for_nonSquarefree_modulus`).

Following the convention of `ConductorSplitLargeSieve`, characters are supplied as **data**
(arithmetic functions `ℕ → ℂ` with declared support conventions), so nothing here depends on
the ambient `DirichletCharacter` API.

Also banked: the Möbius expansion of the coprimality indicator

```
1_{gcd(n,j)=1} = ∑_{d ∣ j, d ∣ n} μ(d),
```

**including non-squarefree `j`** (`coprimeIndicator_moebius_expansion`, and the explicit
non-squarefree instances).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open ArithmeticFunction

namespace Erdos287
namespace HostileAudit

/-! ## §3.1  The coprimality indicator -/

/-- The literal coprimality indicator `1_{gcd(n,j) = 1}` as a complex weight. -/
noncomputable def coprimeIndicator (n j : ℕ) : ℂ := if Nat.gcd n j = 1 then 1 else 0

@[simp] theorem coprimeIndicator_of_coprime {n j : ℕ} (h : Nat.Coprime n j) :
    coprimeIndicator n j = 1 := by
  simp [coprimeIndicator, h]

@[simp] theorem coprimeIndicator_of_not_coprime {n j : ℕ} (h : ¬ Nat.Coprime n j) :
    coprimeIndicator n j = 0 := by
  simp [coprimeIndicator, Nat.Coprime] at h ⊢
  simp [h]

/-- **`coprime_mul_split`.**  `LEAN_PROVED`.  `gcd(n, f·j) = 1 ↔ gcd(n,f) = 1 ∧ gcd(n,j) = 1`.
No squarefreeness and no `gcd(f,j) = 1` is used. -/
theorem coprime_mul_split (n f j : ℕ) :
    Nat.Coprime n (f * j) ↔ Nat.Coprime n f ∧ Nat.Coprime n j :=
  Nat.coprime_mul_iff_right

/-! ## §3.2  The induced-character support identity -/

/-- **`InducedCharacterSpec`** — the defining data-level properties of an induced character.

`chiStar` is the primitive character of conductor `f`, `chiR` the character it induces to the
modulus `r = f · j`.  The three fields are exactly the *definition* of "induced":

* `chiStar` is supported on residues coprime to `f`;
* `chiR` agrees with `chiStar` on residues coprime to the full modulus `f·j`;
* `chiR` is supported on residues coprime to the full modulus.

This is a **hypothesis bundle about supplied data**, satisfiable (see
`inducedSpec_holds_for_nonSquarefree_modulus`), not an analytic interface. -/
structure InducedCharacterSpec (chiStar chiR : ℕ → ℂ) (f j : ℕ) : Prop where
  /-- The primitive character vanishes off residues coprime to its conductor. -/
  star_support : ∀ n : ℕ, ¬ Nat.Coprime n f → chiStar n = 0
  /-- On residues coprime to the full modulus the two characters agree. -/
  agree : ∀ n : ℕ, Nat.Coprime n (f * j) → chiR n = chiStar n
  /-- The induced character vanishes off residues coprime to the full modulus. -/
  full_support : ∀ n : ℕ, ¬ Nat.Coprime n (f * j) → chiR n = 0

/-- **`induced_character_pointwise`.**  `LEAN_PROVED`.

The corrected general-modulus identity:

```
χ_r(n) = χ*(n) · 1_{gcd(n, j) = 1}    for every n,
```

with **no** hypothesis that `r = f·j` be squarefree and **no** hypothesis `gcd(f, j) = 1`. -/
theorem induced_character_pointwise {chiStar chiR : ℕ → ℂ} {f j : ℕ}
    (h : InducedCharacterSpec chiStar chiR f j) (n : ℕ) :
    chiR n = chiStar n * coprimeIndicator n j := by
  by_cases hj : Nat.Coprime n j
  · by_cases hf : Nat.Coprime n f
    · rw [h.agree n (coprime_mul_split n f j |>.2 ⟨hf, hj⟩), coprimeIndicator_of_coprime hj,
        mul_one]
    · have hfull : ¬ Nat.Coprime n (f * j) := fun hc => hf ((coprime_mul_split n f j).1 hc).1
      rw [h.full_support n hfull, h.star_support n hf, zero_mul]
  · have hfull : ¬ Nat.Coprime n (f * j) := fun hc => hj ((coprime_mul_split n f j).1 hc).2
    rw [h.full_support n hfull, coprimeIndicator_of_not_coprime hj, mul_zero]

/-- **`inducedSpec_holds_for_nonSquarefree_modulus`.**  `LEAN_PROVED`.

The identity is *not* vacuous, and it needs neither squarefreeness of the modulus nor
`gcd(f, j) = 1`: here `f = 2`, `j = 2`, so `r = 4` is not squarefree and `gcd(f, j) = 2`,
and the principal characters modulo `2` and modulo `4` satisfy the spec. -/
theorem inducedSpec_holds_for_nonSquarefree_modulus :
    InducedCharacterSpec (fun n => if Nat.Coprime n 2 then 1 else 0)
      (fun n => if Nat.Coprime n 4 then 1 else 0) 2 2 := by
  have hiff : ∀ n : ℕ, Nat.Coprime n 4 ↔ Nat.Coprime n 2 := by
    intro n
    have h4 : (4 : ℕ) = 2 * 2 := by norm_num
    rw [h4, Nat.coprime_mul_iff_right]
    tauto
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    rw [if_neg hn]
  · intro n hn
    have h : Nat.Coprime n 2 := (Nat.coprime_mul_iff_right.1 hn).1
    rw [if_pos ((hiff n).2 h), if_pos h]
  · intro n hn
    have h : ¬ Nat.Coprime n 2 := fun hc => hn (Nat.coprime_mul_iff_right.2 ⟨hc, hc⟩)
    rw [if_neg (fun hc => h ((hiff n).1 hc))]

/-- **`induced_character_nonSquarefree_instance`.**  `LEAN_PROVED`.

The pointwise identity in the non-squarefree instance `f = j = 2`, `r = 4`. -/
theorem induced_character_nonSquarefree_instance (n : ℕ) :
    (if Nat.Coprime n 4 then (1 : ℂ) else 0)
      = (if Nat.Coprime n 2 then (1 : ℂ) else 0) * coprimeIndicator n 2 :=
  induced_character_pointwise inducedSpec_holds_for_nonSquarefree_modulus n

/-! ## §3.3  The Möbius expansion of the coprimality indicator -/

/-- **`gcd_divisors_eq_filter`.**  `LEAN_PROVED`.

For `j ≠ 0`, the divisors of `gcd(n, j)` are exactly the divisors of `j` that divide `n`.
This holds for arbitrary `j`, squarefree or not. -/
theorem gcd_divisors_eq_filter {n j : ℕ} (hj : j ≠ 0) :
    (Nat.gcd n j).divisors = j.divisors.filter (fun d => d ∣ n) := by
  ext d
  simp only [Nat.mem_divisors, Finset.mem_filter]
  constructor
  · intro hd
    exact ⟨⟨hd.1.trans (Nat.gcd_dvd_right n j), hj⟩, hd.1.trans (Nat.gcd_dvd_left n j)⟩
  · intro hd
    exact ⟨Nat.dvd_gcd hd.2 hd.1.1, Nat.gcd_ne_zero_right hj⟩

/-- **`coprimeIndicator_moebius_expansion`.**  `LEAN_PROVED`.

```
∑_{d ∣ j, d ∣ n} μ(d) = 1_{gcd(n,j) = 1},
```

for every `j ≠ 0` — **including non-squarefree `j`** (the Möbius factor kills the
non-squarefree divisors by itself; no hypothesis on `j` is needed). -/
theorem coprimeIndicator_moebius_expansion {n j : ℕ} (hj : j ≠ 0) :
    ∑ d ∈ j.divisors.filter (fun d => d ∣ n), moebius d
      = if Nat.Coprime n j then 1 else 0 := by
  rw [← gcd_divisors_eq_filter (n := n) hj]
  exact Erdos287.PostBalanced7Pro.coprime_indicator_eq n j

/-- **`moebius_expansion_nonSquarefree_j_four`.**  `LEAN_PROVED` (kernel-decidable).

An explicit non-squarefree instance: `j = 4`.  The expansion runs over `d ∈ {1, 2, 4}`, the
divisor `4` contributes `μ(4) = 0`, and the identity holds at `n = 6` (not coprime) and at
`n = 3` (coprime). -/
theorem moebius_expansion_nonSquarefree_j_four :
    (∑ d ∈ (4 : ℕ).divisors.filter (fun d => d ∣ 6), moebius d) = 0 ∧
      (∑ d ∈ (4 : ℕ).divisors.filter (fun d => d ∣ 3), moebius d) = 1 := by
  constructor
  · rw [coprimeIndicator_moebius_expansion (n := 6) (by norm_num)]
    norm_num [Nat.Coprime]
  · rw [coprimeIndicator_moebius_expansion (n := 3) (by norm_num)]
    norm_num [Nat.Coprime]

/-- **`induced_character_moebius_form`.**  `LEAN_PROVED`.

The two banked identities combined: the induced character is the primitive character times
the Möbius expansion over the divisors of the complementary factor `j`. -/
theorem induced_character_moebius_form {chiStar chiR : ℕ → ℂ} {f j : ℕ}
    (h : InducedCharacterSpec chiStar chiR f j) (hj : j ≠ 0) (n : ℕ) :
    chiR n = chiStar n * ((∑ d ∈ j.divisors.filter (fun d => d ∣ n), moebius d : ℤ) : ℂ) := by
  rw [induced_character_pointwise h n, coprimeIndicator_moebius_expansion hj]
  by_cases hc : Nat.Coprime n j
  · rw [if_pos hc, coprimeIndicator_of_coprime hc]
    norm_num
  · rw [if_neg hc, coprimeIndicator_of_not_coprime hc]
    norm_num

end HostileAudit
end Erdos287
