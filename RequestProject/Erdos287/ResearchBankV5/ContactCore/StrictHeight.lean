import Mathlib.Tactic

/-!
# Contact-core route — the STRICT-HEIGHT contact theorem (kernel bank)

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

Let `p < q` be distinct odd first-power owners and let `N = ⌊M/p⌋ = ⌊M/q⌋` be their common
height.  Then **no** cofactors `1 ≤ c, d ≤ N` satisfy `|p c - q d| = 1`:
a unit contact between two owners of the same height is impossible
(`strictHeight_no_unit_contact`, `strictHeight_no_unit_contact_symm`).

Equivalently, a unit contact forces the height to change strictly:
`p < q` in contact implies `⌊M/q⌋ < ⌊M/p⌋` (`strictHeight_floor_lt`).

The proof is exact elementary arithmetic.  The hypothesis `p, q > √M` used in the informal
statement of the programme is **not needed** and is therefore omitted from the general theorem;
`strictHeight_high_owners` records the specialization to high owners which does carry it.

**Firewall (mandatory).**  STRICT-HEIGHT says only that *each edge* changes the height; it does
**not** give a monotone height along a path.  An undirected path may zigzag
(`strict_change_not_monotone`).  Same-height edges and same-height first-power cycles are
impossible; global monotone descent is **not proved**.
-/

namespace Erdos287
namespace ResearchBankV5
namespace ContactCore

/-- **(STRICT-HEIGHT), edge form.**  Two distinct odd owners `p < q` of the same height `N`
admit no unit contact with cofactors in `[1, N]`. -/
theorem strictHeight_no_unit_contact {M p q N c d : ℕ}
    (hp : 0 < p) (hpq : p < q) (hpodd : Odd p) (hqodd : Odd q)
    (hNp : M / p = N) (hNq : M / q = N)
    (hc1 : 1 ≤ c) (hcN : c ≤ N) (hd1 : 1 ≤ d) (hdN : d ≤ N) :
    ((p : ℤ) * c - (q : ℤ) * d).natAbs ≠ 1 := by
  have hq : 0 < q := lt_trans hp hpq
  have hgap : p + 2 ≤ q := by
    obtain ⟨a, ha⟩ := hpodd
    obtain ⟨b, hb⟩ := hqodd
    omega
  have hNqM : N * q ≤ M := by
    rw [← hNq]; exact Nat.div_mul_le_self M q
  have hMlt : M < (N + 1) * p := by
    have hlt : M / p < N + 1 := by omega
    exact (Nat.div_lt_iff_lt_mul hp).1 hlt
  have hP : (0 : ℤ) < p := by exact_mod_cast hp
  have hgapZ : (p : ℤ) + 2 ≤ q := by exact_mod_cast hgap
  have hNqZ : (N : ℤ) * q ≤ M := by exact_mod_cast hNqM
  have hMltZ : (M : ℤ) < ((N : ℤ) + 1) * p := by exact_mod_cast hMlt
  have hc1Z : (1 : ℤ) ≤ c := by exact_mod_cast hc1
  have hcNZ : (c : ℤ) ≤ N := by exact_mod_cast hcN
  have hd1Z : (1 : ℤ) ≤ d := by exact_mod_cast hd1
  have hdNZ : (d : ℤ) ≤ N := by exact_mod_cast hdN
  have hkey : (N : ℤ) * ((q : ℤ) - p) < p := by nlinarith
  intro hcontra
  rcases Int.natAbs_eq_iff.1 hcontra with h | h
  · have hstep : (p : ℤ) * ((c : ℤ) - d) = (d : ℤ) * ((q : ℤ) - p) + 1 := by linear_combination h
    have hcd : (1 : ℤ) ≤ (c : ℤ) - d := by nlinarith
    have hdle : (d : ℤ) ≤ (N : ℤ) - 1 := by linarith
    nlinarith
  · have hstep : (p : ℤ) * ((c : ℤ) - d) = (d : ℤ) * ((q : ℤ) - p) - 1 := by linear_combination h
    have hcd : (1 : ℤ) ≤ (c : ℤ) - d := by nlinarith
    have hdle : (d : ℤ) ≤ (N : ℤ) - 1 := by linarith
    nlinarith

/-- **(STRICT-HEIGHT), unordered form.**  No unit contact between *distinct* odd owners of the
same height. -/
theorem strictHeight_no_unit_contact_symm {M p q N c d : ℕ}
    (hp : 0 < p) (hq : 0 < q) (hne : p ≠ q) (hpodd : Odd p) (hqodd : Odd q)
    (hNp : M / p = N) (hNq : M / q = N)
    (hc1 : 1 ≤ c) (hcN : c ≤ N) (hd1 : 1 ≤ d) (hdN : d ≤ N) :
    ((p : ℤ) * c - (q : ℤ) * d).natAbs ≠ 1 := by
  rcases lt_or_gt_of_ne hne with h | h
  · exact strictHeight_no_unit_contact hp h hpodd hqodd hNp hNq hc1 hcN hd1 hdN
  · have hswap := strictHeight_no_unit_contact hq h hqodd hpodd hNq hNp hd1 hdN hc1 hcN
    intro hcontra
    apply hswap
    rw [show ((q : ℤ) * d - (p : ℤ) * c) = -((p : ℤ) * c - (q : ℤ) * d) by ring, Int.natAbs_neg]
    exact hcontra

/-- **(STRICT-HEIGHT), height form.**  If `p < q` are distinct odd owners in unit contact with
cofactors bounded by their own heights, then the height strictly drops: `⌊M/q⌋ < ⌊M/p⌋`. -/
theorem strictHeight_floor_lt {M p q c d : ℕ}
    (hp : 0 < p) (hpq : p < q) (hpodd : Odd p) (hqodd : Odd q)
    (hc1 : 1 ≤ c) (hcN : c ≤ M / p) (hd1 : 1 ≤ d) (hdN : d ≤ M / q)
    (hcontact : ((p : ℤ) * c - (q : ℤ) * d).natAbs = 1) : M / q < M / p := by
  rcases lt_or_ge (M / q) (M / p) with h | h
  · exact h
  · have hle : M / q ≤ M / p := Nat.div_le_div_left (le_of_lt hpq) hp
    have heq : M / q = M / p := le_antisymm hle h
    exact absurd hcontact
      (strictHeight_no_unit_contact hp hpq hpodd hqodd rfl heq hc1 hcN hd1 (heq ▸ hdN))

/-- Specialization to **high owners** `p, q > √M` (the range in which the contact-core route uses
STRICT-HEIGHT).  The two square-root hypotheses are recorded because the programme states them;
the proof does not use them. -/
theorem strictHeight_high_owners {M p q N c d : ℕ}
    (_hpM : M < p * p) (_hqM : M < q * q)
    (hp : 0 < p) (hpq : p < q) (hpodd : Odd p) (hqodd : Odd q)
    (hNp : M / p = N) (hNq : M / q = N)
    (hc1 : 1 ≤ c) (hcN : c ≤ N) (hd1 : 1 ≤ d) (hdN : d ≤ N) :
    ((p : ℤ) * c - (q : ℤ) * d).natAbs ≠ 1 :=
  strictHeight_no_unit_contact hp hpq hpodd hqodd hNp hNq hc1 hcN hd1 hdN

/-! ## Same-height cycles -/

/-- **No same-height first-power cycle.**  A closed walk of odd owners all of the same height, with
consecutive owners distinct and in unit contact, cannot exist: already its first edge is
impossible. -/
theorem sameHeight_cycle_impossible {M N : ℕ} (w c d : ℕ → ℕ)
    (hpos : ∀ i, 0 < w i) (hodd : ∀ i, Odd (w i)) (hne : ∀ i, w i ≠ w (i + 1))
    (hheight : ∀ i, M / w i = N)
    (hc : ∀ i, 1 ≤ c i ∧ c i ≤ N) (hd : ∀ i, 1 ≤ d i ∧ d i ≤ N)
    (hcontact : ∀ i, ((w i : ℤ) * c i - (w (i + 1) : ℤ) * d i).natAbs = 1) : False :=
  strictHeight_no_unit_contact_symm (hpos 0) (hpos 1) (hne 0) (hodd 0) (hodd 1)
    (hheight 0) (hheight 1) (hc 0).1 (hc 0).2 (hd 0).1 (hd 0).2 (hcontact 0)

/-! ## Mandatory firewall: no global monotone descent -/

/-- **Firewall.**  A strict change of height across every edge does **not** imply that the height
is monotone along a path: an undirected path may zigzag. -/
theorem strict_change_not_monotone :
    ∃ h : ℕ → ℕ, (∀ i, h i ≠ h (i + 1)) ∧ ¬ (∀ i j, i ≤ j → h j ≤ h i) := by
  refine ⟨fun i => i % 2, fun i => ?_, ?_⟩
  · show i % 2 ≠ (i + 1) % 2
    omega
  · intro hmono
    have h := hmono 0 1 (by norm_num)
    simp at h

/-! ## Finite regressions (exact finite statements only) -/

/-- Regression fixture: `M = 100`, `p = 41`, `q = 43`, common height `N = 2`; no unit contact. -/
theorem strictHeight_regression_fixture :
    100 / 41 = 2 ∧ 100 / 43 = 2 ∧
      ∀ c ∈ Finset.Icc 1 2, ∀ d ∈ Finset.Icc 1 2,
        41 * c ≠ 43 * d + 1 ∧ 43 * d ≠ 41 * c + 1 := by
  refine ⟨by norm_num, by norm_num, by decide⟩

/-- Exhaustive regression: for `M = 300`, every pair of odd owners `20 ≤ p < q ≤ 60` of equal
height admits no unit contact with cofactors up to that height. -/
theorem strictHeight_regression_sweep300 :
    ∀ p ∈ Finset.Icc 20 60, ∀ q ∈ Finset.Icc 20 60,
      p < q → Odd p → Odd q → 300 / p = 300 / q →
        ∀ c ∈ Finset.Icc 1 (300 / p), ∀ d ∈ Finset.Icc 1 (300 / p),
          p * c ≠ q * d + 1 ∧ q * d ≠ p * c + 1 := by decide

set_option maxRecDepth 20000 in
/-- Exhaustive regression at a second scale: `M = 1000`, owners `120 ≤ p < q ≤ 200`. -/
theorem strictHeight_regression_sweep1000 :
    ∀ p ∈ Finset.Icc 120 200, ∀ q ∈ Finset.Icc 120 200,
      p < q → Odd p → Odd q → 1000 / p = 1000 / q →
        ∀ c ∈ Finset.Icc 1 (1000 / p), ∀ d ∈ Finset.Icc 1 (1000 / p),
          p * c ≠ q * d + 1 ∧ q * d ≠ p * c + 1 := by decide

end ContactCore
end ResearchBankV5
end Erdos287
