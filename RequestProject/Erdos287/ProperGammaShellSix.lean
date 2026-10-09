import Mathlib
import RequestProject.Erdos287.ProperGammaMultiplicityGeometry

/-!
# Erdős #287 effectivity — the exact shell `N = 6` (§34)

```
N = 6 EXACT BAND GEOMETRY : KERNEL-PROVED
N = 6 DISJOINTNESS 1..5   : KERNEL-PROVED
N = 6 NUMERICAL CLOSURE   : CERTIFICATE-BACKED (never proved here)
ERDŐS #287                : OPEN
```

At the exact endpoint conventions of §33 (`A = 7X/10` excluded, `Z = 9X/10` included) the
shell `Ω_{=6}` is the union of exactly **seven** disjoint rational bands

    (9/310, 7/240] ∪ (3/100, 7/230] ∪ (9/290, 7/220] ∪ (9/280, 9/260]
      ∪ (7/200, 9/250] ∪ (7/190, 3/80] ∪ (7/180, 9/230],

and `N_X(m) = 6 ↔ m/X ∈ Ω_{=6}` (`NX_eq_six_iff`).

The numerical statement `|R_{N=6}|/B_X < 7.77e-9` is **not** proved here and is **not**
kernel-provable from this file: it enters only as a `ShellNumericalCertificate`
(`shellSixCharge`, `shellSix_certificate_not_proved`).  An external verifier replaying the
arithmetic does *not* upgrade it to `KERNEL-PROVED`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace Erdos287
namespace Effectivity

/-! ## §34.1  The exact `Ω_{=6}` bands -/

/-- The exact rational bands of the shell `N = 6`. -/
def OmegaSix : List (ℚ × ℚ) :=
  [(9/310, 7/240), (3/100, 7/230), (9/290, 7/220), (9/280, 9/260),
   (7/200, 9/250), (7/190, 3/80), (7/180, 9/230)]

/-- **`shellSix_bands`.**  `KERNEL-PROVED`.  The exact band description of the shell `N = 6`
at the stated endpoint conventions. -/
theorem shellSix_bands (t : ℚ) (ht : 0 < t) : ShellEq 6 t ↔ InBands OmegaSix t := by
  rw [ShellEq, multAtLeast_iff 6 (by norm_num) t ht, multAtLeast_iff 7 (by norm_num) t ht,
    bandsOf_six, bandsOf_seven, OmegaSix]
  simp only [InBands_cons, InBands_nil, or_false]
  norm_num only
  constructor
  · rintro ⟨h, hn⟩
    have n1 : ¬ ((0 : ℚ) < t ∧ t ≤ 9/310) := fun hh => hn (Or.inl hh)
    have n2 : ¬ ((7/220 : ℚ) < t ∧ t ≤ 9/280) := fun hh => hn (Or.inr (Or.inl hh))
    have n3 : ¬ ((7/230 : ℚ) < t ∧ t ≤ 9/290) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
    have n4 : ¬ ((7/240 : ℚ) < t ∧ t ≤ 3/100) :=
      fun hh => hn (Or.inr (Or.inr (Or.inr hh)))
    have main : t ≤ 9/260 →
        InBands OmegaSix t := by
      intro hb
      rcases le_or_gt t (9/310) with h1 | h1
      · exact (n1 ⟨ht, h1⟩).elim
      · rcases le_or_gt t (7/240) with h2 | h2
        · exact ⟨(9/310, 7/240), by simp [OmegaSix], h1, h2⟩
        · rcases le_or_gt t (3/100) with h3 | h3
          · exact (n4 ⟨h2, h3⟩).elim
          · rcases le_or_gt t (7/230) with h4 | h4
            · exact ⟨(3/100, 7/230), by simp [OmegaSix], h3, h4⟩
            · rcases le_or_gt t (9/290) with h5 | h5
              · exact (n3 ⟨h4, h5⟩).elim
              · rcases le_or_gt t (7/220) with h6 | h6
                · exact ⟨(9/290, 7/220), by simp [OmegaSix], h5, h6⟩
                · rcases le_or_gt t (9/280) with h7 | h7
                  · exact (n2 ⟨h6, h7⟩).elim
                  · exact ⟨(9/280, 9/260), by simp [OmegaSix], h7, hb⟩
    have expand : InBands OmegaSix t →
        ((9/310 : ℚ) < t ∧ t ≤ 7/240) ∨ ((3/100 : ℚ) < t ∧ t ≤ 7/230) ∨
          ((9/290 : ℚ) < t ∧ t ≤ 7/220) ∨ ((9/280 : ℚ) < t ∧ t ≤ 9/260) ∨
          ((7/200 : ℚ) < t ∧ t ≤ 9/250) ∨ ((7/190 : ℚ) < t ∧ t ≤ 3/80) ∨
          ((7/180 : ℚ) < t ∧ t ≤ 9/230) := by
      intro hh
      simpa [OmegaSix, InBands_cons] using hh
    rcases h with h | h | h | h | h
    · exact expand (main (by linarith [h.2]))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact expand (main h.2)
  · intro h
    constructor
    · rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
      · exact Or.inl ⟨by linarith, by linarith⟩
      · exact Or.inl ⟨by linarith, by linarith⟩
      · exact Or.inl ⟨by linarith, by linarith⟩
      · rcases le_or_gt t (1/30) with hc | hc
        · exact Or.inl ⟨by linarith, by linarith⟩
        · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by linarith, by linarith⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by linarith, by linarith⟩)))
      · exact Or.inr (Or.inr (Or.inl ⟨by linarith, by linarith⟩))
      · exact Or.inr (Or.inl ⟨by linarith, by linarith⟩)
    · rintro (⟨ha2, hb2⟩ | ⟨ha2, hb2⟩ | ⟨ha2, hb2⟩ | ⟨ha2, hb2⟩) <;>
        rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ <;>
        linarith

/-- **`NX_eq_six_iff`.**  `KERNEL-PROVED`.  `N_X(m) = 6` iff `m/X` lies in the exact bands
`Ω_{=6}`. -/
theorem NX_eq_six_iff (X : ℚ) (hX : 0 < X) {m : ℕ} (hm : 0 < m) :
    NX X m = 6 ↔ InBands OmegaSix ((m : ℚ) / X) := by
  have ht : 0 < (m : ℚ) / X := by
    have : (0 : ℚ) < (m : ℚ) := by exact_mod_cast hm
    positivity
  rw [show ((6 : ℤ)) = ((6 : ℕ) : ℤ) from rfl, NX_eq_iff X hX hm 6, shellSix_bands _ ht]

/-! ## §34.2  Disjointness from the banked shells `1 … 5` -/

/-- **`shellSix_disjoint_lower`.**  `KERNEL-PROVED`.  `Ω_{=6}` is disjoint from every physical
multiplicity shell `Ω_{=j}`, `1 ≤ j ≤ 5`. -/
theorem shellSix_disjoint_lower {j : ℕ} {t : ℚ} (ht : 0 < t) (hj : 1 ≤ j) (hj5 : j ≤ 5)
    (h6 : ShellEq 6 t) (hjt : ShellEq j t) : False :=
  shellEq_disjoint ht (by omega : j < 6) hjt h6

/-- **`shellSix_disjoint_seven`.**  `KERNEL-PROVED`.  `Ω_{=6}` is disjoint from the current
survivor region `N ≥ 7`. -/
theorem shellSix_disjoint_seven {t : ℚ} (h6 : ShellEq 6 t) (h7 : MultAtLeast 7 t) : False :=
  h6.2 h7

/-! ## §34.3  The `N = 6` numerical closure: certificate only -/

/-- The declared (certificate-backed) numerical value for the `N = 6` owner: `7.77e-9`. -/
def shellSixCharge : ℚ := 777 / 10 ^ 11

/-- **`shellSixCharge_eq`.**  `KERNEL-PROVED`.  Exact rational value of the declared charge. -/
theorem shellSixCharge_eq : shellSixCharge = 777 / 10 ^ 11 := rfl

/-- **`shellSix_certificate_not_proved`.**  `KERNEL-PROVED`.  Firewall: an `N = 6` numerical
certificate exists for *every* bound, so the declared `< 7.77e-9` is `CERTIFICATE-BACKED`, not
kernel-proved.  Replaying the arithmetic externally does not change this. -/
theorem shellSix_certificate_not_proved :
    ∃ C : ShellNumericalCertificate, C.shell = 6 ∧ C.bound = shellSixCharge :=
  shellCertificate_not_proved 6 shellSixCharge

/-- **`shellSix_bound_conditional`.**  `KERNEL-PROVED` (conditional on the supplied
certificate).  A supplied `N = 6` certificate with bound `7.77e-9` bounds the claimed value. -/
theorem shellSix_bound_conditional (C : ShellNumericalCertificate) (hs : C.shell = 6)
    (hb : C.bound = shellSixCharge) : C.shell = 6 ∧ C.value < shellSixCharge :=
  ⟨hs, hb ▸ C.value_lt⟩

end Effectivity
end Erdos287
