import Mathlib
import RequestProject.Erdos287.BsrcWeights

/-!
# Erdős #287 effectivity — the proper-γ `q`-fibre reparametrisation (§31)

```
q-FIBRE REPARAMETRIZATION : KERNEL-PROVED
beta MULTIPLICATIVITY     : KERNEL-PROVED (exact coprimality/squarefree hypotheses)
ERDŐS #287                : OPEN
```

The proper-γ range is `ℓ > d` with `d ∣ ℓ`, both odd squarefree.  This file banks the exact
reparametrisation of that range by the *fibre variable*

    q = ℓ / d,     ℓ = d q,   q > 1,  q odd,  q squarefree,  gcd(d,q) = 1,

together with the multiplicativity `β(dq) = β(d) β(q)` valid **exactly** under those
hypotheses.  Nothing analytic is asserted here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos287
namespace Effectivity

/-! ## §31.1  The fibre datum -/

/-- The exact `q`-fibre condition: `ℓ = d q` with `q > 1` odd squarefree and coprime to `d`. -/
def QFibre (d q l : ℕ) : Prop :=
  l = d * q ∧ 1 < q ∧ ¬ 2 ∣ q ∧ Squarefree q ∧ Nat.Coprime d q

/-- A divisor of an odd squarefree number is odd and squarefree. -/
theorem odd_squarefree_of_dvd {l d : ℕ} (hl : Squarefree l) (hodd : ¬ 2 ∣ l) (hdl : d ∣ l) :
    Squarefree d ∧ ¬ 2 ∣ d :=
  ⟨hl.squarefree_of_dvd hdl, fun h => hodd (h.trans hdl)⟩

/-- **`qFibre_reparam`.**  `KERNEL-PROVED`.  For odd squarefree `ℓ` and `d ≠ 0`:

    d ∣ ℓ  ∧  ℓ > d   ↔   ∃! q, ℓ = d q, q > 1, q odd, q squarefree, gcd(d,q) = 1. -/
theorem qFibre_reparam {l d : ℕ} (hl : Squarefree l) (hodd : ¬ 2 ∣ l) (hd : d ≠ 0) :
    (d ∣ l ∧ d < l) ↔ ∃! q : ℕ, QFibre d q l := by
  constructor
  · rintro ⟨hdl, hlt⟩
    refine ⟨l / d, ⟨(Nat.mul_div_cancel' hdl).symm, ?_, ?_, ?_, ?_⟩, ?_⟩
    · -- `q = ℓ/d > 1`
      rcases Nat.lt_or_ge (l / d) 2 with h | h
      · interval_cases hq : (l / d)
        · rw [← Nat.mul_div_cancel' hdl, hq] at hlt; simp at hlt
        · rw [← Nat.mul_div_cancel' hdl, hq] at hlt; simp at hlt
      · omega
    · exact fun h => hodd (h.trans (Nat.div_dvd_of_dvd hdl))
    · exact hl.squarefree_of_dvd (Nat.div_dvd_of_dvd hdl)
    · have hmul : Squarefree (d * (l / d)) := by rwa [Nat.mul_div_cancel' hdl]
      exact (Nat.squarefree_mul_iff.1 hmul).1
    · rintro q ⟨hq, -, -, -, -⟩
      have : d * (l / d) = d * q := by rw [Nat.mul_div_cancel' hdl, hq]
      exact (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hd) this).symm
  · rintro ⟨q, ⟨hq, hq1, -, -, -⟩, -⟩
    refine ⟨⟨q, hq⟩, ?_⟩
    have hd1 : 1 ≤ d := Nat.one_le_iff_ne_zero.2 hd
    calc d = d * 1 := (mul_one d).symm
      _ < d * q := by have := Nat.pos_of_ne_zero hd; nlinarith
      _ = l := hq.symm

/-- **`qFibre_unique`.**  `KERNEL-PROVED`.  The fibre variable is unique. -/
theorem qFibre_unique {l d q q' : ℕ} (hd : d ≠ 0) (h : QFibre d q l) (h' : QFibre d q' l) :
    q = q' :=
  Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hd) (by rw [← h.1, ← h'.1])

/-- **`qFibre_proper`.**  `KERNEL-PROVED`.  A fibre datum always describes a *proper* γ-pair:
`d ∣ ℓ` and `ℓ > d`. -/
theorem qFibre_proper {l d q : ℕ} (hd : d ≠ 0) (h : QFibre d q l) : d ∣ l ∧ d < l := by
  obtain ⟨hq, hq1, -, -, -⟩ := h
  refine ⟨⟨q, hq⟩, ?_⟩
  have hd1 : 1 ≤ d := Nat.one_le_iff_ne_zero.2 hd
  calc d = d * 1 := (mul_one d).symm
    _ < d * q := by have := Nat.pos_of_ne_zero hd; nlinarith
    _ = l := hq.symm

/-- **`qFibre_odd_squarefree`.**  `KERNEL-PROVED`.  A fibre datum over an odd squarefree `ℓ`
has odd squarefree `d`, and conversely `d`, `q` odd squarefree coprime forces `ℓ` odd
squarefree. -/
theorem qFibre_odd_squarefree {l d q : ℕ} (h : QFibre d q l) (hd : Squarefree d)
    (hdodd : ¬ 2 ∣ d) : Squarefree l ∧ ¬ 2 ∣ l := by
  obtain ⟨hl, -, hqodd, hqsq, hcop⟩ := h
  subst hl
  refine ⟨Nat.squarefree_mul_iff.2 ⟨hcop, hd, hqsq⟩, ?_⟩
  intro h2
  rcases (Nat.Prime.dvd_mul Nat.prime_two).1 h2 with h | h
  · exact hdodd h
  · exact hqodd h

/-! ## §31.2  Multiplicativity of `β` along the fibre -/

/-- **`beta_qFibre_mul`.**  `KERNEL-PROVED`.  Along the `q`-fibre, `β(dq) = β(d) β(q)` — the
exact coprimality/squarefree hypotheses are those of the fibre datum. -/
theorem beta_qFibre_mul {l d q : ℕ} (hd : d ≠ 0) (h : QFibre d q l) :
    beta l = beta d * beta q := by
  obtain ⟨hl, hq1, -, -, hcop⟩ := h
  subst hl
  exact beta_mul hd (by omega) hcop

/-- **`beta_qFibre_mul_general`.**  `KERNEL-PROVED`.  The multiplicativity in raw form:
coprime nonzero arguments. -/
theorem beta_qFibre_mul_general {d q : ℕ} (hd : d ≠ 0) (hq : q ≠ 0) (hcop : Nat.Coprime d q) :
    beta (d * q) = beta d * beta q :=
  beta_mul hd hq hcop

/-- **`beta_mul_not_general`.**  `KERNEL-PROVED`.  A firewall: multiplicativity genuinely
needs coprimality — at `d = q = 3` it fails. -/
theorem beta_mul_not_general : beta (3 * 3) ≠ beta 3 * beta 3 := by
  have hns : ¬ Squarefree (9 : ℕ) := by
    intro h
    have := h 3 (by norm_num)
    simp at this
  have h9 : beta 9 = 0 := beta_eq_zero_of_not_squarefree hns
  have h3 : beta 3 = 1 / ((3 : ℚ) - 2) := beta_prime (by norm_num) (by norm_num)
  norm_num [show (3 : ℕ) * 3 = 9 from rfl, h9, h3]

end Effectivity
end Erdos287
