import Mathlib

/-!
# Erdős #287 — September-3 bank, §C: the odd-`d` and `4d` fixed-residue arithmetic

```
FAMILY 0  (modulus d)   p = 2dr + s  ⇒  p ≡ s [ZMOD d]      : KERNEL-PROVED
FAMILY 0  converse integrality                              : KERNEL-PROVED
FAMILY 2  (modulus 4d)  p = 4du + s  ⇒  p ≡ s [ZMOD 4d]     : KERNEL-PROVED
SOURCE-LEVEL CONCLUSION (two physical families)             : KERNEL-PROVED
```

**FIREWALL — `FIXED-RESIDUE-SOURCE  ≠  ANALYTIC-PRIME-DISTRIBUTION-THEOREM`.**
Everything in this module is elementary congruence algebra over `ℤ`.  Nothing here counts
primes, nothing here is an equidistribution statement, and nothing here asserts Maynard,
Bombieri–Vinogradov, Wright, Bordignon–Lee or any other analytic input.  The letter `p` is
used only as a name; no primality is assumed or concluded.

## Content

*Family 0.*  `n = d·r` with `d` odd, and `p = 2·d·r + s` with `s = ±1`.  Then
`p ≡ s (mod d)` — the modulus is the **odd** `d`, not `2d`.  Conversely, under the correct
parity hypotheses (`p` odd, `d` odd, `s = ±1`), `p ≡ s (mod d)` forces `2d ∣ p − s`, i.e.
`(p − s)/(2d)` is an integer; the parity hypotheses are genuinely needed and are not
weakened.

*Family 2.*  `n = 2·d·u` with `d` odd, and `p = 4·d·u + s`.  Then `p ≡ s (mod 4d)`.

*Banked source-level conclusion.*  The apparent generic modulus `2m` of the unpaired source
is replaced, after the 2-adic Möbius pairing of
`Erdos287September3TotTwoAdicMobiusPairing.lean`, by exactly the two physical fixed-residue
families: modulus `d` (family 0) and modulus `4d` (family 2).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos287
namespace September3FixedResidue

/-! ## §C.1  Family 0 — modulus `d` -/

/-- **`family0_fixedResidue`.**  `KERNEL-PROVED`.  With `n = d·r` and `p = 2·d·r + s`,
`p ≡ s (mod d)`.  (The sign restriction `s = ±1` is not needed for this direction; see
`family0_fixedResidue_pm` for the physical instance.) -/
theorem family0_fixedResidue (d r s : ℤ) : (2 * d * r + s) ≡ s [ZMOD d] := by
  have h : (d : ℤ) ∣ (2 * d * r + s) - s := ⟨2 * r, by ring⟩
  exact Int.ModEq.symm (Int.modEq_iff_dvd.2 h)

/-- **`family0_fixedResidue_pm`.**  `KERNEL-PROVED`.  The physical family-0 instance:
`d` odd, `s = ±1`, `n = d·r`, `p = 2·d·r + s`, conclusion `p ≡ s (mod d)`.

The physical hypotheses `hd : Odd d`, `hs : s = ±1` and `hn : n = d·r` are kept because they
are part of the source-level family description; the congruence itself is already true
without them (`family0_fixedResidue`). -/
theorem family0_fixedResidue_pm (d r s n p : ℤ) (hd : Odd d) (hs : s = 1 ∨ s = -1)
    (hn : n = d * r) (hp : p = 2 * d * r + s) : p ≡ s [ZMOD d] := by
  subst hp
  exact family0_fixedResidue d r s

/-- Coprimality of `2` and an odd integer, in the `IsCoprime` form used below. -/
theorem isCoprime_two_of_odd {d : ℤ} (hd : Odd d) : IsCoprime d (2 : ℤ) := by
  obtain ⟨j, hj⟩ := hd
  exact ⟨1, -j, by rw [hj]; ring⟩

/-- **`family0_integrality`.**  `KERNEL-PROVED`.  Converse integrality statement for family
`0`: if `p ≡ s (mod d)` with `p` odd, `d` odd and `s = ±1`, then `2d ∣ p − s`, i.e.
`(p − s)/(2d)` is an integer.  Both parity hypotheses are used. -/
theorem family0_integrality (d s p : ℤ) (hd : Odd d) (hp : Odd p) (hs : s = 1 ∨ s = -1)
    (hcong : p ≡ s [ZMOD d]) : (2 * d) ∣ (p - s) := by
  have hddvd : d ∣ (p - s) := Int.modEq_iff_dvd.1 hcong.symm
  have hs' : Odd s := by rcases hs with rfl | rfl; exacts [⟨0, by ring⟩, ⟨-1, by ring⟩]
  obtain ⟨j, hj⟩ := hp
  obtain ⟨i, hi⟩ := hs'
  have h2 : p - s = 2 * (j - i) := by rw [hj, hi]; ring
  have hdk : d ∣ (j - i) :=
    (isCoprime_two_of_odd hd).dvd_of_dvd_mul_left (by rw [← h2]; exact hddvd)
  obtain ⟨m, hm⟩ := hdk
  exact ⟨m, by rw [h2, hm]; ring⟩

/-- **`family0_integrality_witness`.**  `KERNEL-PROVED`.  The same statement in the explicit
form `p = 2·d·u + s`. -/
theorem family0_integrality_witness (d s p : ℤ) (hd : Odd d) (hp : Odd p)
    (hs : s = 1 ∨ s = -1) (hcong : p ≡ s [ZMOD d]) : ∃ u : ℤ, p = 2 * d * u + s := by
  obtain ⟨u, hu⟩ := family0_integrality d s p hd hp hs hcong
  exact ⟨u, by linarith [hu]⟩

/-! ## §C.2  Family 2 — modulus `4d` -/

/-- **`family2_fixedResidue`.**  `KERNEL-PROVED`.  With `n = 2·d·u` and `p = 4·d·u + s`,
`p ≡ s (mod 4d)`. -/
theorem family2_fixedResidue (d u s : ℤ) : (4 * d * u + s) ≡ s [ZMOD (4 * d)] := by
  have : (4 * d : ℤ) ∣ (4 * d * u + s) - s := ⟨u, by ring⟩
  exact Int.ModEq.symm (Int.modEq_iff_dvd.2 this)

/-- **`family2_fixedResidue_pm`.**  `KERNEL-PROVED`.  The physical family-2 instance.

As in family `0`, the hypotheses `hd`, `hs`, `hn` record the physical family and are not
needed for the congruence itself. -/
theorem family2_fixedResidue_pm (d u s n p : ℤ) (hd : Odd d) (hs : s = 1 ∨ s = -1)
    (hn : n = 2 * d * u) (hp : p = 4 * d * u + s) : p ≡ s [ZMOD (4 * d)] := by
  subst hp
  exact family2_fixedResidue d u s

/-! ## §C.3  The banked source-level conclusion -/

/-- **`fixedResidueFamilies_replace_generic_modulus`.**  `KERNEL-PROVED`.

The exact source-level conclusion that is banked: after the 2-adic Möbius pairing the
apparent generic modulus `2m` is replaced by the **two** physical fixed-residue families

* family `0`: modulus `d` (odd), residue `s = ±1`, positions `p = 2·d·r + s`;
* family `2`: modulus `4·d`, residue `s = ±1`, positions `p = 4·d·u + s`.

This is an algebra/arithmetic result only — see the firewall in the module docstring.  The
physical hypotheses `hd`, `hs` are recorded but not needed for the two congruences. -/
theorem fixedResidueFamilies_replace_generic_modulus (d r u s : ℤ) (hd : Odd d)
    (hs : s = 1 ∨ s = -1) :
    (2 * d * r + s) ≡ s [ZMOD d] ∧ (4 * d * u + s) ≡ s [ZMOD (4 * d)] :=
  ⟨family0_fixedResidue d r s, family2_fixedResidue d u s⟩

end September3FixedResidue
end Erdos287
