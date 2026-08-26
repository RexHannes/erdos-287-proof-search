import RequestProject.Erdos287.CeilingCRT

/-!
# Erdős Problem #287 — the Kernel AP-blocker

Let `A ⊆ [N, M]` be a gap-`≤2` counterexample (`Gap2CE`) with `M ≥ 8152`.  For each prime
`p` write `eₚ = maxₐ vₚ(a)` (`topExp`) and `qₚ = p^(eₚ+1)` (`ceilMod`), the ceiling
modulus: no element of `A` is divisible by `qₚ`, so every multiple of `qₚ` in `[N, M]` is
a hole (`holeForcing_ceilMod`).

Define the **kernel modulus**
`Qₚ = 2^(e₂+1)` for `p = 2`, and `Qₚ = 2·p^(eₚ+1)` for odd `p`
(so `qₚ ∣ Qₚ` in every case).

**Kernel AP-blocker (`Gap2CE.kernel_AP_blocker`).**  There is no prime `r ∈ [N+1, M−1]`
with `r ≡ ±1 (mod Qₚ)`.

*Reason.*  If `Qₚ ∣ (r−1)` then, since `qₚ ∣ Qₚ`, also `qₚ ∣ (r−1)`, so `r−1` is a ceiling
hole; `r` is a prime hole (`primeFree`, using `M ≥ 8152`).  Thus `r−1, r` are two adjacent
holes, contradicting `holes_isolated` (`blockerPair_contradiction`).  Symmetrically for
`Qₚ ∣ (r+1)`, giving the adjacent holes `r, r+1`.
-/

open scoped BigOperators

namespace Erdos287

namespace Gap2CE

variable (ce : Gap2CE)

/-! ## Upward closure of hole-forcing, and the `+1` companion of the AP lemma -/

/-- Hole-forcing is upward closed under divisibility: if `Q ∣ Q'` and `Q` is hole-forcing,
then so is `Q'` (every multiple of `Q'` is a multiple of `Q`). -/
theorem HoleForcing.of_dvd {Q Q' : ℕ} (h : Q ∣ Q') (hf : ce.HoleForcing Q) :
    ce.HoleForcing Q' :=
  fun x hx hdvd => hf x hx (h.trans hdvd)

/-- **AP-prime kills a hole-forcing modulus, `+1` form.**  Companion of
`AP_prime_kills_holeForcing`: if `M ≥ 8152`, `Q` is hole-forcing, `ℓ` is a prime with
`N + 1 ≤ ℓ` and `ℓ + 1 ≤ M`, and `Q ∣ (ℓ + 1)`, then no gap-`≤2` counterexample exists:
`ℓ` is a prime hole and `ℓ+1` is a `Q`-multiple hole, giving two adjacent holes. -/
theorem AP_prime_kills_holeForcing_add {Q ℓ : ℕ} (hM : 8152 ≤ ce.M)
    (hf : ce.HoleForcing Q) (hℓ : ℓ.Prime)
    (hlo : ce.N + 1 ≤ ℓ) (hhi : ℓ + 1 ≤ ce.M) (hdvd : Q ∣ (ℓ + 1)) : False := by
  -- `ℓ` is a prime hole
  have hℓnA : ℓ ∉ ce.A := fun h => ce.primeFree hM ℓ h hℓ
  -- `ℓ + 1` is a `Q`-multiple hole
  have hℓ1nA : ℓ + 1 ∉ ce.A :=
    hf (ℓ + 1) (Finset.mem_Icc.mpr ⟨by omega, hhi⟩) hdvd
  exact ce.blockerPair_contradiction (by omega) hhi hℓnA hℓ1nA

/-! ## The kernel modulus `Qₚ` -/

/-- The **kernel modulus** `Qₚ`: `q₂ = 2^(e₂+1)` for `p = 2`, and `2·p^(eₚ+1)` for odd
`p`. -/
def kernelMod (p : ℕ) : ℕ := if p = 2 then ce.ceilMod 2 else 2 * ce.ceilMod p

/-- The ceiling modulus divides the kernel modulus in every case. -/
theorem ceilMod_dvd_kernelMod (p : ℕ) : ce.ceilMod p ∣ ce.kernelMod p := by
  unfold kernelMod
  split_ifs with h
  · subst h; exact dvd_rfl
  · exact Dvd.intro_left 2 rfl

/-- The kernel modulus is positive for a prime base. -/
theorem one_le_kernelMod {p : ℕ} (hp : p.Prime) : 1 ≤ ce.kernelMod p := by
  unfold kernelMod
  split_ifs with h
  · subst h; exact ce.one_le_ceilMod hp
  · have := ce.one_le_ceilMod hp; omega

/-- The kernel modulus of a prime is hole-forcing (multiples of `Qₚ` are multiples of the
hole-forcing ceiling modulus `qₚ`). -/
theorem kernelMod_holeForcing {p : ℕ} (hp : p.Prime) : ce.HoleForcing (ce.kernelMod p) :=
  HoleForcing.of_dvd ce (ce.ceilMod_dvd_kernelMod p) (ce.holeForcing_ceilMod hp)

/-! ## The Kernel AP-blocker -/

/-- **Kernel AP-blocker.**  Let `M ≥ 8152`.  For every prime `p` there is no prime
`r ∈ [N+1, M−1]` with `r ≡ ±1 (mod Qₚ)`, where `Qₚ = ce.kernelMod p` and the `±1`
congruence is written as `Qₚ ∣ (r−1) ∨ Qₚ ∣ (r+1)`.

If `Qₚ ∣ (r−1)` then `qₚ ∣ (r−1)`, so `r−1` is a ceiling hole while `r` is a prime hole
(`primeFree`); `r−1, r` are adjacent holes.  Symmetrically `Qₚ ∣ (r+1)` gives the adjacent
holes `r, r+1`. -/
theorem kernel_AP_blocker {p : ℕ} (hp : p.Prime) (hM : 8152 ≤ ce.M) :
    ¬ ∃ r : ℕ, r.Prime ∧ ce.N + 1 ≤ r ∧ r ≤ ce.M - 1 ∧
      (ce.kernelMod p ∣ (r - 1) ∨ ce.kernelMod p ∣ (r + 1)) := by
  rintro ⟨r, hr, hlo, hhi, hdvd⟩
  have hf := ce.kernelMod_holeForcing hp
  rcases hdvd with h | h
  · exact ce.AP_prime_kills_holeForcing hM hf hr hlo hhi h
  · exact ce.AP_prime_kills_holeForcing_add hM hf hr hlo (by omega) h

/-- **Kernel AP-blocker, `Nat.ModEq` form.**  The same statement phrased with the literal
congruences `r ≡ 1 (mod Qₚ)` and `r ≡ Qₚ − 1 (mod Qₚ)` (i.e. `r ≡ −1`). -/
theorem kernel_AP_blocker_modEq {p : ℕ} (hp : p.Prime) (hM : 8152 ≤ ce.M) :
    ¬ ∃ r : ℕ, r.Prime ∧ ce.N + 1 ≤ r ∧ r ≤ ce.M - 1 ∧
      (r ≡ 1 [MOD ce.kernelMod p] ∨ r ≡ ce.kernelMod p - 1 [MOD ce.kernelMod p]) := by
  rintro ⟨r, hr, hlo, hhi, hcong⟩
  refine ce.kernel_AP_blocker hp hM ⟨r, hr, hlo, hhi, ?_⟩
  have hQ : 1 ≤ ce.kernelMod p := ce.one_le_kernelMod hp
  -- `r ≥ N + 1 ≥ 2`, so `r ≥ 1`
  have hr1 : 1 ≤ r := le_trans (Nat.le_add_left 1 ce.N) hlo
  rcases hcong with hc | hc
  · -- `r ≡ 1 [MOD Q]` ⟹ `Q ∣ (r - 1)`
    left
    have := (Nat.modEq_iff_dvd' hr1).1 hc.symm
    exact this
  · -- `r ≡ Q - 1 [MOD Q]` ⟹ `Q ∣ (r + 1)`
    right
    have hcong2 : r + 1 ≡ 0 [MOD ce.kernelMod p] := by
      have : r + 1 ≡ (ce.kernelMod p - 1) + 1 [MOD ce.kernelMod p] := Nat.ModEq.add_right 1 hc
      calc r + 1 ≡ (ce.kernelMod p - 1) + 1 [MOD ce.kernelMod p] := this
        _ = ce.kernelMod p := by omega
        _ ≡ 0 [MOD ce.kernelMod p] := (Nat.modEq_zero_iff_dvd).2 dvd_rfl
    exact (Nat.modEq_zero_iff_dvd).1 hcong2

end Gap2CE

end Erdos287
