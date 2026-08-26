import RequestProject.Erdos287.V2SophieFinite

/-!
# Erdős Problem #287 — the V2 fixed interior band compiler

`X = ⌊M/2⌋` and the band `3X/4 < q < 4X/5` are written as the cross-multiplied natural
inequalities

  `3 * X < 4 * q`   and   `5 * q < 4 * X`,

so no real or rational coercion is introduced and every floor/parity loss is explicit.
For `M ≥ 9` the band forces all four numerical hypotheses of the V2 Sophie blockers:

  `3 < q`,  `M < 3q`,  `2q + 1 ≤ M`,  `M < q²`.

The three linear ones are discharged by `omega` (which knows `2·⌊M/2⌋ ≤ M ≤ 2·⌊M/2⌋+1`);
the quadratic one follows from `3M ≤ 8q + 1` and `q ≥ 4`.
-/

open scoped BigOperators

namespace Erdos287

/-- The V2 band: `3·⌊M/2⌋ < 4·q` and `5·q < 4·⌊M/2⌋`, i.e. `3X/4 < q < 4X/5`. -/
def V2Band (M q : ℕ) : Prop := 3 * (M / 2) < 4 * q ∧ 5 * q < 4 * (M / 2)

instance (M q : ℕ) : Decidable (V2Band M q) := by unfold V2Band; infer_instance

/-- **V2 band compiler.**  For `M ≥ 9`, membership in the band gives exactly the four
hypotheses of the V2 Sophie blockers. -/
theorem v2Band_hypotheses {M q : ℕ} (hM : 9 ≤ M) (hb : V2Band M q) :
    3 < q ∧ M < 3 * q ∧ 2 * q + 1 ≤ M ∧ M < q * q := by
  obtain ⟨h1, h2⟩ := hb
  have h3M : 3 * M ≤ 8 * q + 1 := by omega
  have hq4 : 4 ≤ q := by omega
  refine ⟨by omega, by omega, by omega, ?_⟩
  nlinarith

namespace Gap2CE

variable (ce : Gap2CE)

/-- **V2 banded plus blocker.**  A prime `q` in the band with `2q + 1` prime refutes every
gap-`≤2` counterexample with `M ≥ 9`. -/
theorem v2_band_plus_blocker {q : ℕ} (hM : 9 ≤ ce.M) (hq : q.Prime) (hb : V2Band ce.M q)
    (hp : (2 * q + 1).Prime) : False := by
  obtain ⟨hq3, hM3, hfit, hsq⟩ := v2Band_hypotheses hM hb
  exact ce.v2_plus_sophie_blocker hq hq3 hp rfl (by omega) hM3 hsq

/-- **V2 banded minus blocker.**  A prime `q` in the band with `2q - 1` prime refutes every
gap-`≤2` counterexample with `M ≥ 9`. -/
theorem v2_band_minus_blocker {q : ℕ} (hM : 9 ≤ ce.M) (hq : q.Prime) (hb : V2Band ce.M q)
    (hp : (2 * q - 1).Prime) : False := by
  obtain ⟨hq3, hM3, hfit, hsq⟩ := v2Band_hypotheses hM hb
  exact ce.v2_minus_sophie_blocker hq hq3 hp (by omega) (by omega) hM3 hsq

/-- **V2 finite landing theorem.**  If `M ≥ 9` and the band around `⌊M/2⌋` contains a prime
`q` with `2q - 1` or `2q + 1` prime, then no gap-`≤2` counterexample exists.  Everything in
the statement is finite and decidable for each fixed `M`. -/
theorem v2_finite_compiler {q : ℕ} (hM : 9 ≤ ce.M) (hq : q.Prime) (hb : V2Band ce.M q)
    (hp : (2 * q + 1).Prime ∨ (2 * q - 1).Prime) : False := by
  rcases hp with h | h
  · exact ce.v2_band_plus_blocker hM hq hb h
  · exact ce.v2_band_minus_blocker hM hq hb h

end Gap2CE

/-! ## A concrete instance (finite, kernel-checked)

`M = 100`: `X = 50`, the band is `37.5 < q < 40`, and `q = 39` is not prime while `q = 37`
just misses the lower endpoint — but the *V2* band `3X/4 < q < 4X/5` at `M = 104`
(`X = 52`, band `39 < q < 41.6`) contains `q = 41`, and `2·41 - 1 = 81` is not prime while
`2·41 + 1 = 83` is.  So no gap-`≤2` counterexample has `M = 104`. -/

/-- No gap-`≤2` counterexample has largest denominator `104`
(witness: `q = 41` in the band, `2q + 1 = 83` prime). -/
theorem no_Gap2CE_M_eq_104 (ce : Gap2CE) (hM : ce.M = 104) : False := by
  refine ce.v2_band_plus_blocker (by omega) (q := 41) (by norm_num) ?_ (by norm_num)
  constructor <;> simp [hM]

end Erdos287
