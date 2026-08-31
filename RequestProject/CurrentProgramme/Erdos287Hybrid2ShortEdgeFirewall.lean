import Mathlib
import RequestProject.CurrentProgramme.Erdos287Hybrid2CriticalRectangle

/-!
# HYBRID-2 short-edge firewall

**Mandatory firewall.**  The informal slogan *"either a short edge or the rectangle"* is not
used anywhere: the finite-sum pigeonhole inequality behind it is proved here with **explicit
constants** (`C_short = C_rect = 4`), and the converse implication — that a survivor must lie in
the rectangle — is explicitly refuted by a counterexample.

Contents.

* `Hybrid2Survivor` — the non-contraction predicate `C²L²(1/D + 1/M + 1/Q + Q/(DM)) ≥ 1`.
* `ShortD`, `ShortM`, `ShortQ`, `LongEdgeRectangle` — the four explicit predicates.
* `noncontraction_shortEdge_or_rectangle` — the exact pigeonhole inequality.
* `hybrid2_survivor_union` — the survivor is contained in the union of the four predicates.
* `rectangle_alone_does_not_capture_all_survivors` — `LongEdgeRectangle PASS` does **not** imply
  that all Hybrid-2 survivors lie in the rectangle.  Short-edge nodes stay OPEN.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos287
namespace Hybrid2

/-- The Hybrid-2 non-contraction (survivor) condition: the `η²` budget fails to be `< 1`. -/
def Hybrid2Survivor (C L D M Q : ℝ) : Prop :=
  1 ≤ C ^ 2 * L ^ 2 * (1 / D + 1 / M + 1 / Q + Q / (D * M))

/-- Short `D` edge, with the explicit constant `C_short = 4`. -/
def ShortD (C L D : ℝ) : Prop := D ≤ 4 * (C ^ 2 * L ^ 2)

/-- Short `M` edge, with the explicit constant `C_short = 4`. -/
def ShortM (C L M : ℝ) : Prop := M ≤ 4 * (C ^ 2 * L ^ 2)

/-- Short `Q` edge, with the explicit constant `C_short = 4`. -/
def ShortQ (C L Q : ℝ) : Prop := Q ≤ 4 * (C ^ 2 * L ^ 2)

/-- The long-edge critical rectangle, with the explicit constant `C_rect = 4`. -/
def LongEdgeRectangle (C L D M Q : ℝ) : Prop := D * M ≤ 4 * (C ^ 2 * L ^ 2) * Q

/-- **`noncontraction_shortEdge_or_rectangle`.**  `LEAN_PROVED` (unconditional).

The exact finite-sum pigeonhole inequality.  If

```
C²L² ( 1/D + 1/M + 1/Q + Q/(DM) )  ≥  1
```

with `D, M, Q > 0`, then at least one of the four terms carries a quarter of the mass, i.e. at
least one of

```
D ≤ 4 C²L²,     M ≤ 4 C²L²,     Q ≤ 4 C²L²,     D M ≤ 4 C²L² Q
```

holds.  The constants are explicit: `C_short = C_rect = 4` (four terms, pigeonhole). -/
theorem noncontraction_shortEdge_or_rectangle {C L D M Q : ℝ}
    (hD : 0 < D) (hM : 0 < M) (hQ : 0 < Q)
    (h : 1 ≤ C ^ 2 * L ^ 2 * (1 / D + 1 / M + 1 / Q + Q / (D * M))) :
    D ≤ 4 * (C ^ 2 * L ^ 2) ∨ M ≤ 4 * (C ^ 2 * L ^ 2) ∨ Q ≤ 4 * (C ^ 2 * L ^ 2) ∨
      D * M ≤ 4 * (C ^ 2 * L ^ 2) * Q := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨hd, hm, hq, hr⟩ := hcon
  set K : ℝ := C ^ 2 * L ^ 2 with hKdef
  have hK0 : 0 ≤ K := by rw [hKdef]; positivity
  -- `K > 0`, else the hypothesis reads `1 ≤ 0`.
  have hKpos : 0 < K := by
    rcases lt_or_eq_of_le hK0 with h' | h'
    · exact h'
    · exfalso
      rw [← h'] at h
      norm_num at h
  have h1 : K * (1 / D) < 1 / 4 := by
    rw [mul_one_div, div_lt_div_iff₀ hD (by norm_num)]
    nlinarith [hd, hKpos]
  have h2 : K * (1 / M) < 1 / 4 := by
    rw [mul_one_div, div_lt_div_iff₀ hM (by norm_num)]
    nlinarith [hm, hKpos]
  have h3 : K * (1 / Q) < 1 / 4 := by
    rw [mul_one_div, div_lt_div_iff₀ hQ (by norm_num)]
    nlinarith [hq, hKpos]
  have h4 : K * (Q / (D * M)) < 1 / 4 := by
    have hDM : (0 : ℝ) < D * M := by positivity
    rw [← mul_div_assoc, div_lt_iff₀ hDM]
    nlinarith [hr, hKpos, hQ]
  have hexp : K * (1 / D + 1 / M + 1 / Q + Q / (D * M))
      = K * (1 / D) + K * (1 / M) + K * (1 / Q) + K * (Q / (D * M)) := by ring
  rw [hexp] at h
  linarith

/-- **`hybrid2_survivor_union`.**  `LEAN_PROVED` (unconditional bookkeeping).

Every Hybrid-2 survivor lies in the union of the three short-edge predicates and the long-edge
rectangle predicate.  Note carefully the direction: this is an *upper* bound on the survivor
set.  It does **not** say that survivors lie in the rectangle. -/
theorem hybrid2_survivor_union {C L D M Q : ℝ} (hD : 0 < D) (hM : 0 < M) (hQ : 0 < Q)
    (h : Hybrid2Survivor C L D M Q) :
    ShortD C L D ∨ ShortM C L M ∨ ShortQ C L Q ∨ LongEdgeRectangle C L D M Q :=
  noncontraction_shortEdge_or_rectangle hD hM hQ h

/-- **The firewall.**  `LEAN_PROVED`.

`LongEdgeRectangle PASS` does **not** imply that all Hybrid-2 survivors lie in the rectangle.
Explicitly, with `C = L = 1`, `D = 1`, `M = 100`, `Q = 1` the point is a survivor
(`1 + 1/100 + 1 + 1/100 ≥ 1`) but fails the rectangle (`D M = 100 > 4 = 4 C²L² Q`).  It is
caught only by the short-`D` node, which is **OPEN**.

Consequently: unless `Hybrid2ShortD`, `Hybrid2ShortM` and `Hybrid2ShortQ` are all closed by
literal proofs, no conclusion about the survivor set follows from the rectangle alone. -/
theorem rectangle_alone_does_not_capture_all_survivors :
    ∃ C L D M Q : ℝ, 0 < D ∧ 0 < M ∧ 0 < Q ∧
      Hybrid2Survivor C L D M Q ∧ ¬ LongEdgeRectangle C L D M Q := by
  refine ⟨1, 1, 1, 100, 1, by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · unfold Hybrid2Survivor; norm_num
  · unfold LongEdgeRectangle; norm_num

/-- **The three short-edge predicates are not vacuous and not automatic.**  `LEAN_PROVED`.

There is a survivor for which `ShortD` holds and one for which `ShortD` fails, so the node
`Hybrid2ShortD` records genuine information and is not closed by fiat. -/
theorem shortD_is_not_automatic :
    (∃ C L D M Q : ℝ, Hybrid2Survivor C L D M Q ∧ ShortD C L D) ∧
    (∃ C L D M Q : ℝ, Hybrid2Survivor C L D M Q ∧ ¬ ShortD C L D) := by
  constructor
  · exact ⟨1, 1, 1, 1, 1, by unfold Hybrid2Survivor; norm_num,
      by unfold ShortD; norm_num⟩
  · exact ⟨1, 1, 100, 1, 1, by unfold Hybrid2Survivor; norm_num,
      by unfold ShortD; norm_num⟩

end Hybrid2
end Erdos287
