# Erdős #287 — non-adjacent holes and the Kernel AP-blocker

This note answers two follow-up questions on the certified gap-`≤2` kernel. Everything
below is machine-checked (no `sorry`/`axiom`/`unsafe`/`native_decide`); every listed
theorem depends only on `propext`, `Classical.choice`, `Quot.sound`.

The certified adjacent-hole fact is `Gap2CE.blockerPair_contradiction`: two holes at
distance **1** in `[N, M]` contradict all gaps `≤ 2`. This is the *only* pattern the
gap constraint forbids, because the constraint (`Gap2CE.holes_isolated`, symbolically
`LocallyAdmissible`) is a nearest-neighbour subshift whose single forbidden 2-block is
`(hole, hole)`.

## Part A — Do two holes at distance `d > 1` force a contradiction?

**Verdict: No.** No non-adjacent-hole contradiction survives at the level used by
`blockerPair_contradiction`. For every distance `d ≥ 2` there is an explicit locally
admissible configuration exhibiting two holes exactly at distance `d`; since
`blockerPair_contradiction` is derived purely from the local gap rule, no distance-`d`
analogue can hold. Only `d = 1` is inadmissible.

File: `RequestProject/Erdos287/NonAdjacentHoles.lean`.

### Target 1 — prove or refute (refuted)

* `twoHoleWord x d` — the membership word with holes exactly at `x` and `x + d`.
* `twoHoleWord_locallyAdmissible (x) (hd : 2 ≤ d)` — for `d ≥ 2` this word satisfies the
  local gap rule. **This refutes the distance-`d` contradiction claim.**
* `twoHoleWord_has_two_holes` — the two prescribed holes are genuinely present.
* `twoHoleWord_one_not_admissible` — the sharp contrast: `d = 1` (adjacency) is *not*
  admissible. Adjacency is the unique local contradiction.
* `no_nonadjacent_local_contradiction (hd : 2 ≤ d) (x)` — packaged negative answer: a
  locally admissible word with holes at `x` and `x + d` exists for every `d ≥ 2`.
* `distance_band_admissible` — the whole requested band `d ∈ {2, …, 246}` is covered.

### Target 2 — explicit local gap patterns

The word `twoHoleWord x d` *is* the explicit local model: positions `x` and `x + d` are
holes, every other position is in `A`, and (for `d ≥ 2`) no two holes are adjacent, so all
gaps are `≤ 2`. For example at `d = 2`: `…, x-1∈A, x=hole, x+1∈A, x+2=hole, x+3∈A, …`.

### Target 3 — stronger variants (all compatible, none force a contradiction)

* **A block of many forced holes in a short interval.** `many_holes_block k` produces `k`
  holes of the alternating word inside `[0, 2k]`; with `k = 123` that is 123 forced holes
  inside an interval of length 246, none adjacent (`altWord_block_locallyAdmissible`,
  `altWord_holes_nonadjacent`). The densest admissible hole set is an entire parity class.
* **Both parity classes densely.** `mod3HoleWord` (holes at every multiple of 3) hits both
  parities (`mod3HoleWord_both_parities`) yet is admissible
  (`mod3HoleWord_locallyAdmissible`).
* **`gcd`-controlled endpoints.** `gcd_controlled_models` gives admissible witnesses with
  both coprime endpoints (`gcd 6 11 = 1`) and non-coprime endpoints (`gcd 6 12 = 6`);
  admissibility does not depend on `gcd(x, x+d)`.
* **The arithmetic mechanism cannot close either.** `exists_crt_at_distance` shows the
  CRT machinery can *produce* two hole-forcing multiples at any prescribed distance `d ≥ 1`
  (given `Q₁·Q₂ + d ≤ M − N + 1`, `gcd(Q₁,Q₂)=1`). For `d = 1` this is exactly the adjacent
  input of `blockerPair_contradiction`; for `d ≥ 2` the two holes are non-adjacent, so no
  contradiction follows. Producing distance-`d` holes is possible; concluding `False` is
  not.

### Target 4 — output

* Exact theorem names: as listed above.
* Does any non-adjacent-hole contradiction survive? **No.**
* Counterexamples / local models: `twoHoleWord` (distance `d`), `altWord` (dense block /
  one parity), `mod3HoleWord` (both parities). All are `LocallyAdmissible`.

## Part B — the Kernel AP-blocker

This is a genuine *adjacent*-hole blocker packaged from an arithmetic-progression input.

File: `RequestProject/Erdos287/KernelAPBlocker.lean`.

Setup: `A ⊆ [N, M]` a `Gap2CE`, `M ≥ 8152`; for a prime `p`, `qₚ = p^(eₚ+1)` (`ceilMod`).
Kernel modulus `Qₚ` (`Gap2CE.kernelMod p`): `q₂` for `p = 2`, and `2·qₚ` for odd `p`.

* `Gap2CE.HoleForcing.of_dvd` — hole-forcing is upward closed under divisibility.
* `Gap2CE.ceilMod_dvd_kernelMod`, `Gap2CE.one_le_kernelMod`,
  `Gap2CE.kernelMod_holeForcing` — `qₚ ∣ Qₚ`, `Qₚ ≥ 1`, and `Qₚ` is hole-forcing.
* `Gap2CE.AP_prime_kills_holeForcing_add` — the `+1` companion of the existing
  `AP_prime_kills_holeForcing`.
* `Gap2CE.kernel_AP_blocker` — **no prime `r ∈ [N+1, M−1]` has `r ≡ ±1 (mod Qₚ)`**
  (stated as `Qₚ ∣ (r−1) ∨ Qₚ ∣ (r+1)`).
* `Gap2CE.kernel_AP_blocker_modEq` — the same statement with literal congruences
  `r ≡ 1` / `r ≡ Qₚ − 1 (mod Qₚ)`.

Reason: `Qₚ ∣ (r∓1)` gives `qₚ ∣ (r∓1)`, so `r∓1` is a ceiling hole; `r` is a prime hole
(`primeFree`). The two are adjacent, contradicting `blockerPair_contradiction`.
