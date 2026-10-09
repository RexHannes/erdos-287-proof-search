# W3 publication package — checkpoint

**Erdős #287 remains open.** Referee verdict on record: `W3: PASS` (this is about the written
analytic proof, not a Lean fact).

## Frozen interface

`RequestProject/Erdos287/W3Publication.lean` and `W3Publication/Checkpoint.lean` (namespace
`Erdos287.W3Publication`) freeze the interface that W2.984 imports. They add **no new
mathematics**. Every name is an alias of an already-built declaration of `Erdos287.PostV87V90R`
(see `ERDOS287_POSTV87_V90R_REPORT.md`):

* `WidthStatement s` = `PostV87V90R.W3Statement s`, with `WidthStatement.mono`;
* `Wide` = `PostV87V90R.WideWindow`, and `wide_of_exactWord`;
* `counterexample_form`: the width statement in the form "no #287 counterexample with
  \(\max A\ge M_s\) and \(\max A\ge s\min A\)".

The W3 machinery reused unchanged by W2.984 comes from `PostV87V90R` and the earlier frozen
subtrees:
* exact #287 model;
* moment Cauchy consumer `WindowMomentData.false`;
* cyclic contact graph;
* affine gcd/contact compiler `AffineContactCompiler`;
* fixed-relative interval geometry;
* bounded-cofactor row rigidity;
* harmonic width bounds.

## Status

* `W3_of_provider` (in `PostV87V90R`) is kernel-proved. Its analytic provider is an explicit,
  never-constructed input.
* Independently, `Erdos287.W2984Publication.W3_of_selbergPairBound` re-derives W3 from the
  refactored framework with the Selberg constant \(4\) (BFM Lemma 4.6(iii)).
* `lake build RequestProject.Erdos287.W3Publication` succeeds. The historical subtrees are
  unchanged (checked by `W2984Publication/audit.sh`, step 4).
