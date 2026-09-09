import Mathlib

/-!
# Erdős #287 finite-1e60 primality probe

This file is deliberately isolated from the proof architecture.  It tests whether Mathlib's
`norm_num` can kernel-check the two largest prime claims in the new finite certificate directly.
If this is too expensive in CI, the formalization will switch to a Proth/Pocklington certificate
layer rather than trusting probable-prime computation.
-/

namespace Erdos287

set_option maxRecDepth 100000 in
example : Nat.Prime
    613478595181419364517067398874818080046226296254603840192513 := by
  norm_num

set_option maxRecDepth 100000 in
example : Nat.Prime
    306739297590709682258533699437409040023113148127301920096257 := by
  norm_num

end Erdos287
