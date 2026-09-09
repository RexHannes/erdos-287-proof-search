import PrimeCert

/-!
# Erdős #287 finite-1e60 primality probe

The two largest primes in the new finite certificate are both in Proth form.  We certify them
using the Lean-4.28-compatible PrimeCert package pinned in `lakefile.toml`.  No probable-prime
result, `native_decide`, or external oracle is a proof input.
-/

namespace Erdos287

set_option maxRecDepth 100000 in
theorem primeProbe_lastP : Nat.Prime
    613478595181419364517067398874818080046226296254603840192513 := prime_cert%
  [small {2},
   pock3 (613478595181419364517067398874818080046226296254603840192513,
     5, 1, 0, 2 ^ 101)]

set_option maxRecDepth 100000 in
theorem primeProbe_lastq : Nat.Prime
    306739297590709682258533699437409040023113148127301920096257 := prime_cert%
  [small {2},
   pock3 (306739297590709682258533699437409040023113148127301920096257,
     5, 1, 0, 2 ^ 100)]

#print axioms primeProbe_lastP
#print axioms primeProbe_lastq

end Erdos287
