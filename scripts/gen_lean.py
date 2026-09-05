import json
from search_windows import factor, is_prime

LEAF = 10**9
d = json.load(open('/workspace/request-project/scripts/certs.json'))
order = d['order']
certs = {int(k): v for k, v in d['certs'].items()}
wins = json.load(open('/workspace/request-project/scripts/windows.json'))

leaves = set()
for p in order:
    for q, e in certs[p][1]:
        if q not in certs:
            leaves.add(q)
leaves = sorted(leaves)


def fuel(p):
    f = 1
    while (1 << f) <= p - 1:
        f += 1
    return f


def pname(p):
    return "prime_%d" % p


def ref(q):
    return pname(q) if q in certs else "(by norm_num)"


header = r'''import RequestProject.CurrentProgramme.Erdos287September3PrattEngine

/-!
# Erdős Problem #287 — the primality certificate bank for the September-3 finite extension

Every prime used by the 24 new window certificates of
`Erdos287September3FiniteExtension24Window.lean` is certified here, from the bottom up:

* small primes (`< 10^9`) by `norm_num` trial division;
* every larger prime by an explicit **recursive Pratt certificate**
  (`Erdos287.Pratt.prime_of_certificate`): the full factorisation of `p - 1`, each of whose
  bases is itself certified earlier in this file, together with a Lucas witness whose two
  modular-exponentiation side conditions are closed by kernel computation (`decide`) on the
  proved-correct `Erdos287.Pratt.powMod`.

No `native_decide`, no `axiom`, no `sorry`, no `unsafe`, no `implemented_by`.
-/

set_option maxRecDepth 100000

namespace Erdos287
namespace Certificates

'''

out = [header]
out.append("/-! ### Leaf primes (trial division) -/\n")
for q in leaves:
    out.append("theorem %s : Nat.Prime %d := by norm_num\n" % (pname(q), q))
out.append("\n/-! ### Recursive Pratt certificates -/\n")
for p in order:
    a, fac = certs[p]
    l = "[" + ", ".join("(%d, %d)" % (q, e) for q, e in fac) + "]"
    prim = ", ".join(pname(q) for q, e in fac)
    wit = ", ".join(["(by decide)"] * len(fac))
    fexpr = " * ".join("%d^%d" % (q, e) for q, e in fac)
    out.append(f'''
/-- Pratt certificate: `{p}` is prime.
`{p} - 1 = {fexpr}`; Lucas base `{a}`. -/
theorem {pname(p)} : Nat.Prime {p} :=
  Pratt.prime_of_certificate (p := {p}) (a := {a}) (f := {fuel(p)})
    (l := {l})
    (by norm_num) (by norm_num)
    ⟨{prim}, trivial⟩
    (by decide) (by decide)
    ⟨{wit}, trivial⟩
''')
out.append("\nend Certificates\nend Erdos287\n")

open('/workspace/request-project/RequestProject/CurrentProgramme/'
     'Erdos287September3PrattCertificateBank.lean', 'w').write("".join(out))

# ------------------------------------------------------------------ windows
W = []
prevU = 4000000000
for i, (x, U, a, p, b, q) in enumerate(wins):
    L = prevU + 1
    assert x + 1 <= L, (x, L)
    assert U <= 2 * x
    assert x % a == 0 and x // a == p
    assert (x + 1) % b == 0 and (x + 1) // b == q
    assert U // p <= 9 and U // q <= 9
    W.append((i, x, U, L, p, q))
    prevU = U
FINAL = prevU
assert FINAL == 67108856338751594

wh = r'''import RequestProject.CurrentProgramme.Erdos287September3PrattCertificateBank
import RequestProject.Erdos287.FiniteRangeExtension

/-!
# Erdős Problem #287 — the 24-window finite extension (kernel replay)

The unconditional finite bank of `RequestProject/Erdos287/FiniteRangeExtension.lean` stops
at `M ≤ 4·10^9`.  This module replays, **in the Lean kernel**, a chain of 24 further window
certificates which extends the excluded range to

    M ≤ 67108856338751594.

Each window is an instance of the already-proved interval blocker
`Erdos287.Gap2CE.blocker_window`; the only new ingredient is that the two prime-power
witnesses of each window are now primes of size up to `3.4·10^16`, certified in
`Erdos287September3PrattCertificateBank.lean` by recursive Pratt certificates rather than
by trial division.  The windows are contiguous (`L_{i+1} = U_i + 1`), so there is no gap.

Main results:

* `Erdos287.Gap2CE.no_of_M_le_extendedCeiling` — no gap-`≤2` counterexample has
  `3 ≤ M ≤ 67108856338751594`;
* `Erdos287.no_Erdos287Counterexample_of_max_le_extendedCeiling` — no exact Erdős-#287
  counterexample has `max A ≤ 67108856338751594`;
* `Erdos287.arithmeticCoverage_exceeds_twoExp375` — `38643198608805673 < 67108856338751594`
  (the extension covers the recorded arithmetic-coverage endpoint `⌈2·exp(37.5)⌉`).

**FIREWALL — FINITE-CERTIFICATE-COVERAGE.**  This is a *finite arithmetic* result only.
It excludes maxima below an explicit ceiling.  It does **not** assert that the medium
analytic branch is closed, it does not supply any analytic input, and it does not bear on
Erdős #287 itself, which remains open.
-/

set_option maxRecDepth 100000

namespace Erdos287

/-- The ceiling reached by the September-3 finite extension. -/
def extendedCeiling : ℕ := 67108856338751594

namespace Gap2CE

'''
wout = [wh]
for (i, x, U, L, p, q) in W:
    wout.append(f'''/-- Window certificate at `x = {x}` (`{p}^1 ∣ x`, `{q}^1 ∣ x+1`):
no gap-`≤2` counterexample has `{L} ≤ M ≤ {U}`. -/
theorem windowStepExt_{i} (ce : Gap2CE) (h1 : {L} ≤ ce.M) (h2 : ce.M ≤ {U}) : False :=
  ce.blocker_window (x := {x}) (pu := {p}) (au := 1) (pv := {q}) (av := 1)
    Certificates.{pname(p)} Certificates.{pname(q)} (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num [CVal]) (by norm_num) (by norm_num [CVal])
    (by norm_num) (by norm_num) h1 h2

''')

wout.append('''/-- **No gap-`≤2` counterexample has `3 ≤ M ≤ 67108856338751594`.**
The 34 windows of the original bank cover `[3, 4·10^9]`; the 24 windows above are
contiguous and cover `[4000000001, 67108856338751594]`. -/
theorem no_of_M_le_extendedCeiling (ce : Gap2CE) (h3 : 3 ≤ ce.M)
    (hM : ce.M ≤ 67108856338751594) : False := by
  by_cases c : ce.M ≤ 4000000000
  · exact ce.no_of_M_le_4e9 h3 c
''')
for (i, x, U, L, p, q) in W[:-1]:
    wout.append(f'''  by_cases c{i} : ce.M ≤ {U}
  · exact windowStepExt_{i} ce (by omega) c{i}
''')
last = W[-1]
wout.append(f'''  exact windowStepExt_{last[0]} ce (by omega) hM

end Gap2CE

/-- **No exact Erdős-#287 counterexample has maximum `≤ 67108856338751594`.** -/
theorem no_Erdos287Counterexample_of_max_le_extendedCeiling {{A : Finset ℕ}}
    (h : Erdos287Counterexample A) (hM : A.max' h.nonempty ≤ 67108856338751594) : False := by
  refine (h.toGap2CE).no_of_M_le_extendedCeiling ?_ hM
  show 3 ≤ A.max' h.nonempty
  have := h.four_le_max
  omega

/-- The same statement, phrased with the named ceiling. -/
theorem no_Erdos287Counterexample_of_max_le_extendedCeiling' {{A : Finset ℕ}}
    (h : Erdos287Counterexample A) (hM : A.max' h.nonempty ≤ extendedCeiling) : False :=
  no_Erdos287Counterexample_of_max_le_extendedCeiling h hM

/-- **`arithmeticCoverage_exceeds_twoExp375`.**  The recorded arithmetic-coverage endpoint
`⌈2·exp(37.5)⌉ = 38643198608805673` lies strictly below the new ceiling. -/
theorem arithmeticCoverage_exceeds_twoExp375 :
    38643198608805673 < extendedCeiling := by
  norm_num [extendedCeiling]

end Erdos287
''')

open('/workspace/request-project/RequestProject/CurrentProgramme/'
     'Erdos287September3FiniteExtension24Window.lean', 'w').write("".join(wout))
print("windows", len(W), "final", FINAL, "pratt", len(order), "leaves", len(leaves))
