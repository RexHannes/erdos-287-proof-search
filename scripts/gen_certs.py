import json, sys
from search_windows import is_prime, factor

LEAF = 10**9   # primes at most this are proved by norm_num trial division

certs = {}   # p -> (a, factorlist)
order = []   # topological order (dependencies first)

def find_witness(p, fac):
    for a in range(2, 200):
        if pow(a, p-1, p) != 1: continue
        if all(pow(a, (p-1)//q, p) != 1 for q in fac):
            return a
    raise Exception("no witness for %d" % p)

def build(p):
    if p in certs or p <= LEAF:
        return
    fac = factor(p-1)
    for q in fac:
        build(q)
    a = find_witness(p, fac)
    certs[p] = (a, sorted(fac.items()))
    order.append(p)

def fuel(p):
    f = 1
    while (1 << f) <= p-1:
        f += 1
    return f

def lean_name(p):
    return "prime_%d" % p

def emit(p):
    a, fac = certs[p]
    l = "[" + ", ".join("(%d, %d)" % (q, e) for q, e in fac) + "]"
    prim = ", ".join(("prime_%d" % q) if q > LEAF else "(by norm_num)" for q, e in fac)
    wit = ", ".join(["(by decide)"] * len(fac))
    return f"""/-- Pratt certificate for the prime `{p}`
(`{p} - 1 = {' * '.join('%d^%d' % (q,e) for q,e in fac)}`, Lucas base `{a}`). -/
theorem {lean_name(p)} : Nat.Prime {p} :=
  Pratt.prime_of_certificate (p := {p}) (a := {a}) (f := {fuel(p)})
    (l := {l})
    (by norm_num) (by norm_num)
    ⟨{prim}, trivial⟩
    (by decide) (by decide)
    ⟨{wit}, trivial⟩
"""

def main():
    wins = json.load(open('/workspace/request-project/scripts/windows.json'))
    bigs = []
    for (x, U, a, p, b, q) in wins:
        for r in (p, q):
            if r not in bigs:
                bigs.append(r)
    for r in bigs:
        build(r)
    print("distinct primes needing pratt certs:", len(order))
    print("total leaves norm_num:", sum(1 for p in order for q,e in certs[p][1] if q <= LEAF))
    json.dump({"order": order, "certs": {str(k): v for k, v in certs.items()}},
              open('/workspace/request-project/scripts/certs.json', 'w'))
    with open('/workspace/request-project/scripts/certs_body.lean', 'w') as f:
        for p in order:
            f.write(emit(p) + "\n")

main()
