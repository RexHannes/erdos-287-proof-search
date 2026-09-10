#!/usr/bin/env python3
"""Emit the Lean certificate files and the chain file from chain.json."""

import json
import os

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)

ch = json.load(open(os.path.join(HERE, "chain.json")))

# ------------------------------------------------------------------ re-verify the data
TARGET = 10 ** 60
prev = None
for e in ch:
    c, t, q, P, ps = e["c"], e["t"], e["q"], e["P"], e["ps"]
    assert q == c * 2 ** t + 1
    assert P == c * 2 ** (t + 1) + 1
    assert P == 2 * q - 1
    assert q > 11
    prod = 1
    for x in ps:
        prod *= x
    assert prod == c
    assert c * 2 ** (t + 1) < 2 ** 256
    if prev is not None:
        assert prev < P <= 2 * prev, (prev, P)
    prev = P
assert 2 * ch[-1]["P"] >= TARGET
print("data re-verified; chain length", len(ch))

NORM_NUM_LIMIT = 10 ** 7


def prime_thm(name, N, c, t, a, ps):
    if N < NORM_NUM_LIMIT:
        return "theorem %s : Nat.Prime %d := by norm_num\n" % (name, N)
    pslist = "[" + ", ".join(str(x) for x in ps) + "]"
    return (
        "theorem %s : Nat.Prime %d :=\n"
        "  prime_of_cert' (c := %d) (t := %d) (a := %d) (ps := %s)\n"
        "    (by intro p hp; fin_cases hp <;> norm_num) (by norm_num) (by norm_num) (by decide)\n"
        % (name, N, c, t, a, pslist)
    )


# ------------------------------------------------------------------ certificate files
CHUNK = 24
nfiles = (len(ch) + CHUNK - 1) // CHUNK
certdir = os.path.join(ROOT, "RequestProject", "Certificates")
os.makedirs(certdir, exist_ok=True)
for old in os.listdir(certdir):
    os.remove(os.path.join(certdir, old))

for f in range(nfiles):
    lines = [
        "import RequestProject.PowMod",
        "",
        "/-!",
        "# Certified primes, block %d" % f,
        "",
        "Kernel-checked Lucas primality certificates for the prime pairs",
        "`(q_i, P_i = 2 * q_i - 1)` with `%d ≤ i < %d`." % (f * CHUNK, min((f + 1) * CHUNK, len(ch))),
        "-/",
        "",
        "namespace Erdos287",
        "",
        "set_option maxRecDepth 100000",
        "",
    ]
    for i in range(f * CHUNK, min((f + 1) * CHUNK, len(ch))):
        e = ch[i]
        lines.append(prime_thm("prime_q%03d" % i, e["q"], e["c"], e["t"], e["aq"], e["ps"]))
        lines.append(prime_thm("prime_P%03d" % i, e["P"], e["c"], e["t"] + 1, e["aP"], e["ps"]))
    lines.append("end Erdos287")
    open(os.path.join(certdir, "Block%02d.lean" % f), "w").write("\n".join(lines) + "\n")

# ------------------------------------------------------------------ chain file
lines = ["import RequestProject.Small"]
for f in range(nfiles):
    lines.append("import RequestProject.Certificates.Block%02d" % f)
lines += [
    "",
    "/-!",
    "# The certified chain of prime pairs",
    "",
    "For each `i` the pair `(q_i, P_i = 2 * q_i - 1)` consists of two primes with `q_i > 11`,",
    "so `windowPairSupply_of_prime_pair` gives `WindowPairSupply M` for `P_i + 1 <= M <= 2 * P_i`.",
    "The chain satisfies `P_i < P_{i+1} <= 2 * P_i`, hence the intervals `[P_i + 1, 2 * P_i]`",
    "overlap, and together with the small cases they cover every `M <= 10 ^ 60`.",
    "-/",
    "",
    "namespace Erdos287",
    "",
    "/-- Bookkeeping step for chaining the covering intervals. -/",
    "theorem cover_step {M lo B : \u2115} (h : B < M) (hb : lo \u2264 B + 1) : lo \u2264 M := by omega",
    "",
]
for i, e in enumerate(ch):
    lines.append(
        "theorem wps_chain%03d {M : \u2115} (h1 : %d \u2264 M) (h2 : M \u2264 %d) : WindowPairSupply M :=\n"
        "  windowPairSupply_of_prime_pair (q := %d) (P := %d) prime_q%03d (by norm_num)\n"
        "    (by norm_num) prime_P%03d (by omega) (by omega)\n"
        % (i, e["P"] + 1, 2 * e["P"], e["q"], e["P"], i, i)
    )

# split the covering argument into blocks so that no single proof carries too many hypotheses
BLK = 24
blocks = [list(range(i, min(i + BLK, len(ch)))) for i in range(0, len(ch), BLK)]
block_lo = []
block_hi = []
for bi, blk in enumerate(blocks):
    lo = 8 if bi == 0 else 2 * ch[blocks[bi - 1][-1]]["P"] + 1
    hi = 2 * ch[blk[-1]]["P"]
    block_lo.append(lo)
    block_hi.append(hi)
    body = ["theorem wps_block%02d {M : \u2115} (h1 : %d \u2264 M) (h2 : M \u2264 %d) :" % (bi, lo, hi),
            "    WindowPairSupply M := by"]
    small = []
    if bi == 0:
        small = [(14, "windowPairSupply_seven", 8),
                 (26, "windowPairSupply_thirteen", 14),
                 (50, "windowPairSupply_twentyfive", 26),
                 (92, "windowPairSupply_46", 47),
                 (164, "windowPairSupply_82", 83),
                 (316, "windowPairSupply_158", 159)]
    first = True
    for (bound, name, need) in small:
        body.append("  rcases le_or_gt M %d with hle | hgt" % bound)
        if first:
            body.append("  \u00b7 exact %s (le_trans (by norm_num) h1) hle" % name)
            first = False
        else:
            body.append("  \u00b7 exact %s (cover_step hgt (by norm_num)) hle" % name)
    for i in blk:
        body.append("  rcases le_or_gt M %d with hle | hgt" % (2 * ch[i]["P"]))
        if first:
            body.append("  \u00b7 exact wps_chain%03d (le_trans (by norm_num) h1) hle" % i)
            first = False
        else:
            body.append("  \u00b7 exact wps_chain%03d (cover_step hgt (by norm_num)) hle" % i)
    body.append("  exact absurd h2 (Nat.not_le.2 hgt)")
    body.append("")
    lines.extend(body)

lines += [
    "/-- Every `M` with `8 <= M <= 10 ^ 60` admits a window pair supply. -/",
    "theorem windowPairSupply_of_le {M : \u2115} (h1 : 8 \u2264 M) (h2 : M \u2264 10 ^ 60) :",
    "    WindowPairSupply M := by",
]
for bi in range(len(blocks)):
    lines.append("  rcases le_or_gt M %d with hle | hgt" % block_hi[bi])
    if bi == 0:
        lines.append("  \u00b7 exact wps_block%02d h1 hle" % bi)
    else:
        lines.append("  \u00b7 exact wps_block%02d (cover_step hgt (by norm_num)) hle" % bi)
lines.append("  omega")
lines.append("")
lines.append("end Erdos287")
open(os.path.join(ROOT, "RequestProject", "Chain.lean"), "w").write("\n".join(lines) + "\n")

# ------------------------------------------------------------------ data file
json.dump(ch, open(os.path.join(ROOT, "PRIME_PAIR_COVER.json"), "w"), indent=1)
print("emitted %d certificate blocks" % nfiles)
