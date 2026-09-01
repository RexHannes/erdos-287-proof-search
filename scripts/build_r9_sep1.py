#!/usr/bin/env python3
from pathlib import Path
import sys

if len(sys.argv) != 3:
    raise SystemExit('usage: build_r9_sep1.py R8.tex R9.tex')

src = Path(sys.argv[1])
out = Path(sys.argv[2])
s = src.read_text(encoding='utf-8')


def req(old, new, expected=1):
    global s
    n = s.count(old)
    if n != expected:
        raise SystemExit(f'anchor count {n} != {expected}: {old[:120]!r}')
    s = s.replace(old, new, expected)

# Display/version metadata only. Historical dated prose is not globally rewritten.
req(r'\lhead{Erd\H{o}s \#287 -- V16.7 Theory Manual R8}',
    r'\lhead{Erd\H{o}s \#287 -- V16.8 Theory Manual R9}')
req(r'\rhead{31 August 2026}', r'\rhead{1 September 2026}')
req('Version 16.7 -- Public Review R8 (31 August 2026 synchronization)',
    'Version 16.8 -- Public Review R9 (1 September 2026 source reconstruction)')
req(r'\date{31 August 2026}', r'\date{1 September 2026}')

# Replace the first status box after \maketitle.
start = s.index(r'\begin{center}', s.index(r'\maketitle'))
end = s.index(r'\end{center}', start) + len(r'\end{center}')
status = r'''\begin{center}
\fcolorbox{deepblue}{softblue}{\begin{minipage}{0.92\textwidth}
\textbf{Status -- 1 September 2026 source reconstruction.}
\textbf{Erd\H{o}s Problem \#287 remains open.}  The unconditional Lean exclusion up to
$4\times10^9$ is unchanged.  The newest source archaeology has now recovered the literal
Ford--Maynard $G/H$ source and the true labelled seven-prime-vector master index.  On the
corrected strictly smooth balanced-seven cell the paper-level source calculation proves
$H_*(P)=-20$, including the strict Ford threshold and the required factor-$8$ three-prime
bound.

The exact vector-to-integer pushforward carries the physical fibre coefficient
$\Omega_C^{\#}(n)$; it is therefore not silently identified with the older unweighted
integer source.  The next controlling source/compiler nodes are
\[
\boxed{\path{BALANCED7-SP2-STRICTCELL-PHYSICAL-BRIDGE45}}
\quad\text{and then}\quad
\boxed{\path{FORD723-GENERATED-PACKET-CENSUS-AND-REPLACEMENT45}}.
\]
The generated Ford packet census, exact physical Perron census, full-source local analytic
kernel, and final large-$M$/public-predicate bridge remain open.

A supplied append-only Aristotle master-source-frontier bank reports
\texttt{lake build}: 8330 jobs, zero errors, with only ordinary Mathlib foundations in its
axiom audit.  That formal bank is used here as a verification checkpoint, while its generic
master-source/physical-dictionary interfaces remain explicitly uninhabited unless the
newer physical source reconstruction supplies them.  No theorem named \texttt{erdos287}
and no \texttt{Erdos287ClosureInputs} inhabitant are claimed.
\end{minipage}}
\end{center}'''
s = s[:start] + status + s[end:]

# Replace the abstract with a current, compact statement. The historical C0/transverse
# exposition remains in the body and is not erased.
a0 = s.index(r'\begin{abstract}')
a1 = s.index(r'\end{abstract}', a0) + len(r'\end{abstract}')
abstract = r'''\begin{abstract}
Erd\H{o}s Problem \#287 asks whether every representation
\[
1=\frac1{n_1}+\cdots+\frac1{n_k},\qquad 1<n_1<\cdots<n_k,
\]
contains a consecutive gap of size at least $3$.  The strongest unconditional theorem in
this project remains the machine-checked exclusion of exact counterexamples with maximum
denominator at most $4\times10^9$; the large-$M$ problem remains open.

This R9 synchronization re-anchors the later analytic packet work to the literal physical
source.  Ford--Maynard's $G/H$ factorisation has been recovered at paper level.  On the
strictly smooth $k=0,J=\varnothing$ cell it collapses pointwise to the truncated M\"obius
weight.  For seven pairwise distinct primes $p_i\in[Y,2Y)$ with $Y\ge256$, the strict
threshold and depth-three divisor inequalities give
\[
\boxed{H_*(P)=1-7+21-35=-20},\qquad P=\prod_{i=1}^{7}p_i.
\]
The genuine earliest master index is the labelled prime vector, not the downstream
C0/transverse/$b$-diagonal coordinates.  Pushing the vector source to integers introduces
the exact fibre weight $\Omega_C^{\#}(n)$, so the physical integer source is weighted and
is not automatically the older unweighted $P_{\rm sm}$.

A supplied append-only Aristotle master-source-frontier bank reports 8330 build jobs and
zero errors and formally banks the source-realisation firewalls, proof-local $\Omega$
scaffolding, typed packet compiler, Perron counterguards, and abstract reciprocal finite
Fourier kernels.  Physical realisation interfaces remain uninhabited where appropriate.
The next research task is the literal Ford-(7.23) generated-packet census and replacement by
source-specific local owners, followed by exact Perron/source reassembly.  No full-source
local analytic closure, no eventual \texttt{WindowPairSupply}, and no unconditional
solution of Erd\H{o}s \#287 are claimed.
\end{abstract}'''
s = s[:a0] + abstract + s[a1:]

# Replace the status-at-a-glance block.
g0 = s.index(r'\section*{Status at a glance}')
g1 = s.index(r'\tableofcontents', g0)
glance = r'''\section*{Status at a glance}
\addcontentsline{toc}{section}{Status at a glance}
\begin{center}
\scriptsize
\renewcommand{\arraystretch}{1.14}
\begin{tabularx}{\textwidth}{>{\raggedright\arraybackslash}p{0.38\textwidth}
>{\raggedright\arraybackslash}p{0.24\textwidth}X}
\toprule
Item & Status & Meaning \\
\midrule
Finite $M\le4\times10^9$ exclusion & \status{KERNEL-PROVED / UNCHANGED} & Strongest unconditional theorem.\\
Supplied master-source-frontier Aristotle bank & \status{KERNEL-CHECKED BUNDLE} & 8330 jobs, zero errors; physical interfaces remain explicit.\\
Ford $G/H$ source & \status{SOURCE FOUND} & Authoritative source recovered at paper level.\\
Balanced-seven strict cell / $H_*(P)=-20$ & \status{PAPER/RESEARCH PASS} & Strict threshold and factor-$8$ repair included.\\
Labelled prime-vector master source & \status{PAPER/RESEARCH PASS} & Correct earliest physical index recovered.\\
Weighted integer pushforward & \status{PAPER/RESEARCH PASS} & Carries $\Omega_C^{\#}(n)$; unweighted equality is not automatic.\\
\path{BALANCED7-SP2-STRICTCELL-PHYSICAL-BRIDGE45} & \status{FIRST PHYSICAL BRIDGE / OPEN} & Bind literal Ford/source fields into the public packet.\\
\path{FORD723-GENERATED-PACKET-CENSUS-AND-REPLACEMENT45} & \status{NEXT SOURCE/COMPILER FRONTIER / OPEN} & Exhaust generated branches and assign legal owners.\\
\path{MASTER-SOURCE-TO-TYPED-PERRON-PACKETS45} & \status{OPEN} & Exact generated packet/contour census incomplete.\\
\path{FULL-SOURCE-LOCAL-ANALYTIC-KERNEL45} & \status{OPEN} & No 100\% physical source coverage claim.\\
\texttt{WindowPairSupply} / final large-$M$ bridge & \status{OPEN} & End-to-end public-predicate closure not supplied.\\
Erd\H{o}s Problem \#287 & \status{OPEN} & No unconditional solution claim.\\
\bottomrule
\end{tabularx}
\end{center}

\paragraph{Status vocabulary.}
\status{KERNEL-PROVED} is reserved for kernel-checked statements.  \status{PAPER/RESEARCH
PASS} means a source/mathematical argument has survived the current research audit but has
not yet been promoted to the full physical Lean theorem.  \status{OPEN} means precisely
that the stated source, compiler, analytic, or global bridge is not discharged.

'''
s = s[:g0] + glance + s[g1:]

# Place the full September source update immediately after the TOC.
req(r'\tableofcontents',
    r'\tableofcontents\n\n\input{ERDOS287_SEPT1_SOURCE_RECONSTRUCTION_UPDATE.tex}')

# Mark the prior checkpoint and final ledger as historical rather than controlling.
s = s.replace(
    r'\section{31 August 2026 C0/transverse synchronization}\label{sec:aug31sync}',
    r'\section{31 August 2026 C0/transverse synchronization (historical checkpoint)}\label{sec:aug31sync}',
    1)
s = s.replace(
    'This section is the controlling analytic checkpoint for this revision. It changes the\nfrontier/status assignment, not the underlying Gate~0--2 theory manual.',
    'This section records the 31-August analytic checkpoint.  It is retained as historical\nprovenance; the controlling R9 source/compiler status is Section~\\ref{sec:sep1source}.',
    1)
s = s.replace(
    r'\section*{31 August 2026 controlling final status}',
    r'\section*{31 August 2026 historical final status (superseded by R9)}',
    1)
s = s.replace(
    r'\addcontentsline{toc}{section}{31 August 2026 controlling final status}',
    r'\addcontentsline{toc}{section}{31 August 2026 historical final status}',
    1)

# Safety checks.
for needle in [
    'Erd\\H{o}s Problem \\#287 remains open',
    'BALANCED7-SP2-STRICTCELL-PHYSICAL-BRIDGE45',
    'FORD723-GENERATED-PACKET-CENSUS-AND-REPLACEMENT45',
    'Omega_C^{\\#}',
    '8330 jobs',
    'ERDOS287_SEPT1_SOURCE_RECONSTRUCTION_UPDATE.tex',
]:
    if needle not in s:
        raise SystemExit(f'missing R9 status needle: {needle}')
for forbidden in [
    'Erd\\H{o}s \\#287 solved',
    'Proof of Erd\\H{o}s \\#287',
    'FULL-SOURCE-LOCAL-ANALYTIC-KERNEL45: CLOSED',
]:
    if forbidden in s:
        raise SystemExit(f'publication firewall violation: {forbidden}')

out.write_text(s, encoding='utf-8')
print(f'R9 generated: {out} ({len(s)} chars)')
