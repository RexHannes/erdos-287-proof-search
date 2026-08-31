#!/usr/bin/env python3
from pathlib import Path
import sys

if len(sys.argv) != 3:
    raise SystemExit('usage: build_r8_sync.py R7.tex R8.tex')
src_path = Path(sys.argv[1])
out_path = Path(sys.argv[2])
s = src_path.read_text(encoding='utf-8')
orig_len = len(s)

def req(old, new, expected=None):
    global s
    n = s.count(old)
    if n == 0:
        raise SystemExit(f'missing required anchor: {old[:100]!r}')
    if expected is not None and n != expected:
        raise SystemExit(f'anchor count {n} != {expected}: {old[:100]!r}')
    s = s.replace(old, new)

req(r'\lhead{Erd\H{o}s \#287 -- V16.6 Theory Manual R7}',
    r'\lhead{Erd\H{o}s \#287 -- V16.7 Theory Manual R8}', 1)
req(r'\rhead{30 August 2026}', r'\rhead{31 August 2026}', 1)
req('Version 16.6 -- Public Prepublication Candidate R7 (not yet published)',
    'Version 16.7 -- Public Review R8 (31 August 2026 synchronization)', 1)
req(r'\date{30 August 2026}', r'\date{31 August 2026}', 1)

start = s.index(r'\begin{center}', s.index(r'\begin{document}'))
end = s.index(r'\end{center}', start) + len(r'\end{center}')
status = r'''\begin{center}
\fcolorbox{deepblue}{softblue}{\begin{minipage}{0.92\textwidth}
\textbf{Status -- 31 August 2026 synchronization.}
\textbf{Erd\H{o}s Problem \#287 remains open.} The unconditional public Lean theorem
excluding exact counterexamples with maximum denominator at most $4\times10^9$ is
unchanged. The Gate~0--2 theory manual below is retained as theory rather than replaced by
a status-only note.

The newest audited C0 milestone supersedes the controlling 30-August R7 headline. Exact
product collision and Double Type~II are analytically closed. C0 is analytically closed
\emph{conditional on} the separate physical/formal normalisation pin
\[
\boxed{\texttt{SHAREDGCD-OMEGAH-NORMALISATION-SOURCEPIN45}},
\]
together with the complete physical Perron/nuclear normalisation unless absorbed into the
same pin. The repaired finite-Fourier contraction is
\[
\eta_b^2\ll L^C\left(\frac{x}{B}+\frac1N+\frac1{E_b}+\frac1x\right).
\]
The product energy is source-specific to the literal bounded dyadic packet, the complete
unit branch is $\gcd(b a_\rho b_\rho u_\rho,x)=1$, and small-$x$ packets have an explicit
short-conductor/low-$Q$ owner.

The transverse long-conductor branch is strictly reduced but remains \textbf{OPEN}.
One-conductor reciprocity and the $q_C$ unitary-Fourier theorem pass at the audited
research/paper level; the dense-$q_C$ compiler closes only its stated strict subregion. The
naive full-CRT two-signless-carrier DFT is retracted. The current first analytic residual is
\[
\boxed{\texttt{THREEFACTOR-TRANSVERSE-CRITICAL-BEZOUTNUMERATOR-SINGLECARRIER45}}.
\]
The parallel $b$-diagonal node
\texttt{BDIAGONAL-AFFINEA-SURVIVING-VERTEX-RECT45} remains separately open.

The supplied 31-August Aristotle bundle records a completed C0 unitary-Fourier /
transverse-carrier-interface bank with \texttt{lake build: PASS}, 8298 jobs and zero errors;
its audited declarations use only ordinary Mathlib foundations. The newest named Lean files
depend on a larger dependency graph than is presently synchronized in public main, so this
manuscript does not pretend that the same 8298-job build has already been reproduced from
public \texttt{RequestProject/Main.lean}. No unfinished one-conductor formalisation is
fabricated or pre-promoted.
\end{minipage}}
\end{center}'''
s = s[:start] + status + s[end:]

a0 = s.index(r'\begin{abstract}')
a1 = s.index(r'\end{abstract}', a0) + len(r'\end{abstract}')
abstract = r'''\begin{abstract}
Erd\H{o}s Problem \#287 asks whether every representation
\[
1=\frac1{n_1}+\cdots+\frac1{n_k},\qquad 1<n_1<\cdots<n_k,
\]
contains a consecutive gap of size at least $3$. The strongest unconditional theorem in
this project remains machine-checked: there is no exact counterexample with maximum
denominator at most $4\times10^9$. The remaining global range is conditional on explicit
source/analytic compilers; no eventual \texttt{WindowPairSupply} theorem and no
unconditional solution are claimed.

This revision preserves the self-contained Gate~0--2 theory manual and supersedes the
controlling frontier/status layer. The 31-August hostile audit closes the canonical C0
exact-product and Double Type~II analytic cores, conditional on the separately exposed
physical normalisation source pin. After reduced-projective conditioning the relevant
Kloosterman kernel is independent of the balanced $b$ source. Writing
$b=\ell_b d_b e_b$ with $d_b,e_b>Y$ and grouping $n=\ell_bd_b$, residue aggregation and
inversion on units produce a restricted finite Fourier matrix with exact norm $\sqrt{x}$.
Together with fixed-depth source product energy this yields
\[
\eta_b^2\ll L^C\left(\frac{x}{B}+\frac1N+\frac1{E_b}+\frac1x\right).
\]
The statement is source-specific; the complete unit firewall is
$\gcd(b a_\rho b_\rho u_\rho,x)=1$, complementary nonunit cells are separately routed, and
small-$x$ packets are assigned to the short-conductor/low-$Q$ owner. No conjectural
M\"obius cancellation and no new spectral black box are used.

For the transverse long-conductor family, the naive two-signless full-CRT DFT is retracted:
CRT fusion leaves cross-modulus inverse coefficients in the numerator. A repaired
one-conductor reciprocity normal form is banked at the research level. For
\[
\Phi_P=e_q(A\overline{rm})e_r(B\overline{qm}),
\]
reciprocating only the $q$ component gives
\[
\Phi_P=\operatorname{Arch}_P\,e_{m_P}(\Gamma_P^{\rm red}\bar q),\qquad
\Gamma_P=-A+mB\overline m\pmod r,\qquad
m_P=rm/(B-A,r),
\]
with $(\Gamma_P^{\rm red},m_P)=1$. Grouping $q=S_1S_2$ then gives the audited finite-Fourier
contraction
\[
\eta_P^2\ll L^C\left(\frac{m_P}{L_1L_2}+\frac1{L_1}+\frac1{L_2}+\frac1{m_P}\right).
\]
This closes the dense-$q_C$ subregion under explicit dominance/two-long-group hypotheses,
not the full transverse branch.

The first current analytic residual is
\[
\boxed{\texttt{THREEFACTOR-TRANSVERSE-CRITICAL-BEZOUTNUMERATOR-SINGLECARRIER45}},
\]
where both packet orientations and the full B\'ezout-dependent reciprocal numerator remain
active. The parallel $b$-diagonal node
\texttt{BDIAGONAL-AFFINEA-SURVIVING-VERTEX-RECT45} is independently open. The earlier R7
uniform-$k=0$/one-level-M\"obius residual is retained below as historical research
provenance but is superseded as the controlling public first frontier.

The supplied Aristotle C0/unitary-Fourier bank records a successful 8298-job, zero-error
kernel build and ordinary Mathlib axiom footprint. Its latest modules depend on a larger
formal graph than is currently synchronized into public main, so formal and research status
remain explicitly separated. Erd\H{o}s \#287 remains open.
\end{abstract}'''
s = s[:a0] + abstract + s[a1:]

g0 = s.index(r'\section*{Status at a glance}')
g1 = s.index(r'\tableofcontents', g0)
glance = r'''\section*{Status at a glance}
\addcontentsline{toc}{section}{Status at a glance}
\begin{center}
\scriptsize
\renewcommand{\arraystretch}{1.14}
\begin{tabularx}{\textwidth}{>{\raggedright\arraybackslash}p{0.32\textwidth}
>{\raggedright\arraybackslash}p{0.24\textwidth}X}
\toprule
Item & Status & Meaning \\
\midrule
Finite $M\le4\times10^9$ exclusion & \status{KERNEL-PROVED / UNCHANGED} & Strongest unconditional public theorem.\\
C0 unitary-Fourier core & \status{ANALYTICALLY BANKED} & Hostile repairs included; exact four-term contraction.\\
Exact product collision & \status{ANALYTICALLY BANKED} & Closed analytic core, not the whole problem.\\
Double Type II & \status{ANALYTICALLY BANKED} & Closed analytic core, subject to the source architecture.\\
C0 & \status{CONDITIONAL SOURCE PIN} & Analytically closed conditional on physical/formal normalisation.\\
\texttt{SHAREDGCD-OMEGAH-NORMALISATION-SOURCEPIN45} & \status{OPEN SOURCE PIN} & Physical $\Omega_H$ and Perron/nuclear normalisation unless absorbed.\\
Naive transverse two-signless DFT & \status{RETRACTED} & Full CRT leaves moving numerator coefficients.\\
One-conductor reciprocity & \status{ANALYTICALLY BANKED} & Repaired transverse reciprocity normal form.\\
$q_C$ unitary Fourier & \status{ANALYTICALLY BANKED} & Arbitrary $L^2$ vectors; no M\"obius cancellation required.\\
Dense-$q_C$ compiler & \status{BANKED ON EXPLICIT HYPOTHESES} & Strict subregion only.\\
Full transverse branch & \status{STRICT REDUCTION / OPEN} & Critical cells survive.\\
\texttt{THREEFACTOR-TRANSVERSE-CRITICAL-BEZOUTNUMERATOR-SINGLECARRIER45} & \status{FIRST ANALYTIC RESIDUAL / OPEN} & Both orientations and B\'ezout numerator remain.\\
\texttt{BDIAGONAL-AFFINEA-SURVIVING-VERTEX-RECT45} & \status{PARALLEL OPEN} & Kept separate from transverse.\\
Supplied Aristotle C0 bank & \status{KERNEL-CHECKED BUNDLE} & 8298 jobs, zero errors; public dependency-complete import pending.\\
Gate~0--2 / FCL / effectivity / \texttt{WindowPairSupply} & \status{OPEN / DOWNSTREAM} & No implication is collapsed.\\
Erd\H{o}s Problem \#287 & \status{OPEN} & No unconditional solution claim.\\
\bottomrule
\end{tabularx}
\end{center}

\paragraph{Status vocabulary.}
\status{KERNEL-PROVED} is reserved for statements checked by the Lean kernel in the stated
formal bank. \status{ANALYTICALLY BANKED} means the research/paper theorem survived the
current analytic audit; it is not automatically a Lean proof. \status{CONDITIONAL SOURCE
PIN} exposes a literal physical-source obligation. \status{STRICT REDUCTION} means the
parent has been reduced but not closed. \status{OPEN}, \status{SUPERSEDED}, and
\status{RETRACTED} have their literal meanings. Historical material is retained for
provenance even when it is no longer controlling.

'''
s = s[:g0] + glance + s[g1:]

anchor = r'\section{The problem and the scope of this note}'
if anchor not in s:
    raise SystemExit('theory anchor missing')
checkpoint = r'''\section{31 August 2026 C0/transverse synchronization}\label{sec:aug31sync}

This section is the controlling analytic checkpoint for this revision. It changes the
frontier/status assignment, not the underlying Gate~0--2 theory manual. Earlier R7
uniform-$k=0$ material remains later in the document as a dated research branch.

\subsection{C0 exact product and Double Type II}
After canonical reduced-projective conditioning the Kloosterman kernel becomes independent
of the balanced $b$ source. For $b=\ell_b d_b e_b$ with $d_b,e_b>Y$, combine
$n=\ell_b d_b$. Residue aggregation modulo $x$ and inversion on unit residues give a
restricted discrete Fourier matrix of exact operator norm $\sqrt{x}$. With fixed-depth
physical product energy,
\[
\boxed{\eta_b^2\ll L^C\left(\frac{x}{B}+\frac1N+\frac1{E_b}+\frac1x\right)}.
\]
The product-energy theorem is asserted only for the literal bounded dyadic physical packet;
the complete unit branch is $\gcd(b a_\rho b_\rho u_\rho,x)=1$; nonunit cells belong to D4;
and small-$x$ cells route to the short-conductor/low-$Q$ owner. Constants are chosen in the
order structure, packet losses, $K_*$, $K_{\rm tr}$, $(K_Y,K_x)$, then $k$. Thus exact
product collision and Double Type~II are analytically closed, and C0 is analytically closed
conditional on formal normalisation.

\subsection{C0 corrections}
The old post-conditioning index $n=j\overline{u'}\pmod x$ and old wrap $1+UU'/B$ are
\status{RETRACTED} as controlling C0 architecture. Historical occurrences are preserved.
The full physical source is no longer advertised as requiring a moving-level
inverse-convolution large sieve after canonical projective cancellation.

\subsection{Transverse repaired reciprocity and finite Fourier}
For a packet, $R_P=z^2q_Cq_m$ with
$q_C=2(e/a_1)(r_2/c_2)b_1^\flat$, and symmetrically for the primed packet. Full CRT fusion of
$q_C$ and $q_m$ leaves cross-modulus inverse coefficients in the numerator, so the naive
two-signless DFT is \status{RETRACTED}.

For
\[
\Phi_P=e_q(A\overline{rm})e_r(B\overline{qm}),
\]
reciprocate only the $q$ component. With
\[
\Gamma_P=-A+mB\overline m\pmod r,\qquad g_P=(B-A,r),\qquad m_P=rm/g_P,
\]
one obtains
\[
\boxed{\Phi_P=\operatorname{Arch}_P\,e_{m_P}(\Gamma_P^{\rm red}\bar q)},\qquad
(\Gamma_P^{\rm red},m_P)=1.
\]
This is \texttt{THREEFACTOR-TRANSVERSE-ONECONDUCTOR-RECIPROCITY45}.

If $q=S_1S_2$, the finite operator gives
\[
\left|\sum\alpha(S_1)\beta(S_2)e_{m_P}(\Gamma_P^{\rm red}\overline{S_1}\overline{S_2})\right|
\ll L^C\sqrt{m_P(1+L_1/m_P)(1+L_2/m_P)}\,\|\alpha\|_2\|\beta\|_2,
\]
and hence
\[
\boxed{\eta_P^2\ll L^C\left(\frac{m_P}{L_1L_2}+\frac1{L_1}+\frac1{L_2}+\frac1{m_P}\right)}.
\]
This is \texttt{THREEFACTOR-TRANSVERSE-qC-UNITARYFOURIER45}. It accepts arbitrary $L^2$
vectors and spends no M\"obius cancellation. The dense-$q_C$ compiler closes only packets
satisfying its explicit dominance/two-long-source-group hypotheses.

\subsection{Exact current frontier}
The older \texttt{THREEFACTOR-TRANSVERSE-CARRIERFACTORIZATION-PAIR-EXISTENCE45} is
\status{SUPERSEDED AS FIRST FRONTIER}. The first current analytic residual is
\[
\boxed{\texttt{THREEFACTOR-TRANSVERSE-CRITICAL-BEZOUTNUMERATOR-SINGLECARRIER45}}.
\]
The surviving operator retains both packet orientations and the full B\'ezout-dependent
reciprocal numerator. It includes nondominant $q_C$/$q_C'$ cells, partitions with one short
side, single atomic-carrier dominance, and critical $q\asymp rm$ geometry. Candidate second
Fourier axes include the B\'ezout numerator, an opposite-packet carrier, the $m$ variable
after $TT^*$, a signed $L^2$ carrier, grouped short factors, or both orientations. None is
promoted here.

The parallel branch
\[
\boxed{\texttt{BDIAGONAL-AFFINEA-SURVIVING-VERTEX-RECT45}:\ \status{OPEN}}
\]
is kept separate.

\subsection{Formal/Aristotle firewall}
The supplied 31-August bundle records the completed C0 unitary-Fourier /
transverse-carrier-interface bank and a default \texttt{lake build} of 8298 jobs with zero
errors. New declaration axiom audits report only ordinary Mathlib foundations such as
\texttt{propext}, \texttt{Classical.choice}, and \texttt{Quot.sound}, with no reported
\texttt{sorry}, custom axiom, \texttt{unsafe}, opaque shortcut, \texttt{implemented_by}, or
\texttt{native_decide}. The named newest files depend on a larger formal graph than the
current public-main tree, so the paper records the verified supplied bank without claiming
that public \texttt{RequestProject/Main.lean} already reproduces the 8298-job build.

'''
s = s.replace(anchor, checkpoint + anchor, 1)

for old, new in [
    ('The controlling main line has therefore moved downstream to the uniform $k=0$ SP-2\nreassembly.',
     'Historical R7 branch (superseded as controlling on 31 August 2026): the 30-August analysis had moved downstream to the uniform $k=0$ SP-2 reassembly.'),
    ('The main analytic frontier has therefore moved to uniform $k=0$.',
     'Historical R7 branch (superseded as controlling on 31 August 2026): the 30-August analysis had moved to uniform $k=0$.'),
    ('Accordingly the first exact main-line analytic residual is',
     'Accordingly, in the superseded 30-August R7 branch, the first exact main-line analytic residual was'),
    ('The current first exact main-line\nanalytic residual is',
     'The superseded 30-August R7 branch recorded the first exact main-line analytic residual as'),
    ('CURRENT MAIN PARENT', 'HISTORICAL R7 PARENT / SUPERSEDED AS CONTROLLING'),
    ('current first exact main-line analytic residual is',
     'historical R7 first exact main-line analytic residual was'),
]:
    s = s.replace(old, new)

old_label = '287-K0-SP2-DET1-SHAREDGCD-ONELEVEL-MOBIUS-GRAM45'

enddoc = s.rfind(r'\end{document}')
if enddoc < 0:
    raise SystemExit('end document missing')
final = r'''\section*{31 August 2026 controlling final status}
\addcontentsline{toc}{section}{31 August 2026 controlling final status}
\begin{center}
\small
\begin{tabular}{ll}
\toprule
Finite $M\le4\times10^9$ & \status{KERNEL-PROVED / unchanged}\\
C0 exact-product / Double Type II & \status{ANALYTICALLY BANKED}\\
C0 & \status{ANALYTICALLY CLOSED / CONDITIONAL SOURCE PIN}\\
Formal source pin & \texttt{SHAREDGCD-OMEGAH-NORMALISATION-SOURCEPIN45}\\
Full transverse branch & \status{STRICTLY REDUCED / OPEN}\\
First transverse residual & \texttt{CRITICAL-BEZOUTNUMERATOR-SINGLECARRIER45}\\
Parallel $b$-diagonal & \status{OPEN}\\
Supplied latest formal build & \status{8298 jobs / 0 errors; public dependency sync pending}\\
Erd\H{o}s \#287 & \status{OPEN}\\
\bottomrule
\end{tabular}
\end{center}

The historical Gate~0--2 theory, R7 uniform-$k=0$ branch, Ford/FCL architecture, and finite
compiler are preserved above. No implication from the local C0/transverse milestones to a
complete solution is asserted. Downstream Twin Prime work, if referenced, is a separate
programme and is not proved by this manuscript.

'''
s = s[:enddoc] + final + s[enddoc:]

for needle in [
    r'Erd\H{o}s Problem \#287 remains open',
    'SHAREDGCD-OMEGAH-NORMALISATION-SOURCEPIN45',
    'THREEFACTOR-TRANSVERSE-CRITICAL-BEZOUTNUMERATOR-SINGLECARRIER45',
    'BDIAGONAL-AFFINEA-SURVIVING-VERTEX-RECT45',
    '8298 jobs',
]:
    if needle not in s:
        raise SystemExit(f'missing required R8 status: {needle}')
for stale in [
    'The controlling main line has therefore moved downstream to the uniform $k=0$',
    'The main analytic frontier has therefore moved to uniform $k=0$.',
    'current first exact main-line analytic residual is',
]:
    if stale in s:
        raise SystemExit(f'stale controlling R7 phrase survives: {stale}')
for forbidden in ['Proof of Erd\\H{o}s \\#287', 'Erd\\H{o}s \\#287 solved']:
    if forbidden in s:
        raise SystemExit(f'publication-firewall phrase found: {forbidden}')

out_path.write_text(s, encoding='utf-8')
print(f'R8 generated: {out_path} ({orig_len} -> {len(s)} chars)')
print(f'historical R7 residual occurrences retained: {s.count(old_label)}')
