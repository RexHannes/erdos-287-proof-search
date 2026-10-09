# Merikoski v3 ↔ fixed-affine W2.984 dictionary

Sources: J. Merikoski, arXiv:1811.03008v3 [M]; Banks–Freiberg–Maynard arXiv:1404.5094v2 [BFM];
Polymath8b arXiv:1407.4897v4 [PM]. Section numbers (§) refer to `AFFINE_CHEN_TRANSFER_W2984.md`.

## Notation

| Merikoski (shifts) | fixed affine (W2.984) |
|---|---|
| \(n\in(N,2N]\), \(n\equiv b\ (W)\) | \(t\in\mathcal T=(T_1,T_2]\cap(t_0+W\mathbb Z)\) |
| \(n+h_i\) | \(L_i(t)=a_it+1\), \(a_i\le H\) distinct |
| \(P^+(\prod(h_j-h_i))\le\epsilon\log N\) | \(P^+(\prod a_i\prod(a_i-a_k))\le H<\epsilon\log X\) (§1.3) |
| \(\frac NW B^{-K}L_K(F)\) | \(\mathfrak M=\#\mathcal T\,B^{-K}L_K(F)\) |
| \(\nu_{\mathcal H,j,\ell}\) (with the \(Z\)-factor) | \(\nu_{j\ell}\) (without the \(Z\)-factor; Remark 8.3) |
| \(P(Y)\), \(P_0(Y)\) | \(P_{\mathcal P}(Y)\) with \(\mathcal P\) = primes \(\ne Z_{\rm exc}\) |
| \(y_1=\exp(\log^{1/3}N)\), \(y_2=N^{\delta^2}\), \(\varrho\), \(G\) | \(y=\exp((\log X)^{1/3})\), \(z_0=X^{\delta^2}\), \(\rho\), \(H\) (§4) |

## Results

| Merikoski v3 | Fixed-affine W2.984 | Changed? | Nature | Proof location |
|---|---|---|---|---|
| Lemma 13 (Chen inequality) | Lemma 2.1 / 2.2, affine Chen decomposition + \(S_{\rm sq}\) | **yes**: the pointwise inequality is false for non-squarefree \(n\) (kernel counterexample \(n=1925\)); corrected by \(\frac12\mathrm{sq}(n)\) | new correction; combinatorics independent of affine setting | §2; Lean `chen_pointwise`, `chen_weighted`, `affine_chen_weighted`, `merikoski_pointwise_fails` |
| — | Lemma 10.1 `AffineSquareTail` | new | new (elementary) | §10 |
| Lemma 14 (linear sieve) | same | no | citation [FI, Ch. 11–12] | §7.2, §8.4 |
| Lemma 15 (\(S_1\)) | Lemma 7.1 `AffineChenS1` | **yes**: literal CRT system for \(p=L_j(t)\), base \(a_jW\), \(\phi(a_jW)=a_j\phi(W)\), remainder classification (a)–(e) | new derivation, same main term | §3, §7 |
| Lemma 16 (\(S_2\)) | Lemma 8.1 `AffineChenS2` | **yes**: as Lemma 15, plus a two-sided small-prime split; \(p\) never overlaps spectators (\(p>X^\delta\)) | new derivation, same main term | §8 |
| Lemma 17 (\(S_3\)) | Lemma 9.1 `AffineChenS3` | **yes**: switch \(x=L_\ell(t)\), \(L_j=(a_jx+a_\ell-a_j)/a_\ell\), non-squarefree base \(a_\ell W\), exceptional prime in \(s\) (Remark 9.4) | new derivation, same main term | §9 |
| Prop 8 = [BFM, Thm 4.2] | Lemma 6.1 (primes) | **proof re-verified**: conductor \(W\)-part \(a'\mid aW\) instead of \(a'\mid q_0\) | statement cited; proof modifications listed (steps 1–9) | §6 |
| Prop 11 (BV for almost-primes) | Lemma 6.1 (\(\Lambda_0\)) | **proof re-verified** as above; support hypotheses checked for the switched source | statement cited; proof modifications listed | §6, §9.4 |
| §6 "Lemma 21" (exceptional set, \(1_{(n,P_0(y_1))=1}=\varrho+O(\tau^2\psi)\)) | Lemma 4.1 | written two-sided: \(0\le\rho-1\le\tau^2\psi\) | rederived | §4.1 |
| §6 "Lemma 22" (smooth numbers) | Lemma 4.2 | affine count \(\#\{t:e\mid L_\ell(t)\}\le\#\mathcal T/e+1\); decay \(\exp(-c\delta^2(\log X)^{2/3})\) | rederived; \(\Psi(x,y)\ll xe^{-u/2}\) cited | §4.2 |
| §6 overlap bound \(N\log^{O(1)}/(Wy_1^{1/2})\) | Lemma 4.3 | same exponent \(y^{-1/2}\); affine count via (A1) | rederived | §4.3 |
| §6 generalised Polymath lemma (Euler evaluation) | Lemma 4.4 | pairwise coprimality derived from distinct affine roots (A2); local factors \(1/\phi(q)\) (Lemma 3.6) | lemma cited; the reduction to its hypotheses is new | §4.4 |
| (main) evaluation \((1+o(1))\frac NW B^{-K+1}L_K\) | Lemma 3.5 + 4.4 | slope cancels: \(\pi(I_j)/\phi(a_jW)=(1+o(1))\#\mathcal TB^{-1}\) | new bookkeeping | §3, §4.4 |
| Proposition 12 (\(3.99\)) | Theorem 11.1 (\(c_{\rm cert}+C_{\rm err}\delta\)) | yes (affine source; constant sharpened to \(<3.984\)) | combination kernel-checked (`pairExpect_le_chen`) | §11 |
| numerics \(\Omega_1\le4.19\), \(\Omega_2\ge0.279\), \(\Omega_3\le0.076\) | \(\Omega_1-\Omega_2+\Omega_3\le3.983412536315\) | yes | kernel-checked | §12 |
| \(O(\delta)\) (unspecified) | \(C_1=392/9\), \(C_2=196\log\frac32\), \(C_3=5/2\), \(C_{\rm err}<85\), \(\delta_0=6\cdot10^{-6}\) | yes | arithmetic kernel-checked; identifying the constants is a paper-level obligation | §13 |
| [BFM] Lemma 4.6(iii) (Selberg, constant \(4\)) | `W3_of_selbergPairBound` | no | consistency check | §14 |
