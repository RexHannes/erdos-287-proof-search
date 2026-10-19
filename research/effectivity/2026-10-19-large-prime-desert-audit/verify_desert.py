#!/usr/bin/env python3
"""Exact audit gates and finite regressions; NOT a proof of AC-287.

Published analytic inputs and the all-real-L monotonicity proof are in REPORT.md.
No third-party packages, floating-point acceptance, or assert-based acceptance.
"""
from __future__ import annotations
import argparse
import hashlib
import gzip
import json
import math
import re
from decimal import Decimal, localcontext
from fractions import Fraction as Q
from functools import lru_cache
from pathlib import Path

U_FIN = int('1956133705397046717778190974736999472616446695532707902585955815875256315446820958180997524905721931203956831124758054158389120631935580334344827242044726613751190094927632285179772676256923758038870182176127819839544692888634913427452526986948998235871926690256287211490977461144466452943660559217761720092761742171483201475616751527475567081983746216048541201421547019571171926632012970828115114657970933447532183687804345317057930357149669764172658105674637478937401076033487787691223801818429356596')
U_SHA = '9528aa36b33895dd9827b831036734d23b4a1a853468ebde6eeb7330ace3c61e'

class Rejected(ValueError):
    pass

def require(test: bool, label: str) -> None:
    if not test:
        raise Rejected(label)

@lru_cache(maxsize=None)
def log_bounds(x: Q, terms: int = 100) -> tuple[Q, Q]:
    x = Q(x)
    require(x > 0 and terms >= 1, 'positive logarithm argument and term count')
    k = x.numerator.bit_length() - x.denominator.bit_length()
    y = x / (Q(2) ** k)
    while y < 1:
        y *= 2; k -= 1
    while y >= 2:
        y /= 2; k += 1
    def series(t: Q) -> tuple[Q, Q]:
        z = (t-1)/(t+1)
        S=1<<200
        a=(z.numerator*S)//z.denominator
        zl=Q(a,S); zu=Q(a+1,S)
        def evaluate(v: Q) -> tuple[Q,Q]:
            v2=v*v; power=v; total=Q(0)
            for j in range(terms):
                total += 2*power/(2*j+1)
                power *= v2
            return total,total+2*power/((2*terms+1)*(1-v2))
        return evaluate(zl)[0],evaluate(zu)[1]
    lo, hi = series(y)
    l2,u2 = series(Q(2))
    lower,upper=(lo+k*l2, hi+k*u2) if k>=0 else (lo+k*u2, hi+k*l2)
    S=1<<160
    a=(lower.numerator*S)//lower.denominator
    b=-((-upper.numerator*S)//upper.denominator)
    return Q(a,S),Q(b,S)

def dec(x: Q, places: int = 18) -> str:
    with localcontext() as c:
        c.prec = places + 12
        return format(Decimal(x.numerator)/Decimal(x.denominator), f'.{places}f')

def interval_record(bounds: tuple[Q,Q]) -> dict:
    return {'lower': str(bounds[0]), 'upper': str(bounds[1]),
            'decimal_lower_display': dec(bounds[0]), 'decimal_upper_display': dec(bounds[1])}

def harmonic(n: int) -> Q:
    return sum((Q(1,j) for j in range(1,n+1)),Q(0))

def primes_upto(n: int) -> list[int]:
    flags=bytearray(b'\x01')*(n+1)
    flags[:2]=b'\x00\x00'
    for p in range(2,math.isqrt(n)+1):
        if flags[p]:
            flags[p*p:n+1:p]=b'\x00'*((n-p*p)//p+1)
    return [p for p in range(2,n+1) if flags[p]]

def lcm_prime_powers(n: int) -> int:
    values=[]
    for p in primes_upto(n):
        v=p
        while v*p<=n: v*=p
        values.append(v)
    return math.prod(values)

def scalar_gates(inject: str | None) -> dict:
    L=1154; alpha=Q(30,47); gamma=Q(47,50)
    require((gamma*L).__floor__()==1084,'numerator height endpoint')
    require(gamma*L<33**2 and gamma*L<11**3,'root upper bounds')
    ll,ul=log_bounds(Q(L)); l2,u2=log_bounds(Q(2))
    require(ll>7 and ul<Q(71,10),'log L enclosure')
    require(log_bounds(Q(81,10))[1]<Q(21,10),'nested logarithm enclosure')
    root=32 if inject=='numerator_root_32' else 33
    require(gamma*L<root*root,'REJECT numerator_root_32')
    gupper=Q(36261,36260)*gamma*L+Q(100007,100000)*root+Q(89,50)*11+Q(71,10)+Q(21,10)
    require(gupper==Q(207873544603,181300000),'original rational numerator envelope')
    require(gupper<L-1,'infinite-range numerator gate')
    require(u2<1 and l2>Q(1,2),'log 2 and derivative gates')
    require(1/Q(1+7)<log_bounds(Q(8))[0],'nested-log quotient decreases')
    x=8_000_000_000
    lx,ux=log_bounds(Q(x)); l3,u3=log_bounds(Q(3))
    require(u3 < Q(x)/(8400*ux),'BMOR q=3 to ordinary theta')
    require(Q(1,420)+Q(1,8400)==Q(1,400),'BMOR reciprocal constants')
    # lambda_0 >= L-log(47L/50); all-real-L monotonicity is proved in report.
    log_gammaL=log_bounds(gamma*L)[1]
    require(log_gammaL<L/100,'input endpoints above 0.99 L')
    require(Q(99,100)*L>ux,'input endpoints above BMOR threshold')
    coeff=Q(17,47)-Q(1,198*L)
    require(coeff>Q(1,3),'first moment all-scale initial gate')
    require((1+alpha)/(400*Q(99,100))<Q(1,198),'first moment error coefficient')
    test_alpha=Q(3,5) if inject=='window_three_fifths' else alpha
    require(test_alpha/Q(3,5)>=Q(50,47),'REJECT window_three_fifths')
    require(1+Q(L,2)+Q(L*L,8)>gamma*L,'large-prime threshold exceeds sqrt M')
    require(alpha*Q(L**3,6)>Q(9,25)*L*L,'top input larger than cofactor squared')
    # domain / endpoint provenance only, NOT finite exclusion verification
    require(hashlib.sha256(str(U_FIN).encode()).hexdigest()==U_SHA,'frozen U bytes')
    require(U_FIN>10**501 and U_FIN>2**1665,'finite bank endpoint size')
    require(1665*l2>L,'post-bank starts inside analytic domain')
    H=harmonic(692)
    density=H/(3*L); capacity=Q(17,94)
    if inject=='first_moment_implies_adjacency':
        require(density>capacity,'REJECT first_moment_implies_adjacency')
    require(density<capacity,'first moment does not exhaust path capacity')
    margin=Q(4,15)*Q(49,100)-Q(1,8)-Q(1,100000)-Q(13,15000)
    require(margin==Q(479,100000),'inherited relaxed contract arithmetic only')
    require(Q(113*L,200)>20*u2 and Q(2,2**20)<margin,'terminal exponent reserve')
    return {'L_min':L,'h_max':1084,'B_at_L_min':346,'g_upper':str(gupper),
            'g_upper_display':dec(gupper),'gap_to_L_minus_one':str(L-1-gupper),
            'H_692':interval_record((H,H)), 'first_moment_support_fraction':dec(density),
            'independent_set_capacity_fraction':str(capacity),'capacity_ratio_display':dec(capacity/density),
            'U_decimal':str(U_FIN),'U_sha256':U_SHA,'U_digits':len(str(U_FIN)),
            'finite_bank_replayed':False,'terminal_reserve':str(margin)}

def exact_numerator_check() -> dict:
    h=1084
    D=lcm_prime_powers(h)
    D2=1
    for i in range(1,h+1): D2=math.lcm(D2,i)
    require(D==D2,'independent LCM constructions')
    T=sum(D//i for i in range(1,h+1))
    require(Q(T,D)==harmonic(h),'harmonic numerator exact identity')
    bounds=log_bounds(Q(h*T))
    u2=log_bounds(Q(2))[1]
    require(bounds[1]<1154-u2,'exact endpoint numerator, independent of psi envelope')
    gap=(1154-log_bounds(Q(2))[1]-bounds[1],1154-log_bounds(Q(2))[0]-bounds[0])
    require(gap[0]>63,'endpoint log reserve')
    return {'h':h,'LCM_decimal':str(D),'T_decimal':str(T),
            'log_hT':interval_record(bounds),'L_minus_log2_minus_log_hT':interval_record(gap)}

def finite_rows(inject: str | None) -> dict:
    count=0; identities=0; candidates=0
    for h in range(1,13):
        D=lcm_prime_powers(h); T=sum(D//j for j in range(1,h+1))
        p=next(p for p in primes_upto(max(100,2*T+20)) if p>T)
        require(p>h,'row LCM a unit')
        for mask in range(1,1<<h):
            js=[j for j in range(1,h+1) if mask>>(j-1)&1]
            N=sum(D//j for j in js)
            require(0<N<=T<p and N%p!=0,'nonempty numerator contradiction')
            residue=sum(pow(j,-1,p) for j in js)%p
            require(N%p==(D%p)*residue%p,'row modular identity')
            count+=1
    # W=pQ integer clearing, all subsets at small M; no search for post-bank counterexamples.
    for M in range(3,16):
        W=math.lcm(*range(1,M+1))
        for p in primes_upto(M):
            if p*p<=M: continue
            Q0=W//p
            require(Q0%p!=0,'p-adic exponent exactly one')
            for mask in range(1<<(M-1)):
                nums=[n for n in range(2,M+1) if mask>>(n-2)&1]
                lhs=sum(W//n for n in nums)%p
                rhs=Q0*sum(pow(n//p,-1,p) for n in nums if n%p==0)%p
                require(lhs==rhs,'full physical denominator clearing')
                identities+=1
                if len(nums)>=2 and sum((Q(1,n) for n in nums),Q())==1:
                    require(min(nums)<=M//2,'minimum denominator bound')
                    candidates+=1
    # why the restrictions cannot simply be deleted
    if inject=='drop_p_squared_guard':
        W=math.lcm(*range(1,5)); p=2
        require((W//p)%p!=0,'REJECT drop_p_squared_guard')
    if inject=='drop_numerator_magnitude_guard':
        require(sum(pow(j,-1,5) for j in (1,4))%5!=0,'REJECT drop_numerator_magnitude_guard')
    if inject=='allow_empty_row_as_contradiction':
        require(0>0,'REJECT allow_empty_row_as_contradiction')
    return {'nonempty_row_subsets':count,'physical_modular_identities':identities,
            'small_reciprocal_solution_checks':candidates}

def lpf_sieve(N: int) -> list[int]:
    f=[0]*(N+1)
    for p in range(2,N+1):
        if f[p]==0:
            for n in range(p,N+1,p): f[n]=p
    return f

def source_checks(inject: str | None) -> dict:
    records=0; adjacent=0; split_checks=0; endpoint_hits=[]
    for M in (470,1000,4700,10000,100000):
        loL,hiL=log_bounds(Q(M))
        B=(Q(3,10)*loL).__floor__()
        require(B==(Q(3,10)*hiL).__floor__(),'exact logarithmic cofactor floor')
        C=2*B; N=(30*M+46)//47
        require(N>C*C,'test instance satisfies uniqueness geometry')
        factors=lpf_sieve(M)
        support={}
        for n in range(N,M+1):
            rs=[(c,n//c) for c in range(1,C+1) if n%c==0 and factors[n//c]==n//c]
            require(len(rs)<=1,'same output unique prime representation')
            require(bool(rs)==(n//factors[n]<=C),'largest factor/cofactor equivalence')
            if rs:
                support[n]=rs[0]; records+=1
        for c in range(1,C+1):
            lo=(30*M)//(47*c); hi=M//c
            closed={p for p in primes_upto(hi) if N<=c*p<=M}
            strict={p for p in primes_upto(hi) if 30*M<47*c*p<=47*M}
            correction=closed-strict
            require(strict<=closed,'open lower endpoint gives lower bound')
            require(len(correction)<=1 and all(47*c*p==30*M for p in correction),'exact ceiling correction')
            split_checks+=1
        for n in range(N,M):
            if n in support and n+1 in support:
                a,p=support[n]; b,q=support[n+1]
                require(b*q-a*p==1 and math.gcd(a,b)==1 and (a-b)%2!=0,'adjacent determinant arithmetic')
                require(p!=q,'distinct adjacent large primes')
                adjacent+=1
        if 47*N==30*M: endpoint_hits.append(M)
    for M,B,n in ((1000,2,668),(100000,3,66685)):
        fs=lpf_sieve(n+1)
        a=n//fs[n]; b=(n+1)//fs[n+1]
        require(a>1 and b>1 and a<=2*B and b<=2*B,'both-composite original fixtures')
        require(n*47>=30*M and n+1<=M,'fixture exact physical interval')
    if inject=='reverse_determinant':
        require(3*223-4*167==-1,'REJECT reverse_determinant')
    if inject=='omit_upper_endpoint':
        M=19; C=2; N=(30*M+46)//47
        require(not(N<=19<=M and 19//19<=C),'REJECT omit_upper_endpoint')
    # Reusable deterministic AC verifier, exact prime tuples only; not universal existence.
    require(3*223-4*167==1,'fixture determinant')
    return {'unique_support_records':records,'adjacent_determinant_records':adjacent,
            'exact_first_moment_endpoint_checks':split_checks,'integer_alpha_endpoint_samples':endpoint_hits}

def source_integrity(extract_to: str | None = None) -> dict:
    path=Path(__file__).with_name('SOURCE_RECORD.md')
    raw=path.read_bytes() if path.exists() else gzip.decompress(path.with_suffix('.md.gz').read_bytes())
    pattern=rb'<!-- SOURCE name="([^"]+)" bytes=([0-9]+) sha256=([0-9a-f]{64}) -->\n````text\n'
    records=[]
    for match in re.finditer(pattern,raw):
        name=match.group(1).decode(); size=int(match.group(2)); digest=match.group(3).decode()
        body=raw[match.end():match.end()+size]
        require(hashlib.sha256(body).hexdigest()==digest,'source hash '+name)
        require(raw[match.end()+size:].startswith(b'\n````\n<!-- END SOURCE -->'),'source boundary '+name)
        rel=Path(name)
        require(not rel.is_absolute() and '..' not in rel.parts,'safe source name')
        if extract_to:
            dst=Path(extract_to)/rel;dst.parent.mkdir(parents=True,exist_ok=True);dst.write_bytes(body)
        records.append({'name':name,'bytes':size,'sha256':digest})
    require(len(records)==7 and len({r['name'] for r in records})==7,'seven unique source originals')
    return {'embedded_files':records,'source_record_sha256':hashlib.sha256(raw).hexdigest()}

def main() -> int:
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output',default='CERTIFICATE.json')
    ap.add_argument('--extract-sources',metavar='DIRECTORY')
    ap.add_argument('--inject',choices=['numerator_root_32','window_three_fifths',
        'first_moment_implies_adjacency','drop_p_squared_guard','drop_numerator_magnitude_guard',
        'allow_empty_row_as_contradiction','reverse_determinant','omit_upper_endpoint'])
    a=ap.parse_args()
    try:
        result={'scope':'Exact new scalar gates and finite regressions; no AC-287, no finite-bank replay, no Lean proof.',
                'scalar_gates':scalar_gates(a.inject),'exact_endpoint':exact_numerator_check(),
                'row_checks':finite_rows(a.inject),'source_checks':source_checks(a.inject),
                'source_integrity':source_integrity(a.extract_sources)}
    except Rejected as err:
        print(f'REJECTED: {err}')
        return 2
    raw=json.dumps(result,indent=2,sort_keys=True).encode()+b'\n'
    Path(a.output).write_bytes(raw)
    print(hashlib.sha256(raw).hexdigest())
    return 0

if __name__=='__main__':
    raise SystemExit(main())
