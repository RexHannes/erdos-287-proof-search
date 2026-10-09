#!/usr/bin/env python3
"""Finite regression for the written source-fit parity lemma and V103 integer ledger.
This is not a Lean proof or a substitute for quantified mathematics.
"""
from math import lcm


def plus(xs, D):
    xs = sorted(xs, reverse=True)
    return all((__import__('math').prod(xs[:k])*xs[k]**3 <= D) for k in range(0,len(xs),2))

def minus(xs, D):
    xs = sorted(xs, reverse=True)
    return (len(xs)==0 or xs[0]**2<=D) and all(
       (__import__('math').prod(xs[:k])*xs[k]**3 <= D) for k in range(1,len(xs),2))

def test_parity():
    # Different sizes, including J odd/even and a repeated high-box illustration.
    fixtures=[([5],[3,2],125,24),([13,11],[7,5,3],2197,945),
              ([],[11,7,5],1,9625),([29,23,19],[13,11],29**3*23*19**3,13*11**3),
              ([17,13,11,7],[5,3,2],17**3*13*11**3*7,5**3*3*2**3)]
    for high,low,Dhi,Dlo in fixtures:
        assert plus(high,Dhi)
        assert (plus(low,Dlo) if len(high)%2==0 else minus(low,Dlo))
        assert plus(high+low,Dhi*Dlo)
    return len(fixtures)

def lcm_ledger():
    L=1; B=0; checks=0; computed={}
    for h in range(1,1250):
        prev=L
        L=lcm(L,h)
        B=(L//prev)*B + L//h
        assert L<=4**(h-1), h   # finite regression only
        checks+=1
        for exp in (12,100,501):
            if h*B<10**exp:
                computed[exp]=(h,(h-1)//2)
    assert computed[12]==(24,11), computed[12]
    assert computed[100]==(228,113), computed[100]
    assert computed[501]==(1150,574), computed[501]
    assert 10*7381 < (8/3)**12  # e > 8/3, so exp(12) > (8/3)^12
    return checks,computed

if __name__=='__main__':
    print('parity fixtures:',test_parity())
    print('LCM ledger:',lcm_ledger())
