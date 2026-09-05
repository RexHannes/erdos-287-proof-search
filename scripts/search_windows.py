import random, sys, json
from math import gcd

def is_prime(n):
    if n < 2: return False
    for p in [2,3,5,7,11,13,17,19,23,29,31,37]:
        if n % p == 0: return n == p
    d = n-1; s = 0
    while d % 2 == 0: d//=2; s+=1
    for a in [2,3,5,7,11,13,17,19,23,29,31,37]:
        x = pow(a,d,n)
        if x == 1 or x == n-1: continue
        for _ in range(s-1):
            x = x*x % n
            if x == n-1: break
        else:
            return False
    return True

def pollard(n):
    if n % 2 == 0: return 2
    while True:
        x = random.randrange(2,n); y = x; c = random.randrange(1,n); d = 1
        while d == 1:
            x = (x*x+c) % n
            y = (y*y+c) % n; y = (y*y+c) % n
            d = gcd(abs(x-y), n)
        if d != n: return d

def factor(n, res=None):
    if res is None: res = {}
    if n == 1: return res
    if is_prime(n):
        res[n] = res.get(n,0)+1
        return res
    p = 2
    while p < 100000 and p*p <= n:
        if n % p == 0:
            while n % p == 0:
                n//=p; res[p]=res.get(p,0)+1
            return factor(n,res)
        p += 1
    d = pollard(n)
    factor(d,res); factor(n//d,res)
    return res

CVAL = {0:1,1:1,2:3,3:11,4:25,5:137,6:137,7:1019,8:2143,9:7129}

def cval(j):
    return CVAL.get(j, 0) if j <= 9 else 0

def candidate(x, U):
    for a in [1,2,3,4]:
        if x % a: continue
        p = x//a
        if p < 1000: continue
        w = U//p
        if w > 9 or cval(w) >= p: continue
        if not is_prime(p): continue
        for b in [1,2,3,4,5]:
            if (x+1) % b: continue
            q = (x+1)//b
            if q < 1000: continue
            w2 = U//q
            if w2 > 9 or cval(w2) >= q: continue
            if not is_prime(q): continue
            return (a,p,b,q)
    return None

TARGET = 67108856338751594

def main():
    U = 4000000000
    windows = []
    while U < TARGET:
        found = None
        x = U
        while x > U - 2000000:
            Unew = min(2*x, TARGET)
            c = candidate(x, Unew)
            if c:
                found = (x, Unew, c)
                break
            x -= 1
        if not found:
            print("FAILED at U=", U); return
        x, Unew, (a,p,b,q) = found
        windows.append((x,Unew,a,p,b,q))
        print(f"win {len(windows)}: x={x} U={Unew} a={a} p={p} b={b} q={q} gap={U-x}")
        sys.stdout.flush()
        U = Unew
    print("total windows", len(windows), "final", U)
    json.dump(windows, open('/workspace/request-project/scripts/windows.json','w'))

if __name__ == '__main__':
    main()
