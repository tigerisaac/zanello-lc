from itertools import product
import random

P=1000003

def mons(d):
    return [(a,b,d-a-b) for a in range(d+1) for b in range(d-a+1)]

def rank_mod(A,p=P):
    if not A:return 0
    A=[[(x%p) for x in row] for row in A]
    m,n=len(A),len(A[0]); r=0
    for c in range(n):
        q=next((q for q in range(r,m) if A[q][c]),None)
        if q is None:continue
        A[r],A[q]=A[q],A[r]
        inv=pow(A[r][c],-1,p)
        A[r]=[(x*inv)%p for x in A[r]]
        for q in range(m):
            if q!=r and A[q][c]:
                z=A[q][c]
                A[q]=[(x-z*y)%p for x,y in zip(A[q],A[r])]
        r+=1
        if r==m:return r
    return r

def hvec(F,G,e):
    out=[]
    for i in range(e+1):
        mi,mj=mons(i),mons(e-i)
        A=[]
        for H in (F,G):
            for b in mj:
                A.append([H.get(tuple(a[t]+b[t] for t in range(3)),0) for a in mi])
        out.append(rank_mod(A))
    return out

def good(h):
    return h[0]==1 and h[1]==3 and h[-1]==2

def lc(h):
    return all(h[i-1]*h[i+1]<=h[i]*h[i] for i in range(1,len(h)-1))

if __name__=='__main__':
 for e in range(3,19):
    me=mons(e)
    seen=set()
    for it in range(10000):
        # sparse and structured random supports
        dens=random.choice([2,3,4,5,7,10,15,25,40,60,100])
        ss1=random.sample(me,min(dens,len(me)))
        ss2=random.sample(me,min(dens,len(me)))
        F={a:random.randrange(1,10) for a in ss1}
        G={a:random.randrange(1,10) for a in ss2}
        h=tuple(hvec(F,G,e))
        if good(h):seen.add(h)
        if good(h) and not lc(h):
            print('COUNTER',e,h,F,G);raise SystemExit
    print(e,len(seen),sorted(seen)[:5],sorted(seen)[-5:])
