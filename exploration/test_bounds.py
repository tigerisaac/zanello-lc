from math import comb

def macaulay_next(a,d):
    # d>=1, unique d-binomial expansion
    if a==0:return 0
    rem=a; top=10**9; s=0
    terms=[]
    for j in range(d,0,-1):
        n=j-1
        # largest n<top with C(n,j)<=rem
        lo,hi=j-1,top-1
        if top>10**8:
            hi=j
            while comb(hi,j)<=rem: hi*=2
        while lo<hi:
            mid=(lo+hi+1)//2
            if comb(mid,j)<=rem and mid<top:lo=mid
            else:hi=mid-1
        n=lo
        if n>=j:
            rem-=comb(n,j); terms.append((n,j));top=n
        else: top=n
    assert rem==0,(a,d,rem,terms)
    return sum(comb(n+1,j+1) for n,j in terms)

def mod_next(a,d):
    N=comb(d+2,2)
    q,r=divmod(a,N)
    assert q<=2
    if q==2:return 2*comb(d+3,2)
    return q*comb(d+3,2)+(macaulay_next(r,d) if d else (comb(r+1,1) if False else None))

if __name__=='__main__':
 for e in range(4,101):
  for i in range(1,e):
   if i in (1,e-1): continue
   d=e-i
   if d==0:continue
   for b in range(1,min(comb(i+2,2),2*comb(d+2,2))+1):
    if i==1 and b!=3: continue
    c=macaulay_next(b,i)
    a=mod_next(b,d)
    if a*c>b*b:
     print('FAIL',e,i,d,a,b,c,a*c-b*b);raise SystemExit
 print('all')
