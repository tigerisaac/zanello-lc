from itertools import product
from math import comb
from test_bounds import macaulay_next

def osequences(e,codim=3):
    out=[]
    def rec(a):
        d=len(a)-1
        if len(a)==e+1:out.append(tuple(a));return
        maxn=min(comb(d+3,2),macaulay_next(a[-1],d) if d else codim)
        # allow zero then forced
        for x in range(maxn+1):rec(a+[x])
    # variable h1 too up to 3
    for x in range(codim+1):rec([1,x])
    return out

def si_gors(e):
  # enumerate first half via differentiable sequence delta=(1,g1-1,...)
  m=e//2
  gs=[]
  # directly tuples prefix and check delta O via Macaulay
  def rec(pref):
    i=len(pref)
    if i==m+1:
      g=list(pref)+([pref[-1]] if e%2 else [])+list(pref[-2::-1])
      assert len(g)==e+1
      gs.append(tuple(g));return
    prev=pref[-1]
    # nondecreasing first half, max polynomial ring
    for x in range(prev,comb(i+2,2)+1):
      delta=[pref[0]]+[pref[j]-pref[j-1] for j in range(1,len(pref))]+[x-prev]
      d=i-1
      if i==1 or delta[-1]<=macaulay_next(delta[-2],d): rec(pref+[x])
  rec([1])
  return gs

if __name__=='__main__':
 for e in range(3,10):
  G=si_gors(e);B=osequences(e)
  print('e',e,'G',len(G),'B',len(B))
  for g in G:
    if g[1]!=3: continue
    for b in B:
      q=b[::-1]
      h=tuple(x+y for x,y in zip(g,q))
      if h[0]!=1 or h[1]!=3 or h[-1]!=2:continue
      # h O
      if any(h[i+1]>macaulay_next(h[i],i) for i in range(1,e)):continue
      if any(h[i-1]*h[i+1]>h[i]*h[i] for i in range(1,e)):
        print('FAIL',g,b,q,h);raise SystemExit
 print('all')
