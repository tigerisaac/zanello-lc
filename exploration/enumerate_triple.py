from enumerate_decomp import osequences,si_gors
from test_bounds import macaulay_next
def isO(x):
 if x[0]!=1:return False
 return all(x[i+1]<=macaulay_next(x[i],i) for i in range(1,len(x)-1))
for e in range(3,10):
 G=si_gors(e);B=osequences(e)
 print('e',e,len(G),len(B))
 fails=[]
 for g in G:
  if g[1]!=3: continue
  for b in B:
   q=b[::-1]
   h=tuple(x+y for x,y in zip(g,q))
   d=tuple(x-y for x,y in zip(g,q))
   if min(d)<0 or h[0]!=1 or h[1]!=3 or h[-1]!=2:continue
   if not isO(h) or not isO(d):continue
   if any(h[i-1]*h[i+1]>h[i]*h[i] for i in range(1,e)):
    fails.append((g,b,q,d,h))
    if len(fails)>=20:break
  if len(fails)>=20:break
 print('fails',len(fails))
 for z in fails[:5]:print('FAIL',z)
 if e>=7:break
print('all')
