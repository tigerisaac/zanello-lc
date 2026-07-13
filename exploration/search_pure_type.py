from search_tensor import mons
from itertools import combinations
import random
def sh(U): return {tuple(a[j]-(j==q) for j in range(3)) for a in U for q in range(3) if a[q]}
for typ in range(2,7):
 for e in range(2,20):
  M=mons(e)
  C=combos=combinations(M,typ) if len(M)<30 else (random.sample(M,typ) for _ in range(200000))
  for W in C:
   U=set(W); g=[len(U)]
   for j in range(e):U=sh(U);g.append(len(U))
   h=g[::-1]
   if h[1]==3 and any(h[i-1]*h[i+1]>h[i]**2 for i in range(1,e)):
    print('FAIL type/e',typ,e,W,h);raise SystemExit
 print('type ok',typ)
