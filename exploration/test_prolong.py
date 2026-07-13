from itertools import combinations
from math import comb
from search_tensor import mons

def shadow(U):
 return {tuple(a[j]-(j==t) for j in range(3)) for a in U for t in range(3) if a[t]}
def prolong(U,d):
 out=[]
 for a in mons(d+1):
  if all(tuple(a[j]-(j==t) for j in range(3)) in U for t in range(3) if a[t]):out.append(a)
 return set(out)
for d in range(1,9):
 M=mons(d)
 if len(M)<=20:
  its=(set(M[j] for j in range(len(M)) if mask>>j&1) for mask in range(1,1<<len(M)))
 else:
  import random
  its=(set(random.sample(M,random.randrange(1,len(M)))) for _ in range(100000))
 for U in its:
  a=len(shadow(U));b=len(U);p=len(prolong(U,d))
  if a*p>b*b:
   print('FAIL',d,a,b,p,U,prolong(U,d));raise SystemExit
 print('ok',d)
