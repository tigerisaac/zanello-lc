from search_tensor import mons
import random
def sh(U): return {tuple(a[j]-(j==t) for j in range(3)) for a in U for t in range(3) if a[t]}
for d in range(1,15):
 M=mons(d+1)
 if len(M)<=22: its=(set(M[j] for j in range(len(M)) if mask>>j&1) for mask in range(1,1<<len(M)))
 else: its=(set(random.sample(M,random.randrange(1,len(M)+1))) for _ in range(1000000))
 for P in its:
  U=sh(P);A=sh(U)
  if len(A)*len(P)>len(U)**2:
   print('FAIL',d,len(A),len(U),len(P),P);raise SystemExit
 print('ok',d)
