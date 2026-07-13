from fractions import Fraction as Q
from math import comb
import random

def pure(s,a,b):
 b1=Q(b*s,(b-a)*(s-a));b2=Q(a*s,(b-a)*(s-b));b3=Q(a*b,(s-a)*(s-b))
 H=[]
 for n in range(s-2): # e=s-3 => 0..s-3
  z=Q(comb(n+2,2))
  if n>=a:z-=b1*comb(n-a+2,2)
  if n>=b:z+=b2*comb(n-b+2,2)
  H.append(z)
 return b3,H

for s in range(6,35):
 P=[(a,b,*pure(s,a,b)) for a in range(2,s) for b in range(a+1,s)]
 # individual exact type2
 for a,b,r,h in P:
  if r==2 and any(h[i]*h[i]<h[i-1]*h[i+1] for i in range(1,len(h)-1)):
   print('pure fail',s,a,b,r,h);raise SystemExit
 # all 2-mixtures bracketing avg2
 for ix,x in enumerate(P):
  for y in P[ix:]:
   r1,h1=x[2],x[3];r2,h2=y[2],y[3]
   if not (min(r1,r2)<=2<=max(r1,r2)) or r1==r2:continue
   if r1==r2:
    if r1!=2:continue
    w=Q(1,2)
   else:w=(Q(2)-r2)/(r1-r2)
   h=[w*u+(1-w)*v for u,v in zip(h1,h2)]
   if all(z.denominator==1 for z in h) and any(h[i]*h[i]<h[i-1]*h[i+1] for i in range(1,len(h)-1)):
    print('integral mix fail',s,x[:3],y[:3],'w',w,'h',h);raise SystemExit
 print('ok',s)
