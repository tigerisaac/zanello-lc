from test_bounds import macaulay_next
from lex_betti import lex_betti

def gen(e):
 out=[]
 def rec(a):
  i=len(a)-1
  if i==e:
   if a[-1]==2:out.append(tuple(a))
   return
  hi=macaulay_next(a[-1],i)
  # positive until terminal
  for z in range(1,hi+1):rec(a+[z])
 rec([1,3])
 return out
for e in range(3,9):
 H=gen(e);print('e',e,'n',len(H))
 for h in H:
  nonlc=any(h[i-1]*h[i+1]>h[i]*h[i] for i in range(1,e))
  _,b=lex_betti(h)
  obstruction=any(b[3].get(j,0)>b[2].get(j,0) for j in b[3] if j<e+3)
  if nonlc and not obstruction:
   print('MISS',h,b);raise SystemExit
print('all')
