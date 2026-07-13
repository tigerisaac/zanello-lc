from math import comb
from search_tensor import mons

def lex_order(d):
 return sorted(mons(d), reverse=True) # tuples lex x>y>z
def lex_betti(h):
 e=len(h)-1
 I=[]; Isets=[]
 for d in range(e+2):
  hd=h[d] if d<=e else 0
  Id=set(lex_order(d)[:len(mons(d))-hd]);Isets.append(Id)
  for a in Id:
   if d==0: I.append(a);continue
   if all(tuple(a[j]-(j==q) for j in range(3)) not in Isets[d-1] for q in range(3) if a[q]):
    I.append(a)
  # actually minimal iff NO divisor lies in ideal
 bet={1:{},2:{},3:{}}
 for a in I:
  d=sum(a);mx=max(q+1 for q,z in enumerate(a) if z)
  for q in range(1,4):
   v=comb(mx-1,q-1) if mx-1>=q-1 else 0
   if v:bet[q][d+q-1]=bet[q].get(d+q-1,0)+v
 return I,bet

if __name__=='__main__':
 for h in [(1,3,3,4,2),(1,3,4,5,2),(1,3,6,10,7,10,6,3,1)]:
  I,b=lex_betti(h);print(h,'gens',I,'bet',b)
