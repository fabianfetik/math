"""Independent exact verifier; standard library only.
Does not import search, capacity optimization, domain tightening or NumPy.
The tree is traversed from the original domain. Stored discovery states are absent.
"""
from fractions import Fraction as F
from itertools import product
from functools import lru_cache
from pathlib import Path
import json,gzip,time,sys,argparse
if not __debug__:
 raise RuntimeError("Run without -O: this certificate verifier uses assertions.")
D=F(5,6)

@lru_cache(None)
def parts(n,lo=1):
 if n==0:return ((),)
 return tuple((a,)+b for a in range(lo,n+1) for b in parts(n-a,a))
@lru_cache(None)
def weights(n):
 if n==1:return ((1,),)
 out=set()
 for q in parts(n):
  if len(q)>1:
   for child in product(*(weights(k) for k in q)):
    out.add(tuple(sorted(len(q)*w for v in child for w in v)))
 return tuple(sorted(out))
FORESTS=[]
for k in range(1,8):
 for a in weights(k):
  for b in weights(8-k):FORESTS.append((tuple(enumerate(a)),tuple((i+k,w) for i,w in enumerate(b))))

def normalize(l,u,ls=0,us=0):
 l=list(l);u=list(u)
 for i in range(5,-1,-1):
  if l[i+1]>l[i]:l[i]=l[i+1];ls=(ls&~(1<<i))|(((ls>>(i+1))&1)<<i)
  elif l[i+1]==l[i] and (ls>>(i+1))&1:ls|=1<<i
 for i in range(1,7):
  if u[i-1]<u[i]:u[i]=u[i-1];us=(us&~(1<<i))|(((us>>(i-1))&1)<<i)
  elif u[i-1]==u[i] and (us>>(i-1))&1:us|=1<<i
 if any(a>b or (a==b and ((ls|us)>>i)&1) for i,(a,b) in enumerate(zip(l,u))):return None
 low=sum(l);high=sum(u)
 if low>D or high<D or (low==D and ls) or (high==D and us):return None
 return tuple(l),tuple(u),ls,us

def extrema(S):
 # Proven coordinate lower/upper bounds for the closed ordered-box slice.
 l,u,_,_=S
 low=[];high=[]
 for i in range(7):
  low.append(max([l[i]]+[(D-sum(u[:i])-sum(u[j+1:]))/F(j-i+1) for j in range(i,7)]))
  high.append(min([u[i]]+[(D-sum(l[:j])-sum(l[i+1:]))/F(i-j+1) for j in range(i+1)]))
 return low,high

def complement(S,c):
 l,u,ls,us=S;l=list(l);u=list(u);out=[]
 for i in range(7):
  # Keep these intervals untightened: feasibility uses only order and sum.
  if u[i]>c[i]:
   ll=l[:];lm=ls
   if ll[i]<=c[i]:ll[i]=c[i];lm|=1<<i
   x=normalize(ll,u,lm,us)
   if x is not None:out.append(x)
   u[i]=c[i];us&=~(1<<i)
   if l[i]>u[i] or (l[i]==u[i] and ((ls|us)>>i)&1):break
 return out

def bound(low,high,co):
 val=sum(a*b for a,b in zip(low,co));rem=D-sum(low)
 for i in sorted(range(7),key=lambda i:co[i],reverse=True):
  t=min(rem,high[i]-low[i]);val+=co[i]*t;rem-=t
 return val

def check_word(word,cap):
 P=len(word);assert P and all(isinstance(x,int) and 0<=x<8 for x in word)
 rr=cap[:6]+[cap[6],cap[6]];comparisons=0
 for i,r in enumerate(rr):
  pp=[j for j,a in enumerate(word) if a==i];c=len(pp);assert c and r>0
  assert r.numerator*P<=r.denominator*c
  doubled=pp+[j+P for j in pp]
  for k in range(1,c+1):
   span=max(doubled[j+k]-doubled[j] for j in range(c))
   assert r.numerator*(span-1)<=r.denominator*k,(i,r,k,span)
   comparisons+=c
 return comparisons

def verify(path,allow_partial=True):
 start=time.time();data=json.loads(gzip.decompress(Path(path).read_bytes()));sources=data['sources'];caps=[];cmp=0
 assert data['format']=='R420-cover-v1'
 assert data['domain']=={'density':'5/6','delta_lo':'1/21','delta_hi':'1/11'}
 for k,o in enumerate(sources):
  c=list(map(F,o['caps']));assert len(c)==7 and all(c[i]>=c[i+1] for i in range(6));caps.append(c)
  cmp+=check_word(o['word'],c)
 print('verified words',len(sources),'occurrence comparisons',cmp,'seconds',round(time.time()-start,3),flush=True)
 nodes=data['nodes']
 for rec in nodes:
  assert set(rec).issubset({'split','leaf'}) and not ('split' in rec and 'leaf' in rec)
  if 'split' in rec:
   k,ids=rec['split'];assert isinstance(k,int) and 0<=k<len(sources)
   assert all(isinstance(v,int) and 0<=v<len(nodes) for v in ids)
  if 'leaf' in rec:
   kind,k=rec['leaf'];assert isinstance(k,int)
   assert (kind=='word' and 0<=k<len(sources)) or (kind=='flat' and 0<=k<=6) or (kind=='forest' and 0<=k<len(FORESTS))
 assert len(data['frontier'])==len(set(data['frontier']))
 assert all(isinstance(v,int) and 0<=v<len(nodes) for v in data['frontier'])
 todo=[(0,normalize([F(1,21)]*7,[D]*6+[F(1,11)]))];seen=set();leaves={};front=[]
 while todo:
  nd,S=todo.pop();assert S is not None and nd not in seen;seen.add(nd);rec=nodes[nd]
  if 'split' in rec:
   k,ids=rec['split'];cc=complement(S,caps[k]);assert len(ids)==len(cc),('branch count',nd,len(ids),len(cc))
   todo.extend(zip(ids,cc))
  elif 'leaf' in rec:
   kind,k=rec['leaf'];low,high=extrema(S)
   if kind=='word':assert all(x<=y for x,y in zip(high,caps[k])),('word leaf',nd,k,high,caps[k])
   elif kind=='flat':
    co=[0]*7
    if k==0:co[0]=8
    else:co[0]=k;co[k]=8-k
    assert bound(low,high,co)<=1,('flat leaf',nd,k)
   elif kind=='forest':
    a,b=FORESTS[k]
    for i,w in a:
     for j,v in b:
      co=[0]*7;co[min(i,6)]+=w;co[min(j,6)]+=v
      assert bound(low,high,co)<=1,('forest leaf',nd,k,co)
   else:raise AssertionError(kind)
   leaves[kind]=leaves.get(kind,0)+1
  else:front.append(nd)
 assert len(seen)==len(nodes),('unreachable nodes',len(seen),len(nodes))
 assert set(front)==set(data['frontier']),('frontier mismatch',front,data['frontier'])
 if not allow_partial:assert not front,'Unresolved frontier: not a complete certificate'
 result={'sources':len(sources),'nodes':len(nodes),'frontier':len(front),'leaves':leaves,'rank_comparisons':cmp,'complete':not front}
 print(json.dumps(result,sort_keys=True),'seconds',round(time.time()-start,3),flush=True)
 return result
if __name__=='__main__':
 parser=argparse.ArgumentParser(description=__doc__)
 parser.add_argument('certificate',nargs='?',type=Path,default=Path(__file__).with_name('cover.json.gz'))
 parser.add_argument('--require-complete',action='store_true',help='reject any unresolved frontier')
 parser.add_argument('--output',type=Path,default=Path(__file__).with_name('verification.json'))
 args=parser.parse_args()
 result=verify(args.certificate,allow_partial=not args.require_complete)
 args.output.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
