import os,json,urllib.request,random
S=[21+r*10+f for r in range(8) for f in range(8)]
D=(9,11,-9,-11,1,-1,10,-10)
N=(8,12,19,21,-8,-12,-19,-21)
V=(0,100,325,340,510,970,20000)
PH=(0,0,1,1,2,4,0)
rng=random.Random(76123).getrandbits
Z=[[rng(64) for s in range(120)] for p in range(13)]
R=[rng(64) for i in range(137)]
KEEP=[15]*120
for s,v in ((21,13),(28,14),(25,12),(91,7),(98,11),(95,3)):KEEP[s]=v
MG=[[0]*120 for _ in range(13)];EG=[[0]*120 for _ in range(13)]
for p in range(-6,7):
 if not p:continue
 c=1 if p>0 else -1;t=abs(p)
 for s in S:
  r=(s//10-2) if c==1 else (9-s//10);f=s%10-1
  x=min(f,7-f);z=x+min(r,7-r)
  m=(0,100+7*r+5*x*r/3,325+13*z-46,340+7*z-18+2*r,510+2*x+18*(r==6),970+3*z-12,18*(r==0)+22*(f in (1,6) and r<2)-22*r-8*x)[t]
  e=(0,120+11*r+3*r*r,305+9*z-32,335+7*z-18,525+4*r,945+4*z,13*z-45)[t]
  MG[p+6][s]=int(c*m);EG[p+6][s]=int(c*e)
def square(t):return 21+ord(t[0])-97+10*(int(t[1])-1)
def uci(m):
 a=m&127;b=m>>7&127;p=m>>14
 return ''.join(chr(96+s%10)+str(s//10-1) for s in (a,b))+(' pnbrqk'[p] if p else '')
def move(t):return square(t[:2])|(square(t[2:4])<<7)|((' pnbrqk'.index(t[4])<<14) if len(t)>4 else 0)
class Position:
 def __init__(self,fen):
  b=self.b=[7]*120;self.k={};self.mg=self.eg=self.phase=self.key=0
  for s in S:b[s]=0
  rows,side,rights,ep,clock,_=fen.split()
  for r,row in enumerate(rows.split('/')):
   f=0
   for ch in row:
    if ch.isdigit():f+=int(ch);continue
    p=' pnbrqk'.index(ch.lower())*(1 if ch.isupper() else -1);s=91-r*10+f;f+=1;b[s]=p
    self.mg+=MG[p+6][s];self.eg+=EG[p+6][s];self.phase+=PH[abs(p)];self.key^=Z[p+6][s]
    if abs(p)==6:self.k[1 if p>0 else -1]=s
  self.s=1 if side=='w' else -1;self.c=sum(1<<i for i,ch in enumerate('KQkq') if ch in rights);self.e=square(ep) if ep!='-' else 0;self.h=int(clock)
  self.e=self.ep();self.check=self.attack(self.k[self.s],-self.s)
  self.key^=R[self.c]^R[16+self.e]^(R[136] if self.s<0 else 0);self.hist=[self.key]
 def ep(self):
  ep=self.e;b=self.b;c=self.s
  if ep:
   z=ep-10*c
   for f in (ep-9*c,ep-11*c):
    if b[f]==c:
     b[f]=b[z]=0;b[ep]=c;ok=not self.attack(self.k[c],-c);b[f]=c;b[z]=-c;b[ep]=0
     if ok:return ep
  return 0
 def attack(self,s,c):
  b=self.b
  if b[s-9*c]==c or b[s-11*c]==c:return True
  for d in N:
   q=s+d
   if b[q]==2*c:return True
  for i,d in enumerate(D):
   q=s+d;p=b[q]
   if p==6*c:return True
   while not p:q+=d;p=b[q]
   if p==5*c or p==(3 if i<4 else 4)*c:return True
  return False
 def moves(self,caps=False):
  b=self.b;c=self.s;ep=self.e
  for a in S:
   p=b[a]*c
   if not 0<p<7:continue
   if p==1:
    z=a+10*c
    targets=[]
    if not b[z]:
     if not caps or z//10 in (2,9):targets.append(z)
     if not caps and a//10==(3 if c==1 else 8) and not b[z+10*c]:targets.append(z+10*c)
    for z in (a+9*c,a+11*c):
     if -6<=b[z]*c<0 or z==ep:targets.append(z)
    for z in targets:
     for v in ((5,4,3,2) if z//10 in (2,9) else (0,)):yield a|(z<<7)|(v<<14)
   else:
    for d in N if p==2 else D[:4] if p==3 else D[4:] if p==4 else D:
     z=a+d
     while True:
      t=b[z]
      if t==7 or t*c>0:break
      if not caps or t:yield a|(z<<7)
      if t or p in (2,6):break
      z+=d
    if p==6 and not caps and self.c and not self.attack(a,-c):
     for bit,delta,rook in ((1 if c==1 else 4,2,a+3),(2 if c==1 else 8,-2,a-4)):
      step=1 if delta>0 else -1
      if self.c&bit and b[rook]==4*c and all(not b[a+j*step] for j in range(1,3 if step>0 else 4)) and not self.attack(a+step,-c) and not self.attack(a+delta,-c):yield a|((a+delta)<<7)
 def hasmove(self):
  for m in self.moves():
   u=self.make(m)
   if u:self.unmake(u);return 1
  return 0
 def make(self,m):
  a=m&127;z=m>>7&127;promo=m>>14;b=self.b;p=b[a];c=self.s
  cap=z-10*c if abs(p)==1 and z==self.e else z;t=b[cap]
  u=(m,p,t,cap,self.c,self.e,self.h,self.key,self.mg,self.eg,self.phase,self.check)
  b[a]=0;b[cap]=0;q=promo*c if promo else p;b[z]=q
  self.mg+=MG[q+6][z]-MG[p+6][a]-MG[t+6][cap];self.eg+=EG[q+6][z]-EG[p+6][a]-EG[t+6][cap];self.phase+=PH[abs(q)]-PH[abs(p)]-PH[abs(t)]
  self.key^=Z[p+6][a]^Z[q+6][z]^(Z[t+6][cap] if t else 0)^R[self.c]^R[16+self.e]^R[136]
  if abs(p)==6:
   self.k[c]=z
   if abs(z-a)==2:
    rf=a+3 if z>a else a-4;rt=(a+z)//2;b[rf]=0;b[rt]=4*c
    self.mg+=MG[4*c+6][rt]-MG[4*c+6][rf];self.eg+=EG[4*c+6][rt]-EG[4*c+6][rf];self.key^=Z[4*c+6][rf]^Z[4*c+6][rt]
  self.c&=KEEP[a]&KEEP[z];self.e=0
  if abs(p)==1 and abs(z-a)==20 and (b[z-1]==-c or b[z+1]==-c):self.e=(a+z)//2
  self.h=0 if t or abs(p)==1 else self.h+1;self.s=-c;self.key^=R[self.c]^R[16+self.e];self.hist.append(self.key)
  k=self.k[c]
  if self.attack(k,-c):self.unmake(u);return None
  self.check=self.attack(self.k[-c],c)
  ep=self.e;self.e=self.ep();self.key^=R[16+ep]^R[16+self.e];self.hist[-1]=self.key
  return u
 def unmake(self,u):
  m,p,t,cap,self.c,self.e,self.h,self.key,self.mg,self.eg,self.phase,self.check=u
  a=m&127;z=m>>7&127;b=self.b;self.s=-self.s;c=self.s;b[z]=0;b[a]=p;b[cap]=t;self.hist.pop()
  if abs(p)==6:
   self.k[c]=a
   if abs(z-a)==2:b[a+3 if z>a else a-4]=4*c;b[(a+z)//2]=0
 def evaluate(self):
  ph=min(24,self.phase);b=self.b;bonus=0;pawns={1:[],-1:[]};bish={1:0,-1:0}
  for s in S:
   p=b[s];t=abs(p);c=1 if p>0 else -1
   if t==1:pawns[c].append(s)
   if t==3:bish[c]+=1
   if 1<t<6:
    mob=0
    for d in N if t==2 else D[:4] if t==3 else D[4:] if t==4 else D:
     z=s+d
     while b[z]!=7 and b[z]*c<=0:
      if b[z+9*c]!=-c and b[z+11*c]!=-c:mob+=1
      if b[z] or t==2:break
      z+=d
    bonus+=c*mob*(4 if t<4 else 2 if t==4 else 1)
  key=(*pawns[1],0,*pawns[-1],ph);pawn=PC.get(key)
  if pawn is None:
   pawn=0
   for c in (1,-1):
    files=[s%10 for s in pawns[c]]
    for s in pawns[c]:
     f=s%10;r=(s//10-2) if c>0 else 9-s//10
     v=-13*(files.count(f)-1)-14*(f-1 not in files and f+1 not in files)
     for t in pawns[-c]:
      if abs(t%10-f)<=1 and (t-s)*c>0:break
     else:v+=(0,0,5,12,25,48,90,0)[r]*(32-ph)//16
     pawn+=c*v
   PC[key]=pawn
  for c in (1,-1):
   k=self.k[c]
   bonus+=c*28*(bish[c]>=2)+c*sum(b[k+d*c]==c for d in (9,10,11))*12*ph//24
  return self.s*((self.mg*ph+self.eg*(24-ph))//24+bonus+pawn)+12
TT={};EC={};PC={}
class Search:
 def __init__(self,p,limit=90000):
  for table in (TT,EC,PC):
   if len(table)>120000:table.clear()
  self.p=p;self.limit=limit;self.nodes=0;self.tt=TT;self.evals=EC;self.killers=[0]*81;self.history={};self.best=0;self.depth=0;self.score=0
 def run(self,d,a,b,ply=0,null=True):
  self.nodes+=1
  if self.nodes>self.limit:raise InterruptedError
  p=self.p;check=p.check
  if ply>=80:return p.evaluate()
  draw=p.h>=100 or p.hist.count(p.key)>=3
  if draw:
   if check:
    for m in p.moves():
     u=p.make(m)
     if u:p.unmake(u);return 0
    return -30000+ply
   return 0
  entry=self.tt.get(p.key);tm=entry[3] if entry else 0;old=a
  ev=self.evals.get(p.key)
  if ev is None:ev=p.evaluate();self.evals[p.key]=ev
  q=d<=0
  if d>0 and ply and not check and b-a==1 and d<=3 and abs(b)<28000 and ev-100*d>=b:
   if not p.hasmove():return 0
   return ev
  if q and not check:
   if ev>=b:return ev if p.hasmove() else 0
   a=max(a,ev)
  if d>=3 and null and not check and b-a==1 and ev>=b and p.phase>2 and p.hasmove():
   ep=p.e;k=p.key;hist=p.hist;p.hist=[];p.s=-p.s;p.e=0;p.key^=R[136]^R[16+ep]^R[16]
   try:v=-self.run(d-3,-b,1-b,ply+1,False)
   finally:p.hist=hist;p.key=k;p.e=ep;p.s=-p.s
   if v>=b and abs(v)<29000:return v
  moves=list(p.moves(q and not check))
  def order(m):
   a=m&127;z=m>>7&127;t=abs(p.b[z]);pr=m>>14
   return 10000000 if m==tm else 100000+16*V[t]-V[abs(p.b[a])]+pr*10000 if t or pr or abs(p.b[a])==1 and z==p.e else 90000 if m==self.killers[ply] else self.history.get((p.s,m),0)
  moves.sort(key=order,reverse=True);best=-31000 if check or not q else ev;bm=0;n=0
  for m in moves:
   z=m>>7&127;c=p.s;pc=abs(p.b[m&127]);pr=m>>14;target=V[abs(p.b[z])];attacker=V[pc]
   quiet=not target and not pr and not (pc==1 and z==p.e)
   prune=q and not check and not pr and (ev+target+180<a or target and attacker>target+180 and (p.b[z+9*c]==-c or p.b[z+11*c]==-c))
   u=p.make(m)
   if not u:continue
   if prune and not p.check:p.unmake(u);continue
   n+=1
   try:
    if q or n==1:v=-self.run(d-1,-b,-a,ply+1)
    else:
     red=1+(n>8 and d>4) if d>=3 and n>3 and quiet and not check and not p.check else 0
     v=-self.run(d-1-red,-a-1,-a,ply+1)
     if red and v>a:v=-self.run(d-1,-a-1,-a,ply+1)
     if a<v<b:v=-self.run(d-1,-b,-a,ply+1)
   finally:p.unmake(u)
   if v>best:best=v;bm=m
   if v>a:
    a=v
    if not ply:self.best=m
   if a>=b:
    if quiet and not q:self.killers[ply]=m;self.history[(p.s,m)]=min(80000,self.history.get((p.s,m),0)+d*d)
    break
  if not n:
   if check:return -30000+ply
   if not q:return 0
   if not p.hasmove():return 0
  v=best+ply if best>29000 else best-ply if best< -29000 else best
  if not entry or d>=entry[0]:self.tt[p.key]=(max(0,d),v,1 if best>=b else 2 if best<=old else 0,bm)
  return best
 def choose(self):
  result=0
  for m in self.p.moves():
   u=self.p.make(m)
   if u:self.p.unmake(u);result=m;break
  if not result:return 0
  for d in range(1,32):
   try:v=self.run(d,-31000,31000)
   except InterruptedError:break
   result=self.best or result;self.depth=d;self.score=v
   if abs(v)>29000 or self.nodes>self.limit//2:break
  return result
START='rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1'
def choose(view):
 if not view['legal_moves']:return ''
 p=Position(START)
 for t in view['moves']:p.make(move(t))
 return uci(Search(p).choose())
def main():
 url=os.environ['MAKEFUN_ENV_URL']
 def post(path,data):return json.load(urllib.request.urlopen(url+path,json.dumps(data).encode()))
 v=post('/game',{})
 while v['status']!='done':
  v=post('/move',{'game':v['game'],'move':choose(v)}) if v['status']=='your_move' else post('/game',{})
if __name__=='__main__':main()
