"""Independent sparse reconstruction of the simultaneous policy/decoder LP."""
import numpy as np
from scipy import sparse

def check_structure(z,raw,Fs,leafidx,layers,weights,kind):
 from independent_audit import matrix,norm
 decisions=sum(layers[:-1],[]);di={h:i for i,h in enumerate(decisions)};Q,S=raw.shape;P=2*len(decisions);mm=kind=='native_minimax'
 V=P+int(mm)+sum(1+S*F.shape[1]+Q*F.shape[1] for F in Fs)
 cost=np.zeros(V);eqparts=[];ubparts=[];be=[];bu=[]
 def put(equality,terms,rhs):
  entries=eqparts if equality else ubparts;right=be if equality else bu;base=len(right);right.extend(np.asarray(rhs).ravel())
  for offset,block in terms:
   co=sparse.coo_matrix(block);entries.append((co.row+base,co.col+offset,co.data))
 flow=sparse.lil_matrix((len(decisions),P));fr=np.zeros(len(decisions));fr[0]=1
 for i,h in enumerate(decisions):
  flow[i,2*i]=flow[i,2*i+1]=1
  if h:flow[i,2*di[h[:-1]]+h[-1][0]]=-1
 put(True,[(0,flow)],fr);cursor=P
 if mm:cost[cursor]=1;cursor+=1
 assign=sparse.coo_matrix((np.ones(S),(np.arange(S),leafidx)),shape=(S,P))
 for j,F in enumerate(Fs):
  Y=F.shape[1];d=cursor;dec=d+1;err=dec+S*Y;cursor=err+Q*Y
  if mm:put(False,[(d,[[1]]),(P,[[-1]])],[0])
  else:cost[d]=weights[j]
  put(True,[(dec,sparse.kron(sparse.eye(S),np.ones((1,Y)))),(0,-assign)],np.zeros(S))
  transform=sparse.kron(sparse.csr_matrix(raw),sparse.eye(Y));identity=sparse.eye(Q*Y)
  put(False,[(dec,transform),(err,-identity)],F.ravel())
  put(False,[(dec,-transform),(err,-identity)],-F.ravel())
  put(False,[(err,.5*sparse.kron(sparse.eye(Q),np.ones((1,Y)))),(d,-np.ones((Q,1)))],np.zeros(Q))
 residual=max(norm(cost-z['cost']),norm(np.asarray(be)-z['b_eq']),norm(np.asarray(bu)-z['b_ub']))
 for key,entries,right in [('A_eq',eqparts,be),('A_ub',ubparts,bu)]:
  rr,cc,vv=[np.concatenate([x[i] for x in entries]) for i in range(3)]
  expected=sparse.coo_matrix((vv,(rr,cc)),shape=(len(right),V)).tocsr();saved=matrix(z,key)
  if expected.shape!=saved.shape:raise ValueError('Monolithic matrix shape mismatch')
  residual=max(residual,norm((saved-expected).data))
 return residual
