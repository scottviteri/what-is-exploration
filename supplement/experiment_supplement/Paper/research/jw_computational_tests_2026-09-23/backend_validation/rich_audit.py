"""Additional exact coefficient/tail checks for rich rational-background truncations.

Call after independent_audit.audit; the base audit reconstructs all probability
kernels and LP witnesses. This adds exact chosen-encoding masses and tail bounds.
"""
from pathlib import Path
from fractions import Fraction as F
import json,re

def check_rich(folder):
 folder=Path(folder);m=json.loads((folder/'metadata.json').read_text());r=json.loads((folder/'result.json').read_text());obj=r['objective'];cert=r['certificate']
 epsilon=F(m['rich_epsilon']);adaptive=list(map(F,m['adaptive_weights']));weights=list(map(F,m['weights']));mass=[]
 for target in m['target_specs']:
  if target['kind']!='rational':raise ValueError('Rich background uses literal rational encodings')
  match=re.fullmatch(r'rational-native-v1/a2o2/n(\d+)/d(\d+)/r(\d+)',target['key'])
  if match is None:raise ValueError('Unknown encoding')
  n,d,rank=map(int,match.groups());rows=sum(4**i for i in range(n));count=(d+1)**rows
  if not 0<=rank<count:raise ValueError('Bad target rank')
  mass.append(F(1,2**(n+1+d)*count))
 if not 0<epsilon<1 or sum(adaptive)!=1 or any(v<0 for v in adaptive):raise ValueError('Invalid mixture')
 intended=[(1-epsilon)*v+epsilon*b for v,b in zip(adaptive,mass)];beta=epsilon*(1-sum(mass))
 if len(adaptive)!=len(mass) or weights!=intended or list(map(F,obj['weights']))!=weights or F(obj['omitted_mass'])!=beta:raise ValueError('Rich weights/tail mismatch')
 if sum(weights)+beta!=1:raise ValueError('Mass not normalized')
 lo,hi=map(F,cert['selected_policy_loss_interval']);flo,fhi=map(F,cert['full_finite_policy_loss_interval'])
 if flo!=lo or fhi!=min(F(1),hi+beta):raise ValueError('Full loss bound drops omitted mass')
 if cert['eventual_regret_upper'] is not None:raise ValueError('Unjustified eventual regret certificate')
 return {'status':'passed','omitted_mass':str(beta),'selected_mass':str(sum(weights)),
  'scope':'Exact coefficient/tail arithmetic; numerical probability/LP audit is separate'}
