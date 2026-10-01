#!/usr/bin/env python3
"""Fixed-collector comparison of full-count and majority transfer certificates.

Retains the parent's exact same numerical outer cost sublevels. Saved-policy
errors remain lower witnesses only; no worst-deficiency optimization occurs here.
"""
from pathlib import Path
from fractions import Fraction
from itertools import product
import argparse,csv,hashlib,json

HERE=Path(__file__).resolve().parent
PARENT=HERE.parent
NOISES=((Fraction('0.1'),Fraction('0.1')),(Fraction('0.25'),Fraction('0.25')),
        (Fraction('0.1'),Fraction('0.3')))
TARGETS=('LR','LLL','RRR','LLR','LRR','adaptive_L')
DESIGNS=tuple(map(Fraction,('0','.001','.01','.05','.1')))

def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def word(s):return 'adaptive_L' if s=='adaptive' else s
def physical(c):return tuple(map(Fraction,c['eps']))
def evaluate(c,s):return float(Fraction(c['intercept'])+Fraction(c['slope'])*Fraction(str(s)))
def best(certs,s):
    c=min(certs,key=lambda c:evaluate(c,s))
    return evaluate(c,s),c

def main(path):
    data=json.loads(path.read_text())
    assert data['status']=='passed_requested_stage',data['status']
    assert not data['failures']
    assert all(c['all_exact_checks_pass'] for c in data['certificates'])
    certs=data['certificates']
    expected=set(product(NOISES,('majority3','count3'),TARGETS,DESIGNS))
    observed={(physical(c),c['diagnostic_source'],word(c['word']),Fraction(c['at_loss'])) for c in certs}
    assert observed==expected,(len(expected-observed),len(observed-expected))
    assert len(certs)==len(expected)==180
    assert data['protocol_sha256']==digest(HERE/'PROTOCOL.md')
    assert data['source_sha256']==digest(HERE/'compute_counts.py')
    # Numerical assertions supplement exact witness audits. They do not replace them.
    bykey={}
    for c in certs:bykey.setdefault((physical(c),c['diagnostic_source'],word(c['word'])),[]).append(c)
    prior=list(csv.DictReader((PARENT/'transfer_bounds.csv').open()))
    selected=[r for r in prior if r['objective'] in ('native_repeats','native_minimax')]
    assert len(selected)==252
    rows=[]
    for old in selected:
        noise=tuple(Fraction(str(x)) for x in json.loads(old['noise']))
        target=old['target'];objective=old['objective']
        cost=float(old['native_loss_bound'])
        loss=cost/.2 if objective=='native_repeats' else cost
        mv,mc=best(bykey[noise,'majority3',target],loss)
        cv,cc=best(bykey[noise,'count3',target],loss)
        parent=float(old['guaranteed_upper'])
        # A fresh majority portfolio can differ from the parent off its five
        # design points. Credit that separately before attributing count gains.
        baseline=min(parent,mv)
        improved=min(baseline,cv)
        lo=float(old['witnessed_lower'])
        assert lo<=improved+2e-7,(old['witness_id'],target,lo,improved)
        row=dict(old)
        row.update(diagnostic_average_bound_new=loss,
            new_majority_upper=mv,new_count_upper=cv,
            count_with_lifted_majority_upper=min(cv,mv),
            majority_design=mc['at_loss'],count_design=cc['at_loss'],
            majority_intercept=mc['intercept'],majority_slope=mc['slope'],
            count_intercept=cc['intercept'],count_slope=cc['slope'],
            parent_best_upper=parent,baseline_including_new_majority=baseline,
            refined_upper=improved,count_specific_improvement=baseline-improved,
            total_improvement=parent-improved,
            old_gap=parent-lo,new_gap=improved-lo,
            old_gap_closed=(parent-improved)/(parent-lo) if parent-lo>1e-7 else None)
        rows.append(row)
    with (HERE/'comparison.csv').open('w',newline='') as f:
        wr=csv.DictWriter(f,fieldnames=list(rows[0]));wr.writeheader();wr.writerows(rows)
    held=[r for r in rows if r['held_out']=='True']
    designrows=[]
    for noise,target,s in product(NOISES,TARGETS,DESIGNS):
        mc=next(c for c in bykey[noise,'majority3',target] if Fraction(c['at_loss'])==s)
        cc=next(c for c in bykey[noise,'count3',target] if Fraction(c['at_loss'])==s)
        mv=evaluate(mc,s);cv=evaluate(cc,s)
        assert cv<=mv+2e-7,(noise,target,s,mv,cv)
        designrows.append(dict(noise=[str(x) for x in noise],target=target,loss=str(s),majority=mv,count=cv,improvement=mv-cv))
    def summarize(rs):
        return dict(cases=len(rs),count_specific_improvements=sum(r['count_specific_improvement']>1e-7 for r in rs),
            improved_from_parent=sum(r['total_improvement']>1e-7 for r in rs),
            strict_raw_count_over_majority=sum(r['new_count_upper']<r['new_majority_upper']-1e-7 for r in rs),
            max_count_specific_improvement=max(r['count_specific_improvement'] for r in rs),
            min_witness_slack=min(r['new_gap'] for r in rs))
    out=dict(scope='Fixed parent collectors and objective envelopes; new universal-source transfer certificates, no new policy optimization.',
        protocol_sha256=digest(HERE/'PROTOCOL.md'),source_sha256=digest(HERE/'compute_counts.py'),
        certificate_sha256=digest(path),parent_transfer_sha256=digest(PARENT/'transfer_bounds.csv'),
        all=summarize(rows),held_out=summarize(held),design_comparisons=designrows,
        certificate_coverage=180,design_pairs=90,
        headline_rows=[r for r in rows if r['H']=='4' and r['noise']=='[0.1, 0.1]' and r['fraction']=='0.0'])
    (HERE/'comparison.json').write_text(json.dumps(out,indent=2)+'\n')
    plot(rows)
    print(json.dumps({k:v for k,v in out.items() if k not in ('design_comparisons','headline_rows')},indent=2))

def plot(rows):
    import matplotlib
    matplotlib.use('Agg')
    import matplotlib.pyplot as plt
    fig,axes=plt.subplots(2,3,figsize=(10.8,6.0),sharex=True)
    for i,obj in enumerate(('native_repeats','native_minimax')):
        for j,target in enumerate(('LLR','LRR','adaptive_L')):
            ax=axes[i,j]
            rs=sorted([r for r in rows if r['H']=='4' and r['noise']=='[0.1, 0.1]' and r['objective']==obj
                       and r['target']==target and r['fraction']!=''],key=lambda r:float(r['fraction']))
            xs=[100*float(r['fraction']) for r in rs]
            for field,label,color,style in [('baseline_including_new_majority','Previous + majority bound','#a56345','-'),
                                           ('refined_upper','With full counts','#237c84','-'),
                                           ('witnessed_lower','Saved-policy lower witness','#777777','--')]:
                ax.plot(xs,[float(r[field]) for r in rs],marker='o',markersize=3,lw=1.4,
                        color=color,linestyle=style,label=label)
            ax.set_title('Adaptive target' if target=='adaptive_L' else target)
            ax.set_xticks([0,1,5]);ax.spines[['top','right']].set_visible(False);ax.grid(axis='y',alpha=.15)
            if i==1:ax.set_xlabel('Allowed return gap (% of range)')
            if j==0:ax.set_ylabel(('Repeat sum' if i==0 else 'Minimax')+'\nSimulation error')
    handles,labels=axes[0,0].get_legend_handles_labels()
    fig.legend(handles,labels,loc='upper center',ncol=3,frameon=False)
    fig.subplots_adjust(top=.89,bottom=.12,hspace=.4,wspace=.25)
    fig.savefig(HERE/'count_transfer.pdf',bbox_inches='tight')
    fig.savefig(HERE/'count_transfer.png',dpi=160,bbox_inches='tight')
    plt.close(fig)

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--input',type=Path,default=HERE/'results.json')
    args=ap.parse_args();main(args.input.resolve())
