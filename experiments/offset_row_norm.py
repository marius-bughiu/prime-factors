"""Compare local row obstructions in the same fixed odd-prime lattices."""
import argparse
from collections import Counter
from itertools import islice, product
import json
from math import gcd,isqrt
from pathlib import Path
from statistics import median
from time import perf_counter

from experiments.grouped_offset_rows import local_failures
from experiments.offset_crt_wheel import choose_wheel
from experiments.offset_prime_power_slopes import local_directions


def prime_part(a,p):
    """Valuation and unit for a nonzero signed integer."""
    if a==0:
        raise ValueError('nonzero pivot or modulus required')
    e=0
    while a%p==0:
        e+=1
        a//=p
    return e,a


def rules(n,t,h,x,modulus,primes,bound,work=None):
    """Test the primitive pivot at det(x/g,(j,k)); separate divisible rows and valuation shells."""
    a,b=x
    g=gcd(a,b)
    a,b=a//g,b//g
    scale=modulus//g
    pivot=a*a+4*b*(t*a-h*b)
    assert modulus%g==0
    if not pivot:
        raise ValueError('the pivot of a nonsquare positive product cannot be isotropic')
    multiples,shells=[],[]
    for p in primes:
        if p>bound and scale%p:
            continue
        if work is not None:
            work['normalized_prime_tests'] += 1
        vmod,_=prime_part(scale,p)
        e,unit=prime_part(pivot,p)
        if e%2:
            first_bad=e+1
        elif p==2:
            first_bad=e+(2 if unit%4!=1 else 3) if unit%8!=1 else None
        else:
            first_bad=e+1 if pow(unit%p,(p-1)//2,p)!=1 else None
        if first_bad is not None:
            q=p**max(first_bad-vmod,0)
            if q<=bound:
                multiples.append(q)
        if p!=2 and n%p and e>=2:
            for tval in range(1,e,2):
                if tval>=vmod:
                    q=p**(tval-vmod)
                    if q<=bound:
                        shells.append((q,q*p))
    return sorted(set(multiples)),sorted(set(shells))


def compare(n,drop=2,max_batches=None):
    """Exhaust the specified group prefix; winners and saved visits are checked independently."""
    from experiments.offset_lattice_batches import ROW_PRIMES,ceil_div,direction_basis,row_interval
    t=isqrt(n);h=n-t*t
    if h<=0:
        raise ValueError('a nonsquare positive product is required')
    jlim=isqrt(4*h//3);klim=t*jlim//h+1
    plan=choose_wheel(n,jlim,klim)
    if plan['factor'] is not None:
        return dict(trial_factor=plan['factor'])
    cut=max(0,len(plan['primes'])-drop)
    keep,deferred=plan['primes'][:cut],plan['primes'][cut:]
    # The historical row test used p<=31. Include retained primes in a second
    # new-only stage, charging any improvement from the extra menu separately.
    primes=sorted(set(keep)|set(ROW_PRIMES))
    masks=[local_directions(n,t,p,1) for p in keep]
    allowed={p:{z*z%p for z in range(p)} for p in deferred}
    result=Counter()
    for dirs in islice(product(*masks),max_batches):
        x,y=direction_basis(keep,dirs,jlim,klim,result)
        a,b=x;c,d=y;M=a*d-b*c
        low=ceil_div(min(0,a*klim)-max(0,b*jlim),M)
        high=(max(0,a*klim)-min(0,b*jlim))//M
        B=max(abs(low),abs(high))
        first_bad,higher_bad=local_failures(a*a+4*b*(t*a-h*b),ROW_PRIMES,B)
        old=first_bad+higher_bad
        factors,shell=rules(n,t,h,x,M,ROW_PRIMES,B)
        all_factors,all_shell=rules(n,t,h,x,M,primes,B)
        result['bases']+=1
        for u in range(low,high+1):
            result['rows']+=1
            if any(u%q==0 for q in old):
                result['old_rejections']+=1
                continue
            reason='retained'
            if u:
                if any(u%q==0 for q in factors):
                    reason='scaled'
                elif any(u%q==0 and u%qq for q,qq in shell):
                    reason='shell'
                elif any(u%q==0 for q in all_factors) or any(u%q==0 and u%qq for q,qq in all_shell):
                    reason='wide_menu'
            result[reason+'_rows']+=1
            lower,upper=row_interval(x,y,u,jlim,klim,t,h)
            ws=range(lower,upper+1) if u else [w for w in (-1,1) if lower<=w<=upper]
            for w in ws:
                result[reason+'_positions']+=1
                j,k=a*w+c*u,b*w+d*u
                if gcd(j,k)!=1:
                    continue
                D=j*j+4*k*(t*j-h*k)
                if D<0 or any(D%p not in z for p,z in allowed.items()):
                    continue
                result[reason+'_sqrt']+=1
                z=isqrt(D)
                if z*z==D and 1<gcd(n,(j+2*t*k-z)//2)<n:
                    assert reason=='retained'
                    result['wins']+=1
    return dict(result)


def timings(repetitions,verify=False,forced=False):
    """Run both production modes to the same limits, alternating order each repetition."""
    from experiments.offset_lattice_batches import search,certify
    if repetitions<1:
        raise ValueError('at least one repetition is required')
    root=Path(__file__).resolve().parents[1]
    fixture='offset-row-geometry.json' if forced else 'offset-row-norm.json'
    if forced:
        from experiments.offset_row_geometry import search
    cases=json.loads((root/'benchmarks'/fixture).read_text())
    inputs=json.loads((root/'research/quartic-lane-holdout.json').read_text())['rows']
    panels=[('eight-small',[(int(r['n']),1<<18,2,1<<22) for r in inputs])]
    panels += [(r['id'],[(int(r['n']),r['max_batches'],r['drop'],r['max_events'])]) for r in cases]
    for name,samples in panels:
        totals={False:[],True:[]}
        frozen={}
        for i in range(repetitions):
            for mode in ((False,True) if i%2==0 else (True,False)):
                metrics=Counter();solved=[]
                start=perf_counter()
                for n,budget,drop,event_limit in samples:
                    run=search(n,budget,drop=drop,max_events=event_limit,exhaust=True,primitive_rows=mode)
                    for key in ('started_batches','completed_batches','rows','point_visits','square_tests','proper_hits',
                                'normalized_prime_tests','normalized_mod_tests','determinant_rejections','valuation_rejections'):
                        metrics[key]+=run.get(key,run.get('work',{}).get(key,0))
                    if run['factor'] is not None:
                        solved.append((n,tuple(sorted((run['factor'],run['remaining'])))))
                totals[mode].append(perf_counter()-start)
                receipt=(dict(metrics),solved)
                if mode in frozen and frozen[mode]!=receipt:
                    raise ArithmeticError('nonreproducible event counts')
                frozen[mode]=receipt
        if frozen[False][1]!=frozen[True][1] or frozen[False][0]['proper_hits']!=frozen[True][0]['proper_hits']:
            raise ArithmeticError('exhaustive modes disagree about the winning positions')
        if verify:
            for n,pair in frozen[True][1]:
                certify(n,pair)
        print(json.dumps(dict(panel=name,baseline=frozen[False][0],normalized=frozen[True][0],
              median_seconds=[median(totals[False]),median(totals[True])],factors=frozen[True][1],
              checked_pairs=len(frozen[True][1]) if verify else 0)),flush=True)


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('n',type=int,nargs='?')
    parser.add_argument('--drop',type=int,default=2)
    parser.add_argument('--max-batches',type=int)
    parser.add_argument('--timings',type=int,metavar='REPEATS')
    parser.add_argument('--forced',action='store_true',help='time the row rules on the forced-lift partial wheels')
    parser.add_argument('--verify',action='store_true',help='kernel-check normal search splits in the timing panel')
    args=parser.parse_args()
    if args.timings is not None:
        timings(args.timings,args.verify,args.forced)
        raise SystemExit
    if args.verify or args.forced:
        parser.error('--verify and --forced require --timings')
    if args.n is not None:
        print(json.dumps(compare(args.n,args.drop,args.max_batches)))
    else:
        root=Path(__file__).resolve().parents[1]
        rows=json.loads((root/'research/quartic-lane-holdout.json').read_text())['rows']
        for row in rows:
            print(row['sample'],json.dumps(compare(int(row['n']))),flush=True)
        frozen=json.loads((root/'benchmarks/offset-lattice-batches.json').read_text())
        for case in frozen:
            if case['id'] in ['offset-lattice-batches-midpoint-holdout-49','offset-lattice-batches-fresh-2048','offset-lattice-batches-crossed-2048']:
                print(case['id'],json.dumps(compare(int(case['n']),case['drop'],case['max_batches'])),flush=True)
