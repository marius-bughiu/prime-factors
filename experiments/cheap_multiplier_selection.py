"""Select the next 16 weighted traces with an input-independent table.

For a factor assignment (a,b) of k, score the predicted interior width by
2*k^(1/4)*sqrt(height)/a. Average over 24 half-integer phases of 2*sqrt(kN),
using 28-bit fixed point. The stationary point is eligible when b/a is at
least N/(2^w-1)^2. Ordinary Fermat gets the half-width at its endpoint and
only the increase after the first 16 ordinary traces. Exact clipped widths and
phase fluctuations need not agree with scores. Ties go to the smaller k.
"""
from collections import Counter, defaultdict
from fractions import Fraction
from hashlib import sha256
import argparse
import json
from math import comb, gcd, isqrt
from time import process_time_ns

from .affine_radix_holdout import draw_prime
from .shared_multiplier_selection import MENU, ROOT, UNITS24, bounds, catalogue, labels, merge, plan, positions

ONE = ((1,2,2),)
THREE = ((3,4,12),(2,3,6),(1,2,2))
FOUR = ((5,6,30),)+THREE
LOOKUP = {1:FOUR, 5:THREE, 7:THREE, 11:ONE, 13:FOUR, 17:THREE, 19:THREE, 23:ONE}
SAMPLES = {'pilot':(b'cheap-marginal-multiplier-v1',(12,16,20,24),256),
           'confirmation':(b'cheap-marginal-multiplier-confirm-v1',(12,16,20,24,28,32),1024)}


def compile_lookup(tables):
    """Recompute the frozen thresholds. Only this offline construction uses fourth roots."""
    out = {}
    roots = 0
    for r in UNITS24:
        extras = defaultdict(Counter)
        for k in MENU:
            classes,allowed = tables[k,r]
            for a,rs in classes.items():
                b = k//a
                if b>a or a>2*b:
                    continue
                prices = []
                for count in ((16,32) if k==1 else (16,)):
                    total = 0
                    for phase in range(24):
                        end = labels(phase+1,allowed,count)[-1]+1
                        while end%24 not in rs:
                            end += 1
                        # floor(2^28 * 2*k^(1/4)*sqrt(end-phase-1/2)/a).
                        total += isqrt(isqrt((4*k*(2*(end-phase)-1)**2)<<112))//a
                        roots += 1
                    prices.append(total)
                if k==1:
                    ordinary = (prices[1]-prices[0])//2
                else:
                    extras[Fraction(b,a)][k] += prices[0]
        score = Counter({1:ordinary})
        winner = 1
        changes = []
        for ratio,delta in sorted(extras.items(),reverse=True):
            score.update(delta)
            best = max(MENU,key=score.__getitem__)
            if best != winner:
                changes.append((ratio.numerator,ratio.denominator,best))
                winner = best
        out[r] = tuple(changes)
    if out != LOOKUP:
        raise ArithmeticError('precompiled table differs from the frozen score')
    return roots


def choose(n):
    if gcd(n,6) != 1 or n <= 1:
        raise ValueError('requires an odd product greater than one coprime to six')
    jumps = LOOKUP[n%24]
    cap = (1<<((n.bit_length()+1)//2))-1
    square = cap*cap
    lo,hi,tests = 0,len(jumps),0
    while lo<hi:
        mid = (lo+hi)//2
        b,a,_ = jumps[mid]
        tests += 1
        if a*n <= b*square:
            lo = mid+1
        else:
            hi = mid
    return (jumps[lo-1][2] if lo else 1), tests


def evaluate(n,alloc,tables):
    """All tested labels are generated from N. Always exhaust the stated allocations."""
    factors = set()
    gcds = 0
    witness = None
    for k,count in alloc:
        first = isqrt(4*k*n-1)+1
        for index,s in enumerate(labels(first,tables[k,n%24][1],count)):
            delta = s*s-4*k*n
            d = isqrt(delta)
            if d*d == delta:
                g = gcd((s+d)//2,n)
                gcds += 1
                if 1<g<n:
                    factors.add(min(g,n//g))
                    if witness is None:
                        witness = (k,first,index,s,d,g)
    tests = sum(count for _,count in alloc)
    return dict(factors=sorted(factors),gcds=gcds,witness=witness,
                trace_tests=tests,total_roots=tests+len(alloc))


def search(n,tables):
    k,guards = choose(n)
    allocations = [(1,32)] if k==1 else [(1,16),(k,16)]
    return dict(k=k,guards=guards,**evaluate(n,allocations,tables))


def round_robin(total,prior=0):
    left = total-len(MENU)-prior
    return [(k,left//len(MENU)+int(i<left%len(MENU))+(prior if k==1 else 0)) for i,k in enumerate(MENU)]


def timed(f,*args):
    start = process_time_ns()
    result = f(*args)
    return result,process_time_ns()-start


def two_sided(w,l):
    """Exact two-sided binomial sign-test on paired discordant outcomes."""
    n = w+l
    p = min(Fraction(1),Fraction(2*sum(comb(n,i) for i in range(min(w,l)+1)),2**n))
    return dict(numerator=str(p.numerator),denominator=str(p.denominator),approx=float(p))


def prior_products(bits):
    """Reserve earlier recorded panels by their independent draws, without using outcomes."""
    result = set()
    if bits not in SAMPLES['pilot'][1]:
        return result
    for seed,size in ((SAMPLES['pilot'][0],256),(b'weighted-covered-positions-v1',64),
                      (b'marginal-shared-wheel-v1',64)):
        own = set()
        attempt = 0
        while len(own)<size:
            p,q = (draw_prime(side,attempt,bits=bits,seed=seed+bits.to_bytes(2,'big'))
                   for side in (b'p',b'q'))
            attempt += 1
            if p!=q and (p*q).bit_length()==2*bits:
                own.add(p*q)
        result.update(own)
    return result


def panel(group):
    seed,widths,count = SAMPLES[group]
    tables,t0 = timed(catalogue)
    roots,t1 = timed(compile_lookup,tables)
    out = dict(group=group,seed=seed.decode(),count_per_width=count,menu=MENU,
               compilation=dict(catalogue_cpu_ns=t0,score_cpu_ns=t1,small_fourth_roots=roots),
               widths={},representative=None)
    total = Counter()
    for bits in widths:
        seen = set()
        excluded = prior_products(bits) if group == 'confirmation' else set()
        old_draws = 0
        attempt = 0
        counts = Counter()
        names = Counter()
        inputs = []
        while len(seen) < count:
            draw_seed = seed+bits.to_bytes(2,'big')
            p,q = sorted(draw_prime(side,attempt,bits=bits,seed=draw_seed) for side in (b'p',b'q'))
            attempt += 1
            n = p*q
            if n.bit_length()!=2*bits or p==q or n in seen:
                continue
            if n in excluded:
                old_draws += 1
                continue
            # Scheduling the comparison first on alternate inputs must not add
            # any untimed selection work to the measured selected arm.
            k,_ = choose(n)
            budget = 33+int(k!=1)
            ordinary_alloc = [(1,budget-1)]
            if len(seen)%2:
                direct,dt = timed(evaluate,n,ordinary_alloc,tables)
                selected,st = timed(search,n,tables)
            else:
                selected,st = timed(search,n,tables)
                direct,dt = timed(evaluate,n,ordinary_alloc,tables)
            seen.add(n)
            inputs.append(n)
            names[k] += 1
            first = evaluate(n,[(1,16)],tables)
            equal32 = evaluate(n,[(1,32)],tables)
            rr = evaluate(n,round_robin(budget),tables)
            pref = evaluate(n,round_robin(budget,16),tables)
            if (selected['total_roots'] != direct['total_roots'] or
                    any(v['factors'] not in ([],[p]) for v in (selected,direct,first,equal32,rr,pref))):
                raise ArithmeticError('incorrect factors or unmatched cost')
            win = bool(selected['factors'] and not direct['factors'])
            loss = bool(direct['factors'] and not selected['factors'])
            counts.update(dict(inputs=1,selected=bool(selected['factors']),ordinary_equal=bool(direct['factors']),
                               uniquely_selected=win,uniquely_ordinary=loss,ordinary16=bool(first['factors']),
                               ordinary32=bool(equal32['factors']),round_robin_equal=bool(rr['factors']),
                               common_prefix_round_robin=bool(pref['factors']),comparisons=selected['guards'],
                               roots=budget,selected_cpu_ns=st,ordinary_cpu_ns=dt))
            if bits>=20 and win and out['representative'] is None:
                out['representative']=dict(n=str(n),factor=str(p),cofactor=str(q),bits=bits,attempt=attempt-1,
                                           selected=selected,ordinary=direct)
        out['widths'][bits]=dict(counts,attempts=attempt,skipped_prior_draws=old_draws,multipliers=dict(sorted(names.items())),
                                 p_value=two_sided(counts['uniquely_selected'],counts['uniquely_ordinary']),
                                 product_sha256=sha256(json.dumps(inputs).encode()).hexdigest())
        total.update(counts)
    out['total'] = dict(total,p_value=two_sided(total['uniquely_selected'],total['uniquely_ordinary']))
    controls = []
    for c in json.loads((ROOT/'research'/'reciprocal-sum-lanes.json').read_text())['control_sections']:
        if c['end'] != 'first':
            continue
        n = int(c['n'])
        run,ts = timed(search,n,tables)
        k = run['k']
        direct,dt = timed(evaluate,n,[(1,run['total_roots']-1)],tables)
        rg = bounds(n)
        first1 = isqrt(4*n-1)+1
        prior = plan(n,1,first1,tables,rg,16)[1]
        later = plan(n,k,isqrt(4*k*n-1)+1,tables,rg,32 if k==1 else 16)[1]
        eq = plan(n,1,first1,tables,rg,direct['trace_tests'])[1]
        covered = positions(merge(prior+later))
        controls.append(dict(input=c['input'],selected=run,ordinary=direct,selected_cpu_ns=ts,
                             ordinary_cpu_ns=dt,positions=str(covered),ordinary_equal_positions=str(positions(eq)),
                             remaining=str(rg[1]-rg[0]+1-covered)))
    out['controls'] = controls
    return out


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--panel',choices=tuple(SAMPLES),default='confirmation')
    args = parser.parse_args()
    print(json.dumps(panel(args.panel),indent=2))
