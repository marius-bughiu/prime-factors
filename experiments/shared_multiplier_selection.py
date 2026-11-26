"""Prospective selection by covered smaller-factor positions, with matched root budgets.

The menu, sample sizes, seeds and tie rule were fixed before examining the
respective samples. Each candidate arm uses the union of admissible traces
modulo 24. Geometry presumes equal-width factors; the discriminant gcd needs
only N and the trace. Timings exclude sample generation and the once-per-menu
residue tables, whose construction is reported separately.
"""
import argparse
from collections import Counter
from hashlib import sha256
import json
from math import gcd, isqrt
from pathlib import Path
from time import process_time_ns

from .affine_radix_holdout import draw_prime
from .shared_multiplier_prefix import UNITS24, bounds, divisors, interval, merge

MENU = (1,2,6,12,30,60,210,21_621_600)
SEEDS = {'initial': b'weighted-covered-positions-v1', 'marginal': b'marginal-shared-wheel-v1'}
ARMS = ('selected','ordinary','round_robin','ordinary_equal','round_robin_equal','prefixed_equal')
CAP = 16
ROOT = Path(__file__).resolve().parents[1]


def catalogue():
    tables = {}
    for k in MENU:
        weights = divisors(k)
        for r in UNITS24:
            # d is a unit mod 24, d²=1. Therefore a*d+(k/a)*N/d
            # has one of the following residues for this oriented allocation.
            classes = {a:{(a+r*(k//a))*x%24 for x in UNITS24} for a in weights}
            tables[k,r] = classes,set.union(*classes.values())
    return tables


def labels(start, allowed, count):
    result = []
    for x in range(start,start+24*count):
        if x%24 in allowed:
            result.append(x)
            if len(result)==count:
                break
    return result


def positions(ranges):
    return sum(h-l+1 for l,h in ranges)


def plan(n,k,first,tables,rg,count):
    classes,allowed = tables[k,n%24]
    tests = labels(first,allowed,count)
    roots = {}
    windows = []
    for a,rs in classes.items():
        t = tests[-1]+1
        while t%24 not in rs:
            t += 1
        if t not in roots:
            roots[t] = isqrt(t*t-4*k*n-1)
        l,h = interval(a,t,roots[t],*rg)
        if l <= h:
            windows.append((l,h))
    return tests,merge(windows),len(roots),len(classes)


def probe(n,k,tests):
    found = set()
    gcds = 0
    for t in tests:
        delta = t*t-4*k*n
        d = isqrt(delta)
        if d*d == delta:
            f = gcd((t+d)//2,n)
            gcds += 1
            if 1 < f < n:
                found.add(min(f,n//f))
    return found,gcds


def reference(n,tables,menu,root_cap,initial=0):
    """Start each used arm once; spend the remaining roots on fresh labels."""
    start = process_time_ns()
    tests = root_cap-len(menu)
    leftover = tests-initial
    counts = {k:leftover//len(menu)+int(i<leftover%len(menu)) for i,k in enumerate(menu)}
    counts[1] += initial
    found = set()
    gcds = 0
    for k in menu:
        ts = labels(isqrt(4*k*n-1)+1,tables[k,n%24][1],counts[k])
        hits,g = probe(n,k,ts)
        found.update(hits)
        gcds += g
    return dict(factors=sorted(found),roots=root_cap,tests=tests,gcds=gcds,cpu_ns=process_time_ns()-start)


def run(n,tables,policy):
    start = process_time_ns()
    rg = bounds(n)
    starts = {k:isqrt(4*k*n-1)+1 for k in MENU if k!=1}
    # Reuse the actual floor sqrt(N) already in the public endpoints.
    u = rg[1]
    starts[1] = 2*u+int(n>u*u)+int(4*n>(2*u+1)**2)
    plans = {k:plan(n,k,starts[k],tables,rg,CAP) for k in MENU}
    roots = len(MENU)+sum(v[2] for v in plans.values())
    directions = sum(v[3] for v in plans.values())
    base,prior = plans[1][:2]
    tests0 = []
    if policy=='marginal':
        tests0 = base
        nxt,window,newroots,newdirs = plan(n,1,starts[1],tables,rg,2*CAP)
        plans[1] = nxt[CAP:],window,newroots,newdirs
        roots += newroots
        directions += newdirs
    else:
        prior = []
    unions = {k:merge(prior+v[1]) for k,v in plans.items()}
    k = max(MENU,key=lambda k:positions(unions[k]))
    best = positions(unions[k])
    ordinary = positions(unions[1])
    hits,gcds = probe(n,1,tests0)
    prior_hit = bool(hits)
    more,g = probe(n,k,plans[k][0])
    hits.update(more)
    tests = len(tests0)+CAP
    total = roots+tests
    selected = dict(factors=sorted(hits),roots=total,tests=tests,gcds=gcds+g,cpu_ns=process_time_ns()-start)
    references = dict(ordinary=reference(n,tables,(1,),tests+1),
                      round_robin=reference(n,tables,MENU,tests+len(MENU)),
                      ordinary_equal=reference(n,tables,(1,),total),
                      round_robin_equal=reference(n,tables,MENU,total),
                      prefixed_equal=reference(n,tables,MENU,total,initial=len(tests0)))
    return dict(k=k,earlier_hit=prior_hit,positions=best,ordinary_positions=ordinary,
                remaining=rg[1]-rg[0]+1-best,selected_intervals=unions[k],
                covers_more=best>ordinary, setup_roots=roots,locations_priced=directions,
                selected=selected,**references)


def summarize(rows):
    return dict(inputs=len(rows),choice_histogram=dict(sorted(Counter(r['k'] for r in rows).items())),
                earlier_hits=sum(r['earlier_hit'] for r in rows),larger_than_ordinary=sum(r['covers_more'] for r in rows),
                positions=str(sum(r['positions'] for r in rows)),ordinary_positions=str(sum(r['ordinary_positions'] for r in rows)),
                remaining_positions=str(sum(r['remaining'] for r in rows)),setup_roots=sum(r['setup_roots'] for r in rows),
                locations_priced=sum(r['locations_priced'] for r in rows),
                methods={k:dict(hits=sum(bool(r[k]['factors']) for r in rows),roots=sum(r[k]['roots'] for r in rows),
                                trace_tests=sum(r[k]['tests'] for r in rows),gcds=sum(r[k]['gcds'] for r in rows),
                                cpu_ns=sum(r[k]['cpu_ns'] for r in rows)) for k in ARMS})


def panel():
    start = process_time_ns()
    tables = catalogue()
    output = dict(menu=MENU,cap=CAP,catalogue_cpu_ns=process_time_ns()-start,conditions={})
    for policy,base_seed in SEEDS.items():
        data = dict(seed=base_seed.decode(),widths={},controls=[])
        for bits in (12,16,20,24):
            seed = base_seed+bits.to_bytes(2,'big')
            seen = set()
            numbers = []
            rows = []
            attempt = 0
            while len(rows)<64:
                p,q = sorted(draw_prime(x,attempt,bits=bits,seed=seed) for x in (b'p',b'q'))
                n = p*q
                attempt += 1
                if n.bit_length()!=2*bits or p==q or n in seen:
                    continue
                seen.add(n)
                numbers.append(n)
                r = run(n,tables,policy)
                if any(r[k]['factors'] not in ([],[p]) for k in ARMS):
                    raise ArithmeticError('wrong smaller factor on held-out product')
                if any(l<=p<=h for l,h in r['selected_intervals']) and r['selected']['factors'] != [p]:
                    raise ArithmeticError('algorithm missed the actual occupied position')
                rows.append(r)
            data['widths'][bits] = dict(attempts=attempt,sha256=sha256(json.dumps(numbers).encode()).hexdigest(),
                                        **summarize(rows))
        for c in json.loads((ROOT/'research'/'reciprocal-sum-lanes.json').read_text())['control_sections']:
            if c['end']=='first':
                r = run(int(c['n']),tables,policy)
                n = int(c['n'])
                # Diagnostic geometry for the strongest direct comparison.
                # This extra interval is unnecessary for detecting its squares.
                first = isqrt(4*n-1)+1
                rg = bounds(n)
                cost_matched = plan(n,1,first,tables,rg,r['ordinary_equal']['tests'])[1]
                same_tests = plan(n,1,first,tables,rg,r['ordinary']['tests'])[1]
                joined = positions(merge(same_tests+r['selected_intervals']))
                data['controls'].append(dict(input=c['input'],ordinary_equal_positions=str(positions(cost_matched)),
                                             selected_only_positions=str(joined-positions(same_tests)),
                                             ordinary_only_positions=str(joined-r['positions']),**summarize([r])))
        output['conditions'][policy] = data
    return output


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.parse_args()
    print(json.dumps(panel(),indent=2))
