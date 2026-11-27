"""Price eager and first-lookup representatives for equal weighted trace keys."""
import argparse
from collections import Counter, defaultdict
from itertools import combinations
import json
from math import gcd
from pathlib import Path
from time import process_time_ns

from experiments.weighted_global_trace import FIXTURE, schedule
from scripts.factor import primes_through

ROOT = Path(__file__).resolve().parents[1]
REPORT = ROOT / 'research/weighted-trace-representatives.json'
POLICIES = ('original','eager','first_lookup')


def power_table(n,bits,cap,slots):
    start = process_time_ns()
    gaps, positions, common = schedule(n,bits,cap,slots)
    h = n//2
    pre = set()
    buckets = defaultdict(list)
    if gcd(2,n)!=1:
        raise ValueError('odd modulus required')
    for e in gaps:
        y = pow(2,h*e,n)
        yi = pow(y,-1,n)
        g = gcd(y*y-1,n)
        if 1 < g < n:
            pre.add(g)
        buckets[(y+yi)%n].append((y,yi,g))
    left = []
    for _,_,c,s,_ in positions:
        x = pow(2,s-(h+1)*c,n)
        left.append((x,(x+pow(x,-1,n))%n))
    return buckets,left,pre,common['weight_gcds']+1+len(gaps),process_time_ns()-start


def evaluate(n,buckets,left,pre,policy,skip_obvious=False):
    """All policies receive the same stored right powers, inverses and prechecks."""
    started = process_time_ns()
    groups,lookups,gcds,obvious = set(),0,Counter(),Counter()
    found = set(pre)
    def check(x, entry, stage):
        y,yi,precheck = entry
        if skip_obvious and x == y:
            obvious[stage] += 1
            return
        if skip_obvious and x == yi:
            obvious[stage] += 1
            g = precheck
        else:
            gcds[stage] += 1
            g = gcd(x-y,n)
        if 1 < g < n:
            found.add(g)

    def duplicates(bucket):
        representative = bucket[0]
        for y,_,_ in bucket[1:]:
            check(y,representative,'duplicates')

    if policy=='eager':
        for bucket in buckets.values():
            duplicates(bucket)
    for x,key in left:
        bucket = buckets.get(key)
        if not bucket:
            continue
        lookups += 1
        if policy=='original':
            for entry in bucket:
                check(x,entry,'left')
        else:
            if policy=='first_lookup' and key not in groups:
                duplicates(bucket)
                groups.add(key)
            check(x,bucket[0],'left')
    return found,gcds,obvious,lookups,process_time_ns()-started


def compare(n,bits,cap,slots):
    buckets,left,pre,fixed,key_cpu = power_table(n,bits,cap,slots)
    hits = Counter(k for _,k in left)
    duplicates = sum(len(b)-1 for b in buckets.values())
    gain_eager = sum((len(b)-1)*(hits[k]-1) for k,b in buckets.items())
    gain_lazy = sum((len(b)-1)*max(0,hits[k]-1) for k,b in buckets.items())
    diag=Counter()
    for bucket in buckets.values():
        y, yi, _ = bucket[0]
        for other,_,_ in bucket[1:]:
            diag['equal' if other==y else 'inverse' if other==yi else 'mixed'] += 1
    stats={}
    for skip in (False,True):
        variants = {}
        for policy in POLICIES:
            found,calls,avoided,h,cpu = evaluate(n,buckets,left,pre,policy,skip)
            variants[policy] = dict(split=bool(found),divisors=sorted(found),gcds=sum(calls.values()),
                                    setup_duplicates=calls['duplicates'], scan_gcds=calls['left'],
                                    skipped_known=sum(avoided.values()), hit_coordinates=h,cpu_ns=cpu)
        if not skip:
            for policy,gain in [('eager',gain_eager),('first_lookup',gain_lazy)]:
                if variants['original']['gcds']-variants[policy]['gcds'] != gain:
                    raise ArithmeticError('per-bucket cost identity failed')
        if any(variants['original']['split'] and not data['split'] for data in variants.values()):
            raise ArithmeticError('representatives dropped the original factorization')
        stats['classified' if skip else 'explicit']=variants
    if any(stats['classified'][p]['divisors']!=stats['explicit'][p]['divisors'] for p in POLICIES):
        raise ArithmeticError('exact/inverse shortcut changed a reported divisor')
    return dict(n=str(n), coordinates=len(left), right=sum(map(len,buckets.values())),
                duplicates=duplicates, duplicate_types=dict(diag),fixed_gcds=fixed,
                common_cpu_ns=key_cpu,policies=stats)


def summarize(rows):
    summary=dict(inputs=len(rows), fixed_gcds=sum(r['fixed_gcds'] for r in rows),
                 duplicate_inputs=sum(bool(r['duplicates']) for r in rows),
                 common_cpu_ns=sum(r['common_cpu_ns'] for r in rows))
    types=Counter()
    for r in rows:types.update(r['duplicate_types'])
    summary['duplicate_types']=dict(types)
    for regime in ('explicit','classified'):
        summary[regime]={}
        for policy in POLICIES:
            total=Counter()
            for row in rows:
                v=row['policies'][regime][policy]; old=row['policies'][regime]['original']
                total.update(inputs_split=int(v['split']),extra_splits=int(v['split'] and not old['split']),
                             variable_gcds=v['gcds'],total_gcds=row['fixed_gcds']+v['gcds'],
                             fewer_gcds=int(v['gcds']<old['gcds']),more_gcds=int(v['gcds']>old['gcds']),
                             new_setup_gcds=v['setup_duplicates'],scan_gcds=v['scan_gcds'],
                             skipped_known=v['skipped_known'],comparison_cpu_ns=v['cpu_ns'])
            summary[regime][policy]=dict(total)
    return summary


def panel():
    cells=[]
    heavy=None
    for bits in (9,10,11):
        primes=[p for p in primes_through((1<<bits)-1) if p>=1<<(bits-1)]
        by_width=defaultdict(list)
        for p,q in combinations(primes,2):
            row=compare(p*q,bits,64,2)
            if any(g not in (p,q) for v in row['policies']['explicit'].values() for g in v['divisors']):
                raise ArithmeticError('factor disagrees with the finite input population')
            by_width[(p*q).bit_length()].append(row)
            if heavy is None or (-row['duplicates'],p*q)<(-heavy['duplicates'],int(heavy['n'])):
                heavy = row
        cells.extend(dict(factor_bits=bits,product_bits=w,**summarize(rows))
                     for w,rows in sorted(by_width.items()))
    prior=json.loads((ROOT/'research/local-gap-polynomial.json').read_text())
    hold=[compare(int(r['n']),r['factor_bits'],256,4) for r in prior['holdout']]
    controls=[dict(id=c['id'],**compare(int(c['n']),1024,64,2))
              for c in json.loads(FIXTURE.read_text()) if c['factor_bits']==1024]
    return dict(base=2, census_cap=64, census_per_row=2,
                fixed_gcds='Candidate weight gcds, one base gcd and one right precheck per gap.',
                classified='Skip gcds for exact matches and infer inverse-match gcds from the stored right precheck.',
                timings='Single process-CPU measurement, common schedule and power generation timed once per case. Policy times include instrumentation.',
                cells=cells, holdout_cap=256, holdout_per_row=4, holdout=summarize(hold),
                duplicate_heavy_control='Largest duplicate count among all census inputs, ties by smallest product.',
                selected=heavy, controls=controls)


if __name__=='__main__':
    cli=argparse.ArgumentParser(description=__doc__)
    cli.add_argument('--write',action='store_true')
    output=json.dumps(panel(),indent=2)+'\n'
    if cli.parse_args().write:REPORT.write_text(output)
    else:print(output,end='')
