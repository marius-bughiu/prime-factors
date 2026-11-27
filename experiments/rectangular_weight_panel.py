"""Test which difference-of-squares rows are accessible to balanced prime factors."""
import argparse
import json
from math import isqrt
from math import gcd, isqrt
from pathlib import Path
from time import process_time_ns

from experiments.affine_radix_holdout import draw_prime
from experiments.rectangular_root_windows import bounds, multiplier_ratio, product_count_bound, run
from experiments.split_prime_holdout import certificate

ROOT = Path(__file__).resolve().parents[1]
SEED = b'rectangular-weight-window/v1'
SCALE = 1024


def price(n, bits):
    b,h,k = bounds(n,1)
    excess = multiplier_ratio(n,h,bits,SCALE)
    allowed = product_count_bound(k,SCALE,excess)
    root = isqrt(k)
    odd = (root+1)//2
    even = isqrt(k//4)
    log_bound = root.bit_length()+1
    extra = h*h*(6*SCALE*log_bound+2*excess*odd+excess*even)//(8*SCALE*isqrt(n))
    return dict(denominator_cap=str(b), numerator_cap=str(h), rows=str(k),
                ratio_scale=SCALE, ratio_excess=excess, allowed_at_most=str(allowed),
                coordinates_at_most=str(allowed+extra),ruled_out_at_least=str(k-allowed))


def compare(n, bits, sample, *, rows=None, per_row=None):
    results = {}
    for rotation in range(4):
        rules = ('ordinary','weights') if (rotation+sample)%2==0 else ('weights','ordinary')
        for rule in rules:
            start = process_time_ns()
            result = run(n,[1],factor_bits=bits if rule=='weights' else None,rows=rows,per_row=per_row)
            elapsed = process_time_ns()-start
            first = result.pop('first_cpu_ns')
            if rule not in results:
                results[rule] = dict(data=result, times=[], first_times=[])
            if results[rule]['data'] != result:
                raise ValueError('inconsistent search')
            results[rule]['times'].append(elapsed)
            results[rule]['first_times'].append(first)
    return results


def check_small():
    from scripts.factor import primes_through
    seen = saved = 0
    ps = [p for p in primes_through(127) if p > 3]
    for i, p in enumerate(ps):
        for q in ps[i+1:]:
            if p.bit_length() != q.bit_length():
                continue
            n = p*q
            if bounds(n,1)[1] >= 1 << (p.bit_length()-1):
                continue
            a = run(n,[1])
            b = run(n,[1],factor_bits=p.bit_length())
            assert int(b['factor']) in (p,q) and a['roots']==b['roots']
            assert b['work']['rows'] <= int(price(n,p.bit_length())['allowed_at_most'])
            seen += 1
            saved += a['work']['rows']-b['work']['rows']
    return dict(products=seen, rows_removed=saved)


def report():
    rows = []
    for bits in (16,20,24):
        kept = sample = 0
        while kept < 8:
            p,q=sorted(draw_prime(side,sample,bits=bits,seed=SEED+b'/'+str(bits).encode())
                       for side in (b'p',b'q'))
            sample += 1
            n=p*q
            if p==q or n.bit_length()!=2*bits:
                continue
            kept += 1
            data=compare(n,bits,sample)
            for rec in data.values():
                if int(rec['data']['factor']) not in (p,q):
                    raise ValueError('incorrect factor')
            rows.append(dict(bits=bits,sample=sample-1,n=str(n),methods=data,bound=price(n,bits),
                             factors=[str(p),str(q)], certificate=certificate(n,(p,q))))
    full=[]
    for case in json.loads((ROOT/'benchmarks/target-norm-multipliers.json').read_text()):
        if case['status']!='partial':
            continue
        n=int(case['n'])
        data=compare(n,1024,0,rows=65536,per_row=1)
        full.append(dict(id=case['id'],n=str(n),bound=price(n,1024),methods=data,
                         remaining=[str(n)] if all(not v['data']['factor'] for v in data.values()) else []))
    return dict(seed=SEED.decode(),small_check=check_small(),panel=rows,full_size=full,
                timing='CPU nanoseconds; four alternating comparisons, including generating and merging weight pairs.')


if __name__=='__main__':
    cli=argparse.ArgumentParser(description=__doc__)
    cli.add_argument('--output',type=Path)
    cli.add_argument('--check-small',action='store_true')
    args=cli.parse_args()
    data=check_small() if args.check_small else report()
    encoded=json.dumps(data,indent=2)+'\n'
    if args.output:
        args.output.write_text(encoded)
    else:
        print(encoded,end='')
