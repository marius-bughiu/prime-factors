"""Project primitive difference-of-squares weight pairs onto the smaller divisor."""

import argparse
from collections import Counter
import json
from math import isqrt
from pathlib import Path
from time import process_time_ns

from experiments.rectangular_root_windows import bounds, multiplier_ratio
from experiments.rectangular_weight_streams import starts, next_entry, scan
from experiments.secant_quotient_cells import ParallelStrip, plan, secant_lattices, sweep
from experiments.split_prime_holdout import certificate

ROOT = Path(__file__).resolve().parents[1]


def ceil_div(n,d):
    return -(-n//d)


def divisor_range(n,bits):
    return max(1<<(bits-1),ceil_div(n,(1<<bits)-1)),isqrt(n)


def window(n,b,h,a,big,t,lo,hi):
    """Solve both |t(big*p−a*N/p)|≤2H and t(big*p+a*N/p)≤2B exactly."""
    gap = 2*h//t
    total = 2*b//t
    norm = 4*a*big*n
    room = total*total-norm
    if room<0:
        return None
    sum_root = isqrt(room)
    gap_square = gap*gap+norm
    gap_root = isqrt(gap_square)
    denom = 2*big
    low = max(lo, ceil_div(total-sum_root,denom),
              ceil_div(gap_root+(gap_root*gap_root!=gap_square)-gap,denom))
    high = min(hi,(total+sum_root)//denom,(gap_root+gap)//denom)
    return (low,high) if low<=high else None


def make_windows(n,bits,cap=None):
    b,h,limit = bounds(n,1)
    lo,hi = divisor_range(n,bits)
    if hi<lo or lo<=h or b+h>=n:
        raise ValueError("expected a balanced input with H below the prime lower bound")
    if cap is not None:
        limit=min(limit,cap)
    ex = multiplier_ratio(n,h,bits)
    records,work = [],Counter()
    for t in (1,2):
        for entry in starts(t*t,limit,1024,ex,work):
            while entry is not None:
                _,_,a,big,_ = entry
                item=window(n,b,h,a,big,t,lo,hi)
                work["pairs"]+=1
                if item is not None:
                    records.append((*item,a,big,t))
                entry=next_entry(*entry,work)
    return records,work


def merged(records):
    answers=[]
    for lo,hi,*_ in sorted(records):
        if answers and lo<=answers[-1][1]+1:
            answers[-1][1]=max(answers[-1][1],hi)
        else:
            answers.append([lo,hi])
    return answers


def count_overlaps(records):
    changes=Counter()
    for lo,hi,*_ in records:
        changes[lo]+=1
        changes[hi+1]-=1
    sizes=Counter()
    active=previous=0
    for x,change in sorted(changes.items()):
        if active:
            sizes[active]+=x-previous
        active+=change
        previous=x
    if active!=0 or max(sizes,default=0)>2:
        raise ArithmeticError("projected multiplicity exceeded two")
    return sizes


def trial(n,intervals):
    divisor=None
    visits=0
    for lo,hi in intervals:
        for p in range(lo|1,hi+1,2):
            visits+=1
            if n%p==0:
                divisor=p
                break
        if divisor is not None:
            break
    return divisor,visits


def compute(n,bits,do_secant=False):
    lo,hi=divisor_range(n,bits)
    start=process_time_ns()
    records,work=make_windows(n,bits)
    windows=merged(records)
    setup=process_time_ns()-start
    ts=process_time_ns()
    factor,visits=trial(n,windows)
    after=process_time_ns()-ts
    if factor is None:
        raise ArithmeticError("complete divisor projection missed")
    ps=process_time_ns()
    ordinary,full=trial(n,[(lo,hi)])
    plain=process_time_ns()-ps
    if ordinary!=factor:
        raise ArithmeticError("ordinary divisor search disagrees")
    counts=count_overlaps(records)
    found=[(a,b,t) for l,u,a,b,t in records if l<=factor<=u]
    row,rtimes=scan(n,bits,"pair_order")
    pair=list(map(str,(factor,n//factor)))
    if row["first"]["pair"]!=pair:
        raise ArithmeticError("known-positive row search disagrees")
    out=dict(n=str(n),bits=bits,range=[str(lo),str(hi)],span=hi-lo+1,pairs=work["pairs"],
             windows=len(records),merged=len(windows),single=counts[1],double=counts[2],
             covered=counts[1]+counts[2],weighted_positions=counts[1]+2*counts[2],
             odd_covered=sum((u+1)//2-l//2 for l,u in windows),factor=pair,witness_windows=found,
             projected=dict(setup_cpu_ns=setup,scan_cpu_ns=after,total_cpu_ns=setup+after,visits=visits),
             full_divisor=dict(cpu_ns=plain,visits=full),
             weight_rows=dict(first_cpu_ns=rtimes[0],full_cpu_ns=rtimes[2],first=row["first"],work=row["work"]))
    if do_secant:
        _,_,width,wheel,_=plan(n,30,max_width=True)
        charts=list(secant_lattices(n,wheel))
        def run(subranges):
            work=Counter()
            splits=[]
            start=process_time_ns()
            for l,u in subranges:
                r=sweep(n,l,u,width,charts,ParallelStrip)
                for k in ("blocks","floor_sums","quadratic_solves"):
                    work[k]+=r[k]
                splits.extend(r["pairs"])
            elapsed=process_time_ns()-start
            if splits!=[pair]:
                raise ArithmeticError("quotient slope scan disagrees")
            return dict(cpu_ns=elapsed,**work)
        out["secant_full"]=run([(lo,hi)])
        out["secant_union"]=run(windows)
        out["secant_union"]["with_window_setup_cpu_ns"]=setup+out["secant_union"]["cpu_ns"]
    out["certificate"]=certificate(n,pair)
    return out


def large(fixture):
    n=int(fixture["n"])
    lo,hi=divisor_range(n,1024)
    b,h,k=bounds(n,1)
    first=window(n,b,h,1,1,1,lo,hi)
    rs,work=make_windows(n,1024,65536)
    combine=merged(rs)
    c=count_overlaps(rs)
    return dict(id=fixture["id"],n=str(n),span=str(hi-lo+1),h=str(h),k_limit=str(k),
                relaxed_k_limit=str((b+1)**2//n),ratio_excess=multiplier_ratio(n,h,1024),
                relaxed_ratio_excess=multiplier_ratio(n,h+1,1024),
                k1_positions=str(first[1]-first[0]+1),k1_odds=str((first[1]+1)//2-first[0]//2),
                prefix=dict(k_cap=65536,pairs=work["pairs"],windows=len(rs),merged=len(combine),
                            covered=str(c[1]+c[2]),double=str(c[2]),odd_positions=str(sum(
                                (u+1)//2-l//2 for l,u in combine))))


def report():
    src=json.loads((ROOT/"research/rectangular-multiplier-products.json").read_text())
    cases=[]
    for bits in (16,20,24):
        for i,old in enumerate([r for r in src["panel"] if r["bits"]==bits][:4]):
            case=compute(int(old["n"]),bits,do_secant=(i==0))
            if case["certificate"]!=old["certificate"]:
                raise ArithmeticError("factor certificate changed")
            cases.append(case)
    return dict(selection="First four inputs of each width from the pre-existing independent rectangular-weight panel. Each first input also gets a complete quotient-strip scan. Single timed runs; checked counts carry across machines.",
                cases=cases,controls=[large(f) for f in src["full_size"]])


if __name__=="__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output",type=Path)
    args=parser.parse_args()
    text=json.dumps(report(),indent=2)+"\n"
    if args.output:
        args.output.write_text(text)
    else:
        print(text,end="")
