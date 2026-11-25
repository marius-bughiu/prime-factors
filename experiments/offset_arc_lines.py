"""Cover a signed factor-gap band by parallel integer lines and solve each line exactly."""

import argparse
import json
from collections import Counter
from dataclasses import dataclass
from math import gcd, isqrt

from experiments.continued_square import convergents
from experiments.modular_hyperbola import Work, floor_sum, report_progression
from experiments.offset_coordinate_gaps import (
    chart_window, coordinate_pairs, gap_band, lifted_classes, residues, subintervals,
)
from experiments.offset_gap_lift import choose_divisor
from experiments.offset_winner_window import bounds


@dataclass(frozen=True)
class Strip:
    """Integer points (i,y) with 0<=i<=width and low<=den*y-slope*i<=high."""
    width: int
    slope: int
    den: int
    low: int
    high: int


def projection(strip, work, limit=None):
    """Choose a primitive direction and bound the level count for any direction."""
    width, den = strip.width, strip.den
    height = strip.high-strip.low
    if limit is None:
        limit = max(1,isqrt(width*den//height)) if height else den
    # At least the first convergent has denominator one, including negative slopes.
    for numerator, denominator in convergents(strip.slope, den):
        work['convergent_steps'] += 1
        if denominator > limit:
            break
        p,q = numerator,denominator
    error = q*strip.slope-p*den
    first = (q*strip.low+min(0,error*width)+den-1)//den
    last = (q*strip.high+max(0,error*width))//den
    lower = min((q*height+abs(error)*width)//den, width//q)
    if error:
        lower = min(lower,height//abs(error))
    return p,q,first,last,lower


def line_roots(trace, step, product, F, G, q, work):
    """Integer indices where (F+G*i)/q lies on the conic. May include a negative height."""
    quad = G*G-(q*step)**2
    center = G*F-q*q*trace*step
    if not quad:
        work['linear_equations'] += 1
        # When center also vanishes the residual equals q²*product > 0.
        const = F*F-q*q*(trace*trace-product)
        if center and const%(2*center) == 0:
            yield -const//(2*center)
        return
    x = G*trace-step*F
    disc = x*x-product*quad
    if disc < 0:
        return
    work['discriminant_roots'] += 1
    root = isqrt(disc)
    if root*root == disc:
        for signed in ((root,-root) if root else (0,)):
            i, rem = divmod(q*signed-center,quad)
            if not rem:
                yield i


def projected_hits(params, strip, direction, count, work):
    trace,step,product,r,beta,modulus,sign = params
    p,q,first,_,_ = direction
    G = sign*beta*q+modulus*p
    for level in range(first,first+count):
        F = sign*r*q+modulus*level
        for i in line_roots(trace,step,product,F,G,q,work):
            if 0 <= i <= strip.width and (level+p*i)%q == 0:
                height = (F+G*i)//q
                if height >= 0:
                    yield i,sign*height


def narrow_indices(strip, work):
    for left,right in residues(strip.low,strip.high,strip.den):
        for i,_ in report_progression(-strip.slope,0,strip.den,0,strip.width+1,left,right,work):
            yield i


def direct_hits(params, strip, count, narrow, work):
    trace,step,product,r,beta,modulus,sign = params
    if narrow:
        for _,i in zip(range(count),narrow_indices(strip,work)):
            y = (strip.slope*i+strip.low+strip.den-1)//strip.den
            height = sign*(r+beta*i)+modulus*y
            if height >= 0 and height*height == (trace+step*i)**2-product:
                yield i,sign*height
    else:
        for i in range(count):
            delta = (trace+step*i)**2-product
            height = isqrt(delta)
            if height*height == delta and (sign*height-r-beta*i)%modulus == 0:
                yield i,sign*height


def scan_strip(params, strip, hybrid, budget, work, sums):
    direction = projection(strip,work)
    _,_,first,last,lower = direction
    levels = max(0,last-first+1)
    work['oriented_bands'] += 1
    work['projection_lower'] += lower
    work['projected_levels'] += levels
    mode = 'lines'
    cost = levels
    if hybrid and levels:
        narrow = strip.high-strip.low+1 < strip.den
        direct_cost = strip.width+1
        if narrow:
            sums.range_counts += 1
            direct_cost = (floor_sum(direct_cost,strip.den,strip.slope,strip.high,sums)
                           -floor_sum(direct_cost,strip.den,strip.slope,strip.low-1,sums))
        if direct_cost <= levels:
            mode = 'points' if narrow else 'vertical'
            cost = direct_cost
    used = min(cost, budget-work['tests'])
    work['scheduled_'+mode] += cost
    work['tested_'+mode] += used
    work['tests'] += used
    if mode == 'lines':
        return projected_hits(params,strip,direction,used,work)
    return direct_hits(params,strip,used,mode=='points',sums)


def record_factor(hits, n, s, v, shift, total, z):
    """Recover the two factors with their prescribed orientation and require exact division."""
    k = s*v
    j = total-shift
    p,pr = divmod(total+z,2*s*s)
    q,qr = divmod(total-z,2*v*v)
    if not pr and not qr and gcd(j,k)==1 and 1<p<q and p*q==n:
        hits.add((j,k,str(p),str(q)))


def search(n, parts, *, max_vectors, max_tests, all_vectors=False, hybrid=True,
           lift_cap=8, unit_square=1, trace_units=True):
    if (n < 5 or n%2 == 0 or isqrt(n)**2 == n or min(parts,max_vectors,lift_cap)<1 or max_tests<0
            or unit_square not in (1,8,24) or trace_units and unit_square!=1):
        raise ValueError('expected an odd nonsquare and valid budgets and lift settings')
    box = bounds(n)
    keys = ('vectors classes bands oriented_bands bound_roots convergent_steps projection_lower '
            'projected_levels scheduled_lines scheduled_points scheduled_vertical tested_lines '
            'tested_points tested_vertical tests linear_equations discriminant_roots').split()
    work = dict.fromkeys(keys,0)
    sums = Work()
    setup = Counter()
    hits = set()
    exhausted = False
    for s,v in coordinate_pairs(box,all_vectors):
        if work['vectors'] == max_vectors:
            break
        k = s*v
        shift,first,length = chart_window(n,box,s,v)
        work['vectors'] += 1
        work['bound_roots'] += 1
        product = 4*n*k*k
        divisor = choose_divisor(k,lift_cap,setup)
        classes = lifted_classes(n,box['T'],s,v,first,length,divisor,False,unit_square,trace_units,setup)
        work['classes'] += len(classes)
        for start,stride,size,base,beta,modulus in classes:
            step = 2*stride
            for left,right in subintervals(size,parts):
                width = right-left-1
                trace = shift+first+2*start+step*left
                r = (base+beta*left)%modulus
                band,roots = gap_band(trace,step*width,product,True)
                a,b,low,high = band
                work['bands'] += 1
                work['bound_roots'] += roots
                if high < low:
                    continue
                for sign in (-1,1):
                    strip = Strip(width,a*step-b*sign*beta,b*modulus,low-b*sign*r,high-b*sign*r)
                    params = trace,step,product,r,beta,modulus,sign
                    for i,z in scan_strip(params,strip,hybrid,max_tests,work,sums):
                        record_factor(hits,n,s,v,shift,trace+step*i,z)
    else:
        exhausted = True
    scheduled = sum(work['scheduled_'+key] for key in ('lines','points','vertical'))
    return dict(**work, scheduled=scheduled, remaining_tests=scheduled-work['tests'],
                range_counts=sums.range_counts, floor_sum_steps=sums.euclidean_steps, setup=dict(setup),
                schedule_exhausted=exhausted, all_vectors=all_vectors, max_vectors=max_vectors,
                max_tests=max_tests, parts=parts, hybrid=hybrid, lift_cap=lift_cap, unit_square=unit_square,
                trace_units=trace_units, hits=[list(row) for row in sorted(hits)])


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('n',type=int)
    parser.add_argument('--parts',type=int,default=16)
    parser.add_argument('--max-vectors',type=int,default=4)
    parser.add_argument('--max-tests',type=int,default=3)
    parser.add_argument('--all-vectors',action='store_true')
    parser.add_argument('--lines-only',action='store_true')
    args = parser.parse_args()
    print(json.dumps(search(args.n,args.parts,max_vectors=args.max_vectors,max_tests=args.max_tests,
                            all_vectors=args.all_vectors,hybrid=not args.lines_only),indent=2))
