"""Count and test short factor-curve arcs with at most one line per sign."""

import argparse
import json
from collections import Counter
from math import isqrt

from experiments.offset_arc_lines import Strip, projected_hits, projection, record_factor
from experiments.offset_coordinate_gaps import chart_window, coordinate_pairs, lifted_classes
from experiments.offset_gap_lift import choose_divisor
from experiments.offset_winner_window import bounds


def cube_root(n):
    """Integer cube root by monotone Newton iteration from a binary upper bound."""
    if n < 2:
        return n
    root = 1 << ((n.bit_length()+2)//3)
    while True:
        smaller = (2*root+n//(root*root))//3
        if smaller >= root:
            return root
        root = smaller


def epochs(trace, step, length, product, modulus, work):
    """Partition a class into dyadic epochs, each with a single safe chunk size."""
    if length:
        yield 0,1,1
    first = 1
    while first < length:
        stop = min(2*first,length)
        height = isqrt((trace+first*step)**2-product)
        work['epoch_roots'] += 1
        # The one-line conditions become easier as the floor of the root grows.
        radicand = modulus * height**3 // (4*(product+2*height)*step**2)
        width = min(modulus//8, cube_root(radicand))
        work['width_cube_roots'] += 1
        yield first,stop,width+1
        first = stop


def arc_hits(trace, step, width, product, residue, slope, modulus, work):
    delta = trace*trace-product
    height = isqrt(delta)
    work['arc_roots'] += 1
    if not width:
        work['singletons_tested'] += 1
        if height*height == delta:
            for z in {height,-height}:
                if (z-residue)%modulus == 0:
                    yield 0,z
        return
    error = delta-height*height
    bend = (product+error)*(step*width)**2//(2*height**2)
    for sign in (-1,1):
        strip = Strip(width,trace*step-height*sign*slope,height*modulus,
                      height*(height-sign*residue)-bend,height*(height+1-sign*residue))
        assert 4*width*(strip.high-strip.low) <= strip.den
        direction = projection(strip,work,limit=2*width)
        _,_,first,last,_ = direction
        levels = max(0,last-first+1)
        assert levels <= 1
        work['line_equations'] += levels
        params = trace,step,product,residue,slope,modulus,sign
        yield from projected_hits(params,strip,direction,levels,work)


def shifted_bounds(n):
    """Use the integer preceding floor(sqrt(n)) to keep the remainder comparable to sqrt(n)."""
    root = isqrt(n)
    t = root-1
    h = n-t*t
    j = isqrt(4*h//3)
    bits = (n.bit_length()+1)//2
    cap = (1 << bits)-1
    return dict(T=t,h=h,J=j,K=t*j//h+1,L=max(1 << (bits-1),(n+cap-1)//cap))


def search(n, *, max_vectors, max_arcs, all_vectors=False, lift_cap=8, unit_square=1,
           trace_units=True, shifted_base=False):
    if (n<5 or n%2==0 or isqrt(n)**2==n or min(max_vectors,lift_cap)<1 or max_arcs<0
            or unit_square not in (1,8,24) or trace_units and unit_square!=1):
        raise ValueError('expected an odd nonsquare and valid budgets and lift settings')
    box = shifted_bounds(n) if shifted_base else bounds(n)
    keys = ('vectors classes eligible_positions epochs epoch_roots width_cube_roots planned_arcs '
            'planned_singletons visited_arcs singletons_tested arc_roots line_equations '
            'linear_equations discriminant_roots convergent_steps').split()
    work = dict.fromkeys(keys,0)
    setup = Counter()
    hits = set()
    exhausted = False
    for s,v in coordinate_pairs(box,all_vectors):
        if work['vectors']==max_vectors:
            break
        work['vectors'] += 1
        k = s*v
        product = 4*n*k*k
        shift,first,length = chart_window(n,box,s,v)
        divisor = choose_divisor(k,lift_cap,setup)
        classes = lifted_classes(n,box['T'],s,v,first,length,divisor,False,unit_square,trace_units,setup)
        work['classes'] += len(classes)
        for start,stride,size,base,beta,modulus in classes:
            trace, step = shift+first+2*start, 2*stride
            work['eligible_positions'] += size
            for begin,end,chunk in epochs(trace,step,size,product,modulus,work):
                count = (end-begin+chunk-1)//chunk
                work['epochs'] += 1
                work['planned_arcs'] += count
                work['planned_singletons'] += count if chunk==1 else int((end-begin)%chunk==1)
                used = min(count,max_arcs-work['visited_arcs'])
                work['visited_arcs'] += used
                for index in range(used):
                    left = begin+index*chunk
                    width = min(end-left,chunk)-1
                    S = trace+step*left
                    r = (base+beta*left)%modulus
                    for i,z in arc_hits(S,step,width,product,r,beta,modulus,work):
                        record_factor(hits,n,s,v,shift,S+step*i,z)
    else:
        exhausted = True
    if shifted_base:
        work.update(shifted_base=True, integer_base=str(box['T']), base_remainder=str(box['h']),
                    max_offset=str(box['J']), max_multiplier=str(box['K']))
    return dict(**work, equation_upper=2*work['planned_arcs']-work['planned_singletons'],
                remaining_arcs=work['planned_arcs']-work['visited_arcs'], setup=dict(setup),
                schedule_exhausted=exhausted, all_vectors=all_vectors, max_vectors=max_vectors,
                max_arcs=max_arcs, lift_cap=lift_cap, unit_square=unit_square, trace_units=trace_units,
                hits=[list(row) for row in sorted(hits)])


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('n',type=int)
    parser.add_argument('--max-vectors',type=int,default=4)
    parser.add_argument('--max-arcs',type=int,default=3)
    parser.add_argument('--all-vectors',action='store_true')
    parser.add_argument('--shifted-base',action='store_true',help='use the integer just below the floor square root')
    parser.add_argument('--plain',action='store_true',help='use the original signed gap residue at modulus 4k²')
    args = parser.parse_args()
    print(json.dumps(search(args.n,max_vectors=args.max_vectors,max_arcs=args.max_arcs,
                            all_vectors=args.all_vectors,shifted_base=args.shifted_base,
                            lift_cap=1 if args.plain else 8,trace_units=not args.plain),indent=2))
