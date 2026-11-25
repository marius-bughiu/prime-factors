"""Cover successive odd divisor positions using the same quartic rows for several chunks."""

import argparse
from collections import Counter
import json
from pathlib import Path
from time import process_time

from .norm_auxiliary import integer_roots, reduced_basis
from .quartic_basis_translation import translate, window_layout
from .quartic_divisor_window import checked_height, evaluate, jet_basis


def bernstein(row, left, right):
    """Degree-four Bernstein coefficients with positive per-coordinate scaling."""
    a,b,c,d,e = translate(row,left)
    width = right-left
    b *= width
    c *= width**2
    d *= width**3
    e *= width**4
    return (a,4*a+b,6*a+3*b+c,4*a+3*b+2*c+d,a+b+c+d+e)


def level_range(row, left, right, denominator):
    """Integer levels strictly between the two certified margins on this chunk."""
    numerators = bernstein(row,left,right)
    return (min(-(-a//b) for a,b in zip(numerators,denominator)),
            max(a//b for a,b in zip(numerators,denominator)))


class Chart:
    def __init__(self, n, center, active, work):
        self.n, self.center, self.rows, self.work = n, center, active, work
        self.square = [center**2,4*center,4,0,0]
        self.tables = {}

    def table(self, prime):
        """For each quotient residue, give the bit set of permissible x residues.

        Only primes not dividing N are used, hence a genuine d is invertible.
        """
        if prime in self.tables:
            return self.tables[prime]
        mask = 0
        table = [[0]*prime for _ in self.rows]
        residues = [[a%prime for a in row] for row in self.rows]
        for r in range(prime):
            d = (self.center+2*r)%prime
            if not d:
                continue
            mask |= 1<<r
            inverse = pow(d*d,-1,prime)
            self.work['residue_inversions'] += 1
            for masks,row in zip(table,residues):
                masks[evaluate(row,r)*inverse%prime] |= 1<<r
                self.work['residue_evaluations'] += 1
        self.tables[prime] = mask,table
        return mask,table

    def check(self, left, right, level_cap, hits, *, save_cert=False):
        """Certify or exhaust a chunk. Failure leaves its entire interval unconsumed."""
        work = self.work
        denominator = bernstein(self.square,left,right)
        if min(denominator)<=0:
            raise ArithmeticError('expected positive denominator Bernstein coefficients')
        work['chunk_attempts'] += 1
        work['denominator_bounds'] += 1
        bounds = []
        def witness(indices, modulus):
            if not save_cert:
                return None
            return dict(center=self.center,anchor=(self.n-self.center)//2,left=left,right=right,
                        modulus=modulus,rows=[dict(coefficients=self.rows[i],low=bounds[i][0],
                                                   high=bounds[i][1]) for i in indices])
        for i,row in enumerate(self.rows):
            low,high = level_range(row,left,right,denominator)
            work['row_bounds'] += 1
            bounds.append((low,high))
            if low>high:
                work['empty_level_chunks'] += 1
                return True,witness([i],None)
        surviving_masks = []
        for prime in (2,3,5,7,11):
            if self.n%prime == 0 or all(hi-lo+1>=prime for lo,hi in bounds):
                continue
            mask, tables = self.table(prime)
            used = []
            for i,((lo,hi),table) in enumerate(zip(bounds,tables)):
                if hi-lo+1>=prime:
                    continue
                allowed = 0
                for k in range(lo,hi+1):
                    allowed |= table[k%prime]
                    work['mask_lookups'] += 1
                if mask & allowed != mask:
                    if allowed:
                        used.append(i)
                    else:
                        used = [i]
                    mask &= allowed
                if not mask:
                    work['modular_chunks'] += 1
                    if len(used)>1:
                        work['multirow_modular_chunks'] += 1
                    return True,witness(used,prime)
            surviving_masks.append((prime,mask,tables))
        # A row equal to an integer multiple of d² is uninformative in root isolation.
        options = sorted((hi-lo+1,i) for i,(lo,hi) in enumerate(bounds) if hi-lo+1<=level_cap)
        for _,i in options:
            row = self.rows[i]
            lo,hi = bounds[i]
            if all(a*self.square[0]==row[0]*b for a,b in zip(row,self.square)):
                continue
            before = work['root_polynomials']
            for k in range(lo,hi+1):
                for prime,mask,tables in surviving_masks:
                    work['mask_lookups'] += 1
                    if not (mask & tables[i][k%prime]):
                        work['root_levels_sieved'] += 1
                        break
                else:
                    polynomial = [a-k*b for a,b in zip(row,self.square)]
                    work['root_polynomials'] += 1
                    for x in integer_roots(polynomial,left,right,work):
                        work['divisor_tests'] += 1
                        d = self.center+2*x
                        if self.n%d == 0:
                            hits.add(d)
            if before == work['root_polynomials']:
                work['sieved_level_chunks'] += 1
            else:
                work['root_checked_chunks'] += 1
            return True,None
        work['failed_chunks'] += 1
        return False,None


def search(n, *, full, max_reductions, mode='joint', level_cap=3, chunks_per_basis=32,
           sample_certificate=False):
    """Progress from the lower band endpoint or the published quartile, under a reduction cap.

    Each chunk contains up to 2W+1 odd candidates. A failed continuation starts a
    new reduction at that same chunk. A failed first chunk stops with the suffix open.
    """
    if (mode not in ('joint','single') or max_reductions is None or max_reductions<0
            or level_cap<1 or chunks_per_basis<1):
        raise ValueError('expected a bounded reduction budget, positive caps and known mode')
    start_cpu = process_time()
    layout = window_layout(n,full=full,blocks=0)
    w, size = layout['radius'],2*layout['radius']+1
    first = layout['first_center']-2*w
    cursor, last = first, layout['last_odd']
    prefix = (first-layout['first_odd'])//2
    scales = [w**i for i in range(5)]
    work = Counter({key:0 for key in (
        'lll_calls','lll_swaps','lll_reductions','translations','jet_checks','chunk_attempts',
        'denominator_bounds','row_bounds','residue_evaluations','residue_inversions','mask_lookups',
        'empty_level_chunks','modular_chunks','multirow_modular_chunks','sieved_level_chunks','root_checked_chunks',
        'root_levels_sieved','root_polynomials','integer_root_nodes','divisor_tests','failed_chunks',
        'covered_chunks')})
    previous, previous_center = None,None
    hits = set()
    certificate = None
    best_certificate = ()
    stalled = False
    while cursor<=last and work['lll_calls']<max_reductions:
        center = cursor+2*w
        anchor = (n-center)//2
        if previous is None:
            basis = jet_basis(n,anchor)
        else:
            shift = (center-previous_center)//2
            basis = [translate(row,shift) for row in previous]
            work['translations'] += 1
        scaled = [[a*z for a,z in zip(row,scales)] for row in basis]
        _, rows = reduced_basis(scaled,work,initial_coefficients=basis)
        heights = [checked_height(n,anchor,w,row) for row in rows]
        work['jet_checks'] += 2*len(rows)
        order = sorted(range(5),key=heights.__getitem__)
        if mode=='single':
            order = order[:1]
        chart = Chart(n,center,[rows[i] for i in order],work)
        before = cursor
        for _ in range(chunks_per_basis):
            if cursor>last:
                break
            left = (cursor-center)//2
            right = min(left+size-1,(last-center)//2)
            ok, cert = chart.check(left,right,level_cap,hits,save_cert=sample_certificate)
            if not ok:
                break
            if cert:
                multi = len(cert['rows'])>1
                levels = any(row['low']<row['high'] for row in cert['rows'])
                # Prefer a genuinely multilevel, multirow receipt outside the initial chunk.
                score = (multi and levels and left>w, multi and levels, levels and left>w,
                         multi and left>w, multi, left>w)
                if score>best_certificate:
                    best_certificate, certificate = score, cert
            work['covered_chunks'] += 1
            cursor = center+2*(right+1)
        previous, previous_center = rows,center
        if cursor==before:
            stalled = True
            break
    suffix = max(0,(last-cursor)//2+1)
    visited = (cursor-first)//2
    return dict(radius=w,mode=mode,max_reductions=max_reductions,level_cap=level_cap,
                chunks_per_basis=chunks_per_basis,first_odd=layout['first_odd'],last_odd=last,
                start_odd=first,covered_odd_positions=visited,unvisited_prefix_odd=prefix,
                unvisited_suffix_odd=suffix,unvisited_odd_positions=prefix+suffix,
                fixed_window_count=layout['total_blocks'],schedule_exhausted=prefix+suffix==0,
                stalled=stalled,work=dict(work),divisors=sorted(hits),unsplit_n=None if hits else n,
                sample_certificate=certificate,cpu_seconds=process_time()-start_cpu)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--case',required=True,choices=('49','fresh-2048','crossed-2048'))
    parser.add_argument('--max-reductions',type=int)
    parser.add_argument('--mode',choices=('joint','single'),default='joint')
    parser.add_argument('--sample-certificate',action='store_true')
    args = parser.parse_args()
    fixture = Path(__file__).resolve().parents[1]/'benchmarks/quartic-basis-translation.json'
    row = next(r for r in json.loads(fixture.read_text())
               if r['id']=='quartic-basis-translation-'+args.case)
    cap = row['blocks'] if args.max_reductions is None else args.max_reductions
    if not 0<=cap<=row['blocks']:
        parser.error('budget outside the published schedule')
    print(json.dumps(search(int(row['n']),full=row['full'],max_reductions=cap,mode=args.mode,
                            sample_certificate=args.sample_certificate),indent=2))
