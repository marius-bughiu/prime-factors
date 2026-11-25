"""Count exact weighted-trace giant records and sparse baby entries, without prime labels."""
from bisect import bisect_left
from itertools import product
from math import gcd, isqrt, prod

from .weighted_windows import weighted_window


def local_runs(ell):
    """A first longest cyclic run of nonsquares of x²-c, for every nonzero c."""
    squares = {x*x % ell for x in range(ell)}
    runs = {}
    for c in range(1, ell):
        best = streak = start = 0
        for x in range(2*ell):
            if (x*x-c) % ell in squares:
                streak = 0
            else:
                streak += 1
                if streak > best:
                    best, start = streak, (x+1-streak) % ell
        runs[c] = best, start
    return runs


class Wheel:
    def __init__(self, primes, *, runs=True, max_period=1000000, max_run_work=1000000):
        self.primes = tuple(primes)
        if any(not isinstance(p,int) or p<5 for p in self.primes) or len(set(self.primes)) != len(self.primes):
            raise ValueError('expected distinct primes at least five')
        if sum(2*p*(p-1) for p in self.primes) > max_run_work:
            raise ValueError('local run census exceeds the explicit work budget')
        self.period = prod(self.primes)
        if self.period > max_period:
            raise ValueError('period exceeds the explicit residue-table budget')
        if any(any(p%i==0 for i in range(2,isqrt(p)+1)) for p in self.primes):
            raise ValueError('expected distinct primes at least five')
        self.holes = []
        self.starts = []
        self.crt = []
        for ell in self.primes:
            local = local_runs(ell)
            self.holes.append(min(v[0] for v in local.values()) if runs else 1)
            self.starts.append({c: v[1] for c, v in local.items()})
            chunk = self.period//ell
            self.crt.append(chunk*pow(chunk,-1,ell))
        self.allowed = [i for i in range(self.period)
                        if all(i%p >= k for p,k in zip(self.primes,self.holes))]

    def prefix(self, end):
        periods, tail = divmod(end,self.period)
        return periods*len(self.allowed) + bisect_left(self.allowed,tail)

    def phases(self, a, b, n, step, first):
        """Return j in [0,D) such that the giant start is first-step*j."""
        choices = []
        for ell,k,starts,weight in zip(self.primes,self.holes,self.starts,self.crt):
            inverse = pow(step,-1,ell)
            c = 4*a*b*n*inverse*inverse % ell
            z_values = (starts[c],) if c else ((0,) if k == 1 else (0,k))
            choices.append([weight*(first*inverse-z) for z in z_values])
        return [sum(coords)%self.period for coords in product(*choices)]

    def sparse_records(self, span, length, phase):
        """Exact nonempty giant blocks after padding on each end."""
        if span % self.period or span < 1:
            raise ValueError('span must be a positive multiple of the common period')
        if not length:
            return 0
        stop = phase+length
        last = (stop-1)//span
        if not last:
            return int(self.prefix(stop)>self.prefix(phase))
        first_used = self.prefix(span)>self.prefix(phase)
        last_used = self.prefix(stop)>self.prefix(last*span)
        return last-1 + first_used + last_used

    def lane_records(self, a, b, n, step, first, length, babies):
        """Exact minimum using one arithmetic-progression giant per residue lane."""
        total = 1
        local = []
        for ell in self.primes:
            c = 4*a*b*n % ell
            if c:
                legendre = 1 if pow(c,(ell-1)//2,ell) == 1 else -1
                total *= (ell+legendre)//2
            else:
                total *= ell-1
            local.append((ell,c))
        count, tail = divmod(length, self.period*babies)
        if tail >= self.period:
            return (count+1)*total
        kept = 0
        for i in range(tail):
            t = first+step*i
            if all((pow((t*t-c)%ell,(ell-1)//2,ell) != ell-1 if c else t%ell != 0)
                   for ell,c in local):
                kept += 1
        return count*total+kept


def census(n, k, dense_babies, wheel, span, *, max_slopes):
    """Compare complete or slope-capped schedules without computing a factor."""
    if gcd(n,24*wheel.period) != 1:
        raise ValueError('expected N coprime to the common modulus')
    if k < 1 or min(dense_babies,span) < 1 or max_slopes < 0:
        raise ValueError('expected positive table sizes and nonnegative slope cap')
    if span % wheel.period:
        raise ValueError('span must be a multiple of the common period')
    result = dict(slopes=0, covered_slopes=0, dense_giants=0, lane_giants=0,
                  min_lane_or_dense=0, sparse_giants=0, phase_schedules=0,
                  sparse_babies=wheel.prefix(span), span=span, complete=True)
    for b in range(1,k+1):
        for a in range(b,2*b+1):
            if gcd(a,b) != 1:
                continue
            if result['slopes'] >= max_slopes:
                return dict(result, complete=False)
            result['slopes'] += 1
            low, high = weighted_window(n,k,a,b)
            c = a+b*n
            step = gcd(24,2*c)
            first = low + (c-low)%step
            if first > high:
                continue
            result['covered_slopes'] += 1
            length = (high-first)//step+1
            dense = (length+dense_babies-1)//dense_babies
            result['dense_giants'] += dense
            lanes = wheel.lane_records(a,b,n,step,first,length,dense_babies)
            result['lane_giants'] += lanes
            result['min_lane_or_dense'] += min(lanes,dense)
            phases = wheel.phases(a,b,n,step,first)
            result['phase_schedules'] += len(phases)
            result['sparse_giants'] += sum(wheel.sparse_records(span,length,j) for j in phases)
    return result


if __name__ == '__main__':
    import json
    from pathlib import Path

    controls = json.loads((Path(__file__).resolve().parents[1]/'benchmarks'/'weighted-stride.json').read_text())
    comparisons = []
    for case in controls:
        n, k, m = int(case['n']), case['k'], case['baby_steps']
        rows = []
        for primes in [(5,), (5,7), (5,13), (5,7,11)]:
            wheel = Wheel(primes)
            if len(wheel.allowed) > m:
                continue
            span = wheel.period*(m//len(wheel.allowed))
            counts = census(n,k,m,wheel,span,max_slopes=case['max_slopes'])
            rows.append(dict(primes=list(primes), holes=wheel.holes, **counts))
        comparisons.append(dict(id=case['id'], n=str(n), k=k, dense_babies=m, cases=rows))
    print(json.dumps(comparisons, indent=2))
