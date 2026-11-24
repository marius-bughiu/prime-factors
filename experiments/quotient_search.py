"""Exact product-error moments in a rational strip around xy=N.

The complete balanced search uses only N. --method plain counts and bisects
every occupied strip; line and errors use exact moments to stop earlier.
Use --self-test for bounded direct checks of the weighted floor recurrence.
"""
import argparse
import json
from dataclasses import asdict, dataclass
from math import comb, gcd, isqrt

if __package__:
    from .modular_hyperbola import floor_sum
else:
    from modular_hyperbola import floor_sum


@dataclass
class Work:
    blocks: int = 0
    strip_counts: int = 0
    euclidean_steps: int = 0
    moment_states: int = 0
    initial_strip_points: int = 0
    empty_strips: int = 0
    collinear_blocks: int = 0
    collinear_beyond_area: int = 0
    quadratic_solves: int = 0
    sparse_exclusions: int = 0
    cauchy_exclusions: int = 0
    sparse_recoveries: int = 0
    bisected: int = 0
    tested_columns: int = 0


def signed_choose(n, k):
    return comb(n, k) if n >= 0 else (-1)**k*comb(k-1-n, k)


def coefficients(values):
    """Newton coefficients of a polynomial from consecutive values at zero."""
    result = []
    while values:
        result.append(values[0])
        values = [b-a for a, b in zip(values, values[1:])]
    return result


class Strip:
    def __init__(self, n, lo, hi, work, lattice=(1, 0, 1, 0, 0)):
        self.n, self.lo, self.hi = n, lo, hi
        step, residue, self.ymod, self.shift, self.slope = lattice
        self.step = step
        self.x0 = hi-(hi-residue)%step
        self.length = max(0, (self.x0-lo)//step+1)
        self.work = work
        # x=x0-step*i, y=shift+slope*x+ymod*v. Bound integer v.
        offset = self.shift+self.slope*self.x0
        self.upper = (lo*hi*self.ymod, step*(n+self.slope*lo*hi),
                      n*(lo+hi-self.x0)-offset*lo*hi)
        self.lower = (lo*lo*self.ymod, step*(n+self.slope*lo*lo),
                      n*(2*lo-self.x0)-offset*lo*lo-1)
        self.memo = {}

    def count(self):
        self.work.strip_counts += 1
        return (floor_sum(self.length, *self.upper, self.work)
                - floor_sum(self.length, *self.lower, self.work))

    def basis(self, length, mod, a, b, r, s):
        key = (length, mod, a, b, r, s)
        if key not in self.memo:
            self.memo[key] = self._basis(*key)
        return self.memo[key]

    def _basis(self, length, mod, a, b, r, s):
        """Sum binom(i,r) binom(floor((ai+b)/mod),s) by Euclidean transpose."""
        self.work.moment_states += 1
        if not length:
            return 0
        if s == 0:
            return comb(length, r+1)
        qa, aa = divmod(a, mod)
        qb, bb = divmod(b, mod)
        if qa or qb:
            value = 0
            for j in range(s+1):
                cc = coefficients([comb(i, r)*signed_choose(qa*i+qb, s-j)
                                   for i in range(r+s-j+1)])
                for k, c in enumerate(cc):
                    if c:
                        value += c*self.basis(length, mod, aa, bb, k, j)
            return value
        high = (a*(length-1)+b)//mod
        if high == 0:
            return 0
        return (comb(length, r+1)*comb(high, s)
                - self.basis(high, a, mod, mod-b+a-1, s-1, r+1))

    def raw_moment(self, r, s):
        """Exact sum of x^r v^s over all enclosed integer points."""
        cx = coefficients([(self.x0-self.step*i)**r for i in range(r+1)])
        cy = coefficients([sum(j**s for j in range(1, y+1)) for y in range(s+2)])
        return sum(a*b*(self.basis(self.length, *self.upper, i, j)
                        - self.basis(self.length, *self.lower, i, j))
                   for i, a in enumerate(cx) if a for j, b in enumerate(cy) if b)

    def moment(self, r, s):
        if self.slope == self.shift == 0 and self.ymod == 1:
            return self.raw_moment(r, s)
        return sum(comb(s,j)*comb(s-j,k)*self.ymod**j*self.slope**k
                   *self.shift**(s-j-k)*self.raw_moment(r+k,j)
                   for j in range(s+1) for k in range(s-j+1))

    def errors(self, degree, extra_x=0):
        return sum(comb(degree, j)*(-self.n)**(degree-j)*self.moment(j+extra_x, j)
                   for j in range(degree+1))


def sparse_root(strip, count):
    """Newton identities, then weight by the polynomial vanishing on nonzero errors."""
    powers = [count]+[strip.errors(j) for j in range(1, count+1)]
    # Descending monic coefficients of the polynomial of all product errors.
    poly = [1]
    for i in range(1, count+1):
        poly.append(-sum(poly[i-j]*powers[j] for j in range(1, i+1))//i)
    if poly[-1]:
        return "empty", None
    while poly[-1] == 0:
        poly.pop()
    if len(poly) != count:
        return "multiple", None
    weighted = sum(a*strip.errors(len(poly)-1-i, 1) for i, a in enumerate(poly))
    return "factor", weighted//poly[-1]


def line_factors(box, count):
    """Return all divisors in a collinear strip, or None for a rank-two cloud."""
    sx = box.moment(1, 0)
    vx = count*box.moment(2, 0)-sx*sx if count > 1 else 0
    if vx == 0:
        candidates = {sx//count}
    else:
        sy = box.moment(0, 1)
        cov = count*box.moment(1, 1)-sx*sy
        vy = count*box.moment(0, 2)-sy*sy
        if vx*vy != cov*cov:
            return None
        a, b, c = count*cov, vx*sy-cov*sx, -count*vx*box.n
        box.work.quadratic_solves += 1
        if a == 0:
            candidates = {-c//b} if b and (-c)%b == 0 else set()
        else:
            disc = b*b-4*a*c
            root = isqrt(disc) if disc >= 0 else -1
            candidates = {t//(2*a) for t in (-b-root, -b+root)
                          if root >= 0 and root*root == disc and t%(2*a) == 0}
    box.work.collinear_blocks += 1
    if count >= 3 and box.n*(box.hi-box.lo)**3 >= box.step*box.ymod*box.lo**2*box.hi:
        box.work.collinear_beyond_area += 1
    return sorted(x for x in candidates if box.lo <= x <= box.hi
                  and (x-box.x0)%box.step == 0 and box.n%x == 0
                  and (box.n//x-box.slope*x-box.shift)%box.ymod == 0)


def wheel_lattices(n, wheel):
    if wheel == 1:
        yield (1, 0, 1, 0, 0)
        return
    square = wheel*wheel
    for a in range(1, wheel):
        if gcd(a, wheel) == 1:
            i = pow(a, -1, square)
            d = -(n*i*i % square)
            c = (n*i-d*a) % square - square
            yield wheel, a, square, c, d


def search(n, width=None, degree=2, method="line", wheel=1):
    if n < 9 or (width is not None and width < 1) or wheel < 1 or degree not in range(1, 4) or method not in ("line", "errors", "plain"):
        raise ValueError("require N >= 9, positive wheel and width, and degree in 1..3")
    requested_wheel, setup_divisor = wheel, None
    # A shared divisor can lie outside the balanced band. Report it separately,
    # and remove all shared primes so that the subsequent band scan is complete.
    common = gcd(n, wheel)
    while common > 1:
        if common < n and setup_divisor is None:
            setup_divisor = str(common)
        wheel //= common
        common = gcd(n, wheel)
    lo, hi = max(2, isqrt((n-1)//2)+1), isqrt(n)
    work, pairs = Work(), []
    def visit(left, right, lattice, initial=False):
        box = Strip(n, left, right, work, lattice)
        c = box.count()
        if initial:
            work.blocks += 1
            work.initial_strip_points += c
        if not c:
            work.empty_strips += 1
            return
        if left == right:
            work.tested_columns += 1
            if n % left == 0:
                pairs.append((left, n//left))
            return
        if method == "line":
            factors = line_factors(box, c)
            if factors is not None:
                pairs.extend((x, n//x) for x in factors)
                return
        elif method == "errors" and c <= degree:
            status, x = sparse_root(box, c)
            if status == "empty":
                work.sparse_exclusions += 1
                return
            if status == "factor":
                if not left <= x <= right or n % x:
                    raise ArithmeticError("invalid reconstructed factor")
                work.sparse_recoveries += 1
                pairs.append((x, n//x))
                return
        elif method == "errors" and degree >= 2 and box.errors(1)**2 > (c-1)*box.errors(2):
            work.cauchy_exclusions += 1
            return
        work.bisected += 1
        middle = (left+right)//2
        visit(left, middle, lattice)
        visit(middle+1, right, lattice)
    # One conservative width for the whole balanced band. The -1 makes
    # N*(width-1)^3 < wheel^3*lo^3 exact at integer cube boundaries.
    if width is None:
        low, high = 0, hi-lo+1
        while low < high:
            mid = (low+high+1)//2
            if n*mid**3 < (wheel*lo)**3:
                low = mid
            else:
                high = mid-1
        width = 1+low
    classes = 0
    for lattice in wheel_lattices(n, wheel):
        classes += 1
        for left in range(lo, hi+1, width):
            visit(left, min(left+width-1, hi), lattice, True)
    pairs.sort()
    return dict(n=str(n), width=width, wheel=wheel, requested_wheel=requested_wheel,
                setup_divisor=setup_divisor, residue_classes=classes, method=method, degree=degree if method == "errors" else None, balanced_integers=hi-lo+1,
                pairs=[[str(x), str(y)] for x, y in pairs], **asdict(work))


def self_test():
    incidental = search(51, wheel=18)
    assert incidental["setup_divisor"] == "3" and incidental["wheel"] == 2
    assert incidental["pairs"] == []
    assert search(77, wheel=77)["pairs"] == [["7", "11"]]
    for n in range(21, 155):
        first, last = isqrt((n-1)//2)+1, isqrt(n)
        for lo in range(first, last+1):
            box = Strip(n, lo, last, Work())
            direct = [(x, y) for x in range(lo, last+1)
                      for y in range((n*(2*lo-x)-1)//(lo*lo)+1,
                                     n*(lo+last-x)//(lo*last)+1)]
            assert box.count() == len(direct)
            for j in range(4):
                assert box.errors(j) == sum((x*y-n)**j for x, y in direct)
                assert box.errors(j, 1) == sum(x*(x*y-n)**j for x, y in direct)
        expected = [[str(x), str(n//x)] for x in range(first, last+1) if n%x == 0]
        for method in ("plain", "line", "errors"):
            assert search(n, 5, method=method)["pairs"] == expected
        assert search(n, 5, degree=3, method="errors")["pairs"] == expected
        for m in (2, 3, 6, 10):
            if gcd(m, n) == 1:
                run = search(n, wheel=m)
                assert run["pairs"] == expected and run["bisected"] == 0


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("n", nargs="?", type=int)
    parser.add_argument("--width", type=int, help="default to the uniform collinearity guarantee")
    parser.add_argument("--wheel", type=int, default=1, help="modulus to enumerate, with shared primes removed")
    parser.add_argument("--degree", type=int, choices=range(1,4), default=2)
    parser.add_argument("--method", choices=("line", "errors", "plain"), default="line")
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    if args.self_test:
        self_test()
    elif args.n is None:
        parser.error("provide N or --self-test")
    else:
        print(json.dumps(search(args.n, args.width, args.degree, args.method, args.wheel), indent=2))
