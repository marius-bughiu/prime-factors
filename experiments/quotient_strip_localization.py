"""Measure which trial divisors moment bounds remove from rational hyperbola strips."""

import hashlib
import json
from collections import Counter, defaultdict
from math import isqrt
from pathlib import Path

from experiments.quartic_interval_extension import _sign_runs
from experiments.quotient_search import Strip, Work, line_factors, sparse_root
from scripts.factor import primes_through


FIXTURE = Path(__file__).resolve().parents[1] / 'benchmarks/quotient-strip-localization.json'
METHODS = ('line_sparse', 'marginal_x', 'marginal_xy', 'regression', 'quartic', 'cauchy', 'gram')


def ratio_cohort():
    primes = [p for p in primes_through(8191) if p >= 257]
    return [(p, next(q for q in primes if q > 5*p//4)) for p in primes[::8] if 5*p//4 < primes[-1]]


def holdout_cohort():
    primes = [p for p in primes_through(1023) if p >= 512]
    pairs = []
    i = 0
    while len(pairs) < 64:
        def choose(side):
            digest = hashlib.sha256(f'quotient-strip-holdout-v1:{i}:{side}'.encode()).digest()
            return primes[int.from_bytes(digest, 'big') % len(primes)]
        pair = tuple(sorted((choose('p'), choose('q'))))
        if pair[0] != pair[1] and pair not in pairs:
            pairs.append(pair)
        i += 1
    return pairs


def blocks(n, multiplier=2):
    # Round the sixth root to the nearest integer using exact arithmetic.
    root = 1
    while (2*root+1)**6 < 64*n:
        root += 1
    width = multiplier*root
    first, last = isqrt((n-1)//2)+1, isqrt(n)
    return [(a, min(last, a+width-1)) for a in range(first, last+1, width)]


class ObservedProduct(int):
    """Count the actual divisor tests inside the shared line intersection routine."""

    def __mod__(self, x):
        self.divisor_tests += 1
        return int.__mod__(self, x)


class MeasuredStrip(Strip):
    """Store each requested mixed moment once alongside the base class's cached recurrence states."""

    def __init__(self, n, a, b):
        observed = ObservedProduct(n)
        observed.divisor_tests = 0
        super().__init__(observed, a, b, Work())
        self.mixed = {}

    def moment(self, r, s):
        if (r, s) not in self.mixed:
            self.mixed[r, s] = super().moment(r, s)
        return self.mixed[r, s]

    def costs(self):
        return Counter(strip_counts=self.work.strip_counts, euclidean_steps=self.work.euclidean_steps,
                       moment_states=self.work.moment_states, mixed_moments=len(self.mixed),
                       line_equations=self.work.quadratic_solves, divisibility_tests=self.n.divisor_tests)


def direct_points(n, a, b):
    """Independent reference enumeration of all integer points between the tangent and chord."""
    return [(x, y) for x in range(a, b+1)
            for y in range(-(-n*(2*a-x)//(a*a)), n*(a+b-x)//(a*b)+1)]


def direct_moments(n, points):
    xs = [x for x, _ in points]
    errors = [x*y-n for x, y in points]
    return (len(xs), sum(xs), sum(x*x for x in xs), sum(errors),
            sum(x*e for x, e in zip(xs, errors)), sum(e*e for e in errors))


def coordinate_moments(points):
    return (len(points), sum(x for x, _ in points), sum(x*x for x, _ in points),
            sum(y for _, y in points), sum(x*y for x, y in points), sum(y*y for _, y in points))


def reference_state(n, points):
    if len(points) <= 3:
        return 'sparse'
    (x, y), (u, v) = points[:2]
    if all((s-x)*(v-y) == (t-y)*(u-x) for s, t in points[2:]):
        return 'line'
    c, _, _, e, _, f = direct_moments(n, points)
    return 'cauchy_excluded' if e*e > (c-1)*f else 'eligible'


def determinant(c, sx, xx, se, xe, ee):
    return c*(xx*ee-xe*xe) - sx*(sx*ee-se*xe) + se*(sx*xe-xx*se)


def positive_after_deletion(moments, k):
    """Reference using every principal minor of the symmetric residual Gram matrix."""
    c, sx, xx, se, xe, ee = moments
    c, sx, xx = c-1, sx-k, xx-k*k
    return (min(c, xx, ee) >= 0 and c*xx >= sx*sx and c*ee >= se*se and xx*ee >= xe*xe
            and determinant(c, sx, xx, se, xe, ee) >= 0)


def integer_window(coefficient, offset, square, costs):
    """All integer solutions to (coefficient*k+offset)^2 ≤ square."""
    if coefficient <= 0:
        raise ValueError('Positive coefficient required for integer endpoint division')
    if square < 0:
        return 1, 0
    costs.update(window_square_roots=1, window_endpoint_divisions=2)
    root = isqrt(square)
    return -((offset+root)//coefficient), (root-offset)//coefficient


def quadratic_bounds(a, b, coefficient, offset, square, costs):
    low, high = integer_window(coefficient, offset, square, costs)
    return max(a, low), min(b, high)


def marginal(a, b, c, total, squares, costs):
    return quadratic_bounds(a, b, c, -total, (c-1)*(c*squares-total*total), costs)


def gram_bounds(a, b, moments, costs):
    c, sx, xx, se, xe, ee = moments
    if not c or se*se > (c-1)*ee:
        return 1, 0
    a, b = marginal(a, b, c, sx, xx, costs)
    if a > b:
        return a, b
    coefficient = c*ee-se*se
    if coefficient == 0:
        # All residuals agree. A nonzero common value rules out a factor.
        return (1, 0) if se else (a, b)
    offset = se*xe-sx*ee
    square = offset*offset + coefficient*(determinant(*moments)-(xx*ee-xe*xe))
    return quadratic_bounds(a, b, coefficient, offset, square, costs)


def interval(low, high):
    return [(low, high)] if low <= high else []


def coordinate_windows(n, x0, x1, moments, costs):
    """Intersect the integer x and y marginal intervals along xy=N."""
    c, _, _, sy, _, yy = moments
    y0, y1 = marginal(1, n, c, sy, yy, costs)
    if y0 > y1:
        return []
    costs['window_endpoint_divisions'] += 2
    return interval(max(x0, -(-n//y1)), min(x1, n//y0))


def regression_ranges(n, ranges, moments, costs):
    """Intersect a projected integer band with the hyperbola using two quadratics."""
    if not ranges:
        return []
    c, sx, xx, sy, xy, yy = moments
    u, v = sx*sy-c*xy, c*xx-sx*sx
    if u <= 0 or v <= 0:
        return ranges
    costs['regression_bands'] += 1
    total = u*sx+v*sy
    squares = u*u*xx+2*u*v*xy+v*v*yy
    low, high = integer_window(c, -total, (c-1)*(c*squares-total*total), costs)
    # For k>0, u*k+v*N/k ≤ high is an interval. The strict reverse
    # inequality at the lower edge removes an open central interval.
    a, b = ranges[0]
    costs['projection_discriminants'] += 1
    a, b = quadratic_bounds(a, b, 2*u, -high, high*high-4*u*v*n, costs)
    if a > b:
        return []
    costs['projection_discriminants'] += 1
    cut0, cut1 = quadratic_bounds(a, b, 2*u, -low, low*low-4*u*v*n-1, costs)
    if cut0 > cut1:
        return [(a, b)]
    return interval(a, cut0-1) + interval(cut1+1, b)


def quartic_ranges(n, ranges, moments, costs):
    """Keep the nonnegative runs of k² det(G - (1,k,N/k)ᵀ(1,k,N/k))."""
    if not ranges:
        return []
    c, sx, xx, sy, xy, yy = moments
    vx, vy = c*xx-sx*sx, c*yy-sy*sy
    coefficients = [-vx*n*n, -2*(sx*xy-sy*xx)*n,
                    determinant(*moments)-(xx*yy-xy*xy)-2*(sx*sy-c*xy)*n,
                    -2*(sy*xy-sx*yy), -vy]
    costs['quartic_polynomials'] += 1
    kept = []
    before = costs['sign_evaluations']
    for a, b, sign in _sign_runs(coefficients, *ranges[0], costs):
        if sign >= 0:
            if kept and kept[-1][1]+1 == a:
                a = kept.pop()[0]
            kept.append((a, b))
    # _sign_runs evaluates once at its constant or singleton base case.
    # Every other call evaluates the midpoint in a monotone binary search.
    costs['sign_bisection_halvings'] += costs['sign_evaluations']-before-1
    return kept


def span(a, b):
    return max(0, b-a+1)


def odd_span(a, b):
    return max(0, (b+1)//2-a//2)


def occupancy(c):
    if c <= 3:
        return '0_to_3'
    if c <= 8:
        return '4_to_8'
    if c <= 16:
        return '9_to_16'
    return '17_or_more'


def reference_band(c, total, squares, num, den):
    """Both integer neighbors of the rational query must pass scalar deletion."""
    floor, remainder = divmod(num, den)
    ceiling = floor+int(bool(remainder))
    bound = (c-1)*(c*squares-total*total)
    return max((c*floor-total)**2, (c*ceiling-total)**2) <= bound


def coordinate_deletion(moments, n, k):
    """All principal minors of k²G - (k,k²,N)ᵀ(k,k²,N) using plain integers."""
    c, sx, xx, sy, xy, yy = moments
    k2 = k*k
    residual = (k2*(c-1), k2*(sx-k), k2*(xx-k2), k2*sy-k*n, k2*(xy-n), k2*yy-n*n)
    a, b, d, h, j, f = residual
    return (min(a, d, f) >= 0 and a*d >= b*b and a*f >= h*h and d*f >= j*j
            and determinant(*residual) >= 0)


def reference_coordinate_sets(n, a, b, points, moments):
    c, sx, xx, sy, xy, yy = moments
    u, v = sx*sy-c*xy, c*xx-sx*sx
    values = [u*x+v*y for x, y in points]
    total, squares = sum(values), sum(r*r for r in values)
    marginal_set, regression_set, quartic_set = [], [], []
    for k in range(a, b+1):
        if reference_band(c, sx, xx, k, 1) and reference_band(c, sy, yy, n, k):
            marginal_set.append(k)
            if u <= 0 or v <= 0 or reference_band(c, total, squares, u*k*k+v*n, k):
                regression_set.append(k)
            if coordinate_deletion(moments, n, k):
                quartic_set.append(k)
    return dict(marginal_xy=marginal_set, regression=regression_set, quartic=quartic_set)


def register_strip(n, a, b, points, state, bins, actual=None):
    group = bins[occupancy(len(points))]
    group.update(all_strips=1)
    if state in ('sparse', 'line'):
        group[state] += 1
        return
    stats = direct_moments(n, points)
    c, sx, xx = stats[:3]
    coord = coordinate_moments(points)
    x0, x1 = marginal(a, b, c, sx, xx, Counter())
    if actual is None:
        xy_ranges = coordinate_windows(n, x0, x1, coord, Counter())
        actual = dict(marginal_xy=xy_ranges, regression=regression_ranges(n, xy_ranges, coord, Counter()),
                      quartic=quartic_ranges(n, xy_ranges, coord, Counter()),
                      gram=interval(*gram_bounds(a, b, stats, Counter())))
    targets = [x for x, y in points if x*y == n]
    for name, reference in reference_coordinate_sets(n, a, b, points, coord).items():
        ranges = actual[name]
        result = [x for lo, hi in ranges for x in range(lo, hi+1)]
        if result != reference or any(x not in result for x in targets):
            raise ArithmeticError(f'{name} disagrees with direct deletion or product at {n}, {a}, {b}')
        if state == 'eligible':
            count = len(reference)
            odds = sum(x%2 for x in reference)
            group.update({f'{name}_positions': count, f'{name}_odd_positions': odds})
            if name != 'marginal_xy':
                narrowed = count < sum(span(*r) for r in actual['marginal_xy'])
                group.update({f'{name}_empty': int(not count), f'{name}_no_odd_candidate': int(not odds),
                              f'{name}_disconnected': int(len(ranges)>1), f'{name}_narrower_than_xy': int(narrowed),
                              f'{name}_with_factor_narrower_than_xy': int(bool(targets) and narrowed)})
    if state != 'eligible':
        group[state] += 1
        return
    low, high = actual['gram'][0] if actual['gram'] else (1, 0)
    reference = [x for x in range(a, b+1) if positive_after_deletion(stats, x)]
    if list(range(low, high+1)) != reference:
        raise ArithmeticError(f'Integer interval disagrees with principal minors at {n}, {a}, {b}')
    if not all(low <= x <= high for x in targets):
        raise ArithmeticError(f'Interval discarded a true factor at {n}')
    group.update(eligible=1, original_positions=span(a, b), x_only_positions=span(x0, x1),
                 gram_positions=span(low, high), original_odd_positions=odd_span(a, b),
                 x_only_odd_positions=odd_span(x0, x1), gram_odd_positions=odd_span(low, high),
                 narrowed=int(span(low, high)<span(a, b)), narrower_than_x_only=int(span(low, high)<span(x0, x1)),
                 empty=int(low>high), singleton=int(low==high), no_odd_candidate=int(not odd_span(low, high)),
                 with_factor=int(bool(targets)), with_factor_narrowed=int(bool(targets) and span(low, high)<span(a, b)))


def analyze_strip(n, a, b):
    """Share nested calculations, taking a separate cost snapshot for each method."""
    box = MeasuredStrip(n, a, b)
    c = box.count()
    settled = None
    state = 'sparse'
    if c <= 3:
        settled = []
        if c:
            status, x = sparse_root(box, c)
            if status == 'factor' and box.n % x == 0:
                settled = [x]
            elif status != 'empty':
                raise ArithmeticError(f'Unexpected sparse reconstruction status at {n}')
    else:
        settled = line_factors(box, c)
        state = 'line'
    if settled is not None:
        return state, {name: (box.costs(), None, settled) for name in METHODS}

    sx, xx = box.moment(1, 0), box.moment(2, 0)
    cheap = box.costs()
    rows = {'line_sparse': (cheap.copy(), [(a, b)], None)}
    xc = cheap.copy()
    x0, x1 = marginal(a, b, c, sx, xx, xc)
    rows['marginal_x'] = (xc.copy(), interval(x0, x1), None)
    xy = box.moment(1, 1)
    coord = (c, sx, xx, box.moment(0, 1), xy, box.moment(0, 2))
    xy_ranges = coordinate_windows(n, x0, x1, coord, xc)
    rows['marginal_xy'] = (xc, xy_ranges, None)
    for name, localize in (('regression', regression_ranges), ('quartic', quartic_ranges)):
        work = xc.copy()
        rows[name] = (work, localize(n, xy_ranges, coord, work), None)
    se = xy-c*n
    ee = box.moment(2, 2)-2*n*xy+c*n*n
    if se*se > (c-1)*ee:
        for name in ('cauchy', 'gram'):
            rows[name] = (box.costs(), None, [])
        return 'cauchy_excluded', rows
    rows['cauchy'] = (box.costs(), [(a, b)], None)
    xe = box.moment(2, 1)-n*sx
    gc = box.costs()
    gc['gram_mixed_sums'] += 1
    rows['gram'] = (gc, interval(*gram_bounds(a, b, (c, sx, xx, se, xe, ee), gc)), None)
    return 'eligible', rows


def scan_product(n, bins, control_block=None):
    totals = {name: Counter() for name in METHODS}
    first = {}
    found = defaultdict(list)
    control = None
    for a, b in blocks(n):
        state, rows = analyze_strip(n, a, b)
        pts = direct_points(n, a, b)
        if reference_state(n, pts) != state:
            raise ArithmeticError(f'Independent strip classification disagrees at {n}')
        register_strip(n, a, b, pts, state, bins, {name: row[1] for name, row in rows.items()})
        for name, (work, ranges, answers) in rows.items():
            cost = totals[name]
            cost.update(work)
            if ranges is None:
                if answers:
                    found[name].extend(answers)
                    first.setdefault(name, cost.copy())
                continue
            for low, high in ranges:
                for x in range(low+(low%2 == 0), high+1, 2):
                    cost.update(divisibility_tests=1, terminal_divisibility_tests=1)
                    if n % x == 0:
                        found[name].append(x)
                        first.setdefault(name, cost.copy())
        if control_block == a:
            control = dict(product=str(n), block=[a, b], state=state, points=pts,
                           moments=direct_moments(n, pts), coordinate_moments=coordinate_moments(pts),
                           intervals={k: row[1] for k, row in rows.items()})
    return totals, first, found, control


def direct_trial(n):
    a, b = isqrt((n-1)//2)+1, isqrt(n)
    count, hits = 0, []
    for x in range(a+(a%2 == 0), b+1, 2):
        count += 1
        if n % x == 0:
            hits.append((x, count))
    if len(hits) != 1:
        raise ArithmeticError(f'Expected one balanced divisor of {n}')
    return hits[0][0], hits[0][1], count


def compare(cohort, controls):
    bins = defaultdict(Counter)
    stages = {stage: defaultdict(Counter) for stage in ('complete', 'to_first')}
    trial = Counter()
    examples = []
    for p, q in cohort:
        n = p*q
        total, first, found, example = scan_product(n, bins, controls.get(n))
        for name in METHODS:
            if found[name] != [p]:
                raise ArithmeticError(f'{name} returned {found[name]} for {n}')
            stages['complete'][name].update(total[name])
            stages['to_first'][name].update(first[name])
        factor, to_first, complete = direct_trial(n)
        if factor != p:
            raise ArithmeticError(f'Direct trial disagrees at {n}')
        trial.update(complete_divisions=complete, divisions_to_first=to_first)
        if example:
            example['verified_factors'] = [str(p), str(q)]
            examples.append(example)
    return dict(products=len(cohort), occupancy=bins, methods=stages, direct_trial=trial, controls=examples)


def study():
    ratio = ratio_cohort()
    wider = defaultdict(Counter)
    for p, q in ratio:
        n = p*q
        for a, b in blocks(n, multiplier=4):
            pts = direct_points(n, a, b)
            register_strip(n, a, b, pts, reference_state(n, pts), wider)
    degeneracies = [(15, [(1,15),(3,5),(5,3),(15,1)]), (13, [(1,15),(3,5),(5,3),(15,1)]),
                    (21, [(2,1),(2,2),(2,3),(3,7)]), (22, [(2,1),(2,2),(2,3),(3,7)]),
                    (11, [(2,8),(2,9),(2,10)]), (15, [])]
    for n, pts in degeneracies:
        stats = direct_moments(n, pts)
        a, b = gram_bounds(1, 20, stats, Counter())
        if list(range(a, b+1)) != [x for x in range(1, 21) if positive_after_deletion(stats, x)]:
            raise ArithmeticError('Degenerate Gram calculation disagrees with the principal minors')
    covariance_controls = [[(2, 2), (2, 3), (4, 2), (4, 3)], [(2, 2), (2, 3), (4, 3), (4, 4)]]
    for pts in covariance_controls:
        moments = coordinate_moments(pts)
        bounds = marginal(1, 10, *moments[:3], Counter())
        xy_ranges = coordinate_windows(6, *bounds, moments, Counter())
        work = Counter()
        projected = regression_ranges(6, xy_ranges, moments, work)
        expected = reference_coordinate_sets(6, 1, 10, pts, moments)['regression']
        if work or projected != xy_ranges or [k for lo, hi in projected for k in range(lo, hi+1)] != expected:
            raise ArithmeticError('Nonnegative covariance fallback disagrees with marginal bounds')
    return dict(ratio_design='Every eighth prime p from 257 through 8191, with q the first prime above floor(5p/4) in the same range. Omit p if q would be outside the range.',
                holdout_design='64 distinct unordered pairs of different 10-bit primes. Choose the two prime indices independently by SHA-256 with counter and side labels. No prescribed ratio.',
                blocks='Ascending blocks of width twice the nearest sixth root of N in the balanced interval. The wider control uses four times the same root.',
                work='Every search starts from N alone. All methods use Newton error moments on at most three points and the same line test on other strips. Cauchy and Gram also apply the first two residual moments. Regression and quartic reuse the coordinate moments of the line test and first apply the integer x and y bounds. Regression counts its unnormalized projected bands and quadratic discriminants. Quartic counts polynomial builds and all finite-difference sign evaluations during root isolation. The remaining intervals visit odd trial divisors in ascending order. To-first snapshots stop at the first returned factor. Window square roots and endpoint divisions count added location calculations. Line intersections and shared Euclidean states are reported separately. Counters measure operations in their own units. Reference enumerations are excluded.',
                reference='Every block left unresolved by sparse and collinear reconstruction compares the two coordinate filters to independent integer-neighbor variance and scaled principal-minor tests at every position. The eligible occupancy rows use exactly the strips that survive Newton, line, and residual-only Cauchy. Wider-block numbers use direct reference points.',
                ratio=compare(ratio, {14043943:3322, 119423:301, 11286761:3006}), holdout=compare(holdout_cohort(), {}),
                wider_ratio_occupancy=wider, singular_and_repeated_coordinate_controls=len(degeneracies),
                nonnegative_coordinate_covariance_controls=len(covariance_controls))


if __name__ == '__main__':
    result = study()
    if json.loads(json.dumps(result)) != json.loads(FIXTURE.read_text()):
        raise SystemExit('Strip localization results differ from the reviewed fixture')
    print(f"Verified {result['ratio']['products']} ratio-selected inputs and {result['holdout']['products']} holdout inputs.")
