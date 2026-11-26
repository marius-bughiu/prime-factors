"""Minimize the total giant blocks needed for a continuous interval of factor ratios.

All geometry and optimization use only the input, its public ratio interval, and
the available slopes. A covering plan and a matching set of weighted test ratios
make the minimum independently checkable without replaying the optimization.
"""

from fractions import Fraction
from heapq import heappop, heappush
from math import gcd

from .farey_allocation import bounded_slopes, lattice_start, needed


def cover_cost(n, window, block, ratio):
    """First budget whose weighted trace threshold strictly exceeds the trace."""
    a, b, start, step = window
    labels = needed(n, a, b, ratio.numerator, ratio.denominator, start, step)
    return (labels + block - 1) // block


def envelope(n, windows, block, budgets, left, right):
    """Return the active segments and a rational witness for each uncovered end.

    The normalized traces share a positive factor sqrt(N/x). Their order is
    the order of straight lines (a+b*x)/T for first omitted thresholds T.
    """
    lines = []
    for index, ((a, b, start, step), g) in enumerate(zip(windows, budgets)):
        threshold = start + g * step * block
        lines.append((Fraction(b, threshold), Fraction(a, threshold), index))
    lines.sort(key=lambda line: (-line[0], line[1]))
    hull = []
    cuts = []
    for slope, intercept, index in lines:
        if hull and hull[-1][0] == slope:
            continue
        while hull:
            old_slope, old_intercept, _ = hull[-1]
            cut = (intercept-old_intercept) / (old_slope-slope)
            if len(hull) == 1 or cuts[-1] < cut:
                break
            hull.pop()
            cuts.pop()
        cuts.append(None if not hull else cut)
        hull.append((slope, intercept, index))
    cells, missing = [], set()
    for j, (_, _, index) in enumerate(hull):
        lo = left if j == 0 else max(left, cuts[j])
        hi = right if j+1 == len(hull) else min(right, cuts[j+1])
        if lo > hi or (lo == hi and left != right):
            continue
        cells.append((lo, hi, index))
        for x in (lo, hi):
            if cover_cost(n, windows[index], block, x) > budgets[index]:
                missing.add(x)
    return cells, missing


def sampled_cover(n, windows, block, points):
    """Minimum interval-cover cost on sorted test ratios, with integral dual prices."""
    intervals = [[] for _ in points]
    for index, window in enumerate(windows):
        levels = sorted((cover_cost(n, window, block, x), j) for j, x in enumerate(points))
        lo, hi = len(points), -1
        for k, (cost, j) in enumerate(levels):
            lo, hi = min(lo, j), max(hi, j)
            if k+1 == len(levels) or levels[k+1][0] != cost:
                intervals[lo].append((hi, cost, index))

    # dp[j] is the optimal cost on the first j points. An interval [lo,hi]
    # offers dp[lo]+cost at each next point from lo to hi.
    dp, choices, active = [0], [], []
    for j, starts in enumerate(intervals):
        for hi, cost, index in starts:
            heappush(active, (dp[j]+cost, -hi, j, index, cost))
        while -active[0][1] < j:
            heappop(active)
        value, _, lo, index, cost = active[0]
        dp.append(value)
        choices.append((lo, index, cost))
    budgets = [0]*len(windows)
    j = len(points)
    while j:
        j, index, cost = choices[j-1]
        budgets[index] = max(budgets[index], cost)
    prices = [(x, dp[j+1]-dp[j]) for j, x in enumerate(points) if dp[j+1] > dp[j]]
    return budgets, prices


def verify(n, windows, block, left, right, budgets, prices):
    """Check continuous coverage and the lower bound for every alternative budget."""
    if len(budgets) != len(windows) or any(type(g) is not int or g < 0 for g in budgets):
        raise ValueError('invalid budget vector')
    if not all(left <= x <= right and type(w) is int and w > 0 for x, w in prices):
        raise ValueError('invalid weighted test ratio')
    cells, missing = envelope(n, windows, block, budgets, left, right)
    if not cells or missing:
        raise ValueError('the schedule leaves a ratio uncovered')
    for window in windows:
        paid = 0
        for cost, weight in sorted((cover_cost(n, window, block, x), w) for x, w in prices):
            paid += weight
            if paid > cost:
                raise ValueError('a window covers more test-ratio weight than its cost')
    minimum = sum(budgets)
    if minimum != sum(w for _, w in prices):
        raise ValueError('cost and lower bound disagree')
    return minimum


def solve(n, k, block, *, left=Fraction(1), right=Fraction(2), max_centers=32768):
    if type(n) is not int or n < 2 or type(block) is not int or block < 1:
        raise ValueError('expected positive block size and input at least two')
    left, right = Fraction(left), Fraction(right)
    if not 1 <= left <= right <= 2:
        raise ValueError('expected a closed ratio interval within [1,2]')
    windows = [(a, b, *lattice_start(n, a, b, 24)) for a, b in bounded_slopes(k, max_centers)]
    points = {left, right}
    rounds = 0
    while True:
        rounds += 1
        budgets, prices = sampled_cover(n, windows, block, sorted(points))
        cells, missing = envelope(n, windows, block, budgets, left, right)
        if not missing:
            optimum = verify(n, windows, block, left, right, budgets, prices)
            return dict(windows=windows, budgets=budgets, prices=prices, cells=cells,
                        optimum=optimum, rounds=rounds, points=len(points))
        if missing & points:
            raise ArithmeticError('a previously checked point became uncovered')
        points.update(missing)


def two_slopes(n, block=1):
    """Exact minimum for slopes 1 and 2 without listing any individual block.

    In the interior case (2T-U)(U-T) is a concave quadratic in the blocks
    assigned to slope one. The best integer allocation is next to its vertex.
    """
    if type(n) is not int or n <= 1 or gcd(n, 6) != 1 or type(block) is not int or block < 1:
        raise ValueError('expected N > 1 coprime to six and a positive block size')
    windows = [(a, 1, *lattice_start(n, a, 1, 24)) for a in (1, 2)]
    (_, _, s, step1), (_, _, t, step2) = windows
    alpha, beta = step1*block, step2*block
    single1 = cover_cost(n, windows[0], block, Fraction(2))
    single2 = cover_cost(n, windows[1], block, Fraction(1))
    def best(g, lo, hi):
        # P(u)=(A+h*u)(B-k*u), with g-u blocks assigned to slope two.
        A, B = 2*s-t-beta*g, t+beta*g-s
        h, k = 2*alpha+beta, alpha+beta
        vertex_floor = (h*B-k*A)//(2*h*k)
        lower = min(hi, max(lo, vertex_floor))

        def score(u):
            return (A+h*u)*(B-k*u)

        u = max((lower, min(hi, lower+1)), key=score)
        return u, score(u)

    def allocation(g):
        if g >= single1:
            return g
        if g >= single2:
            return 0
        # If the weighted minimum is integral, its first omitted label
        # at zero blocks can coincide with the center itself.
        lower = int(s*s == 4*n)
        upper = g-int(t*t == 8*n)
        if lower <= upper:
            u, peak = best(g, lower, upper)
            if peak > n:
                return u
        return None

    lo, hi = -1, min(single1, single2)
    checks = 0
    while hi-lo > 1:
        mid = (hi+lo)//2
        checks += 1
        if allocation(mid) is None:
            lo = mid
        else:
            hi = mid
    u = allocation(hi)
    budgets = [u, hi-u]
    cells, holes = envelope(n, windows, block, budgets, Fraction(1), Fraction(2))
    if holes:
        raise ArithmeticError('two-slope schedule leaves part of the interval uncovered')
    lower_vertex, lower_peak = best(hi-1, 0, hi-1) if hi else (None, None)
    return dict(optimum=hi, budgets=budgets, single=[single1, single2],
                lower_vertex=lower_vertex, lower_peak=lower_peak, cells=cells, decisions=checks)


def run_allocation(n, block, result):
    """Run the existing collision search on exactly the allocated label prefixes."""
    from . import weighted_stride_search
    windows = result['windows']
    lengths = [0]*len(windows)
    for left, right, index in result['cells']:
        a, b, start, step = windows[index]
        lengths[index] = max(lengths[index], *(needed(n, a, b, x.numerator, x.denominator, start, step)
                                             for x in (left, right)))
    if sum((length+block-1)//block for length in lengths) != result['optimum']:
        raise ArithmeticError('unused blocks in the minimum schedule')
    def build(n, k, m, max_giants, max_slopes, beta, stride, work):
        return weighted_stride_search.records_from_allocation(
            n, m, max_giants, max_slopes, beta, stride, work, [w[:2] for w in windows],
            [w[2:] for w in windows], lengths, len(windows))
    k = max(b for _, b, _, _ in windows)
    return weighted_stride_search.search(n, k, block, result['optimum'], max_slopes=len(windows),
                                        record_builder=build)


def compare(n, k, block, *, search_factors=False, equal_width=False, sparse=False, certificate=None):
    """Compute the optimum from public information; optionally run the priced search."""
    from time import perf_counter
    from .farey_allocation import optimal_with_skips, verify as verify_plan

    if gcd(n, 6) != 1:
        raise ValueError('the stride-24 search requires a product coprime to six')
    right = Fraction(2)
    if equal_width:
        bits = (n.bit_length()+1)//2
        low, cap = 1 << (bits-1), (1 << bits)-1
        right = min(right, Fraction(cap*cap, n), Fraction(n, low*low))
        if right < 1:
            raise ValueError('no pair has the specified equal widths')
    start = perf_counter()
    if certificate is not None:
        from .trace_cover_sparse import read_certificate, verify_sparse
        if right != 2:
            raise ValueError('the archived plan covers the full balanced interval')
        result = read_certificate(certificate, n, k, block)
        verify_sparse(n, result['windows'], block, Fraction(1), right, result['budgets'], result['prices'])
        result['cells'], _ = envelope(n, result['windows'], block, result['budgets'], Fraction(1), right)
    elif sparse:
        if right != 2:
            raise ValueError('the sparse planner covers the full balanced interval')
        from .trace_cover_sparse import solve as sparse_solve
        result = sparse_solve(n, k, block)
    else:
        result = solve(n, k, block, right=right)
    elapsed = perf_counter()-start
    start = perf_counter()
    run = run_allocation(n, block, result) if search_factors else None
    search_time = perf_counter()-start if search_factors else None
    summary = dict(catalogue=len(result['windows']), block=str(block), right=str(right),
                   optimum=result['optimum'], probes=len(result['prices']), cells=len(result['cells']),
                   plan_seconds=elapsed, search_seconds=search_time, executed=search_factors)
    if certificate is not None:
        summary['replayed_plan'] = True
    if run is not None:
        summary.update(outcome=run['outcome'], work=run['work'], schedule_complete=run['schedule_complete'])
    if right == 2 and k <= 40:
        previous = optimal_with_skips(n, k, block, gap=3)
        summary['gap_three_blocks'] = verify_plan(n, block, previous)['giants']
    return result, summary, run['factor'] if run is not None else None
