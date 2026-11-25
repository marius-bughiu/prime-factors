"""Allocate the two sides of adjacent Farey slopes with integer coverage checks."""
from itertools import islice
from math import gcd, isqrt


MAX_CENTERS = 32768
MAX_STATES = 1000000
MAX_TRANSITIONS = 5000000


def slopes(k):
    """Increasing Farey fractions from 1 through 2, inclusive."""
    if k < 1:
        raise ValueError("Farey order must be positive")
    a, b = 1, 1
    c, d = k+1, k
    yield a, b
    while True:
        yield c, d
        if c == 2*d:
            break
        multiple = (k+b)//d
        a, b, c, d = c, d, multiple*c-a, multiple*d-b


def bounded_slopes(k, max_centers):
    if k+1 > max_centers or max_centers < 2:
        raise ValueError("Farey center budget exhausted")
    centers = list(islice(slopes(k), max_centers+1))
    if len(centers) > max_centers:
        raise ValueError("Farey center budget exhausted")
    return centers


def lattice_start(n, a, b, stride):
    step = gcd(stride, 2*(a+b*n))
    low = 1+isqrt(4*a*b*n-1)
    return low+(a+b*n-low)%step, step


def needed(n, a, b, A, B, start, step):
    """Number of possible labels up to the ratio A/B, using only integer arithmetic."""
    upper = isqrt(n*(a*B+b*A)**2//(A*B))
    return max(0, (upper-start)//step+1)


def counts(lengths, m):
    return dict(retained_slopes=len(lengths), nonempty_slopes=sum(t > 0 for t in lengths),
                giants = sum((t+m-1)//m for t in lengths), labels = sum(lengths))


def verify(n, m, plan):
    """Check the full interval, including empty windows, from public integer inequalities."""
    if n < 2 or m < 1 or not isinstance(plan, (tuple, list)) or len(plan) != 4:
        raise ValueError("invalid input or certificate shape")
    fractions, windows, cuts, lengths = plan
    if not all(isinstance(column, (tuple, list)) for column in plan):
        raise ValueError("certificate columns must be sequences")
    if not fractions or not len(fractions) == len(windows) == len(lengths) == len(cuts)-1:
        raise ValueError("inconsistent number of cells, windows or cuts")
    if cuts[0] != (1, 1) or cuts[-1] != (2, 1):
        raise ValueError("the cuts must span the balanced ratio interval")
    for pairs in (fractions, windows, cuts):
        for pair in pairs:
            if (not isinstance(pair, (tuple, list)) or len(pair) != 2
                    or any(type(value) is not int or value <= 0 for value in pair)):
                raise ValueError("each coordinate and window field must be a positive integer")
    for (a, b), (start, step), left, right, length in zip(fractions, windows, cuts, cuts[1:], lengths):
        if type(length) is not int or length < 0:
            raise ValueError("a label count must be a nonnegative integer")
        if step != gcd(24, 2*(a+b*n)) or (start-a-b*n) % step:
            raise ValueError("window does not match the public weighted-sum residue")
        if start*start < 4*a*b*n or (start >= step and (start-step)**2 >= 4*a*b*n):
            raise ValueError("incorrect first admissible label")
        if left[0]*b > a*left[1] or right[0]*b < a*right[1]:
            raise ValueError("a claimed cell does not contain its slope")
        first_omitted = start+step*length
        for A, B in (left, right):
            if n*(a*B+b*A)**2 >= A*B*first_omitted**2:
                raise ValueError("the endpoint reaches an omitted label")
    return counts(lengths, m)


def meeting(n, left, right, T, U):
    """Return an exact jointly covered cut, or None, on this entire ratio gap."""
    a, b = left
    c, d = right
    if 2*a*b*U >= (c*b+d*a)*T:
        valid = 4*n*a*b < T*T and n*(c*b+d*a)**2 < a*b*U*U
        return left if valid else None
    if (a*d+b*c)*U <= 2*c*d*T:
        valid = n*(a*d+b*c)**2 < c*d*T*T and 4*n*c*d < U*U
        return right if valid else None
    A, B = c*T-a*U, b*U-d*T
    return (A, B) if A*B > n*(b*c-a*d)**2 else None


def optimal_with_skips(n, k, m, *, gap=2, max_centers=MAX_CENTERS, max_states=MAX_STATES,
                       max_transitions=MAX_TRANSITIONS):
    """Exact minimum with at most gap original edges between consecutive retained slopes."""
    if min(k, m, gap) < 1 or n < 2:
        raise ValueError('invalid allocation settings')
    fractions = bounded_slopes(k, max_centers)
    windows = [lattice_start(n, a, b, 24) for a, b in fractions]
    baseline_cuts = [fractions[0]]+[(a+c, b+d) for (a, b), (c, d) in zip(fractions, fractions[1:])]+[fractions[-1]]
    prefix = [0]
    for (a, b), (s, step), lo, hi in zip(fractions, windows, baseline_cuts, baseline_cuts[1:]):
        size = max(needed(n, a, b, *lo, s, step), needed(n, a, b, *hi, s, step))
        prefix.append(prefix[-1]+(size+m-1)//m)
    # Replacing one costly center and the adjacent skipped centers by the feasible
    # baseline limits its optimal budget to the baseline sum over these neighboring gaps.
    caps = [prefix[min(i+gap+1, len(fractions))]-prefix[max(0, i-gap)] for i in range(len(fractions))]
    if sum(cap+1 for cap in caps) > max_states:
        raise ValueError("allocation state budget exhausted")
    if sum((cap+1)*min(i, gap) for i, cap in enumerate(caps)) > max_transitions:
        raise ValueError("allocation transition budget exhausted")
    total = prefix[-1]
    # An optimal path costs at most the baseline in blocks; break ties by center count.
    scale = len(fractions)+1
    unreachable = (total+1)*scale
    # suffixes[j][g] stores the cheapest prefix ending at j with at least g blocks.
    histories = []
    suffixes = {}
    for i, (right, (rstart, rstep)) in enumerate(zip(fractions, windows)):
        costs = [unreachable]*(caps[i]+1)
        parents = [None]*len(costs)
        if i == 0:
            costs = [g*scale+1 for g in range(caps[i]+1)]
        else:
            for j in range(max(0, i-gap), i):
                left = fractions[j]
                lstart, lstep = windows[j]
                suffix = suffixes[j]
                cut = len(suffix)
                # Increasing the new budget only lowers the required previous budget.
                for g in range(caps[i]+1):
                    U = rstart+rstep*m*g
                    while cut and meeting(n, left, right, lstart+lstep*m*(cut-1), U) is not None:
                        cut -= 1
                    if cut < len(suffix):
                        old, prev = suffix[cut]
                        trial = old+g*scale+1
                        if trial < costs[g]:
                            costs[g], parents[g] = trial, (j, prev)
        histories.append(parents)
        suffix = [(0, 0)]*len(costs)
        best = (unreachable, 0)
        for g in reversed(range(len(costs))):
            best = min(best, (costs[g], g))
            suffix[g] = best
        suffixes[i] = suffix
        suffixes.pop(i-gap, None)
    index = len(fractions)-1
    _, g = suffixes[index][0]
    selected = []
    while True:
        selected.append((index, g))
        if index == 0:
            break
        index, g = histories[index][g]
    selected.reverse()
    return finalize(n, m, fractions, windows, selected)


def finalize(n, m, fractions, strides, selected):
    chosen = [fractions[i] for i, _ in selected]
    windows = [strides[i] for i, _ in selected]
    tops = [strides[i][0] + strides[i][1]*m*g for i, g in selected]
    cuts = [chosen[0]]
    for left, right, T, U in zip(chosen, chosen[1:], tops, tops[1:]):
        cut = meeting(n, left, right, T, U)
        if cut is None:
            raise ValueError("adjacent budgets leave a gap")
        cuts.append(cut)
    cuts.append(chosen[-1])
    lengths = [max(needed(n, a, b, *lo, start, step), needed(n, a, b, *hi, start, step))
               for (a, b), (start, step), lo, hi in zip(chosen, windows, cuts, cuts[1:])]
    return chosen, windows, cuts, lengths


def min_top(n, target, fixed, top):
    """Least integer target threshold for strict overlap with a fixed threshold."""
    a, b = target
    c, d = fixed
    delta = top*top-4*c*d*n
    if delta <= 0:
        return None
    mix = a*d+b*c
    if n*mix*mix <= a*b*top*top:
        return isqrt(4*a*b*n)+1
    det = abs(b*c-a*d)
    ceiling = 1+isqrt(det*det*delta-1)
    return (mix*top-ceiling)//(2*c*d)+1


def fast(n, k, m, passes=2, *, max_centers=MAX_CENTERS):
    """Start with stride-weighted cuts, remove covered centers, and shrink neighboring budgets."""
    if min(k, m) < 1 or n < 2 or passes < 0:
        raise ValueError("invalid allocation settings")
    fractions = bounded_slopes(k, max_centers)
    windows = [lattice_start(n, a, b, 24) for a, b in fractions]
    initial = [(1, 1)]
    weights = {s:isqrt(100*s) for s in (2, 4, 6, 8, 12, 24)}
    for (a, b), (c, d), (_, s), (_, t) in zip(fractions, fractions[1:], windows, windows[1:]):
        u, v = weights[t], weights[s]
        initial.append((u*a+v*c, u*b+v*d))
    initial.append((2, 1))
    blocks = [(max(needed(n, a, b, *lo, s, st), needed(n, a, b, *hi, s, st))+m-1)//m
            for (a, b), (s, st), lo, hi in zip(fractions, windows, initial, initial[1:])]
    indices = list(range(len(fractions)))
    def top(i):
        return windows[i][0]+windows[i][1]*m*blocks[i]
    def requirement(i, j, known):
        low = min_top(n, fractions[i], fractions[j], known)
        if low is None:
            raise ValueError('fixed window must cover its own center')
        s, step = windows[i]
        return max(0, (low-s+m*step-1)//(m*step))
    for _ in range(passes):
        survivors = [indices[0]]
        for j, after in zip(indices[1:-1], indices[2:]):
            before = survivors[-1]
            # Test removing j while enlarging either neighbor, keeping the other fixed.
            new_after = max(blocks[after], requirement(after, before, top(before)))
            new_before = max(blocks[before], requirement(before, after, top(after)))
            if min(new_after-blocks[after], new_before-blocks[before]) <= blocks[j]:
                if new_after-blocks[after] <= new_before-blocks[before]:
                    blocks[after] = new_after
                else:
                    blocks[before] = new_before
                continue
            survivors.append(j)
        survivors.append(indices[-1])
        indices = survivors
        for pos, i in enumerate(indices):
            required = 0
            if pos:
                j = indices[pos-1]
                required = requirement(i, j, top(j))
            if pos+1 < len(indices):
                j = indices[pos+1]
                required = max(required, requirement(i, j, top(j)))
            blocks[i] = required
        indices.reverse()
    indices.sort()
    return finalize(n, m, fractions, windows, [(i, blocks[i]) for i in indices])
