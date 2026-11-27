"""Product-guided rectangular search across small odd seeds and even centers."""

from collections import Counter
from math import gcd

from .short_pascal_row import interval
from .twelve_residue_collision import directions, keys
from .wide_modulus import product_tree, values_at


def schedule(n, height, width, compressed=False):
    if height < 1 or width < 1:
        raise ValueError("require positive rectangle dimensions")
    lower, _ = interval(n)
    first = lower | 1
    if compressed and height < 3:
        raise ValueError("the expanded signed interval needs at least three baby slots")
    radius = height+2 if compressed else height
    babies = [b for b in range(1, 2*radius, 2) if not compressed or b not in (3,9)]
    giants = [first+2*radius-1+4*radius*j for j in range(width)]
    return babies, giants


def search(n, height, width, method="twelve"):
    if method not in ("twelve", "expanded_twelve", "squares", "screened_squares"):
        raise ValueError("unknown rectangle method")
    babies, giants = schedule(n, height, width, compressed=method == "expanded_twelve")
    grouped = method in ("twelve","expanded_twelve")
    work = Counter()
    source, witness = "none", []

    def gcd_test(z, counter):
        work[counter] += 1
        return gcd(z, n)

    def branches(b, g):
        nonlocal source, witness
        forms = directions(b) if grouped else [(b, 1)]
        for index, (a, d) in enumerate(forms):
            for sign in (1, -1):
                h = gcd_test(d*g-sign*a, "branch_gcds")
                if 1 < h < n:
                    source, witness = "branch", [b,g,2*index+(sign == -1)]
                    return h
        return None

    def find():
        nonlocal source, witness
        left, right = babies, giants
        if method != "squares":
            batch = 1
            for x in left+right:
                batch = batch*(x*x+3) % n
            g = gcd_test(batch, "setup_gcds")
            if 1 < g < n:
                source = "denominator"
                return g
            if g == n:
                poles = set()
                for x in left+right:
                    h = gcd_test(x*x+3, "setup_gcds")
                    if 1 < h < n:
                        source = "denominator"
                        return h
                    if h == n:
                        poles.add(x)
                # At a simultaneous pole both normalized keys can lose the
                # signed interval comparison. Test its row or column directly.
                pole_giants = [y for y in right if y in poles]
                for b in left:
                    for y in (right if b in poles else pole_giants):
                        h = branches(b, y)
                        if h:
                            return h
                left = [x for x in left if x not in poles]
                right = [x for x in right if x not in poles]
        if not left or not right:
            return None
        if grouped:
            values = keys(left+right, n)
            work["inversions"] += 1
        else:
            values = [x*x % n for x in left+right]
        roots, points = values[:len(left)], values[len(left):]
        unique = list(dict.fromkeys(roots))
        work.update(polynomial_degree=len(unique), evaluation_points=len(points))
        polynomial = product_tree(unique, n)[-1][0]
        for y, key, value in zip(right, points, values_at(polynomial, points, n)):
            h = gcd_test(value, "row_gcds")
            if h == 1:
                continue
            for b, root in zip(left, roots):
                d = gcd_test(key-root, "pair_gcds")
                if 1 < d < n:
                    source, witness = "key difference", [b,y]
                    return d
                if d == n:
                    d = branches(b,y)
                    if d:
                        return d
        return None

    factor = find()
    return factor, dict(work), source, witness
