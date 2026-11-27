"""Enumerate bounded signed norm representations by covering conics with rational lines."""

import argparse
from collections import Counter
from functools import lru_cache
import json
from math import gcd, isqrt
from pathlib import Path
import platform
from statistics import median
from time import process_time_ns

from experiments.affine_radix_holdout import draw_prime
from experiments.norm_directions import arc as ellipse_arc
from experiments.phase_interval import approximate_slope, cube_radius
from experiments.salie_reference import ceil_div
from experiments.split_prime_holdout import certificate
from experiments.three_root_targets import menu


ROOT = Path(__file__).resolve().parents[1]
SEED = b"signed-norm-arc-holdout-v1"
MULTIPLIERS = (1, -1, 2, -2)


def integer_arc(total, a, b, lo, hi, work, *, hyperbolic=True):
    """Use integer rounding for both b*z²=total±a*u² charts."""
    span = hi - lo
    width = span + 1
    scale = 4*(a+b+1)*width**2
    sign = 1 if hyperbolic else -1
    left = isqrt((total+sign*a*lo*lo)*scale**2 // b)
    right = isqrt((total+sign*a*hi*hi)*scale**2 // b)
    low_num, low_den = a*lo*scale, b*(left+1)
    high_num, high_den = a*(2*lo+span)*scale, b*(left+right)
    den, rem, steps = approximate_slope(low_num, low_den, width)
    if not 1 <= den <= width or abs(rem)*span > low_den:
        raise ArithmeticError("continued-fraction slope approximation exceeded its certified error")
    num = (den*low_num-rem) // low_den
    work["euclidean_steps"] += steps
    # Absolute chord slopes are enclosed by the initial tangent and last secant.
    # Reverse the bounds for the decreasing ellipse; avoid constructing Fractions.
    if hyperbolic:
        slope_lo, denom_lo = den*low_num - num*low_den, low_den
        slope_hi, denom_hi = den*high_num - num*high_den, high_den
    else:
        slope_lo, denom_lo = num*high_den - den*high_num, high_den
        slope_hi, denom_hi = num*low_den - den*low_num, low_den
    low = ceil_div(den*left*denom_lo + scale*min(0, slope_lo)*span, scale*denom_lo)
    high = (den*(left+1)*denom_hi + scale*max(0, slope_hi)*span) // (scale*denom_hi)
    if hyperbolic and high-low+1 > 5 and (width == 1 or (8*a*width**3)**2 <= b*total):
        raise ArithmeticError("certified hyperbola block has more than five intercepts")
    quadratic = b*num**2 - sign*a*den**2
    for intercept in range(low, high+1):
        work["line_tests"] += 1
        linear = sign*(b*intercept*num - a*den**2*lo)
        constant = b*intercept**2 - den**2*(total+sign*a*lo**2)
        if quadratic:
            delta = linear**2 - quadratic*constant
            if delta < 0:
                continue
            work["discriminant_roots"] += 1
            root = isqrt(delta)
            if root*root != delta:
                continue
            offsets = ((root-linear, quadratic), (-root-linear, quadratic)) if root else ((-linear, quadratic),)
        elif linear:
            offsets = ((-constant, 2*linear),)
        else:
            if constant == 0:
                raise ArithmeticError("a nondegenerate hyperbola contains a whole line")
            continue
        for numerator, denominator in offsets:
            j, extra = divmod(numerator, denominator)
            if extra or not 0 <= j <= span:
                continue
            z, extra = divmod(intercept+sign*num*j, den)
            if extra or z < 1:
                continue
            u = lo+j
            if b*z*z != total+sign*a*u*u:
                raise ArithmeticError("line returned a point off the conic")
            yield u, z


UNIT_REAL_PART = {2: 3, 3: 2, 6: 5}


def unit_multiplier(n, d):
    if d in (-1, -2, -3, 2):
        return 1
    if d == -6:
        return 1 if n % 3 == 1 else 2
    if d in (3, 6):
        return 1 if n % 3 == 1 else -1
    raise ValueError("no unit-reduced chart for this target")


def in_window(n, d, m, x, y, domain):
    if domain == "broad":
        return x*x+abs(d)*y*y < 3*n
    return d < 0 or 2*d*y*y <= (UNIT_REAL_PART[d]-m)*n


def axes(n, d, m, work, domain):
    total = m*n
    if total > 0:
        x = isqrt(total)
        work["axis_isqrts"] += 1
        if x*x == total and in_window(n, d, m, x, 0, domain):
            yield x, 0
    value, extra = divmod(total, -d)
    if extra == 0 and value > 0:
        y = isqrt(value)
        work["axis_isqrts"] += 1
        if y*y == value and in_window(n, d, m, 0, y, domain):
            yield 0, y


def charts(n, d, m, work, domain="broad"):
    """In each chart z is the larger curved coordinate, u is scanned from 1."""
    total = abs(m)*n
    if d < 0:
        if m < 0:
            return
        for a, b, swapped in ((1, -d, False), (-d, 1, True)):
            work["bound_isqrts"] += 1
            yield False, a, b, swapped, isqrt(total//(2*a))
    else:
        # x²+Dy² = |m|N + 2a*u². Subtract 1 for the strict height bound.
        a, b, swapped = (d, 1, True) if m > 0 else (1, d, False)
        work["bound_isqrts"] += 1
        ceiling = 3*n-1-total if domain == "broad" else (UNIT_REAL_PART[d]-1)*n
        yield True, a, b, swapped, isqrt(ceiling//(2*a))


@lru_cache(maxsize=None)
def possible(d, modulus):
    return frozenset((x*x-d*y*y) % modulus for x in range(modulus) for y in range(modulus))


def point_scan(n, d, m, method, work, *, max_blocks=None, max_positions=None, domain="broad"):
    """Return absolute coordinates once, including zero; all sign changes preserve the norm."""
    if (n < 2 or not 1 <= abs(d) <= 6 or m not in MULTIPLIERS or
            method not in ("direct", "arcs", "integer_arcs") or domain not in ("broad", "unit")):
        raise ValueError("expected n≥2, 1≤|D|≤6, m in {±1,±2}, and an available scanner")
    if (max_blocks is not None and max_blocks < 0) or (max_positions is not None and max_positions < 0):
        raise ValueError("caps must be nonnegative")
    if domain == "unit" and m != unit_multiplier(n, d):
        return
    if d < 0 and m < 0:
        work["impossible_sign"] += 1
        return
    if any(m*n % modulus not in possible(d, modulus) for modulus in (16, 3)):
        work["local_exclusions"] += 1
        return
    yield from axes(n, d, m, work, domain)
    total = abs(m)*n
    for hyperbolic, a, b, swapped, last in charts(n, d, m, work, domain):
        if not last:
            continue
        if method == "direct":
            limit = last if max_positions is None else min(last, max_positions-work["coordinate_positions"])
            recorded_u = roots = 0
            for u in range(1, limit+1):
                value = total+a*u*u if hyperbolic else total-a*u*u
                quotient, extra = divmod(value, b)
                if extra:
                    continue
                z = isqrt(quotient)
                roots += 1
                if z*z == quotient and z > 0 and (hyperbolic or not swapped or a*u*u != b*z*z):
                    work["coordinate_positions"] += u-recorded_u
                    work["coordinate_isqrts"] += roots
                    recorded_u, roots = u, 0
                    yield (z, u) if swapped else (u, z)
            work["coordinate_positions"] += limit-recorded_u
            work["coordinate_isqrts"] += roots
            if limit < last:
                work["capped"] = 1
                return
        else:
            width = max(1, cube_radius(8*isqrt(b*total)//a))
            work["bound_isqrts"] += 1
            for lo in range(1, last+1, width):
                if max_blocks is not None and work["blocks"] >= max_blocks:
                    work["capped"] = 1
                    return
                hi = min(last, lo+width-1)
                work["blocks"] += 1
                work["hyperbola_blocks" if hyperbolic else "ellipse_blocks"] += 1
                work["coordinate_positions"] += hi-lo+1
                work["endpoint_isqrts"] += 2
                previous_tests = work["line_tests"]
                if hyperbolic or method == "integer_arcs":
                    points = integer_arc(total, a, b, lo, hi, work, hyperbolic=hyperbolic)
                else:
                    points = ellipse_arc(total, a, b, lo, hi, work)
                for u, z in points:
                    if hyperbolic or not swapped or a*u*u != b*z*z:
                        yield (z, u) if swapped else (u, z)
                work["max_lines_per_block"] = max(work["max_lines_per_block"], work["line_tests"]-previous_tests)


def search(n, method, *, domain="broad", **caps):
    start = process_time_ns()
    if n < 5 or gcd(n, 6) != 1 or isqrt(n)**2 == n:
        raise ValueError("expected a nonsquare product coprime to 6")
    work = Counter(dict.fromkeys(("blocks", "ellipse_blocks", "hyperbola_blocks", "line_tests",
                                  "max_lines_per_block", "coordinate_positions", "coordinate_isqrts",
                                  "discriminant_roots", "endpoint_isqrts", "axis_isqrts",
                                  "bound_isqrts", "euclidean_steps", "capped"), 0))
    first = {}
    points = []
    witnesses = []
    factor = None
    first_work = first_time = None
    for d in menu(n, "signed"):
        for m in (MULTIPLIERS if domain == "broad" else (unit_multiplier(n, d),)):
            for x, y in point_scan(n, d, m, method, work, domain=domain, **caps):
                if x*x-d*y*y != m*n or not in_window(n, d, m, x, y, domain):
                    raise ArithmeticError("signed norm or strict height bound failed")
                points.append((d, m, x, y))
                common = gcd(y, n)
                if common == 1:
                    r = x*pow(y, -1, n) % n
                    if (r*r-d) % n:
                        raise ArithmeticError("unit-denominator root failed verification")
                    if d not in first:
                        first[d] = (r, (d, m, x, y))
                    common = gcd(first[d][0]-r, n)
                if 1 < common < n and factor is None:
                    factor = common
                    witnesses = ([first[d][1]] if gcd(y, n) == 1 else []) + [(d, m, x, y)]
                    first_time = process_time_ns()-start
                    first_work = dict(work)
            if work["capped"]:
                break
        if work["capped"]:
            break
    if len(set(points)) != len(points):
        raise ArithmeticError("duplicate representation")
    return dict(targets=menu(n, "signed"), points=sorted(points), work=dict(work),
                complete=not work["capped"], factor=str(factor) if factor else None,
                witnesses=witnesses, first_work=first_work, first_cpu_ns=first_time)


def exact_points(n, d, m, domain="broad"):
    """Small independent oracle scans x directly and tests the signed quotient for y."""
    out = set()
    if domain == "unit" and m != unit_multiplier(n, d):
        return out
    cap = 3*n-1 if domain == "broad" else 6*n
    for x in range(isqrt(cap)+1):
        y2, rem = divmod(x*x-m*n, d)
        if rem or y2 < 0:
            continue
        y = isqrt(y2)
        if y*y == y2 and in_window(n, d, m, x, y, domain):
            out.add((x, y))
    return out


def check_small():
    cases = solutions = 0
    for n in range(2, 129):
        for d in (-6, -3, -2, -1, 1, 2, 3, 6):
            for m in MULTIPLIERS:
                expected = exact_points(n, d, m)
                for method in ("arcs", "direct"):
                    obtained = list(point_scan(n, d, m, method, Counter()))
                    if expected != set(obtained) or len(expected) != len(obtained):
                        raise ArithmeticError(f"incomplete point set for {n}, {d}, {m}, {method}")
                cases += 1
                solutions += len(expected)
    # Wide blocks exercise rounded slopes away from the automatic small-size width.
    for total, a, b, lo, hi in ((44011, 1, 3, 19, 134), (437, 2, 1, 7, 170),
                                 (81, 1, 1, 1, 120), (2211, 1, 6, 1, 999)):
        expected = []
        for u in range(lo, hi+1):
            value, rest = divmod(total+a*u*u, b)
            z = isqrt(value)
            if rest == 0 and z*z == value:
                expected.append((u, z))
        if sorted(integer_arc(total, a, b, lo, hi, Counter())) != expected:
            raise ArithmeticError("wide convex block disagrees with independent enumeration")
    return dict(signed_equations=cases, nonnegative_solutions=solutions, wide_blocks=4)


def holdouts():
    for bits in (16, 20):
        source = SEED+b"/"+str(bits).encode()
        kept = sample = 0
        while kept < 4:
            p, q = (draw_prime(side, sample, bits=bits, seed=source) for side in (b"p", b"q"))
            if p != q:
                yield bits, sample, p*q
                kept += 1
            sample += 1


def panel(repetitions):
    rows = []
    for bits, sample, n in holdouts():
        results = {}
        durations = {"arcs": [], "direct": []}
        first_times = {"arcs": [], "direct": []}
        for rep in range(repetitions):
            for method in (("arcs", "direct") if (sample+rep)%2 == 0 else ("direct", "arcs")):
                possible.cache_clear()
                start = process_time_ns()
                value = search(n, method)
                durations[method].append(process_time_ns()-start)
                first_times[method].append(value.pop("first_cpu_ns"))
                if method in results and value != results[method]:
                    raise ArithmeticError("non-repeatable computation")
                results[method] = value
        if not all(r["complete"] and r["factor"] for r in results.values()):
            raise ArithmeticError("a complete signed search missed a factor")
        if results["arcs"]["points"] != results["direct"]["points"]:
            raise ArithmeticError("the two methods enumerated different point sets")
        p = int(results["arcs"]["factor"])
        pair = sorted((p, n//p))
        if int(results["direct"]["factor"]) not in pair or n % p:
            raise ArithmeticError("the methods disagree on the factorization")
        rows.append(dict(bits=bits, sample=sample, n=str(n), pair=[str(x) for x in pair],
                         targets=results["arcs"]["targets"], representations=len(results["arcs"]["points"]),
                         methods={m: dict(work=v["work"], witnesses=v["witnesses"],
                                          first_work=v["first_work"], median_first_cpu_ns=int(median(first_times[m])),
                                          median_cpu_ns=int(median(durations[m]))) for m,v in results.items()},
                         certificate_sha256=certificate(n, pair)))
    return rows


def domain_size(n, domain):
    total_positions = total_blocks = 0
    for d in menu(n, "signed"):
        for m in (MULTIPLIERS if domain == "broad" else (unit_multiplier(n, d),)):
            if d < 0 and m < 0 or any(m*n % mod not in possible(d, mod) for mod in (16, 3)):
                continue
            for _, a, b, _, last in charts(n, d, m, Counter(), domain):
                width = max(1, cube_radius(8*isqrt(b*abs(m)*n)//a))
                total_positions += last
                total_blocks += (last+width-1)//width
    return total_positions, total_blocks


def full_size(domain="broad", arc_method="arcs"):
    source = json.loads((ROOT/"benchmarks/projected-divisor-wheel.json").read_text())
    rows = []
    for fixture in source:
        n = int(fixture["n"])
        if n.bit_length() != 2048:
            continue
        total_positions, total_blocks = domain_size(n, domain)
        methods = {}
        for method, caps in ((arc_method, {"max_blocks": 64}), ("direct", {"max_positions": 4096})):
            start = process_time_ns()
            result = search(n, method, domain=domain, **caps)
            methods[method] = dict(result, cap=caps, cpu_ns=process_time_ns()-start)
        rows.append(dict(id=fixture["id"], n=str(n), total_chart_positions=str(total_positions),
                         total_arc_blocks=str(total_blocks), methods=methods))
    return rows


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--repetitions", type=int, default=2)
    parser.add_argument("--check-small", action="store_true")
    args = parser.parse_args()
    if args.repetitions < 1:
        parser.error("repetitions must be positive")
    checks = check_small()
    result = checks if args.check_small else dict(
        seed=SEED.decode(), repetitions=args.repetitions, machine=platform.machine(), python=platform.python_version(),
        timing="Complete same-menu enumeration through the strict height bound, includes setup, all representations and gcd checks. Cold local residue tables. Large controls have separate caps.",
        checks=checks, rows=panel(args.repetitions), full_size=full_size())
    data = json.dumps(result, indent=2)+"\n"
    if args.output:
        args.output.write_text(data)
    else:
        print(data, end="")
