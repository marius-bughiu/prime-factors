"""Compare complete signed conic charts in integer and congruence-tangent coordinates."""

import argparse
from collections import Counter
import json
from math import gcd, isqrt, prod
from pathlib import Path
from statistics import median
from time import process_time_ns

from experiments.phase_interval import approximate_slope, cube_radius
from experiments.salie_reference import ceil_div
from experiments.signed_norm_arcs import axes, charts, exact_points, holdouts, menu, point_scan, possible, unit_multiplier
from scripts.factor import primes_through


def modulus(total, a, b, sign, level):
    """Select split primes using the public equation and combine their local slopes by CRT."""
    limit = 257 if level == "through257" else 61
    primes = [p for p in primes_through(limit) if
              gcd(2*a*b*total, p) == 1 and pow(sign*a*b, (p-1)//2, p) == 1]
    if level != "through257":
        primes = primes[:2 if level == "pair" else 1]
    factors = [p*p if level == 2 else p for p in primes]
    h = prod(factors)
    t = 0
    for f in factors:
        local = next(t for t in range(1, f) if (b*t*t-sign*a) % f == 0)
        t += local*(h//f)*pow(h//f, -1, f)
    return h, t % h, prod(f-f//p for p,f in zip(primes,factors))


def split_basis(total, a, b, sign, level):
    """Enumerate each unit parameter and construct its full tangent lattice."""
    h,t,_ = modulus(total,a,b,sign,level)
    c = total*pow(b, -1, h) % h
    for left in range(1, h):
        if gcd(left,h) != 1:
            continue
        right = c*pow(left, -1, h) % h
        r, s = (right-left)*pow(2*t, -1, h) % h, (right+left)*pow(2, -1, h) % h
        residual, extra = divmod(b*s*s-sign*a*r*r-total, h)
        if extra:
            raise ArithmeticError("point parameterization failed")
        alpha, beta = -2*sign*a*r, 2*b*s
        g = gcd(beta, h)
        mod = h//g
        i0 = -residual*pow(alpha, -1, g) % g if g > 1 else 0
        j0 = -(residual+alpha*i0)//g * pow(beta//g, -1, mod) % mod if mod > 1 else 0
        k = -alpha*pow(beta//g, -1, mod) % mod if mod > 1 else 0
        if (residual + alpha*i0 + beta*j0) % h or (alpha*g + beta*k) % h:
            raise ArithmeticError("tangent congruence failed")
        yield h, g, r+h*i0, s+h*j0, h*g, h*k, h*mod


def block(total, a, b, sign, u0, z0, step, shear, height, width, work):
    """Enclose v=(z-z0-shear*j)/height at u=u0+step*j by integer lines."""
    span = width-1
    scale = 4*(a+b+1)*width**2
    end = u0+step*span
    left = isqrt((total+sign*a*u0*u0)*scale**2//b)
    right = isqrt((total+sign*a*end*end)*scale**2//b)
    tangent_n, tangent_d = step*a*u0*scale, b*(left+1)
    chord_n, chord_d = step*a*(u0+end)*scale, b*(left+right)
    if sign < 0:
        tangent_n, tangent_d, chord_n, chord_d = -chord_n, chord_d, -tangent_n, tangent_d
    low_num, low_den = tangent_n-shear*tangent_d, height*tangent_d
    high_num, high_den = chord_n-shear*chord_d, height*chord_d
    den, residue, steps = approximate_slope(low_num, low_den, width)
    if not 1 <= den <= width or abs(residue)*span > low_den:
        raise ArithmeticError("invalid rational slope approximation")
    num = (den*low_num-residue)//low_den
    work["euclidean_steps"] += steps
    ll = left-scale*z0
    scale_y = scale*height
    lower = ceil_div(den*ll*low_den + scale_y*min(0, residue)*span, scale_y*low_den)
    upper = (den*(ll+1)*high_den + scale_y*max(0, den*high_num-num*high_den)*span)//(scale_y*high_den)
    work["max_lines_per_block"] = max(work["max_lines_per_block"], max(0,upper-lower+1))
    angular = shear*den + height*num
    quadratic = b*angular**2-sign*a*(den*step)**2
    for intercept in range(lower, upper+1):
        work["line_tests"] += 1
        constant_y = den*z0+height*intercept
        linear = b*angular*constant_y-sign*a*den**2*u0*step
        constant = b*constant_y**2-den**2*(total+sign*a*u0*u0)
        if quadratic:
            delta = linear**2-quadratic*constant
            if delta < 0:
                continue
            work["discriminant_roots"] += 1
            root = isqrt(delta)
            if root*root != delta:
                continue
            offsets = [(root-linear, quadratic)]
            if root:
                offsets.append((-root-linear, quadratic))
        elif linear:
            offsets = [(-constant, 2*linear)]
        else:
            if constant == 0:
                raise ArithmeticError("whole line on a nondegenerate conic")
            continue
        for numerator, denominator in offsets:
            j, extra = divmod(numerator, denominator)
            if extra or not 0 <= j <= span:
                continue
            v, extra = divmod(intercept+num*j, den)
            if extra:
                continue
            u, z = u0+step*j, z0+shear*j+height*v
            if z>0:
                if b*z*z != total+sign*a*u*u:
                    raise ArithmeticError("line recovery failed")
                yield u, z


def scan(n, d, m, level, work):
    if level == 0:
        yield from point_scan(n, d, m, "integer_arcs", work, domain="unit")
        return
    if (d < 0 and m < 0) or any(m*n % h not in possible(d,h) for h in (16,3)):
        return
    yield from axes(n,d,m,work,"unit")
    total = abs(m)*n
    for hyperbolic,a,b,swapped,last in charts(n,d,m,work,"unit"):
        sign = 1 if hyperbolic else -1
        work["bound_isqrts"] += 1
        width = max(1,cube_radius(8*isqrt(b*total)//a))
        for h,g,r,s,step,shear,height in split_basis(total,a,b,sign,level):
            work["classes"] += 1
            first, stop = ceil_div(1-r,step), (last-r)//step+1
            w = max(1,width//g)
            for i in range(first,stop,w):
                used = min(w,stop-i)
                work["blocks"] += 1
                work["endpoint_isqrts"] += 2
                for u,z in block(total,a,b,sign,r+step*i,s+shear*i,step,shear,height,used,work):
                    if hyperbolic or not swapped or a*u*u != b*z*z:
                        yield (z,u) if swapped else (u,z)


def collect(n, level):
    work = Counter()
    points = []
    for d in menu(n, "signed"):
        m = unit_multiplier(n,d)
        for x,y in scan(n,d,m,level,work):
            points.append((d,m,x,y))
    if len(points) != len(set(points)):
        raise ArithmeticError("duplicate conic point")
    counts = {k: work[k] for k in ("classes", "blocks", "endpoint_isqrts", "euclidean_steps",
                                     "line_tests", "discriminant_roots", "max_lines_per_block")}
    return sorted(points), counts


def validate_small():
    count = 0
    for n in [35,65,77,143,221,323,391,667,899,1147]:
        for d in (-6,-3,-2,-1,2,3,6):
            m = unit_multiplier(n,d)
            expected = sorted(exact_points(n,d,m,domain="unit"))
            for level in (1,2,"pair"):
                actual = sorted(scan(n,d,m,level,Counter()))
                if expected != actual:
                    raise ArithmeticError((n,d,m,level,expected,actual))
                count += 1
    return count


def panel(reps):
    from hashlib import sha256
    rows = []
    for bits,sample,n in holdouts():
        levels = (0,1,2,"pair")
        results, times = {}, {level:[] for level in levels}
        wanted = None
        for turn in range(reps):
            for level in levels[turn%len(levels):]+levels[:turn%len(levels)]:
                possible.cache_clear()
                start = process_time_ns()
                points, counts = collect(n, level)
                times[level].append(process_time_ns()-start)
                if wanted is not None and wanted != points:
                    raise ArithmeticError((n,level,"point sets disagree"))
                wanted = points
                results[str(level)] = counts
        for level in levels:
            results[str(level)]["median_cpu_ns"] = int(median(times[level]))
        rows.append(dict(bits_per_prime=bits, sample=sample, n=str(n), points=len(wanted),
                         points_sha256=sha256(json.dumps(wanted).encode()).hexdigest(),levels=results))
    return rows


def full_size():
    """Count ordinary setup exactly and bound tangent setup without visiting its classes."""
    from experiments.signed_norm_arcs import ROOT
    out = []
    fixtures = json.loads((ROOT/"benchmarks/projected-divisor-wheel.json").read_text())
    for fixture in fixtures:
        n = int(fixture["n"])
        if n.bit_length() != 2048:
            continue
        ordinary = upper = classes = 0
        for d in menu(n, "signed"):
            m = unit_multiplier(n,d)
            if any(m*n % h not in possible(d,h) for h in (16,3)):
                continue
            total = abs(m)*n
            for hyperbolic,a,b,_,last in charts(n,d,m,Counter(),"unit"):
                w = max(1,cube_radius(8*isqrt(b*total)//a))
                h,_,phi = modulus(total,a,b,1 if hyperbolic else -1,"through257")
                if not 0<h<=w or not last:
                    raise ArithmeticError("finite stride bound unavailable")
                ordinary += ceil_div(last,w)
                upper += phi*ceil_div(last,h*(w-h+1))
                classes += phi
        out.append(dict(id=fixture["id"],product=str(n),split_limit=257,classes=str(classes),
                        ordinary_blocks=str(ordinary),tangent_block_upper=str(upper),
                        upper_ppm=ceil_div(1000000*upper,ordinary),scanned_blocks=0,remaining=[str(n)]))
    return out


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repetitions", type=int, default=3)
    parser.add_argument("--check-small", action="store_true")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if args.repetitions < 1:
        parser.error("at least one repetition required")
    result = {"exact_coordinate_checks":validate_small()}
    if not args.check_small:
        result["timing_repetitions"] = args.repetitions
        result["rows"] = panel(args.repetitions)
        result["full_size_block_bounds"] = full_size()
    text = json.dumps(result,indent=2)+"\n"
    if args.output:
        args.output.write_text(text)
    else:
        print(text,end="")
