"""Finite census of small totient denominators and actual Euclidean convergents."""
import argparse
from fractions import Fraction
from itertools import combinations
import json
from math import gcd, isqrt, lcm
from pathlib import Path

from experiments.continued_square import convergents
from scripts.factor import primes_through

ROOT = Path(__file__).resolve().parents[1]
RECORD = ROOT / "research/power-denominator-census.json"
SHORT_POWER = lcm(*range(1,9))
LONG_POWER = lcm(*range(1,17))


def menu(n):
    return (("one", 1), ("product_minus_one", n-1), ("half_predecessor", (n-1)//2),
            ("lcm_through_8", SHORT_POWER), ("lcm_through_16", LONG_POWER))


def probe(n, e, *, gate=True, factor_bits=None, early_stop=False):
    """Public convergent search, including every totient check in the finite list."""
    if n < 2 or not 1 <= e <= n:
        raise ValueError("expected a positive exponent at most the product")
    if factor_bits is not None and factor_bits < 2:
        raise ValueError("the common odd-prime width must be at least two")
    if early_stop and factor_bits is None:
        raise ValueError("early stopping requires the common prime width")
    remainder = n%e
    passed = (remainder+1)**2 >= 4*n
    result = dict(remainder=str(remainder), passed=passed, convergents=0, integer_totients=0,
                  width_survivors=0, square_tests=0, pair=[], witness=None)
    if early_stop:
        result["stopped_early"] = False
    if gate and not passed:
        return result
    for a,b in convergents(e,n):
        result["convergents"] += 1
        if not a:
            continue
        if early_stop:
            residual = n*a-e*b
            if residual == 0:
                break
            if 0 < residual < a*(1<<factor_bits):
                result["stopped_early"] = True
                break
        phi, leftover = divmod(e*b,a)
        if leftover or not 0<phi<n:
            continue
        result["integer_totients"] += 1
        if factor_bits is not None:
            deficit = n-phi
            if not (1<<factor_bits) <= deficit < (2<<factor_bits):
                continue
            result["width_survivors"] += 1
        total = n+1-phi
        discriminant = total*total-4*n
        if discriminant < 0:
            continue
        root = isqrt(discriminant)
        result["square_tests"] += 1
        if root*root == discriminant and (total-root)%2 == 0:
            p,q = (total-root)//2,(total+root)//2
            if 1<p<=q and p*q==n:
                result["pair"] = [str(p),str(q)]
                result["witness"] = dict(index=result["convergents"], numerator=str(a),
                                         denominator=str(b), totient=str(phi), sum=str(total))
    return result



def run_fixture(case):
    if case["exponent_rule"] != "lcm_through_16":
        raise ValueError("the benchmark fixes the exponent at lcm(1,...,16)")
    bits = case["factor_bits"]
    work = probe(int(case["n"]), LONG_POWER, factor_bits=bits)
    return dict(exponent=str(LONG_POWER), factor_bits=bits, deficit_lower=str(1<<bits),
                deficit_upper_exclusive=str(2<<bits), **work)


def diagnostic(p, q, e):
    """Factors enter only in identification of the target and retrospective checks."""
    n = p*q
    if not 1 <= e <= n:
        raise ValueError("the finite criterion assumes 1 <= exponent <= product")
    fractions = list(convergents(e,n))
    left, right = p-1, q-1
    phi = left*right
    target = Fraction(e, phi)
    a, b = target.numerator, target.denominator
    x, y = left//gcd(left,e), right//gcd(right,e)
    bound = gcd(left,right)*x*y
    if bound % b:
        raise ArithmeticError("the true denominator failed to divide the image bound")
    delta = n-phi
    image = 2*bound**2*delta < phi
    uniform = 2*b*b*delta < phi
    exact = 2*b*b*e*delta < n*phi
    index = next((i for i,r in enumerate(fractions,1) if r==(a,b)), None)
    hit = index is not None
    if ((image and not uniform) or (uniform and not exact) or (exact and not hit)):
        raise ArithmeticError("a sufficient continued-fraction criterion failed")
    last_multiple = e*(n//e)
    remainder_gate = (n%e+1)**2 >= 4*n
    if hit and (phi < last_multiple or not remainder_gate):
        raise ArithmeticError("a true totient ratio failed the public remainder gate")
    raw, screened = probe(n,e,gate=False), probe(n,e)
    by_width = probe(n,e,factor_bits=p.bit_length())
    if q.bit_length()!=p.bit_length() or by_width["width_survivors"]>1:
        raise ArithmeticError("the same-width dyadic deficit condition failed")
    pair = [str(p),str(q)] if hit else []
    if (any(result["pair"]!=pair for result in (raw,screened,by_width))
            or raw["convergents"] != len(fractions)):
        raise ArithmeticError("the public search disagrees with the diagnostic ratio")
    if hit and e*b != phi*a:
        raise ArithmeticError("the identified fraction failed its totient identity")
    return dict(uniform=uniform, image=image, exact=exact, hit=hit, index=index,
                numerator=a, denominator=b, image_sizes=[x,y],
                floor_guess=last_multiple==phi, remainder_gate=remainder_gate,
                convergent_count=len(fractions), ungated_square_tests=raw["square_tests"],
                gated_square_tests=screened["square_tests"],
                integer_totients_without_gate=raw["integer_totients"],
                integer_totients_with_gate=screened["integer_totients"],
                width_survivors=by_width["width_survivors"], width_square_tests=by_width["square_tests"])


def blank():
    return dict(eligible=0, passed_remainder_gate=0, convergents_without_gate=0,
                convergents_with_gate=0, square_tests_without_gate=0, square_tests_with_gate=0,
                integer_totients_without_gate=0, integer_totients_with_gate=0, width_survivors=0,
                width_square_tests=0, hits_after_gate=0, denominator_test=0,
                image_bound_test=0, scaled_legendre_test=0, uniform_hit_neither_image_trivial=0,
                on_convergent_list=0, on_list_without_denominator_test=0,
                hit_reciprocal=0, hit_integer=0, hit_both_terms_greater_than_one=0,
                hit_floor_multiple=0, hit_both_images_trivial=0, hit_one_image_trivial=0,
                hit_neither_image_trivial=0, examples={})


def add(out, d, n, e):
    out["eligible"] += 1
    out["passed_remainder_gate"] += d["remainder_gate"]
    out["convergents_without_gate"] += d["convergent_count"]
    out["convergents_with_gate"] += d["convergent_count"] if d["remainder_gate"] else 0
    out["square_tests_without_gate"] += d["ungated_square_tests"]
    out["square_tests_with_gate"] += d["gated_square_tests"]
    for key in ("integer_totients_without_gate","integer_totients_with_gate","width_survivors","width_square_tests"):
        out[key] += d[key]
    out["hits_after_gate"] += d["hit"] and d["remainder_gate"]
    out["uniform_hit_neither_image_trivial"] += d["uniform"] and min(d["image_sizes"])>1
    out["denominator_test"] += d["uniform"]
    out["image_bound_test"] += d["image"]
    out["scaled_legendre_test"] += d["exact"]
    if not d["hit"]:
        return
    out["on_convergent_list"] += 1
    out["on_list_without_denominator_test"] += not d["uniform"]
    out["hit_reciprocal"] += d["numerator"]==1
    out["hit_integer"] += d["denominator"]==1
    out["hit_both_terms_greater_than_one"] += min(d["numerator"],d["denominator"])>1
    out["hit_floor_multiple"] += d["floor_guess"]
    trivial = d["image_sizes"].count(1)
    out[("hit_neither_image_trivial","hit_one_image_trivial","hit_both_images_trivial")[trivial]] += 1
    categories = ["first_by_prime_pair"]
    if d["uniform"]:
        categories.append("first_denominator_pass")
    if min(d["numerator"],d["denominator"])>1 and trivial==0:
        categories.append("first_nontrivial_fraction_and_images")
    for category in categories:
        if category not in out["examples"]:
            out["examples"][category] = dict(n=str(n), exponent=str(e), **d)


def census():
    cells = []
    for bits in (9,10,11):
        primes = [p for p in primes_through((1<<bits)-1) if p >= 1<<(bits-1)]
        methods = {name:blank() for name,_ in menu(1)}
        union = dict(products=0, uniform=0, image=0, exact=0, hit=0, floor_guess=0, remainder_gate=0,
                     hit_beyond_floor_guess=0)
        for p,q in combinations(primes,2):
            n=p*q
            observed = []
            for name,e in menu(n):
                if 1<=e<=n:
                    diagnostic_row = diagnostic(p,q,e)
                    add(methods[name],diagnostic_row,n,e)
                    observed.append(diagnostic_row)
            union["products"] += 1
            for key in ("uniform","image","exact","hit","floor_guess","remainder_gate"):
                union[key] += any(r[key] for r in observed)
            union["hit_beyond_floor_guess"] += any(r["hit"] for r in observed) and not any(
                r["floor_guess"] for r in observed)
        cells.append(dict(factor_bits=bits, prime_count=len(primes), totals=union, choices=methods))
    return dict(
        population="All p<q of the given common bit width, matching wrapped-gap-census.json.",
        public_choices="1, N−1, (N−1)/2, lcm(1..8), lcm(1..16); retain 1≤E≤N.",
        denominator_test="2*b²*(N−F)<F for E/F=a/b in lowest terms, F=(p−1)(q−1).",
        image_bound_test="Same test with b replaced by gcd(p−1,q−1)*X*Y.",
        scaled_legendre_test="2*b²*E*(N−F)<N*F, the sufficient condition using the actual E/N.",
        convergents="Standard finite Euclidean expansion of the public E/N, one-based positions.",
        floor_guess="The one public totient candidate E*floor(N/E).",
        remainder_gate="Reject before continued fractions whenever (N mod E + 1)² < 4N. Every true hit has p+q−1 ≤ N mod E.",
        width_band="After passing the public gate, test 2^k ≤ N−F_candidate < 2^(k+1) on every integral positive F_candidate below N (k is the common prime width).",
        work="Convergent counts are full-list enumerations, including 0/1 and the final convergent. Each eligible exponent gets one public remainder gate.",
        diagnostics="X=(p−1)/gcd(p−1,E) and Y=(q−1)/gcd(q−1,E). Known factors label the targets and conditions only.",
        cells=cells)


if __name__ == "__main__":
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument("--check",action="store_true")
    cli.add_argument("--write",action="store_true")
    args=cli.parse_args()
    text=json.dumps(census(),indent=2)+"\n"
    if args.check:
        if RECORD.read_text()!=text:
            raise SystemExit("powered denominator census differs")
    elif args.write:
        RECORD.write_text(text)
    else:
        print(text,end="")
