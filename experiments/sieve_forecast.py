"""Exact full-period counts and certified exceptional-row bounds for a primorial.

The input bit width sets an upper envelope on the signed trace window. No
candidate factors, rows, period residues, or divisors of the primorial are
enumerated. All counts and comparisons are integer arithmetic.
"""
import argparse
import json
from math import isqrt, prod


def primes_through(limit):
    return [p for p in range(2, limit + 1)
            if all(p % d for d in range(2, isqrt(p) + 1))]


def coefficients(primes, selected, weights):
    """Each selected prime's second choice raises the degree by one."""
    counts = [1]
    for p in primes:
        keep, fail = weights(p)
        if p in selected:
            counts = [keep*a + fail*b for a, b in zip(counts + [0], [0] + counts)]
        else:
            counts = [(keep+fail)*a for a in counts]
    return counts


def strict_tails(counts):
    """Entry h sums coefficients of degree greater than h."""
    total = sum(counts)
    tails = []
    for n in counts:
        total -= n
        tails.append(total)
    return tails


def max_failures(selected, max_product):
    product, count = 1, 0
    for p in sorted(selected):
        if product*p > max_product:
            break
        product *= p
        count += 1
    return count


def dense_records(rows, width):
    """Fixed public table size using the supplied upper bound on row count."""
    if not rows:
        return 0
    babies = min(width, 1 + isqrt(rows*width - 1))
    return babies + rows*((width+babies-1)//babies)


def forecast(bits=2048, last_prime=293, first_selected=19):
    primes = primes_through(last_prime)
    selected = {p for p in primes if p >= first_selected}
    if (bits < 2 or not primes or primes[-1] != last_prime
            or not selected or 2 in selected):
        raise ValueError("need a bit width >=2, a prime endpoint and selected odd primes")
    m = prod(primes)
    if m <= 4:
        raise ValueError("the signed nonzero coefficient bound assumes m > 4")
    period = prod(selected)
    phi = prod(p-1 for p in primes)
    height = 2*isqrt(m)+2
    # floor(sqrt(N))+1 <= ceil(sqrt(2^bits)) for N < 2^bits.
    s = 1 + isqrt((1 << bits)-1)
    width = 2*(3*s*height//(m*m)+2)+1
    short = isqrt(7*m//6)
    max_bad = max_failures(selected, short)
    dcrit = (128*3**len(primes)*max(m, width)+m-1)//m

    def counts_at_prime(p):
        sign = 1 if p % 4 == 1 else -1
        fail = (p-sign)//4
        return p-fail, fail

    period_tails = strict_tails(coefficients(sorted(selected), selected, counts_at_prime))

    def roots(p):
        return 1 if p == 2 else 2

    basic = strict_tails(coefficients(primes, selected, lambda p: (roots(p)*p*p, p-1)))
    # The common denominator of the basic tail is m².
    raw = [2*short**2 * term//(m*m) for term in basic]
    best = [min(phi, v) for v in raw]
    chosen = ["unit_rows" if v >= phi else "root_bound" for v in raw]

    # k contains each prefix prime present in m/d. Count v in its progression
    # modulo k before charging roots at the remaining primes.
    for last in primes:
        main = strict_tails(coefficients(primes, selected, lambda p:
            (p*(p-1) if p <= last else roots(p)*p*p, p-1)))
        error = strict_tails(coefficients(primes, selected, lambda p:
            (p*(p-1) if p <= last else roots(p)*p, p-1)))
        for h in range(len(best)):
            bound = (2*short**2*main[h] + short*m*error[h])//(m*m)
            if bound < best[h]:
                best[h], chosen[h] = bound, last

    schedule = []
    for h, excluded in enumerate(period_tails):
        if h >= max_bad:
            best[h], chosen[h] = 0, "height"
        retained = period-excluded
        ordinary = retained*((width-1+period + period-1)//period)
        schedule.append(dict(h=h, excluded=excluded, retained=retained,
                             root_row_bound=raw[h], row_bound=best[h], bound_source=chosen[h],
                             ordinary_baby_upper=ordinary,
                             dense_record_upper=dense_records(best[h], width)))
    return dict(bits=bits, m=m, period=period, phi=phi, height=height,
                shortest_height=short, width=width, prime_count=len(primes),
                selected_count=len(selected), max_failures_from_height=max_bad,
                dcrit=dcrit, h_for_dcrit=max_failures(selected, dcrit-1),
                dense_all_records=dense_records(phi, width), schedule=schedule)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--bits", type=int, default=2048)
    parser.add_argument("--last-prime", type=int, default=293)
    parser.add_argument("--first-selected", type=int, default=19)
    parser.add_argument("--h", type=int, action="append", help="report only these allowances")
    args = parser.parse_args()
    result = forecast(args.bits, args.last_prime, args.first_selected)
    if args.h:
        result["schedule"] = [row for row in result["schedule"] if row["h"] in args.h]
    print(json.dumps(result, indent=2))
