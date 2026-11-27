"""Run fixed rectangle schedules against the published twelve-key populations."""

import argparse
import json
from collections import Counter
from itertools import combinations
from math import gcd
from random import Random
from time import process_time

from experiments.factorial_progressions import search as factorial
from experiments.short_pascal_row import interval
from experiments.twelve_rectangle import search
from scripts.factor import primes_through


def run(bits, height, width, sample):
    primes = [p for p in primes_through((1 << bits)-1) if p.bit_length() == bits]
    if sample:
        rng = Random(86412)
        choices = set()
        while len(choices) < sample:
            p, q = sorted(rng.sample(primes, 2))
            if (p*q).bit_length() == 2*bits:
                choices.add((p, q))
        pairs = sorted(choices)
    else:
        pairs = ((p,q) for p,q in combinations(primes,2) if (p*q).bit_length() == 2*bits)
    modes = ("squares","screened_squares","twelve","expanded_twelve","folded_factorial","fourfold_span")
    totals = {m: Counter() for m in modes}
    examples, counts = {}, Counter()
    for p, q in pairs:
        n = p*q
        first = interval(n)[0]
        first_odd = first | 1
        guaranteed = p < first_odd+4*height*width
        expanded = p < first_odd+4*(height+2)*width
        counts["products"] += 1
        counts["smaller_prime_in_prefix"] += guaranteed
        counts["smaller_prime_in_expanded_prefix"] += expanded
        hits = {}
        for mode in modes:
            start = process_time()
            if mode in ("folded_factorial", "fourfold_span"):
                spans = 4 if mode == "fourfold_span" else 1
                row = factorial(n, first_odd-first+spans*4*height*width-1,
                                wheel=2, backend="binary", folded=True, equal_width=True)
                d, work, source, witness = row["factor"], row["work"], row["outcome"], []
            else:
                d, work, source, witness = search(n, height, width, mode)
            totals[mode]["cpu_seconds"] += process_time()-start
            if d is not None and d not in (p,q):
                raise ArithmeticError("incorrect recovered divisor")
            if guaranteed and not d:
                raise ArithmeticError("lost a factor in the guaranteed prefix")
            if mode == "expanded_twelve" and expanded and not d:
                raise ArithmeticError("lost a factor in the expanded guaranteed prefix")
            hits[mode] = bool(d)
            totals[mode]["splits"] += bool(d)
            if d:
                totals[mode][source] += 1
            for key, number in work.items():
                totals[mode][key] += number
            if mode == "twelve" and d and not hits["screened_squares"] and "extra" not in examples:
                examples["extra"] = dict(n=str(n), factors=[str(p),str(q)], first_odd=first_odd,
                                         last_odd=first_odd+4*height*width-2, work=work,
                                         source=source, witness=witness)
            if mode == "expanded_twelve" and d and not hits["squares"] and "wider" not in examples and expanded:
                examples["wider"] = dict(n=str(n), factors=[str(p),str(q)], first_odd=first_odd,
                                         last_odd=first_odd+4*(height+2)*width-2, work=work,
                                         source=source, witness=witness)
        counts["gained_vs_screened_squares"] += hits["twelve"] and not hits["screened_squares"]
        counts["lost_vs_screened_squares"] += hits["screened_squares"] and not hits["twelve"]
        counts["gained_vs_factorial"] += hits["twelve"] and not hits["folded_factorial"]
        counts["lost_vs_factorial"] += hits["folded_factorial"] and not hits["twelve"]
        counts["expanded_gained_vs_squares"] += hits["expanded_twelve"] and not hits["squares"]
        counts["expanded_lost_vs_squares"] += hits["squares"] and not hits["expanded_twelve"]
        counts["expanded_gained_vs_previous_twelve"] += hits["expanded_twelve"] and not hits["twelve"]
        counts["expanded_lost_vs_previous_twelve"] += hits["twelve"] and not hits["expanded_twelve"]
    return dict(prime_bits=bits, baby_count=height, giant_count=width,
                population="sample" if sample else "complete", counts=counts, modes=totals, examples=examples)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--bits", type=int, choices=(12,20,24), required=True)
    bits = parser.parse_args().bits
    dims = {12: (6,6,0), 20: (64,64,512), 24: (128,128,256)}
    print(json.dumps(run(bits, *dims[bits]), indent=2))
