"""Generate a certifiable prime pair in the stated offset interval before testing the search."""
import json
from math import isqrt

from scripts.factor import prime_witness


def construct():
    grid = 1 << 512
    anchor = 161*(1 << 1024)//256
    p_trials = q_trials = 0
    for i in range(anchor//grid, anchor//grid+16384):
        p = 1+grid*i
        p_trials += 1
        if prime_witness(p, 2) is None:
            continue
        # Using the ceiling and floor of the center's root rounds into the interval.
        root = isqrt(3*p//2)
        lower = (3*p+1)//2+2900*(root+1)
        upper = (3*p)//2+3530*root
        for j in range((lower+grid-2)//grid, (upper-1)//grid+1):
            q = 1+grid*j
            q_trials += 1
            if prime_witness(q, 2) is not None:
                return dict(n=str(p*q), factors=[str(p), str(q)], p_trials=p_trials, q_trials=q_trials)
    raise RuntimeError('no certifiable pair found on the bounded grid')


if __name__ == '__main__':
    print(json.dumps(construct(), indent=2))
