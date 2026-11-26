"""Replay the public square-root shift and certify an independently discovered prime split."""

from time import perf_counter

from experiments.block_subresultant import search


def block_subresultant_case(case, proof, agree, certify_split):
    start = perf_counter()
    divisor, work = search(int(case["n"]))
    elapsed = perf_counter() - start
    agree(dict(id=case["id"], **case["checks"]), work, case["checks"])
    return certify_split(case, proof, divisor, elapsed, "block_subresultant", work)
