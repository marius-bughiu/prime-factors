"""Compare both exact quartic recognizers on small odd integers."""

from experiments.local_midpoint_lanes import is_prime
from experiments.quartic_product_strips import fourth_root, recognize


def recognize_y(n):
    y = fourth_root(n // 4)
    x = fourth_root(n - 4*y**4)
    if not x or not y or x**4 + 4*y**4 != n:
        return None
    midpoint, gap = x*x + 2*y*y, 2*x*y
    return midpoint - gap, midpoint + gap


def eligible(pair):
    if pair is None:
        return False
    p, q = pair
    return (p.bit_length() == q.bit_length() and (p*q).bit_length() == 2*p.bit_length()
            and is_prime(p) and is_prime(q))


def compare(limit):
    forward = set()
    reverse = set()
    for x in range(1, fourth_root(limit) + 1, 2):
        cap = min(limit, (x+1)**4 - 1)
        for y in range(1, fourth_root((cap - x**4) // 4) + 1):
            forward.add(x**4 + 4*y**4)
    for y in range(1, fourth_root(limit // 4) + 1):
        cap = min(limit, 4*(y+1)**4 - 1)
        for x in range(1, fourth_root(cap - 4*y**4) + 1, 2):
            reverse.add(x**4 + 4*y**4)
    both = sorted(forward & reverse)
    for n in forward | reverse:
        left, right = recognize(n), recognize_y(n)
        assert (left is not None) == (n in forward)
        assert (right is not None) == (n in reverse)
        assert all(p*q == n for p, q in (v for v in (left, right) if v))
    if limit <= 2**16:
        assert reverse == {n for n in range(1, limit+1, 2) if recognize_y(n)}
    same = [n for n in both if recognize(n) == recognize_y(n)]
    assert same == [n for n in (5, 145, 949) if n <= limit]
    return {
        "forward_only": len(forward - reverse),
        "reverse_only": len(reverse - forward),
        "both": len(both),
        "two_distinct_pairs": [n for n in both if n not in same],
        "forward_eligible": sum(eligible(recognize(n)) for n in forward),
        "additional_eligible": sum(eligible(recognize_y(n)) for n in reverse - forward),
    }


if __name__ == "__main__":
    for bits in (16, 24, 32):
        print(f"Through 2^{bits}: {compare(2**bits)}")
    assert recognize(2126389) is None and recognize_y(2126389) == (1213, 1753)
