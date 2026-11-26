"""Generate a Lean exclusion for a whole interval from consecutive-square bounds."""

from math import isqrt


def sum_interval_receipt(n, a, b, *, max_sums=256):
    """Return (Lean source, number of checked sums), rejecting incomplete certificates."""
    if n < 1 or n % 2 != 1 or a < 1 or a > b or b*b > n or max_sums < 0:
        raise ValueError('expected positive odd N, 1 <= a <= b <= floor(sqrt(N)), and a nonnegative cap')
    low, high = b+(n+b-1)//b, a+n//a
    first = low+(n+1-low) % 4
    count = max(0, (high-first)//4+1)
    if count > max_sums:
        raise ValueError(f'{count} admissible sums exceed the bound {max_sums}')
    floors = []
    for i in range(count):
        s = first+4*i
        delta = s*s-4*n
        root = isqrt(max(0, delta))
        if root*root == delta:
            raise ValueError(f'sum {s} has an exact square discriminant')
        floors.append(str(root))
    source = f'''import PrimeFactors.SumIntervalExclusion

namespace PrimeFactors.Generated
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

private def modulus : ℕ := {n}
private def lower : ℕ := {a}
private def upper : ℕ := {b}
private def first : ℕ := {first}
private def floors : List ℕ := [{', '.join(floors)}]

/-- Every possible odd-factor sum is accounted for by these consecutive-square checks. -/
theorem sumIntervalExclusion (p : ℕ) (lo : lower≤p) (hi : p≤upper) : ¬p∣modulus := by
  apply SumIntervalExclusion.excludes (first:=first) (hs:=floors) _ _ _ _ _ _ _ _ p lo hi <;> decide +kernel

#print axioms sumIntervalExclusion
end PrimeFactors.Generated
'''
    return source, count
