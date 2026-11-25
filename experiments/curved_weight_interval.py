"""Integer endpoints of a weighted trace on the balanced hyperbola."""

from math import isqrt


def curved_interval(n, a, b, left, right):
    """Intersect [left,right] with the exact integer range of the continuous trace.

    A balanced positive pair has h²−d²=n and |d|≤h/3. Both signs of d
    are allowed. An empty intersection is represented by low > high.
    """
    u, v = abs(a+b), abs(a-b)
    high = isqrt((3*u+v)**2 * n // 8)
    if 3*v >= u:
        end = 3*u-v
        numerator = end*end*n
        # ceil(-sqrt(x)) = -floor(sqrt(x)); ceil(sqrt(0)) = 0.
        low = -isqrt(numerator//8) if end <= 0 else 1+isqrt((numerator-1)//8)
    else:
        low = 1+isqrt((u*u-v*v)*n-1)
    if a+b < 0:
        low, high = -high, -low
    return max(left, low), min(right, high)
