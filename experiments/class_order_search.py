"""Search for ambiguous positive definite forms of discriminant -N or -4N.

The search receives the odd product, a limit for split-prime seeds, and a
global composition budget. Its class-number upper bound uses no factor data.
"""

from math import gcd, isqrt
from experiments.local_midpoint_lanes import is_prime


class CompositionLimit(Exception):
    pass


def bezout(a, b):
    """Return g,u,v with g >= 0 and ua+vb=g."""
    r, s = a, b
    u, v, x, y = 1, 0, 0, 1
    while s:
        q = r // s
        r, s = s, r-q*s
        u, x = x, u-q*x
        v, y = y, v-q*y
    return (r, u, v) if r >= 0 else (-r, -u, -v)


class Forms:
    def __init__(self, discriminant, budget):
        self.discriminant = discriminant
        self.parity = discriminant % 2
        self.norm = (self.parity-discriminant)//4
        self.identity = self.reduce(1, self.parity)
        self.budget = budget
        self.compositions = 0

    def reduce(self, a, b):
        while True:
            b = a-(a-b) % (2*a)
            c, rem = divmod(b*b-self.discriminant, 4*a)
            if rem:
                raise ArithmeticError("inconsistent discriminant")
            if a <= c:
                return (a, abs(b) if a == c else b, c)
            a, b = c, -b

    def multiply(self, g, h):
        if self.compositions >= self.budget:
            raise CompositionLimit
        self.compositions += 1
        a, b, _ = g
        c, d, _ = h
        t, v = (b+self.parity)//2, (d+self.parity)//2
        ac_gcd, u, w = bezout(a, c)
        content, k, m = bezout(ac_gcd, self.parity-t-v)
        leading = (a//content)*(c//content)
        # A Bezout combination of product-ideal generators has second
        # coordinate equal to the content. Divide to get coefficient one.
        first = (-k*(u*a*v+w*c*t) + m*(t*v-self.norm))//content
        return self.reduce(leading, 2*((-first) % leading)-self.parity)

    def power(self, g, e):
        if e == 0:
            return self.identity
        result = g
        for bit in bin(e)[3:]:
            result = self.multiply(result, result)
            if bit == '1':
                result = self.multiply(result, g)
        return result

    def inverse(self, f):
        return self.reduce(f[0], -f[1])

    def seed(self, prime):
        D = self.discriminant
        if prime == 2:
            return self.reduce(2, 1) if D % 8 == 1 else None
        for b in range(self.parity, 2*prime, 2):
            if (b*b-D) % (4*prime) == 0:
                return self.reduce(prime, b)
        return None


def window_events(forms, x, low, high, work):
    """Yield an exact order, or successive annihilators in [low,high]."""
    width = high-low+1
    m = isqrt(width-1)+1
    babies = {forms.identity: 0}
    y = forms.identity
    for j in range(1, m+1):
        y = forms.multiply(y, x)
        if y == forms.identity:
            yield 'order', j
            return
        if j < m:
            babies[y] = j
    step = forms.inverse(y)
    y = forms.inverse(forms.power(x, low))
    for start in range(low, high+1, m):
        work['giant_lookups'] += 1
        j = babies.get(y)
        if j is not None and start+j <= high:
            yield 'hit', start+j
        if start+m <= high:
            y = forms.multiply(y, step)


def two_component(forms, g, annihilator):
    """Return x of 2-power order, its successive squares, and its involution."""
    odd = annihilator // (annihilator & -annihilator)
    x = forms.power(g, odd)
    powers = []
    while x != forms.identity:
        powers.append(x)
        x = forms.multiply(x, x)
        if len(powers) >= annihilator.bit_length():
            raise ArithmeticError("invalid annihilator")
    return powers


def from_form(n, f):
    a, b, c = f
    if b == 0 or b == a or a == c:
        for value in (a, c, 4*c-a, 2*a-b, 2*a+b):
            d = gcd(value, n)
            if 1 < d < n:
                return d
    return None


def search(n, prime_limit, max_compositions, shared=True):
    if n < 3 or n % 2 == 0 or isqrt(n)**2 == n:
        raise ValueError("expected an odd nonsquare integer of at least three")
    if prime_limit < 0 or max_compositions < 0:
        raise ValueError("negative budget")
    D = -n if n % 4 == 3 else -4*n
    forms = Forms(D, max_compositions)
    ceiling = isqrt(-D-1)+1
    upper = ceiling*((-D).bit_length()+2)//3
    divisor, known = 1, None
    work = dict(seeds=0, windows=0, giant_lookups=0, divisor_updates=[],
                known_class_number=None, max_compositions=max_compositions, prime_limit=prime_limit)
    components = []
    menu, seen = [], {forms.identity}

    def result(outcome, factor=None):
        return dict(work, outcome=outcome, factor=factor, compositions=forms.compositions)

    try:
        for r in range(2, prime_limit+1):
            if not is_prime(r):
                continue
            if n % r == 0:
                if r < n:
                    return result('seed prime divisor', r)
                continue
            g = forms.seed(r)
            if g is None:
                continue
            menu.append(g)
            seen.update((g, forms.inverse(g)))
        lower = len(seen)
        work['class_window'] = [str(lower), str(upper)]
        for g in menu:
            work['seeds'] += 1
            events, exact = None, None
            if known is not None:
                ann = known
            elif (x := forms.power(g, divisor)) == forms.identity:
                ann = divisor
            else:
                work['windows'] += 1
                low = (lower+divisor-1)//divisor
                events = window_events(forms, x, low, upper//divisor, work)
                kind, e = next(events)
                ann = divisor*e
                if kind == 'order':
                    exact = e
            powers = two_component(forms, g, ann)
            if powers:
                d = from_form(n, powers[-1])
                if d is not None:
                    return result('ambiguous form', d)
                components.append(powers)
            if shared and events is not None:
                if exact is None:
                    second = next(events, None)
                    if second is None:
                        known = ann
                        work['known_class_number'] = known
                    else:
                        exact = second[1]-e
                if exact is not None:
                    divisor *= exact
                    work['divisor_updates'].append(divisor)
                    if (lower+divisor-1)//divisor == upper//divisor:
                        known = divisor*(upper//divisor)
                        work['known_class_number'] = known
        if components:
            pivot = max(components, key=len)
            for powers in components:
                while powers and powers[-1] == pivot[-1]:
                    shifted = forms.multiply(powers[0], pivot[len(pivot)-len(powers)])
                    powers = two_component(forms, shifted, 1 << (len(powers)-1))
                if powers:
                    d = from_form(n, powers[-1]) or from_form(n, forms.multiply(powers[-1], pivot[-1]))
                    if d is not None:
                        return result('combined involutions', d)
        return result('seed limit')
    except CompositionLimit:
        return result('composition limit')
