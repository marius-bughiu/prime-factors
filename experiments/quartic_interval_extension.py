"""Extend a certified quartic across the connected interval where |F(x)| < d²."""

from collections import Counter
from math import comb, gcd

from experiments.norm_auxiliary import integer_roots
from experiments.quartic_divisor_window import checked_height, evaluate


def _first_true(left, right, predicate):
    """First true integer of a monotone predicate on [left,right), or right."""
    while left < right:
        middle = (left+right)//2
        if predicate(middle):
            right = middle
        else:
            left = middle+1
    return left


def _sign_runs(coefficients, lower, upper, work):
    """Partition the integer interval into runs of constant sign, including zeros."""
    coefficients = list(coefficients)
    while len(coefficients)>1 and not coefficients[-1]:
        coefficients.pop()
    if lower > upper:
        return []
    def value(x):
        work['sign_evaluations'] += 1
        return evaluate(coefficients,x)
    if lower == upper or len(coefficients)==1:
        v = value(lower)
        return [(lower,upper,(v>0)-(v<0))]
    # The forward difference has smaller degree. Each of its constant-sign
    # runs [a,b] makes the original polynomial monotone on [a,b+1].
    diff = [sum(coefficients[i]*comb(i,j) for i in range(j+1,len(coefficients)))
            for j in range(len(coefficients)-1)]
    runs = []
    for left,right,sign in _sign_runs(diff,lower,upper-1,work):
        if runs:
            left = max(left,runs[-1][1]+1)
        stop = right+2
        direction = -1 if sign<0 else 1
        zero = _first_true(left,stop,lambda x: direction*value(x)>=0)
        positive = _first_true(zero,stop,lambda x: direction*value(x)>0)
        for a,b,label in [(left,zero-1,-direction),(zero,positive-1,0),(positive,stop-1,direction)]:
            if a<=b:
                if runs and runs[-1][2]==label:
                    a = runs.pop()[0]
                runs.append((a,b,label))
    return runs


def _bernstein_positive(coefficients, left, right):
    """Positive coefficients in the degree-four homogeneous interval basis."""
    width = right-left
    terms = [width**i*sum(comb(j,i)*coefficients[j]*left**(j-i) for j in range(i,5))
             for i in range(5)]
    return all(sum(comb(4-i,k-i)*terms[i] for i in range(k+1))>0 for k in range(5))


def extend(work, *, lower=None, upper=None):
    """Extend the same row with no new reduction. The default domain is [1,N].

    The returned component contains the original center. When the domain contains
    the old window it includes that entire window, as certified by its height bound.
    """
    n,c,s,w = work['n'],work['center'],work['stride'],work['radius']
    t,f = work['anchor'],work['coefficients']
    if n<2 or min(s,w,c-s*w)<1 or gcd(s,n)!=1 or (c+s*t)%n:
        raise ValueError('invalid original progression or anchor')
    height = checked_height(n,t,w,f)
    if not work['relation_verified'] or height!=work['height'] or height>=(c-s*w)**2:
        raise ValueError('expected a verified quartic')
    m = work['rootless_modulus']
    residue_tests = 0
    if m is not None:
        if not 2<=m<=work['modulus_limit']:
            raise ValueError('invalid rootless modulus')
        local = [coefficient%m for coefficient in f]
        for r in range(m):
            residue_tests += 1
            if evaluate(local,r)%m == 0:
                raise ValueError('the supplied modulus admits a quartic root')
    lower = 1 if lower is None else lower
    upper = n if upper is None else upper
    if not 1<=lower<=c<=upper<=n:
        raise ValueError('expected a divisor domain containing the center')
    xlo,xhi = -((c-lower)//s),(upper-c)//s
    square = [c*c,2*c*s,s*s,0,0]
    margins = [[a+sign*b for a,b in zip(square,f)] for sign in (1,-1)]
    counts = Counter(sign_evaluations=0, bernstein_tests=0, integer_root_nodes=0, divisor_tests=0)
    runs = [_sign_runs(g,xlo,xhi,counts) for g in margins]
    # The two positive runs containing zero intersect in the required component.
    spans = [next((a,b) for a,b,sign in parts if a<=0<=b and sign==1) for parts in runs]
    first,last = max(a for a,_ in spans),min(b for _,b in spans)
    cuts = []
    pending = [(first,last)]
    while pending:
        a,b = pending.pop()
        counts['bernstein_tests'] += 1
        if all(_bernstein_positive(g,a,b) for g in margins):
            cuts.append(b)
        elif a < b:
            mid = (a+b)//2
            pending.extend([(mid+1,b),(a,mid)])
        else:
            raise ArithmeticError('positive singleton failed its Bernstein check')
    inside = lambda x: abs(evaluate(f,x)) < (c+s*x)**2
    left_fails = first>xlo and not inside(first-1)
    right_fails = last<xhi and not inside(last+1)
    if (first>xlo and not left_fails) or (last<xhi and not right_fails):
        raise ArithmeticError('neighbor passes the strict magnitude bound')
    roots = [] if m is not None else sorted(integer_roots(f,first,last,counts))
    hits = []
    for x in roots:
        d = c+s*x
        counts['divisor_tests'] += 1
        q,remainder = divmod(n,d)
        if not remainder:
            hits.append(dict(offset=x,divisor=d,cofactor=q))
    covers_interval = s==1 or (s==2 and n%2==1 and c%2==1)
    return dict(n=n,center=c,stride=s,anchor=t,coefficients=f,
                rootless_modulus=m,domain_lower=lower,domain_upper=upper,
                first_offset=first,last_offset=last,lower=c+s*first,upper=c+s*last,
                interval_size=s*(last-first)+1,progression_size=last-first+1,
                previous_progression_size=2*w+1,left_neighbor_fails=left_fails,
                right_neighbor_fails=right_fails,cuts=cuts[:-1],certified_blocks=len(cuts),
                anchor_checks=1,jet_checks=2,height_checks=1,rootless_residue_checks=residue_tests,
                neighbor_tests=int(first>xlo)+int(last<xhi),covers_interval=covers_interval,
                additional_lll_calls=0,**counts,roots=roots,hits=hits,
                divisors=sorted(hit['divisor'] for hit in hits),
                progression_excluded=not hits,excluded=covers_interval and not hits)
