"""Test bounded public width choices at the integer square root."""
from math import gcd, isqrt, prod
from time import perf_counter

from experiments.block_subresultant import probe
from experiments.mixed_ratio_heights import jacobi
from experiments.square_root_formula import readings_at


def search(n):
    """Run each comparison, even after a split, and retain every proper gcd."""
    if n < 25 or n % 2 == 0:
        raise ValueError('expected an odd input of at least 25')
    t = isqrt(n)
    gap = n-t*t
    values = dict(rectangle=gcd(prod(range(t-4,t+5)), n), **readings_at(n,t))
    values['reciprocal_companion'] = gcd(t*t-1,n)
    gcd_calls = len(values)
    selected = None
    symbols = []
    for m in range(3,16,2):
        m2 = m*m
        discriminant = 3*(3*(1+m2)**2-(m2-1)**3)
        symbol = jacobi(discriminant,n)
        symbols.append(symbol)
        if symbol == 0:
            values[f'discriminant_{m}'] = gcd(discriminant,n)
            gcd_calls += 1
        if symbol == -1:
            selected = m
            break

    if selected is not None:
        if selected == 3:
            selected_value = values['fixed_quartic']
        elif selected == 2*gap+3:
            selected_value = values['remainder_width']
        else:
            selected_value = probe(n,selected,t)
            gcd_calls += 1
        values['selected_pivot'] = selected_value

    hits = [name for name, divisor in values.items() if 1 < divisor < n]
    divisor = values[hits[0]] if hits else None
    return divisor, dict(
        outcome='proper_divisor' if hits else 'no_split', center=str(t), gap=str(gap),
        selected_width=selected, width_budget=7, jacobi_symbols=symbols,
        jacobi_tests=len(symbols), square_roots=1, gcd_calls=gcd_calls,
        rectangle_positions=9, gcds={name:str(value) for name,value in values.items()},
        successful_checks=hits,
    )


def adaptive_quartic_case(case, proof, agree, certify_split):
    started = perf_counter()
    divisor, report = search(int(case['n']))
    elapsed = perf_counter()-started
    agree(dict(id=case['id'], **case['checks']), report, case['checks'])
    return certify_split(case, proof, divisor, elapsed, 'adaptive_quartic', report)
