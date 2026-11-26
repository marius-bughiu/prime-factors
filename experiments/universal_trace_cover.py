"""Generate the 32 small rational partitions checked by UniversalTraceCover.lean."""

from fractions import Fraction
from math import floor, isqrt

from .trace_cover import cover_cost, envelope, solve


UNIT_RESIDUES = (1, 5, 7, 11)
BLOCK = 2**1011
SCALE = 2**990


def template(slab, residue):
    hi = (9 + slab) * 2**2044 - 1
    n = hi - (hi - residue) % 12
    end = Fraction(16, 8 + slab)
    plan = solve(n, 8, BLOCK-1, right=end)
    active = [i for _, _, i in plan['cells']]
    windows = [plan['windows'][i] for i in active]
    budgets = [max(1, plan['budgets'][i]) for i in active]
    # Once every selected row is charged a block the overlap usually widens.
    cells, gaps = envelope(n, windows, BLOCK-1, budgets, Fraction(1), end)
    if gaps:
        raise ArithmeticError('uncovered portable template')
    previous = Fraction(1)
    rows = []
    for j, (_, x, i) in enumerate(cells):
        if j+1 < len(cells):
            following = cells[j+1][2]
            def fits(t):
                return (previous <= t < end and cover_cost(n, windows[i], BLOCK-1, t) <= budgets[i]
                        and cover_cost(n, windows[following], BLOCK-1, t) <= budgets[following])
            for d in range(1, 4097):
                a = floor(x*d)
                value = next((r for r in (Fraction(a,d), Fraction(a+1,d)) if fits(r)), None)
                if value is not None:
                    x = value
                    break
        a, b, _, stride = windows[i]
        # Lower bound on the first phase, with a small exact significand.
        mantissa = isqrt(4*a*b*n) // SCALE
        reduced = (a, b, mantissa*SCALE, stride)
        if any(cover_cost(n, reduced, BLOCK-1, r) > budgets[i] for r in (previous, x)):
            raise ArithmeticError('rounded geometric lower bound lost a template endpoint')
        top, bottom = (16, 8 + slab) if j+1 == len(cells) else (x.numerator, x.denominator)
        rows.append((a, b, budgets[i], top, bottom, mantissa))
        previous = x
    return rows


def lean_data():
    result = []
    for j in range(8):
        for index, residue in enumerate(UNIT_RESIDUES):
            rows = template(j, residue)
            literals = ','.join('⟨'+','.join(map(str, row))+'⟩' for row in rows)
            result.append(f'  | {j}, {index} => [{literals}]')
    return '\n'.join(result)


if __name__ == '__main__':
    print(lean_data())
