"""Generate admissible odd factor positions from the sums in the top 2% below sqrt(n)."""
from math import gcd, isqrt

PRIME = 211
WIDTH = 4*PRIME


def endpoints(n):
    if n < 3 or n % 2 == 0:
        raise ValueError('expected an odd integer at least three')
    return (isqrt(2401*n-1)+50)//50, isqrt(n)


def square_table():
    roots = [[] for _ in range(PRIME)]
    for x in range(PRIME):
        roots[x*x % PRIME].append(x)
    return roots


def wheel_count(a, b):
    """Number of odd integers in [a,b] coprime to 211."""
    odds = (b+1)//2-a//2
    odd_multiples = (b//PRIME+1)//2-(((a-1)//PRIME)+1)//2
    return odds-odd_multiples


def block(n, a, b, table):
    """For each possible sum, solve the quadratic over the fixed prime field."""
    low_sum = b + (n+b-1)//b
    high_sum = a + n//a
    sums = range(low_sum + (n+1-low_sum)%4, high_sum+1, 4)
    residues = set()
    local_sums = []
    for s in sums:
        roots = table[(s*s-4*n) % PRIME]
        if roots:
            local_sums.append(s)
        for d in roots:
            residues.add((s+d)*106 % PRIME)  # 2*106 = 1 modulo 211.
    positions = []
    for r in sorted(residues):
        first = a+(r-a)%PRIME
        if first % 2 == 0:
            first += PRIME
        positions.extend(range(first, b+1, 2*PRIME))
    return positions, len(sums), local_sums


def search(n, max_blocks, *, from_end=False):
    """Bounded scan; also count and exhaust the matched, direct Fermat sum tests."""
    low, top = endpoints(n)
    if max_blocks < 0:
        raise ValueError('expected a nonnegative block budget')
    total = max(0, (top-low+WIDTH)//WIDTH)
    count = min(max_blocks, total)
    start = total-count if from_end else 0
    report = dict(lower=str(low), upper=str(top), blocks_needed=str(total), first_block=str(start),
                  untested_blocks=str(total-count), budget=max_blocks, from_end=from_end,
                  blocks=count, square_table_entries=0, ordinary_candidates=0, product_terms=0,
                  sum_lookups=0, local_square_sums=0, fermat_square_roots=0, fermat_factor=None,
                  product=None, factor=None, outcome=None)
    common = gcd(n, PRIME)
    if common != 1:
        report.update(factor=common if common < n else None,
                      outcome='wheel_divisor' if common < n else 'whole_modulus')
        return report
    table = square_table()
    report['square_table_entries'] = PRIME
    product = 1
    last_sum = None
    for i in range(start,start+count):
        a, b = low+WIDTH*i, min(top, low+WIDTH*(i+1)-1)
        positions, lookups, live = block(n,a,b,table)
        report['ordinary_candidates'] += wheel_count(a,b)
        report['sum_lookups'] += lookups
        report['local_square_sums'] += len(live)
        report['product_terms'] += len(positions)
        for x in positions:
            product = product*x % n
        # As x increases, the possible sums decrease. Adjacent blocks can
        # meet in just one integer sum. Test that boundary sum only once.
        for s in reversed(live):
            if s == last_sum:
                continue
            last_sum = s
            delta = s*s-4*n
            root = isqrt(delta)
            report['fermat_square_roots'] += 1
            if root*root == delta:
                p = (s-root)//2
                if low+WIDTH*start <= p <= min(top,low+WIDTH*(start+count)-1) and 1<p<n:
                    report['fermat_factor'] = str(p)
    factor = gcd(product,n)
    report.update(product=str(product), factor=factor if 1<factor<n else None,
                  outcome='proper_gcd' if 1<factor<n else 'unit_gcd' if factor==1 else 'whole_modulus')
    return report


def panel(verify=False):
    import json
    from pathlib import Path
    from scripts.factor import render_certificate, verify_file

    root = Path(__file__).resolve().parents[1]
    inputs = json.loads((root/'research/reciprocal-sum-lanes.json').read_text())
    rows = []
    for i, source in enumerate(inputs['cases']):
        n = int(source['n'])
        run = search(n, 4096)
        if run['untested_blocks'] != '0':
            raise ValueError('incomplete small comparison')
        p = int(source['factors'][0])
        inside = int(run['lower']) <= p <= int(run['upper'])
        if run['factor'] != (p if inside else None):
            raise ValueError('the slice lost or misidentified a sampled factor')
        if run['factor'] and verify:
            proof = root/'build'/'sum-slice-panel'/f'{i}.lean'
            proof.parent.mkdir(parents=True, exist_ok=True)
            proof.write_text(render_certificate(n, [run['factor'],n//run['factor']]))
            verify_file(proof)
        rows.append(dict(n=source['n'], **run))
    controls = []
    for c in inputs['control_sections']:
        n = int(c['n'])
        if c['end'] == 'first':
            controls.append(dict(n=str(n), source=c['input'], first=search(n,2), last=search(n,2,from_end=True)))
    return dict(prime=PRIME, block_width=WIDTH, source_seed=inputs['seed'], cases=rows, controls=controls)


if __name__ == '__main__':
    import argparse
    import json
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('n', type=int, nargs='?')
    parser.add_argument('--max-blocks', type=int, default=2)
    parser.add_argument('--from-end', action='store_true')
    parser.add_argument('--panel', action='store_true')
    parser.add_argument('--verify', action='store_true')
    args = parser.parse_args()
    if args.panel:
        result = panel(args.verify)
    elif args.n is not None:
        result = search(args.n, args.max_blocks, from_end=args.from_end)
    else:
        parser.error('supply the input or --panel')
    print(json.dumps(result, indent=2))
