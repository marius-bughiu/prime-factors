"""Transfer a fixed partition of balanced factor ratios to a new public product.

For a cell [l,r] assigned to (a,b), C=max((a+b*l)^2/l,(a+b*r)^2/r)
depends only on the cell. The true trace on that cell is at most sqrt(N*C):
the squared normalized trace is a²/x + 2ab + b²x, convex for x>0.
The actual search is the existing stride-24 collision engine.
"""

from argparse import ArgumentParser
from dataclasses import dataclass
from fractions import Fraction
from functools import lru_cache
import gc
from hashlib import sha256
import json
from math import gcd, isqrt
from pathlib import Path
import platform
from statistics import median
from time import perf_counter, process_time

from . import weighted_stride_search
from .farey_allocation import fast, lattice_start, verify as verify_plan
from .farey_allocation_comparison import allocated_records
from .trace_cover import envelope
from .trace_cover_sparse import read_certificate, verify_sparse


ROOT = Path(__file__).resolve().parents[1]
ARCHIVE = ROOT/'research/trace-cover-89-a.json'
ARCHIVE_N = 439173623877940919234655961
K, BLOCK, MAX_GIANTS = 231, 53130, 262144
SEED = 'frozen-89a-trace-holdout-v1'
UNITS = (1, 5, 7, 11, 13, 17, 19, 23)
HOLDOUT_CLASSES = (*UNITS, 1, 1, 1, 13)
METHODS = ('historic', 'fast', 'family', 'ordinary')


@dataclass(frozen=True)
class Template:
    slopes: tuple
    coefficients: tuple

    def allocate(self, n):
        if n < 3 or gcd(n, 6) != 1:
            raise ValueError('the stride-24 search requires N>=3 coprime to six')
        windows, lengths = [], []
        for (a, b), (numerator, denominator) in zip(self.slopes, self.coefficients):
            first, step = lattice_start(n, a, b, 24)
            upper = isqrt(n*numerator//denominator)
            windows.append((first, step))
            lengths.append(max(0, (upper-first)//step+1))
        return windows, lengths

    def records(self, n, k, m, max_giants, max_slopes, beta, stride, work):
        if stride != 24 or self.slopes[-1][1] > k:
            raise ValueError('template records require stride 24 and a sufficient slope order')
        windows, lengths = self.allocate(n)
        return weighted_stride_search.records_from_allocation(
            n, m, max_giants, max_slopes, beta, stride, work, self.slopes, windows,
            lengths, len(self.slopes))


def compile_partition(slopes, cuts):
    """Check the tiling, then retain the exact maximal squared coefficient per cell."""
    slopes = [tuple(s) for s in slopes]
    cuts = [Fraction(*x) if isinstance(x, (tuple, list)) else Fraction(x) for x in cuts]
    if not slopes or len(cuts) != len(slopes)+1 or cuts[0] != 1 or cuts[-1] != 2:
        raise ValueError('the partition must cover [1,2]')
    if any(left > right for left, right in zip(cuts, cuts[1:])):
        raise ValueError('the partition cuts must be nondecreasing')
    if len(set(slopes)) != len(slopes):
        raise ValueError('expected one cell per slope')
    cells = []
    for (a, b), left, right in zip(slopes, cuts, cuts[1:]):
        if not 0 < b <= a <= 2*b or gcd(a, b) != 1:
            raise ValueError('invalid primitive weight pair')
        ln, ld = left.numerator, left.denominator
        rn, rd = right.numerator, right.denominator
        numerator, denominator = (a*ld+b*ln)**2, ln*ld
        other, div = (a*rd+b*rn)**2, rn*rd
        if other*denominator > numerator*div:
            numerator, denominator = other, div
        cells.append((b, a, numerator, denominator))
    cells.sort()
    return Template(tuple((a, b) for b, a, _, _ in cells),
                    tuple((u, v) for _, _, u, v in cells))


def archived_template(path, n, k, block, *, validate_optimum=True):
    """Build from a previous allocation. Price checks are optional for transfer safety."""
    start = perf_counter()
    plan = read_certificate(path, n, k, block)
    cells, holes = envelope(n, plan['windows'], block, plan['budgets'], Fraction(1), Fraction(2))
    if holes or any(left[1] != right[0] for left, right in zip(cells, cells[1:])):
        raise ValueError('archived schedule does not cover the interval')
    template = compile_partition([plan['windows'][i][:2] for _, _, i in cells],
                                 [cells[0][0], *(hi for _, hi, _ in cells)])
    preparation = perf_counter()-start
    start = perf_counter()
    if validate_optimum:
        verify_sparse(n, plan['windows'], block, Fraction(1), Fraction(2), plan['budgets'], plan['prices'])
    return template, dict(source_input=str(n), cells=len(cells), prepare_seconds=preparation,
                          verify_optimality_seconds=perf_counter()-start if validate_optimum else 0.0,
                          certificate_sha256=sha256(path.read_bytes()).hexdigest())


def ceiling_template(bits, residue, k, block):
    """Use the greatest integer below 2^bits in this product's stride class.

    For N <= source in this residue class the step is fixed and the real width
    of each cell shrinks with sqrt(N). Its translated lattice has at most one
    more label than the source; only a multiple-of-block source length can
    gain a block. The returned cap concerns exactly this product class.
    """
    if bits < 4 or residue not in (1, 5, 7, 11):
        raise ValueError('expected a bit cap >=4 and a unit residue modulo twelve')
    start = perf_counter()
    top = 2**bits-1
    source = top-(top-residue)%12
    plan = fast(source, k, block)
    slopes, _, cuts, lengths = plan
    blocks = verify_plan(source, block, plan)['giants']
    template = compile_partition(slopes, cuts)
    multiples = sum(length % block == 0 for length in lengths)
    return template, dict(source_input=str(source), cells=len(slopes), blocks=blocks,
                          boundary_cells=multiples, universal_block_cap=blocks+multiples,
                          prepare_seconds=perf_counter()-start)


def _hash(label):
    return int.from_bytes(sha256((SEED+'|'+label).encode()).digest(), 'big')


@lru_cache(maxsize=1)
def _holdout_trial_primes():
    from scripts.factor import primes_through
    return primes_through(isqrt(2**45))


def _small_prime(n):
    """The precomputed trial table covers sqrt(n) on both holdout widths."""
    for divisor in _holdout_trial_primes():
        if divisor*divisor > n:
            break
        if n % divisor == 0:
            return n == divisor
    return n >= 2


def holdout_inputs():
    """Generate the fixed panel and expose only its products to each of the four searches."""
    inputs = []
    for index, residue in enumerate(HOLDOUT_CLASSES):
        bits = 88+index%2
        lower, upper = isqrt(2**(bits-1)-1)+1, isqrt(2**bits-1)
        first_residue = UNITS[_hash(f'{index}|p|residue')%len(UNITS)]
        factors = []
        for label, unit in (('p', first_residue), ('q', residue*pow(first_residue, -1, 24)%24)):
            first = lower+(unit-lower)%24
            slots = (upper-first)//24+1
            offset = _hash(f'{index}|{label}|offset')%slots
            for j in range(slots):
                candidate = first+24*((offset+j)%slots)
                if _small_prime(candidate):
                    factors.append(candidate)
                    break
        if len(factors) != 2 or factors[0] == factors[1]:
            raise ArithmeticError('the prescribed prime-pair generation failed')
        inputs.append(factors[0]*factors[1])
    return inputs


def compare(repetitions=4):
    """Measure complete searches. The four-round default rotates each method into each slot."""
    if repetitions < 1:
        raise ValueError('at least one timed repetition is required')
    inputs = holdout_inputs()
    historic, archive_work = archived_template(ARCHIVE, ARCHIVE_N, K, BLOCK)
    family, family_work = {}, {}
    for residue in (1, 5, 7, 11):
        family[residue], family_work[str(residue)] = ceiling_template(89, residue, K, BLOCK)
    rows = []
    for i, n in enumerate(inputs):
        runs = {}
        builders = dict(historic=historic.records, family=family[n%12].records, fast=allocated_records)
        for r in range(repetitions):
            for offset in range(len(METHODS)):
                method = METHODS[(i+r+offset)%len(METHODS)]
                args = {'record_builder': builders[method]} if method in builders else {}
                gc.collect()
                wall, cpu = perf_counter(), process_time()
                result = weighted_stride_search.search(n, K, BLOCK, MAX_GIANTS, **args)
                cpu, wall = process_time()-cpu, perf_counter()-wall
                factor = result['factor']
                if not factor or not 1 < factor < n or n % factor or not result['schedule_complete']:
                    raise ArithmeticError(f'{method} did not complete the split on {n}')
                factors = tuple(sorted((factor, n//factor)))
                metrics = result['work']
                observed = (factors, result['outcome'], metrics['giants'], metrics['labels_covered'])
                run = runs.setdefault(method, dict(observed=observed, cpu=[], wall=[]))
                if run['observed'] != observed:
                    raise ArithmeticError('repeated searches disagreed')
                run['cpu'].append(cpu)
                run['wall'].append(wall)
        row = dict(n=str(n), bits=n.bit_length(), residue=n%24, methods={})
        for method, run in runs.items():
            factors, outcome, giants, labels = run['observed']
            pair = [str(p) for p in factors]
            if row.setdefault('factors', pair) != pair:
                raise ArithmeticError('the methods found different prime pairs')
            row['methods'][method] = dict(giants=giants, labels=labels, outcome=outcome,
                median_wall_seconds=round(median(run['wall']), 6),
                median_cpu_seconds=round(median(run['cpu']), 6))
        rows.append(row)
    return dict(seed=SEED, platform=platform.platform(), python=platform.python_version(),
        k=K, baby_steps=BLOCK, max_giants=MAX_GIANTS, repetitions=repetitions,
        products_sha256=sha256(json.dumps([str(n) for n in inputs], separators=(',', ':')).encode()).hexdigest(),
        selection='Indices 0..11 alternate 88 and 89 product bits. Factor candidates come from the square root of that bit band, so the factor ratio is below sqrt(2). Each unit residue modulo 24 appears at least once. SHA-256 selects the first factor residue and both starting offsets. The next prime in each prescribed class is taken before any search.',
        reproduction='python3 -m experiments.trace_cover_transfer --output REPORT --proof-dir PROOFS. To regenerate the Lean proofs alone, use --certify-report REPORT --proof-dir PROOFS.',
        timing='Single process. Four methods rotated by case and repetition. Each target time includes its own record allocation, table build and collision search. Archive and ceiling-template preparation are charged separately. Source optimality replay is optional for transfer. Earlier creation of the historical optimum took 155.15 s.',
        historic=archive_work, family=family_work, rows=rows, summary=summarize(rows, archive_work, family_work))


def summarize(rows, archive, family):
    setup = sum(item['prepare_seconds'] for item in family.values())
    groups = [('all', rows), ('historic_mod24', [r for r in rows if r['residue'] == ARCHIVE_N%24]),
              ('historic_mod12', [r for r in rows if r['residue']%12 == ARCHIVE_N%12]),
              ('other_mod12', [r for r in rows if r['residue']%12 != ARCHIVE_N%12])]
    summary = {}
    for name, sample in groups:
        stats = {}
        for method in METHODS:
            clocks = [r['methods'][method]['median_wall_seconds'] for r in sample]
            stats[method] = dict(giants=sum(r['methods'][method]['giants'] for r in sample),
                sum_seconds=round(sum(clocks), 6), median_seconds=round(median(clocks), 6),
                faster_than_fast=sum(t < r['methods']['fast']['median_wall_seconds']
                                     for t, r in zip(clocks, sample)))
        summary[name] = stats
    total = summary['all']
    total['family']['with_all_setup_seconds'] = round(setup+total['family']['sum_seconds'], 6)
    total['family']['first_case_with_all_setup_seconds'] = round(setup+rows[0]['methods']['family']['median_wall_seconds'], 6)
    total['family']['with_setup_per_product_seconds'] = round(total['family']['with_all_setup_seconds']/len(rows), 6)
    first = rows[0]
    total['family']['first_case_with_its_class_setup_seconds'] = round(
        family[str(first['residue']%12)]['prepare_seconds']+first['methods']['family']['median_wall_seconds'], 6)
    total['historic']['first_case_with_setup_seconds'] = round(
        archive['prepare_seconds']+first['methods']['historic']['median_wall_seconds'], 6)
    total['historic']['with_setup_seconds'] = round(archive['prepare_seconds']+total['historic']['sum_seconds'], 6)
    total['historic']['with_setup_and_source_verification_seconds'] = round(
        total['historic']['with_setup_seconds']+archive['verify_optimality_seconds'], 6)
    return summary


def _certify_cli(report, directory):
    """This standalone CLI process uses a larger trial table for the 45-bit Pratt witnesses."""
    from scripts import factor
    directory.mkdir(parents=True, exist_ok=True)
    factor.TRIAL_PRIMES = factor.primes_through(isqrt(2**45))
    factor.prime_witness.cache_clear()
    for i, row in enumerate(report['rows']):
        path = directory/f'trace-transfer-{i:02}.lean'
        path.write_text(factor.render_certificate(int(row['n']), [int(p) for p in row['factors']]))
        factor.verify_file(path)
        proof = dict(file=path.name, sha256=sha256(path.read_bytes()).hexdigest())
        if 'lean_factorization' in row and row['lean_factorization'] != proof:
            raise ValueError(f'the factor proof for {row["n"]} differs from the recorded digest')
        row['lean_factorization'] = proof


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--repetitions', type=int, default=4)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--certify-report', type=Path, help='recheck the reported factors without retiming searches')
    parser.add_argument('--proof-dir', type=Path, help='generate and kernel-check all twelve factorizations')
    args = parser.parse_args()
    if args.certify_report:
        if not args.proof_dir:
            parser.error('--certify-report needs --proof-dir')
        report = json.loads(args.certify_report.read_text())
        if [row['n'] for row in report['rows']] != [str(n) for n in holdout_inputs()]:
            parser.error('the report does not contain the fixed twelve public inputs')
    else:
        report = compare(args.repetitions)
    if args.proof_dir:
        _certify_cli(report, args.proof_dir)
    output = json.dumps(report, indent=2)+'\n'
    if args.output:
        args.output.write_text(output)
    else:
        print(output, end='')


if __name__ == '__main__':
    main()
