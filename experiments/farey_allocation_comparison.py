"""Single-process benchmark harness comparing schedules on the existing collision engine."""
import argparse
import json
import platform
from pathlib import Path
from statistics import median
from time import perf_counter

from . import weighted_stride_search
from .farey_allocation import MAX_CENTERS, fast, optimal_with_skips, slopes, verify


def allocated_records(n, k, m, max_giants, max_slopes, beta, stride, work):
    if stride != 24:
        raise ValueError("this benchmark adapter uses stride 24")
    fractions, windows, _, lengths = fast(n, k, m, max_centers=min(max_slopes, MAX_CENTERS))
    work['slope_visits'] = work['primitive_slopes'] = sum(1 for _ in slopes(k))
    if work['slope_visits'] > max_slopes:
        raise ValueError("the benchmark requires a complete allocation")
    work['allocated_slopes'] = len(fractions)
    work['nonempty_slopes'] = sum(bool(length) for length in lengths)
    work['labels_covered'] = sum(lengths)
    if sum((length+m-1)//m for length in lengths) > max_giants:
        raise ValueError("the benchmark requires a complete allocation")
    records = []
    jump = pow(beta, -stride*m, n)
    # Preserve the ordinary denominator-first search order among retained slopes.
    ordered = sorted(zip(fractions, windows, lengths), key=lambda row: (row[0][1], row[0][0]))
    for (a, b), (start, step), length in ordered:
        if not length:
            continue
        power = pow(beta, (stride//step)*(a+b*n-start), n)
        for offset in range(0, length, m):
            records.append((power, a, b, start+step*offset, step, min(length-offset, m)))
            power = power*jump%n
    return records, None


def run(repetitions):
    path = Path(__file__).resolve().parents[1]/'research'/'weighted-stride-comparison.json'
    cases = []
    for src in json.loads(path.read_text())['cases']:
        n, k, m = int(src['n']), src['k'], src['baby_steps']
        result = {}
        for name in ['ordinary', 'allocated']:
            elapsed = []
            for _ in range(repetitions):
                before = perf_counter()
                if name == 'allocated':
                    found = weighted_stride_search.search(n, k, m, 262144, record_builder=allocated_records)
                else:
                    found = weighted_stride_search.search(n, k, m, 262144)
                elapsed.append(perf_counter()-before)
                divisor = found['factor']
                if not (found['schedule_complete'] and divisor and 1 < divisor < n and n%divisor == 0):
                    raise ValueError('incomplete search')
            result[name] = dict(seconds=round(median(elapsed), 6), samples=[round(t, 6) for t in elapsed],
                                factor=str(divisor), outcome=found['outcome'], work=found['work'])
        plan = fast(n, k, m)
        before = perf_counter()
        greedy = verify(n, m, plan)
        greedy['verification_seconds'] = round(perf_counter()-before, 6)
        exact = []
        for gap in (1, 3):
            before = perf_counter()
            plan = optimal_with_skips(n, k, m, gap=gap)
            elapsed = perf_counter()-before
            exact.append(dict(gap=gap, seconds=round(elapsed, 6), **verify(n, m, plan)))
        cases.append(dict(id=src['id'], n=str(n), k=k, baby_steps=m, methods=result,
                          greedy_certificate=greedy, minimum_giant_schedules=exact))
    return dict(platform=platform.platform(), machine=platform.machine(), python=platform.python_version(),
                repetitions=repetitions, cases=cases)


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--repetitions', type=int, default=3)
    args = parser.parse_args()
    if args.repetitions < 1:
        parser.error('--repetitions must be positive')
    print(json.dumps(run(args.repetitions), indent=2))
