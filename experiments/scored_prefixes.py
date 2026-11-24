"""Compare shorter scored and ordinary walks on the previously fixed 79-bit sample."""

from collections import defaultdict
import json
from pathlib import Path
import platform
from time import process_time_ns

from .scored_multipliers import search


def compare(cases, budgets=(2048, 3072, 4096, 5138)):
    results = []
    for budget in budgets:
        totals = defaultdict(lambda: dict(splits=0, steps=0, relations_tested=0,
                                          solved_indices=[], cpu_nanoseconds=0))
        for index, case in enumerate(cases):
            n = int(case['n'])
            # Alternate which method runs first within each matched pair.
            modes = ('one', 'scored') if index % 2 == 0 else ('scored', 'one')
            for mode in modes:
                start = process_time_ns()
                work = search(n, mode, budget)
                elapsed = process_time_ns() - start
                row = totals[mode]
                row['cpu_nanoseconds'] += elapsed
                row['steps'] += work['steps']
                row['relations_tested'] += work['tested']
                f = work['factor']
                if f is not None:
                    if [str(t) for t in sorted((f, n//f))] != case['expected_factors'] or n % f:
                        raise ValueError('discovered factor failed the stored certificate labels')
                    row['splits'] += 1
                    row['solved_indices'].append(index)
                if budget == 5138 and bool(f) != bool(case['methods'][mode]['factors']):
                    raise ValueError('last prefix disagrees with the paired holdout')
        results.append(dict(max_steps=budget, methods=dict(totals)))
    return results


if __name__ == '__main__':
    path = Path(__file__).resolve().parents[1] / 'research' / 'scored-holdout.json'
    panel = json.loads(path.read_text())
    print(json.dumps(dict(seed=panel['seed'], count=panel['count'], python=platform.python_version(),
                          machine=platform.machine(), platform=platform.platform(),
                          prefixes=compare(panel['cases'])), indent=2))
