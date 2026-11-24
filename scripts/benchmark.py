"""Run the public fixtures from N, check their expected outcomes, and retain proof files."""

import argparse
import json
import os
import platform
import re
import subprocess
import sys
import time
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def cli(args, expected_code=0):
    command = [sys.executable, *map(str, args)]
    proc = subprocess.run(command, cwd=ROOT, text=True, capture_output=True, timeout=900)
    if proc.returncode != expected_code:
        raise RuntimeError(f"{args[0]} exited {proc.returncode}: {proc.stderr}\n{proc.stdout}")
    return json.loads(proc.stdout)


def agree(case, result, keys):
    for key in keys:
        if case[key] != result[key]:
            raise ValueError(f"{case['id']}.{key}: expected {case[key]!r}, got {result[key]!r}")


def run_case(case, subgroup, proofs):
    name = case['id']
    if not re.fullmatch(r'[a-zA-Z0-9_-]+', name):
        raise ValueError(f'Invalid benchmark ID {name!r}')
    proof = proofs / f'{name}.lean'
    start = time.perf_counter()
    factor_args = ['scripts/factor.py', case['n'], '--max-steps', case.get('max_steps', 0),
                   '--verify', '--lean', proof]
    if subgroup:
        factor_args += ['--method', 'subgroup']
        if 'max_base' in case:
            factor_args += ['--max-base', case['max_base']]
    complete = case['status'] == 'complete'
    result = cli(factor_args, 0 if complete else 1)
    agree(case, result, ['n', 'status', 'factors', 'remaining'])
    if subgroup:
        agree(case, result['subgroup'], ['bases_tested'])
    else:
        agree(case, result, ['fermat_steps'])
    if result['verified'] != complete or (complete and not proof.is_file()):
        raise ValueError(f'Unexpected proof status for {name}')
    if 'exclusion' in case:
        exclusion = case['exclusion']
        theorem = exclusion['theorem']
        if not re.fullmatch(r'[A-Za-z][A-Za-z_0-9]*', theorem):
            raise ValueError(f'Invalid exclusion theorem name {theorem!r}')
        half_gap = int(exclusion['half_gap_limit'])
        proof.write_text(
            'import PrimeFactors.Fermat\n\n'
            f'example (p d : ℕ) (h : d ≤ {half_gap}) :\n'
            f'    {int(case["n"])} ≠ p * (p + 2 * d) :=\n'
            f'  PrimeFactors.{theorem} p d h\n')
        check_start = time.perf_counter()
        subprocess.run(['lake', 'env', 'lean', '-DwarningAsError=true', str(proof)], cwd=ROOT,
                       check=True, timeout=900)
        result['exclusion'] = dict(max_gap=str(2 * half_gap), proof=f'proofs/{proof.name}',
                                   verification_seconds=time.perf_counter() - check_start)
    elapsed = time.perf_counter() - start
    return dict(result, id=name, description=case['description'],
                method='subgroup' if subgroup else 'fermat', wall_seconds=elapsed,
                certificate=f'proofs/{proof.name}' if complete else None)


def cpu_name():
    proc = Path('/proc/cpuinfo')
    if proc.is_file():
        for line in proc.read_text().splitlines():
            if line.startswith('model name'):
                return line.split(':', 1)[-1].strip()
    if platform.system() == 'Darwin':
        info = subprocess.run(['/usr/sbin/sysctl', '-n', 'machdep.cpu.brand_string'],
                              capture_output=True, text=True)
        if info.returncode == 0 and info.stdout.strip():
            return info.stdout.strip()
    return platform.processor() or platform.machine()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out', type=Path, default=ROOT / 'build' / 'site')
    args = parser.parse_args()
    out = args.out.resolve()
    proofs = out / 'proofs'
    proofs.mkdir(parents=True, exist_ok=True)
    results = []
    for filename in ['cases.json', 'subgroup.json']:
        cases = json.loads((ROOT / 'benchmarks' / filename).read_text())
        for case in cases:
            result = run_case(case, filename == 'subgroup.json', proofs)
            results.append(result)
            print(f"{result['id']}  {result['status']}  {result['wall_seconds']:.3f}s", flush=True)
    if len(results) != len({case['id'] for case in results}):
        raise ValueError('Duplicate benchmark ID')
    sha = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip()
    data = dict(commit=sha, measured_at=datetime.now(timezone.utc).isoformat(timespec='seconds'),
                repository=os.getenv('GITHUB_REPOSITORY', 'marius-bughiu/prime-factors'),
                run_id=os.getenv('GITHUB_RUN_ID'), platform=platform.platform(), cpu=cpu_name(),
                python=platform.python_version(), lean=(ROOT / 'lean-toolchain').read_text().strip(),
                results=results)
    (out / 'results.json').write_text(json.dumps(data, indent=2) + '\n')


if __name__ == '__main__':
    main()
