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
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from experiments.modular_hyperbola import search as hyperbola_search
from experiments.divisor_samples import search as divisor_sample_search
from experiments.salie_residues import search as salie_residue_search
from experiments.salie_seed import search as salie_seed_search
from experiments.midpoint_readings import search as midpoint_readings_search
from experiments.short_basis_sieve import search as short_basis_search
from experiments.wide_modulus import search as wide_modulus_search
from experiments.pascal_readout import search as pascal_search
from experiments.pell_pairs import search as pell_pair_search
from experiments.pell_relations import search as pell_relation_search
from experiments.salie_blocks import search as salie_block_search
from experiments.folded_square import direct as fixed_phase_search
from experiments.four_square_lines import search as four_square_line_search
from experiments.quotient_search import search as quotient_search
from experiments.inverse_windows import search_product as inverse_windows_search
from experiments.continued_square import search as continued_square_search
from experiments.predecessor_square import search as predecessor_square_search, search_square_offset
from experiments.gap_stride import search as gap_search
from experiments.cyclotomic_periods import expand_cases, reduced_table_search, search as cyclotomic_search


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


def period_case(case, method, proof):
    n, base, stride = int(case['n']), case['base'], case['stride']
    work_keys = ['outcome', 'entries_per_table', 'giants_probed', 'batch_gcds']
    if method == 'cyclotomic':
        work = cyclotomic_search(n, base, case['degree'], stride)
        work['degree'] = case['degree']
        work_keys.append('halving_gcds')
        key = 'cyclotomic'
    else:
        work = reduced_table_search(n, base, stride)
        key = 'reduced_order'
    factor = work.pop('factor')
    search_seconds = work.pop('search_nanoseconds') / 1_000_000_000
    agree(case, work, work_keys)
    return certify_split(case, proof, factor, search_seconds, key, dict(work, base=base, stride=stride))


def certify_split(case, proof, factor, search_seconds, key, work):
    n = int(case['n'])
    result = dict(n=case['n'], bits=n.bit_length(), factors=[], remaining=[case['n']],
                  status='partial', verified=False, verification_seconds=None, certificate_seconds=None,
                  discovery_seconds=search_seconds)
    result[key] = work
    if factor is not None:
        certificate_start = time.perf_counter()
        checked = cli(['scripts/factor.py', case['n'], '--factor-hint', factor, '--max-steps', 0,
                       '--verify', '--lean', proof])
        result.update({key: checked[key] for key in
                       ['factors', 'remaining', 'status', 'verified', 'verification_seconds']})
        result['certificate_seconds'] = time.perf_counter() - certificate_start
    return result


def short_basis_case(case, proof):
    start = time.perf_counter()
    run = short_basis_search(int(case['n']), case['m'], case['m0'], case['primes'],
                             case['max_bad'], exceptional=case['use_exceptional'])
    elapsed = time.perf_counter() - start
    ordinary = run['ordinary']
    exceptional = run.get('exceptional', {})
    fallback = run.get('fallback', {})
    hits = [ordinary['first'], *(sweep['power'] for sweep in exceptional.values()), fallback.get('first')]
    factor = next((hit['factor'] for hit in hits if hit is not None), None)
    work = dict(run, ordinary_gcds=ordinary['work'].get('pair_gcds', 0),
                exceptional_gcds=sum(sweep['work']['pair_gcds'] for sweep in exceptional.values()),
                fallback_gcds=fallback.get('work', {}).get('pair_gcds', 0),
                use_exceptional=case['use_exceptional'])
    agree(case, work, ['sparse_entries', 'ordinary_gcds', 'exceptional_gcds', 'fallback_gcds'])
    return certify_split(case, proof, factor, elapsed, 'short_basis', work)


def run_case(case, method, proofs):
    name = case['id']
    if not re.fullmatch(r'[a-zA-Z0-9_-]+', name):
        raise ValueError(f'Invalid benchmark ID {name!r}')
    proof = proofs / f'{name}.lean'
    start = time.perf_counter()
    complete = case['status'] == 'complete'
    if method == 'modular-hyperbola':
        work = hyperbola_search(int(case['n']))
        elapsed = time.perf_counter() - start
        pairs = work.pop('pairs')
        agree(case, work, ['low_classes', 'modular_hits'])
        factor = pairs[0][0] if pairs else None
        result = certify_split(case, proof, factor, elapsed, 'hyperbola', work)
    elif method == 'quotient-search':
        work = quotient_search(int(case['n']), case['width'], wheel=case['wheel'])
        elapsed = time.perf_counter() - start
        pairs = work.pop('pairs')
        checks = ['blocks', 'initial_strip_points', 'quadratic_solves', 'bisected']
        if 'collinear_beyond_area' in case:
            checks.append('collinear_beyond_area')
        agree(case, work, checks)
        found = work['setup_divisor'] or (pairs[0][0] if pairs else None)
        factor = int(found) if found is not None else None
        result = certify_split(case, proof, factor, elapsed, 'quotient_search', work)
    elif method == 'pell-pairs':
        work = pell_pair_search(int(case['n']), case['max_prime'], case['max_steps'], case['triangles'])
        elapsed = time.perf_counter() - start
        factor = work.pop('factor')
        agree(case, work, ['outcome', 'steps', 'walks', 'centers', 'cycles', 'root'])
        work.update(max_steps=case['max_steps'], max_prime=case['max_prime'], triangles=case['triangles'])
        result = certify_split(case, proof, factor, elapsed, 'pell_pairs', work)
    elif method == 'pell-relations':
        work = pell_relation_search(int(case['n']), case['multiplier'], case['max_steps'])
        elapsed = time.perf_counter() - start
        factor = work.pop('factor')
        agree(case, work, list(work))
        work.update(max_steps=case['max_steps'], multiplier=case['multiplier'])
        result = certify_split(case, proof, factor, elapsed, 'pell_relations', work)
    elif method == 'four-square-lines':
        work = four_square_line_search(int(case['n']), case['max_triples'])
        elapsed = time.perf_counter() - start
        factor = work.pop('factor')
        agree(case, work, list(work))
        work['max_triples'] = case['max_triples']
        result = certify_split(case, proof, factor, elapsed, 'four_square_lines', work)
    elif method == 'salie-blocks':
        work = salie_block_search(int(case['n']), case['max_orbits'], case['fractional_bits'])
        elapsed = time.perf_counter() - start
        factor = work.pop('factor')
        agree(case, work, list(work))
        result = certify_split(case, proof, factor, elapsed, 'salie_blocks', work)
    elif method in ('salie-seed', 'folded-square'):
        search = salie_seed_search if method == 'salie-seed' else fixed_phase_search
        work = search(int(case['n']), case['max_terms'])
        elapsed = time.perf_counter() - start
        factor = work.pop('factor')
        agree(case, work, list(work))
        work['max_terms'] = case['max_terms']
        result = certify_split(case, proof, factor, elapsed, method.replace('-', '_'), work)
    elif method in ('divisor-samples', 'salie-residues'):
        search, key = ((salie_residue_search, 'salie_residues') if method == 'salie-residues'
                       else (divisor_sample_search, 'divisor_samples'))
        work = search(int(case['n']), case['max_terms'])
        elapsed = time.perf_counter() - start
        factor = work.pop('factor')
        common = ['outcome', 'root', 'terms', 'sums', 'unit_gcds', 'inverses',
                  'jacobi_evaluations', 'frequency_gcds']
        counters = (['multiplier', 'coefficient', 'prime_gcds', 'frequency_inverses',
                     'crt_updates', 'square_tests', 'prime_count', 'last_prime', 'max_precision_bits']
                    if method == 'salie-residues' else ['anchor'])
        agree(case, work, common + counters)
        work['max_terms'] = case['max_terms']
        result = certify_split(case, proof, factor, elapsed, key, work)
    elif method == 'wide-modulus':
        work = wide_modulus_search(int(case['n']), **case['parameters'])
        elapsed = time.perf_counter() - start
        factor = work.pop('factor')
        work['order_method'] = work['order']['method']
        agree(case, work, ['route', 'order_method'])
        result = certify_split(case, proof, factor, elapsed, 'wide_modulus', work)
    elif method == 'short-basis':
        result = short_basis_case(case, proof)
    elif method == 'pascal':
        work = pascal_search(int(case['n']), case['cutoff'], case['max_index'])
        elapsed = time.perf_counter() - start
        factor = work.pop('factor')
        agree(case, work, ['index', 'coefficients_evaluated', 'coefficient_bits', 'residue'])
        result = certify_split(case, proof, factor, elapsed, 'pascal', work)
    elif method == 'inverse-windows':
        n = int(case['n'])
        bits = (n.bit_length() + 1) // 2
        work = inverse_windows_search(n, bits, case['side_bits'], case['word_bits'])
        elapsed = time.perf_counter() - start
        pairs = work.pop('factor_pairs')
        agree(case, work, ['n', 'entries', 'geometric_cells', 'modular_points', 'baseline_trial_odds'])
        factor = pairs[0][0] if pairs else None
        result = certify_split(case, proof, factor, elapsed, 'inverse_windows', work)
    elif method == 'midpoint-readings':
        work = midpoint_readings_search(int(case['n']), case['tests'], case['seed'])
        elapsed = time.perf_counter() - start
        pairs = work.pop('pairs')
        agree(case, work, ['midpoints', 'evaluations', 'final_square_tests'])
        factor = pairs[0][0] if pairs else None
        result = certify_split(case, proof, factor, elapsed, 'readings', work)
    elif method == 'continued-square':
        work = continued_square_search(int(case['n']), case['max_convergents'])
        elapsed = time.perf_counter() - start
        factor = work.pop('factor')
        work.pop('cofactor')
        if factor is not None:
            work['scale'] = str(work['scale'])
            work['parameter'] = str(work['parameter'])
        agree(case, work, ['convergents', 'square_tests', 'direction_tests'])
        result = certify_split(case, proof, factor, elapsed, 'continued_square', work)
    elif method == 'square-offset':
        work = search_square_offset(int(case['n']), case['max_gap'])
        elapsed = time.perf_counter() - start
        factor = work.pop('factor')
        agree(case, work, ['gaps_tested', 'discriminants'])
        result = certify_split(case, proof, factor, elapsed, 'square_offset', work)
    elif method == 'predecessor-square':
        work = predecessor_square_search(int(case['n']), case['max_scale'])
        elapsed = time.perf_counter() - start
        factor = work.pop('factor')
        agree(case, work, ['scales_tested'])
        result = certify_split(case, proof, factor, elapsed, 'predecessor_square', work)
    elif method == 'gap-stride':
        work = gap_search(int(case['n']), case['max_exponent'], case['per_root'])
        elapsed = time.perf_counter() - start
        factor = work.pop('factor')
        agree(case, work, ['exponent', 'square_tests', 'lift_tests'])
        result = certify_split(case, proof, factor, elapsed, 'gap_stride', work)
    elif method in ('reduced-order', 'cyclotomic'):
        result = period_case(case, method, proof)
    else:
        factor_args = ['scripts/factor.py', case['n'], '--max-steps', case.get('max_steps', 0),
                       '--verify', '--lean', proof, '--method', method]
        if method == 'subgroup' and 'max_base' in case:
            factor_args += ['--max-base', case['max_base']]
        result = cli(factor_args, 0 if complete else 1)
        if method == 'subgroup':
            agree(case, result['subgroup'], ['bases_tested'])
        else:
            agree(case, result, ['fermat_steps'])
    agree(case, result, ['n', 'status', 'factors', 'remaining'])
    if method == 'shifted':
        if result['shifted']['status'] != case['shifted']['status']:
            raise ValueError(f"Unexpected shifted-square result for {name}")
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
                method=method, wall_seconds=elapsed,
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
    for filename, method in [('cases.json', 'fermat'), ('subgroup.json', 'subgroup'),
                             ('shifted.json', 'shifted'), ('reduced-orders.json', 'reduced-order'),
                             ('cyclotomic-periods.json', 'cyclotomic'), ('gap-stride.json', 'gap-stride'),
                             ('predecessor-square.json', 'predecessor-square'),
                             ('square-offset.json', 'square-offset'), ('continued-square.json', 'continued-square'),
                             ('short-basis.json', 'short-basis'), ('wide-modulus.json', 'wide-modulus'),
                             ('pascal.json', 'pascal'), ('midpoint-readings.json', 'midpoint-readings'),
                             ('divisor-samples.json', 'divisor-samples'),
                             ('salie-residues.json', 'salie-residues'),
                             ('salie-seed.json', 'salie-seed'),
                             ('folded-square.json', 'folded-square'),
                             ('salie-blocks.json', 'salie-blocks'),
                             ('pell-pairs.json', 'pell-pairs'),
                             ('pell-relations.json', 'pell-relations'),
                             ('four-square-lines.json', 'four-square-lines'),
                             ('quotient-search.json', 'quotient-search'),
                             ('inverse-windows.json', 'inverse-windows'),
                             ('modular-hyperbola.json', 'modular-hyperbola')]:
        cases = json.loads((ROOT / 'benchmarks' / filename).read_text())
        if method == 'cyclotomic':
            cases = expand_cases(cases)
        for case in cases:
            result = run_case(case, method, proofs)
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
