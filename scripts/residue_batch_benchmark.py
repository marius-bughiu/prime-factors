"""Replay both 34-root schedules and certify any split the comparison found."""
from time import perf_counter

from experiments.residue_batch_allocation import ALLOCATION
from experiments.residue_batch_comparison import search


def residue_batch_case(case, proof, agree, certify_split):
    n = int(case['n'])
    start = perf_counter()
    common, fixed, adaptive = search(n)
    elapsed = perf_counter()-start
    adaptive_factor = min(common|adaptive, default=None)
    fixed_factor = min(common|fixed, default=None)
    allocation = list(ALLOCATION[n%24])
    work = dict(residue=n%24, weighted_tests=allocation, roots_per_schedule=34,
                shared_run_roots=34+abs(allocation[0]-7),
                adaptive_found=str(adaptive_factor) if adaptive_factor else None,
                fixed_found=str(fixed_factor) if fixed_factor else None)
    agree(dict(id=case['id'], **case['checks']), work, case['checks'])
    result = certify_split(case, proof, adaptive_factor, elapsed, 'residue_batch', work)
    if fixed_factor is not None and adaptive_factor is None:
        reference_proof = proof.with_name(f'{proof.stem}-fixed.lean')
        reference = certify_split(case, reference_proof, fixed_factor, elapsed, 'fixed_batch', work)
        if not reference['verified'] or reference['factors'] != case['fixed_factors']:
            raise ValueError(f"Fixed allocation certificate failed for {case['id']}")
        work['fixed_certificate'] = f'proofs/{reference_proof.name}'
        work['fixed_factors'] = reference['factors']
    return result
