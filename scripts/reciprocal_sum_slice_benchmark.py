"""Compare the quadratic residue table and direct square tests on the same slice."""
from time import perf_counter

from experiments.reciprocal_sum_slice import WIDTH, search
from scripts.factor import verify_file
from scripts.sum_interval_receipt import sum_interval_receipt


def slice_case(case, proof, agree, certify_split):
    n = int(case['n'])
    start = perf_counter()
    run = search(n, case['max_blocks'], from_end=case['from_end'])
    elapsed = perf_counter()-start
    factor = run.pop('factor')
    run['found_divisor'] = str(factor) if factor is not None else None
    agree(dict(id=case['id'], **case['checks']), run, case['checks'])
    result = certify_split(case, proof, factor, elapsed, 'reciprocal_sum_slice', run)
    if case.get('certify_interval'):
        if factor is not None or run['fermat_factor'] is not None or run['blocks']==0:
            raise ValueError('the slice must contain an examined interval with no factor')
        low = int(run['lower']) + WIDTH*int(run['first_block'])
        high = min(int(run['upper']), low+WIDTH*run['blocks']-1)
        source, count = sum_interval_receipt(n, low, high)
        proof.write_text(source)
        check = perf_counter()
        verify_file(proof, 'PrimeFactors.Generated.sumIntervalExclusion')
        result['exclusion'] = dict(lower=str(low), upper=str(high), proof=f'proofs/{proof.name}',
                                   verification_seconds=perf_counter()-check,
                                   method='factor sum square tests', sums=count)
    return result
