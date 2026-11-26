"""Compare the quadratic residue table and direct square tests on the same slice."""
from math import isqrt
from time import perf_counter

from experiments.reciprocal_sum_slice import WIDTH, search
from scripts.factor import verify_file
from scripts.sum_interval_receipt import sum_interval_receipt


def clipped_receipt(n):
    """Prove the percentage from the public endpoints without scanning the full band."""
    if n.bit_length() != 2048:
        raise ValueError('this certificate uses the two 1,024-bit factor bounds')
    top = isqrt(n)
    low = max(2**1023, (n-1)//(2**1024-1)+1)
    blocks = min(top//42200, (top+1-low)//WIDTH)
    if blocks <= 0:
        raise ValueError('the clipped range needs at least one full guaranteed block')
    percent = (2*100*384*blocks-1)//(top-low+2)
    source = f"""import PrimeFactors.ReciprocalSumTail

namespace PrimeFactors.Generated
open ReciprocalSumSlice ReciprocalSumTail
set_option maxRecDepth 16384
set_option exponentiation.threshold 4096

private abbrev input : ℕ := {n}

theorem clippedPercentage :
    {percent}*(ordinary (NearSmoothExclusion.smallest input) input.sqrt).card <
      100*(cut input (NearSmoothExclusion.smallest input) input.sqrt).card := by
  have root : {top} = input.sqrt := by apply Nat.eq_sqrt'.mpr; decide +kernel
  have endpoint : NearSmoothExclusion.smallest input = {low} := by decide +kernel
  rw [← root,endpoint]
  exact percentage_of_margin (k:={blocks}) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms clippedPercentage
end PrimeFactors.Generated
"""
    return source, percent


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
    if 'clipped_percent' in case:
        source, percent = clipped_receipt(n)
        if percent != case['clipped_percent']:
            raise ValueError('unexpected whole-interval percentage')
        receipt = proof.with_name(f'{proof.stem}-clipped.lean')
        receipt.write_text(source)
        check = perf_counter()
        verify_file(receipt, 'PrimeFactors.Generated.clippedPercentage')
        result['clipped_proof'] = dict(percent=percent, proof=f'proofs/{receipt.name}',
                                       verification_seconds=perf_counter()-check)
    return result
