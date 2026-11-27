"""Run the new and original arithmetic on the same public draws and certify positive comparisons."""
from time import perf_counter

from experiments.complementary_keys import search
from experiments.twelve_residue_collision import search as original
from scripts.complementary_exclusion import check_no_matches
from scripts.factor import verify_file


def case_result(case, proof, agree, certify_split):
    n, draws, seed = int(case['n']), case['draws'], case['seed']
    methods = [('folded', search, 'folded'), ('old', original, 'twelve')]
    if n % 12 in (5, 7):
        methods.append(('target', search, 'target'))
        methods.append(('euclid', search, 'euclid'))
    runs = {}
    factors = {}
    for label, method, mode in methods:
        factor, work, seconds = method(n, draws, seed, mode)
        if factor is not None and (factor <= 1 or factor >= n or n % factor):
            raise ArithmeticError('invalid divisor')
        work.update(divisor=str(factor) if factor else None, seconds=seconds)
        wanted = case['checks'][label]
        agree(dict(id=case['id']+'.'+label, **wanted), work, wanted)
        runs[label] = work
        factors[label] = factor
    selected = next((label for label in runs if factors[label] is not None), None)
    data = dict(draws=draws, seed=seed, public_remainder=n % 12, runs=runs, certified_method=selected)
    result = certify_split(case, proof, factors.get(selected), sum(run['seconds'] for run in runs.values()),
                           'complementary_keys', data)
    if case.get('check_no_matches'):
        first_odd_factor = factors['euclid'] if case.get('check_first_odd_coefficient') else None
        if case.get('check_first_odd_coefficient') and first_odd_factor is None:
            raise ValueError('the first odd coefficient receipt needs a discovered Euclid divisor')
        result['complement_no_match_receipt'] = check_no_matches(n, draws, seed, proof, first_odd_factor)
    hit = runs['folded']
    if hit.get('branch') == 'complement' or hit['source'] == 'middle':
        x = int(hit['witness'][0])
        y = int(hit['witness'][-1])
        path = proof.with_name(proof.stem+'-complement.lean')
        comparison = f"Nat.gcd {n} total.natAbs={factors['folded']}"
        if hit['source'] == 'complement norm':
            comparison = (f"Nat.gcd {n} total.natAbs={n} ∧ "
                          f"Nat.gcd {n} ((ComplementaryNormBranches.branches x y)[{hit['norm_index']}]!).natAbs"
                          f"={factors['folded']}")
        path.write_text(f"""import PrimeFactors.ComplementaryNormBranches

namespace PrimeFactors.Generated.ComplementaryKeys
open TwelveResidueCollision
private def x : ℤ := {x}
private def y : ℤ := {y}
private def total : ℤ := num x*den y+num y*den x-den x*den y

theorem checked : Nat.gcd {n} (mask x*mask y).natAbs=1 ∧
    {comparison} := by decide +kernel
#print axioms checked
end PrimeFactors.Generated.ComplementaryKeys
""")
        start = perf_counter()
        verify_file(path, 'PrimeFactors.Generated.ComplementaryKeys.checked')
        result['complement_receipt'] = dict(proof=f'proofs/{path.name}', seconds=perf_counter()-start)
    return result
