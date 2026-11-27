"""Run the new and original arithmetic on the same public draws and certify positive comparisons."""
from time import perf_counter

from experiments.complementary_keys import search
from experiments.twelve_residue_collision import search as original
from scripts.factor import verify_file


def case_result(case, proof, agree, certify_split):
    n, draws, seed = int(case['n']), case['draws'], case['seed']
    methods = [('folded', search, 'folded'), ('old', original, 'twelve')]
    if n % 12 in (5, 7):
        methods.append(('target', search, 'target'))
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
    data = dict(draws=draws, seed=seed, public_remainder=n % 12, runs=runs)
    result = certify_split(case, proof, factors['folded'], runs['folded']['seconds'], 'complementary_keys', data)
    hit = runs['folded']
    if hit['source'] in ('pair', 'middle') and (hit.get('branch') == 'complement' or hit['source'] == 'middle'):
        x = int(hit['witness'][0])
        y = int(hit['witness'][-1])
        path = proof.with_name(proof.stem+'-complement.lean')
        path.write_text(f"""import PrimeFactors.ComplementaryKeys

namespace PrimeFactors.Generated.ComplementaryKeys
open TwelveResidueCollision
private def x : ℤ := {x}
private def y : ℤ := {y}
private def total : ℤ := num x*den y+num y*den x-den x*den y

theorem checked : Nat.gcd {n} (mask x*mask y).natAbs=1 ∧
    Nat.gcd {n} total.natAbs={factors['folded']} := by decide +kernel
#print axioms checked
end PrimeFactors.Generated.ComplementaryKeys
""")
        start = perf_counter()
        verify_file(path, 'PrimeFactors.Generated.ComplementaryKeys.checked')
        result['complement_receipt'] = dict(proof=f'proofs/{path.name}', seconds=perf_counter()-start)
    return result
