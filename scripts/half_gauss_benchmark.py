"""Replay the half Gauss factorial on a bounded prefix, recording each gcd observation."""
from math import gcd
from time import perf_counter

from scripts.factor import verify_file


def search(n, budget):
    if n < 3 or n % 2 == 0 or budget < 0:
        raise ValueError('expected an odd modulus at least three and a nonnegative term budget')
    required = n // 2
    paid = min(required, budget)
    partial = 1
    units = 0
    first_index = first_divisor = None
    for j in range(1, paid + 1):
        divisor = gcd(n, j)
        if divisor == 1:
            partial = partial * j % n
            units += 1
        elif first_divisor is None:
            first_index, first_divisor = j, divisor
    readout = gcd(n, partial + 1) if paid == required else None
    if readout is not None and 1 < readout < n:
        factor = readout
        source = 'completed half product'
    else:
        factor = first_divisor
        source = 'first nonunit in the scan' if first_divisor else None
    return factor, dict(budget=budget, required=str(required), terms=paid,
                        untested=str(required-paid), units=units, prefix_residue=str(partial),
                        first_nonunit=first_index, first_divisor=first_divisor,
                        readout_gcd=readout, factor_source=source)


def half_gauss_case(case, proof, agree, certify_split):
    n = int(case['n'])
    start = perf_counter()
    factor, work = search(n, case['budget'])
    elapsed = perf_counter()-start
    agree(dict(id=case['id'], **case['checks']), work, case['checks'])
    result = certify_split(case, proof, factor, elapsed, 'half_gauss', work)
    paid = work['terms']
    first = work['first_nonunit']
    before = ''
    if first is not None:
        before = f''' ∧
      ((Finset.range {first-1}).filter (fun i => (i+1).Coprime n)).card={first-1} ∧
      Nat.gcd n {first}={work['first_divisor']}'''
    complete = ''
    if work['readout_gcd'] is not None:
        complete = f''' ∧
      HalfGaussProduct.residue n={work['prefix_residue']} ∧
      Nat.gcd n (HalfGaussProduct.residue n+1)={work['readout_gcd']}'''
    path = proof.with_name(proof.stem+'-scan.lean')
    path.write_text(f'''import PrimeFactors.HalfGaussProduct

namespace PrimeFactors.Generated.HalfGauss
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
private abbrev n : ℕ := {n}

theorem checked :
    n/2={work['required']} ∧ {paid}=min (n/2) {work['budget']} ∧ n/2-{paid}={work['untested']} ∧
    ((Finset.range {paid}).filter (fun i => (i+1).Coprime n)).card={work['units']} ∧
    HalfGaussProduct.unitProduct n {paid}%n={work['prefix_residue']}{before}{complete} := by
  decide +kernel

#print axioms checked
end PrimeFactors.Generated.HalfGauss
''')
    start = perf_counter()
    verify_file(path, 'PrimeFactors.Generated.HalfGauss.checked')
    result['half_gauss_receipt'] = dict(proof=f'proofs/{path.name}', seconds=perf_counter()-start)
    return result
