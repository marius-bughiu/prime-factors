"""Replay the same seeded samples under four maps and certify twelve-residue splits."""
from time import perf_counter

from experiments.twelve_residue_collision import search
from scripts.factor import verify_file


def check_witness(n, divisor, work, factor_proof):
    """Check the observed gcd from the public input and reported seeds."""
    source = work['source']
    samples = list(map(int, work['witness']))
    declarations = [f'private def x : ℤ := {samples[0]}']
    if source == 'regularity check':
        claim = f'Nat.gcd {n} (mask x).natAbs = {divisor}'
    else:
        declarations += [f'private def y : ℤ := {samples[1]}',
                         'private def difference : ℤ := num x * den y - num y * den x']
        claim = f'Nat.gcd {n} (mask x * mask y).natAbs = 1 ∧ '
        if source == 'pair':
            claim += f'Nat.gcd {n} difference.natAbs = {divisor}'
        elif source == 'shared key':
            index = work['orientation']
            declarations.append(f'private def oriented : ℤ := imageDen x {index} * y - imageNum x {index}')
            claim += (f'Nat.gcd {n} difference.natAbs = {n} ∧ oriented = '
                      f"({int(work['signed_difference'])}) ∧ Nat.gcd {n} oriented.natAbs = {divisor}")
        else:
            raise ValueError(f'Unknown split source {source}')
    filename = factor_proof.with_name(f'{factor_proof.stem}-witness.lean')
    header = ('import PrimeFactors.TwelveResidueCollision\n'
              'namespace PrimeFactors.Generated.TwelveResidue\nopen TwelveResidueCollision\n')
    filename.write_text(header + '\n'.join(declarations) + '\n' +
                        f'theorem checked : {claim} := by decide +kernel\n'
                        '#print axioms checked\nend PrimeFactors.Generated.TwelveResidue\n')
    start = perf_counter()
    verify_file(filename, 'PrimeFactors.Generated.TwelveResidue.checked')
    return dict(proof=f'proofs/{filename.name}', seconds=perf_counter()-start)


def twelve_residue_case(case, proof, agree, certify_split):
    n, draws, seed = int(case['n']), case['draws'], case['seed']
    runs = {}
    total = 0.0
    for mode in ('twelve', 'matched', 'raw', 'power'):
        divisor, work, seconds = search(n, draws, seed, mode)
        if divisor is not None and (not 1 < divisor < n or n % divisor):
            raise ValueError(f'Invalid {mode} divisor of {n}')
        work.update(divisor=str(divisor) if divisor is not None else None, seconds=seconds)
        runs[mode] = work
        total += seconds
        expected = case['checks'][mode]
        agree(dict(id=f"{case['id']}.{mode}", **expected), work, expected)
    work = dict(draws=draws, seed=seed, runs=runs)
    primary = runs['twelve']
    divisor = int(primary['divisor']) if primary['divisor'] is not None else None
    result = certify_split(case, proof, divisor, total, 'twelve_residue', work)
    if divisor is not None:
        result['twelve_residue_witness'] = check_witness(n, divisor, primary, proof)
    return result
