"""Benchmark three evaluations of the public interval for an equal-width prime pair."""
from time import perf_counter

from experiments.factorial_progressions import search as progressions
from experiments.short_pascal_blocks import search as blocks
from experiments.short_pascal_row import search as exact
from scripts.factor import render_certificate, verify_file


def short_case(case, proof, agree, certify_split):
    n = int(case['n'])
    mode = case['mode']
    start = perf_counter()
    if mode == 'exact':
        divisor, work = exact(n, case['max_column'])
    elif mode == 'tree':
        work = blocks(n, case['wheel'], case['max_side'])
        divisor = work.pop('factor')
    elif mode == 'interpolation':
        work = progressions(n, case['max_span'], wheel=case['wheel'], equal_width=True)
        divisor = work.pop('factor')
    else:
        raise ValueError('unknown short-row evaluation')
    elapsed = perf_counter()-start
    agree(case['checks'] | {'id':case['id']}, work, case['checks'].keys())
    result = certify_split(case, proof, None, elapsed, 'short_pascal', {'mode':mode, **work})
    if divisor is not None:
        start = perf_counter()
        p,q = sorted((divisor,n//divisor))
        base = 1 << ((n.bit_length()+1)//2-1)
        source = render_certificate(n, [p,q], certificate_trial_limit=case.get('certificate_trial_limit',10000))
        claim = 'PrimeFactors.Generated.short_row'
        proof.write_text('import PrimeFactors.ShortPascalRow\n'+source+f'''
namespace PrimeFactors.Generated
theorem short_row : ShortPascalRow.VerifiedRow {n} {base} {p} {q} :=
  @ShortPascalRow.verify_row {n} {base} {p} {q}
    (by decide +kernel) prime_{p} prime_{q} (by decide +kernel)
    (by decide +kernel) (by decide +kernel) factorization
#print axioms short_row
end PrimeFactors.Generated
''')
        check = perf_counter()
        verify_file(proof, claim)
        result.update(factors=[str(p),str(q)], remaining=[], status='complete', verified=True,
                      certificate_seconds=perf_counter()-start, verification_seconds=perf_counter()-check)
    elif mode == 'exact' and work['outcome'] == 'column_limit':
        row, column = int(work['row']), int(work['column'])
        if 2*column <= row:
            exponent = column.bit_length()-1
            base = 1 << ((n.bit_length()+1)//2-1)
            path = proof.with_name(proof.stem+'-size.lean')
            claim = 'PrimeFactors.Generated.entry_size'
            path.write_text(f'''import PrimeFactors.ShortPascalRow
theorem {claim} : PrimeFactors.ShortPascalRow.SizeBound {n} {base} {exponent} := by
  exact @PrimeFactors.ShortPascalRow.checked_size {n} {base} {row} {column} {exponent}
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
#print axioms {claim}
''')
            verify_file(path, claim)
            result['short_row_size'] = dict(proof=f'proofs/{path.name}', exponent=exponent)
    return result
