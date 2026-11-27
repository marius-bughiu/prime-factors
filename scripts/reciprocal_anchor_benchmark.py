"""Run the product-only anchor search and kernel-check its full-size candidate limits."""
from math import isqrt
from time import perf_counter

from experiments.factor_sum_quantile import sum_bounds
from experiments.reciprocal_anchor import compare
from scripts.factor import verify_file


def receipt(n, bits, work, path):
    a = work['anchor']
    d = int(a['period'])
    lines = [
        'import PrimeFactors.ReciprocalSearchWindow',
        'import PrimeFactors.ReciprocalTraceHalving',
        'import PrimeFactors.HalfPeriodWindow',
        'namespace PrimeFactors.Generated.ReciprocalAnchor',
        'open CharacterInterval ReciprocalDivisorSums ReciprocalSearchWindow',
        'set_option maxRecDepth 16384', 'set_option exponentiation.threshold 4096',
        f'private abbrev n : ℕ := {n}', f'private abbrev d : ℕ := {d}',
        f'private abbrev t : ℤ := {a["minus_root"]}',
        'private theorem cop : n.Coprime d := by decide +kernel',
        'private abbrev u := ZMod.unitOfCoprime n cop',
        'private theorem norm : (n : ℤ) ∣ t^2+d := by decide +kernel',
        'private theorem three : d%4=3 := by decide +kernel',
        'private theorem stride : Nat.Coprime 60 d := by decide +kernel',
        f'private theorem square : IsSquare (u : ZMod d) := by\n  refine ⟨{a["root"]}, ?_⟩\n'
        '  rw [show (u : ZMod d) = n from ZMod.coe_unitOfCoprime ..]\n  decide +kernel',
    ]
    if bits == 1024:
        bound = 2**bits
        lo, _, hi = sum_bounds(n, bits)
        windows = [('factor', (n+bound-2)//(bound-1), isqrt(n)),
                   ('sum', lo, hi)]
        for label, low, high in windows:
            # Across starts in the 60 residues, lengths differ by at most one.
            length = (high-low+1)//60
            blocks = (length+d)//d
            kernel_cap = blocks*d//2 if label == 'factor' else blocks*(d+2**130)//4
            permille = (1000*kernel_cap+length-1)//length
            positions = 'divisorClasses d' if label == 'factor' else 'sums u'
            call = ('divisor_capacity three' if label == 'factor' else
                    'sum_capacity three (by decide +kernel) (by decide +kernel) cop norm')
            denom = 2 if label == 'factor' else 4
            rhs = 'd' if label == 'factor' else '(d+2^130)'
            lower_expr = '(n+2^1024-2)/(2^1024-1)' if label == 'factor' else '(4*n-1).sqrt+1'
            upper_expr = 'n.sqrt' if label == 'factor' else '((2^1024)^2+n-1)/2^1024'
            root_expr, integer_root = ('n', isqrt(n)) if label == 'factor' else ('4*n-1', isqrt(4*n-1))
            if label == 'factor':
                upper_expr = str(integer_root)
            else:
                lower_expr = f'{integer_root}+1'
            lines += [
                f'private theorem {label}Root : ({root_expr}).sqrt = {integer_root} :=',
                '  sqrt_of_bounds (by decide +kernel) (by decide +kernel)',
                f'private abbrev {label}Min : ℕ := (({upper_expr})+1-({lower_expr}))/60',
                f'private theorem {label}Size : {label}Min={length} := by',
                '  decide +kernel',
                f'theorem {label}Limit (first len : ℕ) (low : {label}Min≤len) (high : len≤{label}Min+1) :',
                f'    1000*(surviving ({positions}) first 60 len).card ≤ {permille}*len := by',
                f'  rw [{label}Size] at low high',
                f'  have fit : len ≤ {blocks}*d := high.trans (by decide +kernel)',
                f'  have h := {call} first 60 len {blocks} stride fit',
                f'  have ratio : 1000*({blocks}*{rhs}) ≤ {denom}*({permille}*{length}) := by decide +kernel',
                '  exact ReciprocalSearchWindow.ratio (by decide) h ratio low',
            ]
        count = work['complete_sum_periods']
        lines += [
            'theorem sameModulus (first len : ℕ) (low : sumMin≤len) (high : len≤sumMin+1) :',
            f'    {2*count+1}*(surviving (sums u) first 60 len).card ≤',
            f'    {count+1}*(surviving (ReciprocalTraceHalving.ordinary u) first 60 len).card := by',
            f'  exact same_modulus three u square first 60 len {count} stride',
            '    ((by rw [sumSize]; decide +kernel : _ ≤ sumMin).trans low)',
            '    (high.trans (by rw [sumSize]; decide +kernel))',
        ]
    lines += [
        'theorem checked : (n : ℤ) ∣ t^2+d ∧ IsSquare (u : ZMod d) ∧',
        '    2*(sums u).card = (ReciprocalTraceHalving.ordinary u).card :=',
        '  ⟨norm,square,ReciprocalTraceHalving.exact_half three u square⟩',
        '#print axioms checked', 'end PrimeFactors.Generated.ReciprocalAnchor',
    ]
    path.write_text('\n'.join(lines)+'\n')
    start = perf_counter()
    verify_file(path, 'PrimeFactors.Generated.ReciprocalAnchor.checked')
    return dict(proof=f'proofs/{path.name}', seconds=perf_counter()-start)


def run_case(case, proof, agree, certify_split):
    start = perf_counter()
    n, bits = int(case['n']), case['factor_bits']
    work = compare(n, bits, case['steps'], case['prefix'])
    elapsed = perf_counter()-start
    agree(dict(id=case['id'], **case['checks']), work, case['checks'])
    factors = work.get('pairs', [])
    factor = int(factors[0][0]) if factors else None
    result = certify_split(case, proof, factor, elapsed, 'reciprocal_anchor', work)
    if work.get('anchor') and 'period' in work['anchor']:
        path = proof.with_name(proof.stem+'-window.lean')
        result['anchor_receipt'] = receipt(n, bits, work, path)
    return result
