"""Benchmark successive wheel-product checks and certify the reported hit interval."""
from time import perf_counter

from experiments.factorial_progressions import block_size
from experiments.growing_factorial import search
from scripts.factor import render_certificate, verify_file


def range_claim(n, factor, run, wheel, max_span, centered, final_grid):
    low, upper, last = (int(run[key]) for key in ('low', 'upper', 'last'))
    ranges = [tuple(map(int, pair)) for pair in run['ranges']]
    entries = ', '.join(f'({a}, {b})' for a, b in ranges)
    cap = str(upper) if max_span is None else f'min {upper} ({low}+{max_span}-1)'
    clauses = [
        f'ShortPascalRow.lower {n} (2^(Nat.log2 {n}/2)) = {low}',
        f'Nat.sqrt {n} = {upper}',
        f'{last} = {cap}',
        f'scanned.all (fun r => decide ({low} ≤ r.1 ∧ r.1 ≤ r.2 ∧ r.2 ≤ {last})) = true',
        f'(scanned.map (fun r => r.2+1-r.1)).sum = {int(run["covered_span"])}',
        f'scanned.any (fun r => decide (r.1 ≤ {factor} ∧ {factor} ≤ r.2)) = true',
    ]
    # When discovery stops during a doubling, reconstruct its endpoints from
    # the alignment, total represented wheel residues and chosen direction.
    counters = run['work']
    batched = counters.get('batched_candidates', 0)
    if batched:
        alignment = (low+wheel-2)//wheel*wheel
        total_cycles = max(0, (last-alignment)//wheel)
        rho = counters['wheel_residues']
        grid_width = block_size(total_cycles, rho) if final_grid else None
        paired = centered and total_cycles >= 2 and grid_width != 1
        sides = 2 if paired else 1
        available = total_cycles//sides
        if final_grid and paired:
            available = (grid_width//sides)*(total_cycles//grid_width)
        cycles = batched//(sides*rho)
        middle = alignment+wheel*available
        span = wheel*cycles
        expected = (middle-span+1, middle+span) if paired else (low, alignment+span)
        if ranges == [expected]:
            h = counters['last_block_cycles']
            start = f'(({low}+{wheel}-2)/{wheel}*{wheel})'
            raw = f'(({last}-{start})/{wheel})'
            radius = f'({raw}/{sides})'
            terms = f'min ({rho}*{h}+1) ({radius}/{h})'
            if final_grid:
                clauses.extend([
                    f'{grid_width} = 2^{grid_width.bit_length()-1}',
                    f'{raw} ≤ 2*{rho}*{grid_width}^2',
                    f'({grid_width} = 1 ∨ 2*{rho}*({grid_width}/2)^2 < {raw})',
                ])
                if paired:
                    radius = f'(({grid_width}/{sides})*({raw}/{grid_width}))'
                if h == grid_width//sides and cycles == h*(total_cycles//grid_width):
                    terms = f'({raw}/{grid_width})'
                else:
                    terms = f'min ({rho}*{h}+1) ({radius}/{h})'
            clauses.extend([
                f'(List.range {wheel}).countP (fun r => decide (Nat.Coprime r {wheel})) = {rho}',
                f'{batched} = {sides}*{rho}*{cycles}',
                f'{h} = 2^{h.bit_length()-1}',
                f'{cycles} = {h} * {terms}',
            ])
            if paired:
                mid = f'({start}+{radius}*{wheel})'
                clauses.append(f'scanned = [({mid}-{wheel}*{cycles}+1, {mid}+{wheel}*{cycles})]')
            else:
                clauses.append(f'scanned = [({low}, {start}+{wheel}*{cycles})]')
    return f'let scanned : List (ℕ × ℕ) := [{entries}]\n    ' + ' ∧\n    '.join(clauses)


def growing_case(case, proof, agree, certify_split):
    n, wheel, cap = int(case['n']), case['wheel'], case['max_span']
    mode = case['mode']
    if mode not in ('forward', 'centered'):
        raise ValueError(f'unknown growing factorial mode {mode!r}')
    start = perf_counter()
    final_grid = case['final_grid']
    inputs = case.get('max_inputs')
    run = search(n, cap, wheel=wheel, folded=mode == 'centered', final_grid=final_grid,
                 max_inputs=inputs)
    elapsed = perf_counter()-start
    factor = run.pop('factor')
    agree({'id': case['id'], **case['checks']}, run, case['checks'])
    width = max(0, int(run['upper'])-int(run['low'])+1)
    report = dict(run, mode=mode, final_grid=final_grid, wheel=wheel, max_span=cap, full_span=str(width),
                  unvisited_span=str(width-int(run['covered_span'])))
    if inputs is not None:
        spent = run['work'].get('convolution_input_coefficients', 0)
        if spent > inputs or (run['outcome'] == 'convolution_limit' and
                              spent + run['work']['next_convolution_inputs'] <= inputs):
            raise ValueError(f'inconsistent convolution input budget on {case["id"]}')
        report.update(max_inputs=inputs, unused_inputs=inputs-spent)
    if factor is None or run['outcome'] != 'prefix_gcd':
        return certify_split(case, proof, factor, elapsed, 'growing_factorial', report)

    result = certify_split(case, proof, None, elapsed, 'growing_factorial', report)
    start = perf_counter()
    factors = sorted((factor, n//factor))
    upper = int(run['upper'])
    exponent = n.bit_length()-1
    source = render_certificate(n, factors, certificate_trial_limit=case.get('certificate_trial_limit', 10000))
    claim = range_claim(n, factor, run, wheel, cap, mode == 'centered', final_grid)
    proof.write_text('import PrimeFactors.ShortPascalRow\n' + source + f"""
namespace PrimeFactors.Generated
/-- {mode.capitalize()} growth, final grid {str(final_grid).lower()}, wheel {wheel}. -/
theorem growing_factorization : ExactFactorization {n} {factors} ∧
    ({claim}) := by
  refine ⟨factorization, ?_⟩
  dsimp only
  have bits : Nat.log2 {n} = {exponent} := Nat.eq_of_le_of_lt_succ
    ((Nat.le_log2 (by decide : {n} ≠ 0)).mpr (by decide +kernel))
    ((Nat.log2_lt (by decide : {n} ≠ 0)).mpr (by decide +kernel))
  have root : Nat.sqrt {n} = {upper} := Nat.eq_of_le_of_lt_succ
    (Nat.le_sqrt'.mpr (by decide +kernel)) (Nat.sqrt_lt'.mpr (by decide +kernel))
  rw [bits, root]
  decide +kernel
#print axioms growing_factorization
end PrimeFactors.Generated
""")
    verify_start = perf_counter()
    verify_file(proof, 'PrimeFactors.Generated.growing_factorization')
    result.update(factors=list(map(str, factors)), remaining=[], status='complete', verified=True,
                  certificate_seconds=perf_counter()-start, verification_seconds=perf_counter()-verify_start)
    if 'certificate_trial_limit' in case:
        result['certificate_trial_limit'] = case['certificate_trial_limit']
    report['checked_factor_range'] = True
    return result
