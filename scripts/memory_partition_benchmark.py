"""Replay a cap-aware CRT split and check the saturation certificates on the full-size controls."""

from time import perf_counter

from experiments.streamed_sum_join import search
from scripts.factor import verify_file


def _capacity_certificate(n, cap, plan, proof):
    """Check the actual prime-field menu sizes and an obstruction to sign-fixed choices."""
    moduli = plan['right_moduli']
    if 3 not in moduli or n%3 != 1 or plan['right_choices'] != 2*cap:
        raise ValueError('this capacity certificate requires saturation and a nonfixed mod-3 component')
    theorem = 'PrimeFactors.Generated.partitionCapacity'
    lines = ['import PrimeFactors.SumMenuPartition', '', 'open PrimeFactors.SumMenuPartition',
             '', f'private def input : ℕ := {n}', '', f'theorem {theorem} :',
             f'    (({moduli} : List ℕ).map (primeChoices input)).prod = 2*{cap} ∧',
             '    input%3=1 ∧ (∀ s : ZMod 3, PrimeFactors.AdmissibleSum 1 s → s≠-s) ∧',
             '    ∀ best other raw stored fixed : ℕ, 2*stored=raw+fixed →',
             f'      stored≤{cap} → best*(2*{cap})=other*raw → best≤other := by']
    names = []
    for m in moduli:
        residue = n % m
        root = next((x for x in range(m) if x*x % m == residue), None)
        size = (m-1)//2 if root is None else (m+1)//2
        name = f'c{m}'
        names.append(name)
        lines.append(f'  have {name} : primeChoices input {m} = {size} := by')
        if root is None:
            lines.append(f'    apply primeChoices_nonsquare (r:={residue}) (by decide +kernel)')
            lines.append('    all_goals decide +kernel')
        else:
            lines.append(f'    apply primeChoices_square (r:={residue}) (by decide +kernel) (by decide)')
            lines.append('    · decide +kernel')
            lines.append('    · decide +kernel')
            lines.append(f'    · exact ⟨{root}, by decide +kernel⟩')
    rules = ', '.join(['List.map_cons','List.map_nil','List.prod_cons','List.prod_nil',*names])
    lines.extend(['  refine ⟨?_, by decide +kernel, fun _ => mod_three_not_fixed, ?_⟩',
                  f'  · simp only [{rules}]', '    decide +kernel',
                  '  · intro best other raw stored fixed orbit fits same',
                  '    exact optimal_at_cap (by decide) orbit fits same', '',
                  f'#print axioms {theorem}', ''])
    proof.write_text('\n'.join(lines), encoding='utf-8')
    start = perf_counter()
    verify_file(proof, theorem)
    return dict(theorem=theorem, proof=f'proofs/{proof.name}', verification_seconds=perf_counter()-start)


def memory_partition_case(case, proof, agree, certify_split):
    n = int(case['n'])
    options = dict(candidates=tuple(map(int, case['bases'])), max_right=case['max_right'],
                   max_visited=case['max_visited'], reverse=case['reverse'], folded=True)
    start = perf_counter()
    run = search(n, **options, memory_partition=True, partition_budget=case['partition_budget'])
    elapsed = perf_counter()-start
    agree(case, run, ('outcome', 'probes'))
    work = run['work']
    plan = work['partition']
    agree(dict(id=case['id'], **case['work_checks']), work, case['work_checks'])
    agree(dict(id=case['id'], **case['partition_checks']), plan, case['partition_checks'])
    if (plan['left_rows']*plan['right_choices'] != plan['total_choices'] or
            2*plan['stored'] != plan['right_choices']+plan['right_fixed_points']):
        raise ValueError('inconsistent complete Cartesian counts')
    start = perf_counter()
    greedy = search(n, **options)
    old = dict(outcome=greedy['outcome'], seconds=perf_counter()-start,
               **{key:greedy['work'][key] for key in ('right_potential','right_built','left_visited')})
    agree(dict(id=case['id'], **case['baseline_checks']), old, case['baseline_checks'])
    run['greedy'] = old
    if 'origin' in case:
        run['origin'] = case['origin']
    factor = int(run['factors'][0]) if run['factors'] else None
    result = certify_split(case, proof, factor, elapsed, 'memory_partition_sum', run)
    if case.get('check_capacity'):
        run['capacity_certificate'] = _capacity_certificate(n, options['max_right'], plan,
                                                           proof.with_stem(proof.stem+'-capacity'))
    return result
