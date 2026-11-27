"""Check the product-only split and arithmetic that places the ordinary trace out of reach."""
from time import perf_counter

from experiments.interior_prime_family import search, search_blocks
from scripts.factor import render_certificate, verify_file


def interior_family_case(case, proof, agree, certify_split):
    n = int(case['n'])
    blocks = case.get('blocks')
    start = perf_counter()
    if blocks is None:
        budget = case['budget']
        scan = search(n, budget)
    else:
        budget = 2*blocks
        scan = search_blocks(n, blocks)
    elapsed = perf_counter()-start
    f = scan['factor']
    first = scan['first']
    work = dict(budget=budget, tests=scan['tests'], squares=scan['squares'],
                first=str(first), found=None if f is None else str(min(f,n//f)))
    if blocks is not None:
        work['blocks'] = blocks
    agree(dict(id=case['id'], **case['checks']), work, case['checks'])
    result = certify_split(case, proof, None, elapsed, 'interior_prime_family', work)
    if f is None:
        return result
    start = perf_counter()
    p, q = sorted((f, n//f))
    s, d, i = scan['trace'], scan['root'], scan['tests']-1
    if blocks is None:
        rank = (f'({first}-2)^2<24*n ∧ 24*n≤{first}^2 ∧ {first}%2=1 ∧ '
                f'{s}={first}+2*{i} ∧ {i}<{budget}')
    else:
        j = s//6-first//6
        r = s%6
        rank = (f'({first}-1)^2<24*n ∧ 24*n≤{first}^2 ∧ {first}≤{s} ∧ '
                f'{s}=6*({first}/6+{j})+{r} ∧ ({r}=1 ∨ {r}=5) ∧ {j}<{blocks} ∧ '
                f'(({s}+5)/6+({s}+1)/6)-(({first}+4)/6+{first}/6)={i+1}')
    source = render_certificate(n, [p,q], certificate_trial_limit=2)
    source += f'''
namespace PrimeFactors.Generated
private abbrev n : ℕ := {n}
private abbrev p : ℕ := {p}
private abbrev q : ℕ := {q}
/-- The odd trace tested from the product gives the split. Even the ordinary
trace 2^1015 above its minimum is too small, as witnessed by squaring. -/
theorem interiorFamilySplit :
    ExactFactorization n [p,q] ∧
    (9*(2^1024)^2≤16*n ∧ 8*n≤5*(2^1024)^2 ∧
    2^1023≤p ∧ p<q ∧ q<2^1024 ∧
    {rank} ∧ {s}=3*p+2*q ∧
    {s}^2=24*n+{d}^2 ∧ Nat.gcd (({s}+{d})/2) n={f} ∧
    2^1015<p+q ∧ 4*n<(p+q-2^1015)^2) :=
  ⟨factorization,by decide +kernel⟩
#print axioms interiorFamilySplit
end PrimeFactors.Generated
'''
    proof.write_text(source)
    check = perf_counter()
    verify_file(proof, 'PrimeFactors.Generated.interiorFamilySplit')
    result.update(verified=True, status='complete', factors=[str(p),str(q)], remaining=[],
                  verification_seconds=perf_counter()-check, certificate_seconds=perf_counter()-start)
    return result
