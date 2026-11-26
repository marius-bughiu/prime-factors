"""Check the product-only split and arithmetic that places the ordinary trace out of reach."""
from time import perf_counter

from experiments.interior_prime_family import search
from scripts.factor import render_certificate, verify_file


def interior_family_case(case, proof, agree, certify_split):
    n, budget = int(case['n']), case['budget']
    start = perf_counter()
    scan = search(n, budget)
    elapsed = perf_counter()-start
    f = scan['factor']
    first = scan['first']
    work = dict(budget=budget, tests=scan['tests'], squares=scan['squares'],
                first=str(first), found=None if f is None else str(min(f,n//f)))
    agree(dict(id=case['id'], **case['checks']), work, case['checks'])
    result = certify_split(case, proof, None, elapsed, 'interior_prime_family', work)
    if f is None:
        return result
    start = perf_counter()
    p, q = sorted((f, n//f))
    s, d, i = scan['trace'], scan['root'], scan['tests']-1
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
    ({first}-2)^2<24*n ∧ 24*n≤{first}^2 ∧ {first}%2=1 ∧
    {s}={first}+2*{i} ∧ {i}<{budget} ∧ {s}=3*p+2*q ∧
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
