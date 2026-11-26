"""Replay the table-selected prefix and check the recovered gcd and prime factors."""
from time import perf_counter

from experiments.cheap_multiplier_selection import catalogue, evaluate, search
from scripts.factor import render_certificate, verify_file


def cheap_multiplier_case(case,proof,agree,certify_split):
    n = int(case['n'])
    start = perf_counter()
    tables = catalogue()
    one_time = perf_counter()-start
    start = perf_counter()
    selected = search(n,tables)
    elapsed = perf_counter()-start
    ordinary = evaluate(n,[(1,selected['total_roots']-1)],tables)
    witness = selected['witness']
    work = dict(k=selected['k'],comparisons=selected['guards'],trace_tests=selected['trace_tests'],
                total_roots=selected['total_roots'],ordinary_tests=ordinary['trace_tests'],
                ordinary_total_roots=ordinary['total_roots'],ordinary_factors=list(map(str,ordinary['factors'])),
                catalogue_seconds=one_time,witness=None if witness is None else list(map(str,witness)))
    agree(dict(id=case['id'],**case['checks']),work,case['checks'])
    result = certify_split(case,proof,None,elapsed,'cheap_multiplier_selection',work)
    if not selected['factors']:
        return result
    f = selected['factors'][0]
    factors = sorted((f,n//f))
    k,first,index,s,d,g = witness
    allowed = sorted(tables[k,n%24][1])
    rem = first%24
    prefix_limit = 32 if selected['k']==1 else 16
    # The cutoff's accepted residue count and the integer-square bracket
    # bind the GCD witness to the charged prefix at this selected multiplier.
    predicate = f'(fun j => ({allowed} : List ℕ).contains (({rem}+j)%24))'
    theorem = f'''
namespace PrimeFactors.Generated
/-- The selected prefix reaches this square; its gcd gives a proper divisor. -/
theorem cheapMultiplierSplit :
    (({first}-1)^2 < 4*{k}*{n} ∧ 4*{k}*{n} ≤ {first}^2 ∧
     {first}%24={rem} ∧ {first}≤{s} ∧
     ((List.range {s-first+1}).filter {predicate}).length={index+1} ∧
     ({allowed} : List ℕ).contains ({s}%24) = true ∧ {index} < {prefix_limit} ∧
     {s}^2=4*{k}*{n}+{d}^2 ∧ Nat.gcd (({s}+{d})/2) {n}={g} ∧ 1<{g} ∧ {g}<{n})
    ∧ ExactFactorization {n} {factors} :=
  ⟨by decide +kernel, factorization⟩
#print axioms cheapMultiplierSplit
end PrimeFactors.Generated
'''
    cert = perf_counter()
    proof.write_text(render_certificate(n,factors)+theorem)
    check = perf_counter()
    verify_file(proof,'PrimeFactors.Generated.cheapMultiplierSplit')
    result.update(verified=True,status='complete',factors=list(map(str,factors)),remaining=[],
                  verification_seconds=perf_counter()-check,certificate_seconds=perf_counter()-cert)
    return result
