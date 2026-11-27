"""Replay a low binomial column by its public odd progression modulo N."""
from math import gcd
from time import perf_counter

from experiments.short_pascal_row import interval
from scripts.factor import verify_file


def search(n, budget):
    if budget < 0:
        raise ValueError('negative odd-term budget')
    lower, upper = interval(n)
    first = lower+(lower%2 == 0)
    available = max(0, (upper-first)//2+1)
    paid = min(available, budget)
    row = (n-first)//2
    residue = 1
    for index in range(paid):
        residue = residue*(first+2*index)%n
    divisor = gcd(residue, n)
    work = dict(lower=str(lower), upper=str(upper), first=str(first), row=str(row),
                available=str(available), budget=budget, terms=paid, untested=str(available-paid),
                progression_residue=str(residue), gcd=str(divisor))
    return (divisor if 1 < divisor < n else None), work


def receipt(n, work, factors):
    lower, upper, first = (int(work[k]) for k in ('lower','upper','first'))
    row, total, paid = (int(work[k]) for k in ('row','available','terms'))
    residue, divisor = (int(work[k]) for k in ('progression_residue','gcd'))
    base = 1 << ((n.bit_length()+1)//2-1)
    extra = ''
    statement = 'arithmetic'
    if factors:
        p,q = map(int,factors)
        extra = f'''
theorem row_split : Nat.gcd (Nat.choose {row} {paid}) {n}={p} := by
  calc
    Nat.gcd (Nat.choose {row} {paid}) {n} = Nat.gcd (QuotientPascalMasks.progression {first} 2 {paid}) {n} :=
      QuotientPascalMasks.gcd_transfer (p:={p}) (q:={q}) (m:={row}) (d:=2) (c:={first}) (k:={paid})
        (by norm_num) (by norm_num) (by decide) (by decide) (by decide) (by decide)
    _ = {p} := by decide +kernel

theorem verified : Arithmetic ∧ Nat.gcd (Nat.choose {row} {paid}) {n}={p} := ⟨arithmetic,row_split⟩
'''
        statement = 'verified'
    return f'''import PrimeFactors.QuotientPascalMasks

namespace PrimeFactors.Generated.QuotientPascal
set_option maxRecDepth 8192
set_option exponentiation.threshold 8192

abbrev Arithmetic : Prop :=
  ShortPascalRow.lower {n} {base}={lower} ∧ {upper}^2≤{n} ∧ {n}<({upper}+1)^2 ∧
  {first}={lower}+1-{lower}%2 ∧
  (if {first}≤{upper} then QuotientPascalMasks.oddColumn {first} {upper} else 0)={total} ∧ {paid}=min {total} {work['budget']} ∧
  {first}+2*{row}={n} ∧ QuotientPascalMasks.progression {first} 2 {paid}%{n}={residue} ∧
  Nat.gcd {residue} {n}={divisor}

theorem arithmetic : Arithmetic := by decide +kernel
{extra}
#print axioms {statement}
end PrimeFactors.Generated.QuotientPascal
''', 'PrimeFactors.Generated.QuotientPascal.'+statement


def quotient_pascal_case(case, proof, agree, certify_split):
    n = int(case['n'])
    start = perf_counter()
    factor, work = search(n, case['budget'])
    elapsed = perf_counter()-start
    agree(dict(id=case['id'], **case['checks']), work, case['checks'])
    result = certify_split(case, proof, factor, elapsed, 'quotient_pascal', work)
    source, name = receipt(n, work, result['factors'])
    path = proof.with_name(proof.stem+'-column.lean')
    path.write_text(source)
    start = perf_counter()
    verify_file(path, name)
    result['quotient_pascal_receipt'] = dict(proof=f'proofs/{path.name}', seconds=perf_counter()-start)
    return result
