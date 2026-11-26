"""Generate the first independently drawn certified pair with product 5 modulo 12.

The product-only scan receives N and a 64-test budget. Prime labels enter only
after that scan, to check its answer or locate the known witness retrospectively.
"""
import argparse
import json
from pathlib import Path

from .certified_control import lean_source, prime_chain
from .mixed_negative_templates import scan, schedule
from scripts.factor import verify_file

ROOT = Path(__file__).resolve().parents[1]
TAG = 'mixed-negative-residue-5-v1'
WIDTH = 64
RECORD = ROOT / 'research/mixed-negative-control.json'
PROOF = ROOT / 'benchmarks/controls/MixedNegativeControl.lean'


def generate():
    attempt = 0
    while True:
        chains = {side: prime_chain(f'{TAG}/{attempt}/{side}', 1024) for side in ('left', 'right')}
        p, q = (int(chain[-1]['prime']) for chain in chains.values())
        n = p*q
        if p != q and n.bit_length() == 2048 and n % 12 == 5:
            break
        attempt += 1
    found = scan(n, WIDTH)
    first, _, _ = schedule(n)
    p, q = sorted((p, q))
    t, s = (p+q)//6, (q-p)//4
    g = (n-t*t)//4
    if not (t*t+4*g == n and s*s+9*g == 2*n and (3*t-2*s, 3*t+2*s) == (p,q)):
        raise ArithmeticError('constructed prime labels fail the predicted relation')
    rank = (t-first)//2+1
    if (rank <= WIDTH) != bool(found.get('factors')):
        raise ArithmeticError('product-only search disagrees with witness rank')
    search_report = dict(found)
    search_report['remaining_candidates'] = str(search_report.pop('remaining'))
    search_report['unresolved_cofactor'] = None if found.get('factors') else str(n)
    record = dict(domain=TAG, first_eligible_attempt=attempt, product=str(n),
                  factor_bits=[p.bit_length(),q.bit_length()], checked_primes=[str(p),str(q)],
                  budget=WIDTH, search=search_report, retrospective_witness_rank=str(rank))
    source = lean_source(dict(product=str(n),chains=chains), include_signature=False)
    witness = f'''
namespace PrimeFactors.Generated

-- The independently known primes locate the match in the public scan.
theorem witness_position :
    let t := (left1024+right1024)/6
    let s := (max left1024 right1024-min left1024 right1024)/4
    let g := (controlProduct-t^2)/4
    controlProduct%12=5 ∧ t={first}+2*({rank}-1) ∧
      t^2+4*g=controlProduct ∧ s^2+9*g=2*controlProduct ∧
      3*t-2*s=min left1024 right1024 ∧ 3*t+2*s=max left1024 right1024 := by
  decide +kernel

#print axioms witness_position
end PrimeFactors.Generated
'''
    return record, source+witness


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    options = parser.add_mutually_exclusive_group(required=True)
    options.add_argument('--write', action='store_true')
    options.add_argument('--check', action='store_true')
    args = parser.parse_args()
    data, source = generate()
    serialized = json.dumps(data, indent=2)+'\n'
    if args.write:
        RECORD.write_text(serialized)
        PROOF.write_text(source)
    elif RECORD.read_text() != serialized or PROOF.read_text() != source:
        raise SystemExit('generated product or reference certificate changed')
    verify_file(PROOF)
    verify_file(PROOF, 'PrimeFactors.Generated.witness_position')
    print('Checked the independent reference primes and the product-only search outcome.')
