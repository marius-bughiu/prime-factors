"""Construct certified 2048-bit examples where the target size limits 6 and 30 are attained."""
import argparse
from hashlib import sha256
import json
from math import gcd, isqrt, lcm
from pathlib import Path

from experiments.certified_control import SMALL_PRIMES, lean_source
from experiments.mixed_ratio_heights import jacobi
from experiments.norm_direction_check import prime_root
from scripts.factor import verify_file

ROOT = Path(__file__).resolve().parents[1]
RECORD = ROOT/'research/three-target-limits.json'
SCREENS = {
    'signed': (43, 53, 6, [d for d in range(-5, 6) if d < 0 or isqrt(d)**2 != d]),
    'positive': (443, 487, 30, [d for d in range(2, 30) if isqrt(d)**2 != d]),
}


def lift(child, residue, modulus):
    """Search a Pocklington progression above 3*2^1022 in the prescribed residue."""
    r = int(child[-1]['prime'])
    low = ((3 << 1022)-2)//(2*r)+1
    step = modulus//2
    a = (residue-1)//2 * pow(r, -1, step) % step
    start = low + (a-low) % step
    for k in range(start, ((1 << 1024)-2)//(2*r)+1, step):
        n = 1+2*r*k
        if any(n % p == 0 for p in SMALL_PRIMES):
            continue
        z = pow(2, 2*k, n)
        if gcd(z-1,n) == 1 and pow(z,r,n) == 1:
            if n % modulus != residue % modulus or n > r*r:
                raise ArithmeticError('incorrect progression or Pocklington order size')
            return [*child, dict(bits=1024, prime=str(n), multiplier=str(k), order_witness=str(z),
                                 increments=(k-start)//step)]
    raise ArithmeticError('exhausted the prescribed progression')


def make(label, original):
    u, v, extreme, rejected = SCREENS[label]
    modulus = lcm(*(4*abs(d) for d in [extreme, *rejected]))
    chains = {side: lift(original[side][:-1], r, modulus) for side,r in [('left',u),('right',v)]}
    p,q = (int(chain[-1]['prime']) for chain in chains.values())
    n = p*q
    rp,rq = prime_root(extreme,p),prime_root(extreme,q)
    root = (rp + p*((rq-rp)*pow(p,-1,q) % q)) % n
    record = dict(product=str(n), chains=chains)
    source = lean_source(record, include_signature=False,
                         generator_comment='Prescribed small sign classes from experiments/three_target_limits.py.')
    source = 'import PrimeFactors.ThreeRootTargets\n' + source.split('end PrimeFactors.Generated')[0]
    names=[]
    for d in rejected:
        index = len(names)
        name = f'reject{index}'
        if jacobi(d,u) == -1:
            s,r,divisor='left1024',u,'dvd_mul_right'
        elif jacobi(d,v) == -1:
            s,r,divisor='right1024',v,'dvd_mul_left'
        else:
            raise ArithmeticError('the target passes both signs')
        source += f'''private theorem {name} : ¬ IsSquare (({d} : ℤ) : ZMod controlProduct) := by
  apply ThreeRootTargets.reject (p := {s}) (a := {r})
  · change {s} ∣ left1024*right1024
    exact {divisor} ..
  · exact Nat.odd_iff.mpr (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · norm_num

'''
        names.append(name)
    ds = ','.join(map(str,rejected))
    source += f'''theorem sharp : ExactFactorization controlProduct [left1024,right1024] ∧
    2^1023 ≤ left1024 ∧ left1024 < 2^1024 ∧
    2^1023 ≤ right1024 ∧ right1024 < 2^1024 ∧ left1024 ≠ right1024 ∧
    2^2047 ≤ controlProduct ∧ controlProduct < 2^2048 ∧
    ({root} : ZMod controlProduct)^2 = {extreme} ∧
    ∀ d ∈ ([{ds}] : List ℤ), ¬ IsSquare (d : ZMod controlProduct) := by
  refine ⟨factorization, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, full_size.1, full_size.2, by decide +kernel, ?_⟩
  intro d hd
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hd
  rcases hd with {(' | '.join('rfl' for _ in names))}
  all_goals first {' '.join('| exact '+x for x in names)}
#print axioms sharp
end PrimeFactors.Generated
'''
    path = ROOT/'build'/f'ThreeTargetLimit{label.title()}.lean'
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(source)
    verify_file(path,'PrimeFactors.Generated.sharp')
    return dict(menu=label, residues=[u,v], modulus=modulus, n=str(n), primes=[str(p), str(q)],
                rejected=rejected, first_possible=extreme, root=str(root),
                theorem='PrimeFactors.Generated.sharp', source_sha256=sha256(path.read_bytes()).hexdigest())


if __name__ == '__main__':
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument('--write',action='store_true')
    args=cli.parse_args()
    original=json.loads((ROOT/'research/certified-control.json').read_text())['chains']
    data=[make(label,original) for label in SCREENS]
    if args.write:
        RECORD.write_text(json.dumps(data,indent=2)+'\n')
    else:
        if json.loads(RECORD.read_text()) != data:
            raise ValueError('the checked examples differ from the recorded data')
        print('Both full-size sharpness examples and their prime certificates verified.')
