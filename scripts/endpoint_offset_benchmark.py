"""Predict the product of two distances below the public bit-width endpoint."""
from math import gcd, isqrt
from time import perf_counter

from scripts.factor import verify_file


def search(n):
    if n <= 0:
        raise ValueError('expected a positive product')
    bits = n.bit_length()
    endpoint = 1 << ((bits+1)//2)
    stride = gcd(24, 2*(1+n))
    residue = ((endpoint-1)*(endpoint-n)) % (endpoint*stride)
    offset_sum = (endpoint*endpoint+residue-n)//endpoint
    discriminant = offset_sum*offset_sum-4*residue
    root = isqrt(max(discriminant, 0))
    p = max(0, endpoint-(offset_sum+root)//2)
    q = max(0, endpoint-max(0,offset_sum-root)//2)
    accepted = (1 < p <= q <= endpoint and p*q == n and
                (endpoint-p)*(endpoint-q) == residue)
    work = dict(endpoint=str(endpoint), stride=stride, residue=str(residue),
                offset_sum=str(offset_sum), discriminant=str(discriminant), root=str(root),
                predicted_products=1, search_roots=1, candidates=[str(p),str(q)],
                leading_ones=bits-(((1 << bits)-1)^n).bit_length(), accepted=accepted)
    return (p if accepted else None), work


def ordinary_distance(n, p, q):
    """One diagnostic root locates both ordinary starts without scanning the interval."""
    start = 1+isqrt(4*n-1)
    trace = p+q
    midpoint_start = (start+1)//2
    return dict(roots=1, first_trace=str(start), trace_distance=str(trace-start),
                first_midpoint=str(midpoint_start),
                midpoint_distance=str(trace//2-midpoint_start) if trace%2 == 0 else None)


def receipt(n, work, path):
    bits = n.bit_length()
    C, r, s, d = (int(work[k]) for k in ('endpoint','residue','offset_sum','root'))
    p,q = map(int,work['candidates'])
    result = 'some (P,Q)' if work['accepted'] else 'none'
    guard = '1<p ∧ p≤q ∧ q≤c ∧ p*q=n ∧ (c-p)*(c-q)=r'
    condition = f'({guard})' if work['accepted'] else f'¬({guard})'
    branch = 'if_pos good' if work['accepted'] else 'if_neg good'
    generic_result = 'some (p,q)' if work['accepted'] else 'none'
    prefix = work['leading_ones']
    leading_cap = f'N<2^{bits}-2^({bits}-{prefix}-1)' if prefix<bits else f'N=2^{bits}-1'
    diagnostic_type = diagnostic_proof = ''
    if 'ordinary' in work:
        ordinary = work['ordinary']
        f = int(ordinary['first_trace'])
        diagnostic_type = (f'({f}-1)^2<4*N ∧ 4*N≤{f}^2 ∧ '
                           f'P+Q={f}+{ordinary["trace_distance"]} ∧ ')
        diagnostic_proof = 'by decide +kernel,by decide +kernel,by decide +kernel,'
        if ordinary['midpoint_distance'] is not None:
            first_midpoint = int(ordinary['first_midpoint'])
            diagnostic_type += (f'({first_midpoint}-1)^2<N ∧ N≤{first_midpoint}^2 ∧ '
                                f'P+Q=2*({first_midpoint}+{ordinary["midpoint_distance"]}) ∧ ')
            diagnostic_proof += 'by decide +kernel,by decide +kernel,by decide +kernel,'
    src = f"""import PrimeFactors.EndpointOffsetProduct

namespace PrimeFactors.Generated.EndpointOffset
set_option exponentiation.threshold 8192
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000

private abbrev N : ℕ := {n}
private abbrev C : ℕ := {C}
private abbrev R : ℕ := {r}
private abbrev S : ℕ := {s}
private abbrev D : ℕ := {d}
private abbrev P : ℕ := {p}
private abbrev Q : ℕ := {q}

private theorem residue_ok : EndpointOffsetProduct.residue C N=R := by decide +kernel

private theorem sum_ok : (C^2+R-N)/C=S := by decide +kernel

private theorem root_ok : (S^2-4*R).sqrt=D := by
  have lo : D*D≤S^2-4*R := by decide +kernel
  have hi : S^2-4*R<(D+1)*(D+1) := by decide +kernel
  have lower := Nat.le_sqrt.mpr lo
  have upper := Nat.sqrt_lt.mpr hi
  omega

private theorem pair_ok : EndpointOffsetProduct.decode C N=(P,Q) := by
  simp only [EndpointOffsetProduct.decode,residue_ok,sum_ok,root_ok]
  all_goals decide +kernel

private theorem probe_from_pair {{c n p q r : ℕ}} (pair : EndpointOffsetProduct.decode c n=(p,q))
    (rem : EndpointOffsetProduct.residue c n=r) (good : {condition}) :
    EndpointOffsetProduct.probe c n={generic_result} := by
  unfold EndpointOffsetProduct.probe
  rw [pair]
  dsimp only
  rw [rem,{branch}]

private theorem probe_ok : EndpointOffsetProduct.probe C N={result} :=
  probe_from_pair pair_ok residue_ok (by decide +kernel)

theorem verified :
    2^({bits}-1)≤N ∧ N<2^{bits} ∧ C=2^(({bits}+1)/2) ∧
    2^{bits}-2^({bits}-{prefix})≤N ∧ {leading_cap} ∧
    weightedStride N 1 1={work['stride']} ∧ EndpointOffsetProduct.residue C N=R ∧
    (C^2+R-N)/C=S ∧ (S:ℤ)^2-4*R=({work['discriminant']}:ℤ) ∧
    (S^2-4*R).sqrt=D ∧ EndpointOffsetProduct.decode C N=(P,Q) ∧
    {diagnostic_type}EndpointOffsetProduct.probe C N={result} := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,
    by decide +kernel,residue_ok,sum_ok,by decide +kernel,root_ok,pair_ok,{diagnostic_proof}probe_ok⟩

#print axioms verified
end PrimeFactors.Generated.EndpointOffset
"""
    path.write_text(src)
    start = perf_counter()
    verify_file(path, 'PrimeFactors.Generated.EndpointOffset.verified')
    return dict(proof=f'proofs/{path.name}', seconds=perf_counter()-start)


def endpoint_offset_case(case, proof, agree, certify_split):
    n = int(case['n'])
    start = perf_counter()
    factor, work = search(n)
    elapsed = perf_counter()-start
    if factor is not None:
        start = perf_counter()
        work['ordinary'] = ordinary_distance(n, factor, n//factor)
        work['ordinary_seconds'] = perf_counter()-start
    agree(dict(id=case['id'], **case['checks']), work, case['checks'])
    result = certify_split(case, proof, factor, elapsed, 'endpoint_offset', work)
    result['endpoint_offset_receipt'] = receipt(n, work, proof.with_name(proof.stem+'-offset.lean'))
    return result
