"""Run the 34-root pruned search, then replay the comparisons separately."""
from math import gcd, isqrt
from time import perf_counter

from experiments.endpoint_pruned_weights import TABLE, compare, first, search, trace_list
from scripts.factor import verify_file


def strict_receipt(n, proof):
    arms = [(1,1,16), *TABLE[n%24]]
    declarations = []
    for a,b,count in arms:
        k = a*b
        start = first(n, k)
        traces = trace_list(n, a, b, start, count)
        roots = [isqrt(t*t-4*k*n) for t in traces]
        name = f'arm{k}'
        declarations.append(f"""
private abbrev {name}Start : ℕ := {start}

private noncomputable abbrev {name}Label (i : ℕ) := {name}Start +
  MarginalTraceWidth.offset (N%24) ({name}Start%24) {a} {b} i

private theorem {name}First : ceilSqrt (4*{k}*N)={name}Start := by
  apply le_antisymm (ceilSqrt_le_iff.mpr (by decide +kernel))
  by_contra! h
  have smaller := ceilSqrt_le_iff.mp (show ceilSqrt (4*{k}*N)≤{name}Start-1 by omega)
  exact (by decide +kernel : ¬4*{k}*N≤({name}Start-1)^2) smaller

private abbrev {name}Roots : List ℕ := {roots}

private theorem {name}Miss (i : Fin {count}) : ¬ InteriorBatchPopulation.properSquare N {k} ({name}Label i) := by
  have bracket : ∀ j : Fin {count},
      let d := {name}Roots[j.val]?.getD 0
      let m := ({name}Label j)^2-4*{k}*N
      d^2 < m ∧ m < (d+1)^2 := by decide +kernel
  exact EndpointPrunedWeights.bracket_miss (bracket i).1 (bracket i).2
""")
    conjunction = ' ∧ '.join(f'(∀ i : Fin {c}, ¬InteriorBatchPopulation.properSquare N {a*b} (arm{a*b}Label i))'
                             for a,b,c in arms)
    f = first(n,1)
    for hit,t in enumerate(trace_list(n,1,1,f,31)):
        disc = t*t-4*n
        root = isqrt(disc)
        if root*root == disc and 1 < gcd((t+root)//2,n) < n:
            break
    else:
        raise ValueError('The ordinary continuation has no split for this receipt')
    facts = ','.join(f'arm{a*b}Miss' for a,b,_ in arms)
    starts = ' ∧ '.join(f'ceilSqrt (4*{a*b}*N)=arm{a*b}Start' for a,b,_ in arms)
    start_proofs = ','.join(f'arm{a*b}First' for a,b,_ in arms)
    source = f"""import PrimeFactors.EndpointPrunedWeights

namespace PrimeFactors.Generated.EndpointPruning
set_option exponentiation.threshold 8192
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
private abbrev N : ℕ := {n}
{''.join(declarations)}
theorem verified : ({starts}) ∧ ({conjunction}) ∧
    (arm1Label {hit})^2=4*N+{root}^2 ∧
    1<N.gcd ((arm1Label {hit}+{root})/2) ∧ N.gcd ((arm1Label {hit}+{root})/2)<N := by
  exact ⟨⟨{start_proofs}⟩,⟨{facts}⟩,by decide +kernel,by decide +kernel,by decide +kernel⟩

#print axioms verified
end PrimeFactors.Generated.EndpointPruning
"""
    receipt = proof.with_name(proof.stem+'-traces.lean')
    receipt.write_text(source)
    start = perf_counter()
    verify_file(receipt, 'PrimeFactors.Generated.EndpointPruning.verified')
    return dict(proof=f'proofs/{receipt.name}', ordinary_ordinal=hit+1, seconds=perf_counter()-start)


def endpoint_pruning_case(case, proof, agree, certify_split):
    n = int(case['n'])
    bits = case['prime_bits']
    start = perf_counter()
    work = search(n, bits)
    elapsed = perf_counter()-start
    diagnostic_start = perf_counter()
    comparison = compare(n, bits, True)
    if comparison['new_found'] != work['new_found']:
        raise ValueError(f"Comparison replay disagrees on {case['id']}")
    work.update(old_found=comparison['old_found'], ordinary_found=comparison['ordinary_found'],
                bit_width_only_found=comparison['bit_width_only_found'],
                bit_width_only_extra=comparison['bit_width_only_extra'],
                diagnostic_roots=51, diagnostic_seconds=perf_counter()-diagnostic_start)
    agree(dict(id=case['id'], **case['checks']), work, case['checks'])
    factor = int(work['new_found'][0]) if work['new_found'] else None
    result = certify_split(case, proof, factor, elapsed, 'endpoint_pruning', work)
    if case.get('verify_traces'):
        result['endpoint_pruning_receipt'] = strict_receipt(n, proof)
    return result
