"""Benchmark shared powers against two full-exponent controls at identical coverage."""
from math import isqrt
from time import perf_counter

from experiments.shared_smooth_powers import compare, schedule
from scripts.factor import verify_file


def check_exhaustion(n, bound, bits, base, path):
    """Replay the full public exponent; gcd 1 excludes both smooth local orders."""
    plan = schedule(bound,bits)
    lines = ['import PrimeFactors.SharedSmoothPowers', 'import Mathlib.Tactic.ReduceModChar',
             'set_option Elab.async false', 'set_option exponentiation.threshold 8192', 'set_option maxHeartbeats 4000000',
             'set_option maxRecDepth 16384', 'namespace PrimeFactors.Generated.SharedSmooth',
             'open SharedSmoothPowers ReducedSmoothReadout', f'private abbrev n : ℕ := {n}',
             f'private abbrev cap : ℕ := 2^{bits}-1',
             'private noncomputable def block (p : ℕ) : ℕ := p^(Nat.log p cap)']
    residue = pow(base,n-1,n)
    lines += [f'private abbrev z0 : ZMod n := {residue}',
              f'private theorem start : ({base} : ZMod n)^(n-1) = z0 := by reduce_mod_char',
              f'private def tail{len(plan)} : List ℕ := []']
    for i in reversed(range(len(plan))):
        prime = plan[i][0]
        lines.append(f'private def tail{i} : List ℕ := {prime} :: tail{i+1}')
    # Small independent ranges avoid repeatedly reducing a long kernel List.filter.
    lines += [f'private noncomputable def keep (r : ℕ) := trialPrime {isqrt(bound)} r && decide (r ≤ cap)',
              'private theorem join {s m k : ℕ} {xs ys : List ℕ}',
              "    (a : (List.range' s m).filter keep = xs) (b : (List.range' (s+m) k).filter keep = ys) :",
              "    (List.range' s (m+k)).filter keep = xs++ys := by",
              "  rw [← List.range'_append_1, List.filter_append, a, b]",
              f"private theorem span{bound+1} : (List.range' {bound+1} 0).filter keep = tail{len(plan)} := rfl"]
    indexed = [prime for prime,_,_,_ in plan]
    for lo in reversed(range(0,bound+1,16)):
        hi = min(bound+1,lo+16)
        entries = [r for r in indexed if lo <= r < hi]
        offset = sum(r < lo for r in indexed)
        listed = ','.join(map(str,entries))
        lines += [f"private theorem chunk{lo} : (List.range' {lo} {hi-lo}).filter keep = [{listed}] := by decide +kernel",
                  f"private theorem span{lo} : (List.range' {lo} {bound+1-lo}).filter keep = tail{offset} := join chunk{lo} span{hi}"]
    lines += [f'private theorem primes : (List.range ({bound}+1)).filter keep = tail0 :=',
              "  (congrArg (List.filter keep) List.range_eq_range').trans span0"]
    for i,(prime,_,_,high) in enumerate(plan):
        k, power = 0, high
        while power > 1:
            k, power = k+1, power//prime
        residue = pow(residue,high,n)
        lines += [f'private abbrev z{i+1} : ZMod n := {residue}',
                  f'private theorem log{i} : Nat.log {prime} cap = {k} := Nat.log_eq_of_pow_le_of_lt_pow (by decide +kernel) (by decide +kernel)',
                  f'private theorem e{i} : block {prime} = {high} := (congrArg (fun t : ℕ => {prime}^t) log{i}).trans (by decide +kernel)',
                  f'private theorem s{i} : z{i}^(block {prime}) = z{i+1} := (congrArg (fun t : ℕ => z{i}^t) e{i}).trans (by reduce_mod_char)']
    end = len(plan)
    lines += [f'private theorem f{end} : z{end}^(tail{end}.map block).prod = z{end} := pow_one _']
    for i in reversed(range(end)):
        lines.append(f'private theorem f{i} : z{i}^(tail{i}.map block).prod = z{end} := (pow_cons s{i} (tail{i+1}.map block)).trans f{i+1}')
    lines += [f'private theorem plan : schedule {bound} cap = tail0.map block := by',
              '  unfold schedule',
              '  have eqn : (fun r : ℕ => decide (r.Prime ∧ r ≤ cap)) = keep := by',
              '    funext r; by_cases h : r.Prime <;> simp [keep, trialPrime_eq, h]',
              '  rw [eqn]; exact congrArg (List.map block) primes',
              f'private theorem last : Nat.gcd (z{end}.val-1) n = 1 := by decide +kernel',
              f'theorem checked : Nat.Coprime {base} n ∧ ({base} : ZMod n)^(n-1) ≠ 1 ∧',
              f'    Nat.gcd (((({base} : ZMod n)^(n-1))^(schedule {bound} cap).prod).val-1) n = 1 :=',
              '  ⟨by decide +kernel, fun h => (show z0 ≠ 1 from by decide +kernel) (start.symm.trans h),',
              '    (congrArg (fun z : ZMod n => Nat.gcd (z.val-1) n)',
              '      ((congrArg₂ (fun (z : ZMod n) (es : List ℕ) => z^es.prod) start plan).trans f0)).trans last⟩',
              f'theorem excludes {{p q : ℕ}} (hp : p.Prime) (hq : q.Prime) (diff : p ≠ q) (product : n = p*q)',
              '    (pfit : p-1 ≤ cap) (qfit : q-1 ≤ cap) :',
              f'    (∃ l : ℕ, l.Prime ∧ l ∣ (p-1)/(p-1).gcd (q-1) ∧ {bound} < l) ∧',
              f'    (∃ l : ℕ, l.Prime ∧ l ∣ (q-1)/(p-1).gcd (q-1) ∧ {bound} < l) := by',
              '  letI : NeZero (p*q) := ⟨mul_ne_zero hp.ne_zero hq.ne_zero⟩',
              '  have evidence := checked',
              '  rw [product] at evidence',
              '  exact certified_exclusion hp hq diff evidence.1 evidence.2.1 pfit qfit evidence.2.2',
              '#print axioms excludes', 'end PrimeFactors.Generated.SharedSmooth']
    path.write_text('\n'.join(lines) + '\n')
    start = perf_counter()
    verify_file(path,'PrimeFactors.Generated.SharedSmooth.excludes')
    return dict(proof=f'proofs/{path.name}', seconds=perf_counter()-start)


def shared_smooth_case(case, proof, agree, certify_split):
    n = int(case['n'])
    divisor, work = compare(n,case['bound'],case['factor_bits'],case['base_limit'])
    agree(dict(id=case['id'],**case['checks']),work,case['checks'])
    for mode in ('checkpoint','fused'):
        if mode in work:
            agree(dict(id=case['id'],**case[mode]),work[mode],case[mode])
    result = certify_split(case,proof,divisor,work['setup']['seconds']+work['seconds'],
                           'shared_smooth',work)
    if case.get('check_exhaustion'):
        if divisor is not None or work['outcome'] != 'exhausted':
            raise ValueError('expected a completed sweep without a factor')
        path = proof.with_name(f'{proof.stem}-exclusion.lean')
        result['shared_smooth_receipt'] = check_exhaustion(
            n,case['bound'],case['factor_bits'],work['accepted_base'],path)
    return result
