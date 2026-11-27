"""Benchmark the reduced predecessor sweep and replay its numerical gcd in Lean."""
from time import perf_counter

from experiments.reduced_smooth_readout import blocks, ordinary_sweep, search
from scripts.factor import verify_file


def check_sweep(n, work, divisor, proof):
    """Replay the public block list, modular powers, identity tests and actual readout."""
    base = work['accepted_base']
    source = work['source']
    if base is None and source != 'base gcd':
        return None
    path = proof.with_name(f'{proof.stem}-sweep.lean')
    lines = ['import PrimeFactors.ReducedSmoothReadout', 'import Mathlib.Tactic.ReduceModChar',
             'set_option exponentiation.threshold 8192', 'set_option maxRecDepth 16384',
             'set_option maxHeartbeats 3000000', 'namespace PrimeFactors.Generated.ReducedSmooth',
             'open ReducedSmoothReadout', f'private abbrev n : ℕ := {n}']
    if base is None:
        lines.append(f"theorem checked : Nat.gcd {work['bases'] + 1} n = {divisor} := by decide +kernel")
    else:
        bound, bits = work['bound'], work['factor_bits']
        schedule = list(blocks(bound, bits))
        exponents = ','.join(str(e) for _, e in schedule)
        primes = ','.join(str(p) for p, _ in schedule)
        residue = pow(base, n-1, n)
        lines += [
            f'private theorem primes : (List.range ({bound}+1)).filter (fun r => decide (r.Prime ∧ r ≤ 2^{bits}-1)) = [{primes}] := by decide +kernel',
        ]
        logs = []
        powers = []
        for prime, power in schedule:
            exponent, remaining = 0, power
            while remaining > 1:
                exponent, remaining = exponent + 1, remaining // prime
            lines.append(f'private theorem log{prime} : Nat.log {prime} (2^{bits}-1) = {exponent} := Nat.log_eq_of_pow_le_of_lt_pow (by decide +kernel) (by decide +kernel)')
            logs.append(f'log{prime}')
            powers.append(f'{prime}^{exponent}')
        symbolic = ','.join(f'{prime}^Nat.log {prime} (2^{bits}-1)' for prime, _ in schedule)
        lines += [
            f'private theorem plan : schedule {bound} (2^{bits}-1) = [{exponents}] := calc',
            f'  _ = [{symbolic}] := by simp only [schedule, primes, List.map_cons, List.map_nil]']
        if logs:
            lines.append(f"  _ = [{','.join(powers)}] := by rw [{', '.join(logs)}]")
        lines += [
            f'  _ = [{exponents}] := by decide +kernel',
            f'private theorem start : ({base} : ZMod n)^(n-1) = {residue} := by reduce_mod_char',
            f'private theorem accepted : ({residue} : ZMod n) ≠ 1 := by decide +kernel',
        ]
        checkpoints = []
        for index, (_, exponent) in enumerate(schedule):
            previous, residue = residue, pow(residue, exponent, n)
            lines.append(f'private theorem step{index} : ({previous} : ZMod n)^{exponent} = {residue} := by reduce_mod_char')
            follow = '[' + ','.join(str(e) for _, e in schedule[index+1:]) + ']'
            if residue == 1:
                checkpoints.append(f'(identity_step {follow} step{index})')
                residue = previous
                break
            lines.append(f'private theorem live{index} : ({residue} : ZMod n) ≠ 1 := by decide +kernel')
            checkpoints.append(f'(live_step {follow} step{index} live{index})')
        # Separate lemmas keep kernel reductions shallow at the 2,048-bit modulus.
        scan = 'rfl'
        for check in reversed(checkpoints):
            scan = f'({check}.trans {scan})'
        lines += [
            f'private theorem scan : readout ({pow(base,n-1,n)} : ZMod n) [{exponents}] = {residue} := {scan}',
            f'private theorem outcome : Nat.gcd (({residue} : ZMod n).val-1) n = {divisor or 1} := by decide +kernel',
            f'theorem checked : Nat.Coprime {base} n ∧ ({base} : ZMod n)^(n-1) ≠ 1 ∧',
            f'    Nat.gcd ((readout (({base} : ZMod n)^(n-1)) (schedule {bound} (2^{bits}-1))).val-1) n = {divisor or 1} :=',
            '  ⟨by decide +kernel, fun h => accepted (start.symm.trans h),',
            '    (congrArg (fun z : ZMod n => Nat.gcd (z.val-1) n) ((congrArg₂ readout start plan).trans scan)).trans outcome⟩']
    lines += ['#print axioms checked', 'end PrimeFactors.Generated.ReducedSmooth']
    path.write_text('\n'.join(lines) + '\n')
    start = perf_counter()
    verify_file(path, 'PrimeFactors.Generated.ReducedSmooth.checked')
    return dict(proof=f'proofs/{path.name}', seconds=perf_counter()-start)


def reduced_smooth_case(case, proof, agree, certify_split):
    n = int(case['n'])
    start = perf_counter()
    divisor, work = search(n, case['bound'], case['factor_bits'], case['base_limit'])
    elapsed = perf_counter()-start
    agree(dict(id=case['id'], **case['checks']), work, case['checks'])
    work['seconds'] = elapsed
    if work['accepted_base'] is not None:
        start = perf_counter()
        other, baseline = ordinary_sweep(n, work['accepted_base'], case['bound'], case['factor_bits'])
        baseline.update(divisor=str(other) if other is not None else None, seconds=perf_counter()-start)
        agree(dict(id=case['id'], **case['ordinary']), baseline, case['ordinary'])
        work['ordinary'] = baseline
    result = certify_split(case, proof, divisor, elapsed, 'reduced_smooth', work)
    receipt = check_sweep(n, work, divisor, proof)
    if receipt:
        result['reduced_smooth_receipt'] = receipt
    return result
