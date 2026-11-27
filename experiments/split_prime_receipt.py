"""Kernel-check the two large sign panels and round bounds for their actual prime sets."""
from hashlib import sha256
import json
from pathlib import Path

from experiments.split_prime_panel import RESULTS, cases, full_panel
from scripts.factor import verify_file


OUTPUT = Path(__file__).resolve().parents[1] / 'build/split-prime-panel'
THEOREM = 'PrimeFactors.Generated.SplitPrimeReceipt.checked'


def render(row, panel):
    digest = sha256(''.join(f'{d},{a}\n' for d,a in panel).encode('ascii')).hexdigest()
    if digest != row['witnesses_sha256'] or len(panel) != row['count']:
        raise ValueError('replayed roots differ from the recorded panel')
    lines = [
        'import PrimeFactors.SplitPrimeBudget',
        'namespace PrimeFactors.Generated.SplitPrimeReceipt',
        'open DivisorSignPanel',
        'set_option maxRecDepth 65536',
        'set_option maxHeartbeats 4000000',
        'set_option exponentiation.threshold 2048',
        f'private abbrev n : ℕ := {int(row["n"])}',
        f'private abbrev lo : ℕ := {int(row["lower"])}',
        f'private abbrev hi : ℕ := {int(row["upper"])}',
        'private abbrev B : ℕ := 2^1024-1',
    ]
    # Short chunks keep the parser stack small. Every entry is checked by the kernel.
    chunks = []
    for start in range(0,len(panel),16):
        name = f'chunk{start//16}'
        chunks.append(name)
        pairs = ',\n'.join(f'({d}, {a})' for d,a in panel[start:start+16])
        lines.append(f'private def {name} : List Entry := [\n{pairs}]')
    lines.extend([
        'private def entries : List Entry := ' + ' ++ '.join(chunks),
        'private theorem ok : check n lo 1 entries = true := by decide +kernel',
        'private theorem low : (n-1)/B+1 = lo := by decide +kernel',
        'private theorem high : n.sqrt = hi :=',
        "  le_antisymm (Nat.lt_succ_iff.mp (Nat.sqrt_lt'.mpr (by decide +kernel)))",
        "    (Nat.le_sqrt'.mpr (by decide +kernel))",
    ])
    bounds = []
    for band in row['prime_counts']:
        k = band['k']
        hits = f'(primes lo hi (entries.take {k})).card'
        name = f'band{k}'
        if row['interval_error_log2'] != 538:
            raise ValueError('the proof uses the published normalized error budget of 2^538')
        statement = (f'∀ ψ : ℕ → ℝ, SplitPrimeBudget.EndpointBudget {k} lo hi (entries.take {k}) ψ → '
                     f'{int(band["lower"])} ≤ {hits} ∧ {hits} ≤ {int(band["upper"])}')
        lines.append(f'private theorem {name} : {statement} := by\n'
                     '  intro ψ analytic\n'
                     '  have h := SplitPrimeBudget.weightedBounds (by decide +kernel) (by decide +kernel)\n'
                     '    (by decide +kernel) (by decide +kernel) analytic\n'
                     '  exact rounded h (by decide +kernel) (by decide +kernel)')
        bounds.append((name, statement))
    lines.extend([
        'theorem checked : entries.length = 512 ∧',
        '    entries.Pairwise (fun e f => e.1.Coprime f.1) ∧',
        '    (∀ e ∈ entries, e.1 % 4 = 3 ∧ e.1 < lo ∧ n.Coprime e.1 ∧ n ∣ e.2^2+e.1) ∧',
        '    ((2:ℕ)^1023 ≤ lo ∧ hi < 2^1024 ∧ 2^1020 ≤ hi-lo+1) ∧',
        '    (∀ p q : ℕ, n = p*q → p.Prime → 2<p → p≤q → q≤B → p ∈ primes lo hi entries) ∧',
        '    ' + ' ∧\n    '.join(f'({s})' for _,s in bounds) + ' := by',
        '  have data := properties entries 1 ok',
        '  refine ⟨by decide +kernel, data.2, ?_, by decide +kernel, ?_, '
        + ', '.join(name for name,_ in bounds) + '⟩',
        '  · intro e he',
        '    obtain ⟨a,b,c,d,_⟩ := data.1 e he',
        '    exact ⟨a,b,c,d⟩',
        '  · intro p q eq prime large ordered bounded',
        '    simpa only [low,high] using smaller_prime_mem entries ok eq prime',
        '      (prime.odd_of_ne_two (by omega)) ordered bounded',
        '#print axioms checked',
        'end PrimeFactors.Generated.SplitPrimeReceipt',
    ])
    return '\n'.join(lines)+'\n'


def main():
    records = json.loads(RESULTS.read_text())
    public = {case['id']: int(case['n']) for case in cases()}
    if len(records) != 2 or {r['id'] for r in records} != set(public):
        raise ValueError('expected both public comparison products')
    OUTPUT.mkdir(parents=True, exist_ok=True)
    for row in records:
        n = public[row['id']]
        if int(row['n']) != n:
            raise ValueError('recorded product differs from the public fixture')
        path = OUTPUT / (row['id']+'.lean')
        path.write_text(render(row, full_panel(n)))
        verify_file(path, THEOREM)
        print(row['id'], '512 roots and conditional prime counts verified', flush=True)


if __name__ == '__main__':
    main()
