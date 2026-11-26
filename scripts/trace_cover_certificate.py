"""Emit and kernel-check the public weighted-trace schedule and its exact lower bound."""

from argparse import ArgumentParser
from bisect import bisect_left
from fractions import Fraction
import json
from pathlib import Path
from tempfile import TemporaryDirectory

from experiments.trace_cover import envelope
from experiments.trace_cover_sparse import Ratios, read_certificate
from scripts.factor import verify_file


THEOREM = 'PrimeFactors.Generated.traceCoverOptimal'
_IMPORT = 'import PrimeFactors.TraceProgression\n'
_MARKER = '-- Begin generated trace-cover certificate\n'
_END = '#print axioms traceCoverOptimal\nend PrimeFactors.Generated\n'


def _nat(value):
    if type(value) is not int or value < 0:
        raise ValueError('expected a natural number in the trace-cover certificate')
    return str(value)


def _point(value):
    r = Fraction(value)
    return f'⟨{_nat(r.numerator)}, {_nat(r.denominator)}⟩'


def _list(items):
    return '[\n  ' + ',\n  '.join(items) + '\n]'


def _list_def(name, element_type, entries):
    """Keep the elaborator's individual list literals short on the larger controls."""
    entries = list(entries)
    if len(entries) <= 72:
        return f'private noncomputable def {name} : List {element_type} := {_list(entries)}\n'
    chunks, names = [], []
    for i in range(0, len(entries), 72):
        part = f'{name}Part{i//72}'
        names.append(part)
        chunks.append(_list_def(part, element_type, entries[i:i+72]))
    return ''.join(chunks) + f'private noncomputable def {name} : List {element_type} := ' + ' ++ '.join(names) + '\n'


def _tree_def(name, tree_type, leaves, split_at):
    nodes = []

    def branch(lo, hi):
        if hi == lo + 1:
            return f'(.leaf {leaves[lo]})'
        mid = (lo + hi) // 2
        expr = f'(.split {split_at(mid)} {branch(lo, mid)} {branch(mid, hi)})'
        if hi - lo <= 64:
            return expr
        node = f'{name}Node{len(nodes)}'
        nodes.append(f'private noncomputable def {node} : {tree_type} := {expr}\n')
        return node

    root = branch(0, len(leaves))
    return ''.join(nodes) + f'private noncomputable def {name} : {tree_type} := {root}\n'


def _sparse_witness(n, m, ordered_windows, prices):
    points = [x for x, _ in prices]
    if any(w <= 0 for _, w in prices) or points != sorted(set(points)):
        raise ValueError('sparse witness requires increasing ratios and positive prices')
    prefix = [0]
    for _, w in prices:
        prefix.append(prefix[-1] + w)
    ratios = Ratios(points)
    rows = []
    for window in ordered_windows:
        pivot = bisect_left(points, Fraction(window[0], window[1]))
        cap = prefix[-1]
        chain = []
        while cap:
            lo, hi = ratios.extent(n, window, m, pivot, cap-1)
            l, r = prefix[lo], prefix[hi]
            if r-l >= cap:
                raise ValueError('sparse lower certificate violates its claimed budget')
            chain.append(f'({l},{r})')
            cap = r-l
        slope = '⟨' + ', '.join(map(_nat, window)) + '⟩'
        rows.append('(' + slope + ', [' + ', '.join(chain) + '])')
    leaves = [_point(x) for x, _ in prices] or ['⟨1,1⟩']
    tree = _tree_def('traceTree', 'SparseTraceDual.Tree', leaves,
                     lambda i: f'{prefix[i]} {_point(points[i])}')
    # Each proof checks a bounded set of geometric boundaries. Combining the
    # established facts avoids retaining every arithmetic reduction at once.
    parts, checks = [], []
    for i in range(0, len(rows), 64):
        part, checked = f'traceRowsPart{i//64}', f'traceCheckedPart{i//64}'
        tree += _list_def(part, '(Slope × List (ℕ × ℕ))', rows[i:i+64])
        tree += (f'private theorem {checked} : SparseTraceDual.batchCheck traceInput traceBlock '
                 f'{prefix[-1]} traceTree {part} := by decide +kernel\n')
        parts.append(part)
        checks.append(checked)
    tree += 'private noncomputable def traceRows := ' + ' ++ '.join(parts) + '\n'
    tree += (f'private theorem traceChecked : SparseTraceDual.batchCheck traceInput traceBlock '
             f'{prefix[-1]} traceTree traceRows := by\n  simp only [traceRows, SparseTraceDual.batchCheck_append, '
             + ', '.join(checks) + ', Bool.and_self]\n')
    return tree


def _statement(n, k, m, result, right, sparse=False):
    left, right = Fraction(1), Fraction(right)
    if not 1 <= right <= 2:
        raise ValueError('expected an upper ratio in [1, 2]')
    windows, budgets = result['windows'], result['budgets']
    if len(windows) != len(budgets) or sum(budgets) != result['optimum']:
        raise ValueError('inconsistent trace-cover budget vector')
    cells = result.get('cells')
    if cells is None:
        cells, missing = envelope(n, windows, m, budgets, left, right)
        if missing:
            raise ValueError('incomplete trace-cover witness')
    previous = left
    for lo, hi, _ in cells:
        if lo != previous or hi < lo:
            raise ValueError('trace-cover segments must tile the requested interval')
        previous = hi
    if not cells or previous != right:
        raise ValueError('trace-cover witness ends at a different upper ratio')
    order = sorted(range(len(windows)), key=lambda i: (windows[i][1], windows[i][0]))
    ordered = [windows[i] for i in order]
    indices = {original: i for i, original in enumerate(order)}
    slopes = ['⟨' + ', '.join(map(_nat, row)) + '⟩' for row in ordered]
    cuts = _list_def('traceCuts', '(Point × ℕ)',
                     (f'({_point(hi)}, {indices[i]})' for _, hi, i in cells))
    if sparse:
        # The geometry follows cell order. A balanced tree indexes the rows
        # in canonical denominator order and also enumerates the full schedule.
        leaves = [f'({s}, {_nat(budgets[i])})' for s, i in zip(slopes, order)]
        declarations = _tree_def('traceIndex', 'SequentialTraceCover.RowTree', leaves, str)
        declarations += 'private noncomputable def traceSchedule := traceIndex.rows\n'
        declarations += 'private noncomputable def traceCatalogue := traceSchedule.map Prod.fst\n'
        declarations += cuts + _sparse_witness(n, m, ordered, result['prices'])
        upper = 'SequentialTraceCover.indexedCheck traceInput traceBlock ⟨1,1⟩ traceRight traceIndex traceCuts'
        continuous = 'SequentialTraceCover.indexed_real'
        rational = 'SequentialTraceCover.indexed_rational upper ⟨q,p⟩ hp lo hi'
        member = 'List.mem_map.mpr ⟨e,he,rfl⟩'
        lower = '''    have order : SparseTraceDual.ordered traceTree ⟨1,1⟩ traceRight := by decide +kernel
    have rows : traceRows.map Prod.fst = traceCatalogue := by decide +kernel
    exact SparseTraceDual.lower_of_batch traceChecked order (rows ▸ permitted) cover'''
    else:
        declarations = _list_def('traceCatalogue', 'Slope', slopes)
        declarations += _list_def('traceBudgets', 'ℕ', (_nat(budgets[i]) for i in order))
        declarations += 'private noncomputable def traceSchedule := traceCatalogue.zip traceBudgets\n'
        declarations += cuts
        member = '(List.of_mem_zip (show (e.1,e.2)∈traceCatalogue.zip traceBudgets from he)).1'
        upper = 'upperCheck traceInput traceBlock traceSchedule ⟨1,1⟩ traceRight traceCuts'
        continuous = 'upper_real'
        rational = 'upper_sound hp upper lo hi'
        declarations += _list_def('traceProbes', '(Point × ℕ)',
            (f'({_point(x)}, {_nat(w)})' for x, w in result['prices']))
        lower = '''    have solution := certified_minimum upper (catalogue:=traceCatalogue) (probes:=traceProbes)
      allowed (by decide +kernel) (by decide +kernel) (by decide +kernel)
    exact price ▸ solution.2.2 alt permitted cover'''
    return _MARKER + f'''namespace PrimeFactors.Generated
open TraceCoverCertificate

set_option maxHeartbeats 16000000
set_option maxRecDepth 16384

private abbrev traceInput : ℕ := {_nat(n)}
private abbrev traceBlock : ℕ := {_nat(m)}
private abbrev traceRight : Point := {_point(right)}
{declarations}
/-- The catalogue is canonical and the displayed block count is the exact
minimum for covering the closed ratio interval. Each eligible true factor
pair has a weighted trace at an actual label of this schedule. -/
theorem traceCoverOptimal :
    fullCatalogue traceInput {_nat(k)} traceCatalogue ∧
    cost traceSchedule = {_nat(result['optimum'])} ∧ admissible traceCatalogue traceSchedule ∧
    (∀ x : ℝ, (1:ℝ)≤x → x≤(traceRight.value:ℝ) → ∃ e∈traceSchedule,
      (traceInput:ℝ)*((e.1.a:ℝ)+e.1.b*x)^2 < (cutoff traceBlock e.1 e.2:ℝ)^2*x) ∧
    (∀ alternative, admissible traceCatalogue alternative →
      CoversRange traceInput traceBlock alternative ⟨1,1⟩ traceRight → {_nat(result['optimum'])}≤cost alternative) ∧
    (∀ p q : ℕ, 0<p → p*q=traceInput → p.Coprime 6 → p≤q → q*traceRight.den≤traceRight.num*p →
      ∃ e∈traceSchedule, ∃ j<traceBlock*e.2, e.1.start+e.1.step*j=e.1.a*p+e.1.b*q) := by
  have starts : traceCatalogue.all (validStart traceInput) := by decide +kernel
  have coords : traceCatalogue.map (fun s => (s.a,s.b)) = catalogueCoordinates {_nat(k)} := by decide +kernel
  have cat : fullCatalogue traceInput {_nat(k)} traceCatalogue := by
    simp only [fullCatalogue,starts,coords,decide_true,Bool.and_self]
  have member : ∀ e∈traceSchedule, e.1∈traceCatalogue := by
    intro e he; exact {member}
  have allowed : admissible traceCatalogue traceSchedule := by
    apply List.all_eq_true.mpr; intro e he
    exact List.any_eq_true.mpr ⟨e.1,member e he,by simp⟩
  have upper : {upper} := by decide +kernel
  have price : cost traceSchedule={_nat(result['optimum'])} := by decide +kernel
  refine ⟨cat,price,allowed,?_,?_,?_⟩
  · intro x lo hi
    exact {continuous} upper (by simpa [Point.value] using lo) hi
  · intro alt permitted cover
{lower}
  · intro p q hp product cop order top
    have lo : before ⟨1,1⟩ ⟨q,p⟩ := by simpa [before] using order
    have hi : before ⟨q,p⟩ traceRight := decide_eq_true top
    obtain ⟨e,he,covered⟩ := {rational}
    exact ⟨e,he,actual_index product cop (List.all_eq_true.mp starts e.1 (member e he)) covered⟩

#print axioms traceCoverOptimal
end PrimeFactors.Generated
'''


def check_schedule(n, k, m, result, right, proof, *, sparse=None):
    """Verify before publishing, preserving a factor certificate already at `proof`.

    `result` is the unmodified dictionary returned by either trace-cover solver.
    The certificate verifies its input, order, block size, interval and optimum
    without replaying optimization or using known factors.
    """
    proof = Path(proof)
    previous = proof.read_text() if proof.exists() else ''
    base, marked, section = previous.partition(_MARKER)
    suffix = ''
    if marked:
        _, end, suffix = section.partition(_END)
        if not end:
            raise ValueError('existing trace-cover section is incomplete')
    if _IMPORT not in base.splitlines(keepends=True):
        base = _IMPORT + base
    if sparse is None:
        dense_tests = len(result['windows']) * result['optimum'] * len(result['prices'])
        sparse = 'stats' in result or dense_tests > 1_000_000
    if sparse:
        for module in ('SparseTraceDual', 'SequentialTraceCover'):
            line = f'import PrimeFactors.{module}\n'
            if line not in base.splitlines(keepends=True):
                base = line + base
    source = base.rstrip() + '\n\n' + _statement(n, k, m, result, right, sparse) + suffix
    proof.parent.mkdir(parents=True, exist_ok=True)
    with TemporaryDirectory(dir=proof.parent) as work:
        candidate = Path(work) / 'CheckedTraceCover.lean'
        candidate.write_text(source)
        verify_file(candidate, THEOREM)
        candidate.replace(proof)
    return THEOREM


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('archive', type=Path, help='compact public schedule and weighted-probe JSON')
    parser.add_argument('proof', type=Path, help='destination Lean source')
    args = parser.parse_args()
    parameters = json.loads(args.archive.read_text())
    n, k, m = int(parameters['n']), parameters['k'], parameters['block']
    witness = read_certificate(args.archive, n, k, m)
    name = check_schedule(n, k, m, witness, Fraction(2), args.proof, sparse=True)
    print(f'{name} verified {witness["optimum"]} blocks in {args.proof}')
