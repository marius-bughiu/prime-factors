"""Certify a union of divisor intervals against one set of weighted trace checks."""

from math import isqrt
from time import perf_counter

from scripts.factor import verify_file


THEOREM = "PrimeFactors.Generated.sharedTraceExclusion"


def _pieces(lower, upper, rows):
    """Cover this merged interval with consecutive pieces of witnessed orientations."""
    pieces = []
    cursor = lower
    while cursor <= upper:
        choices = [(end, a) for a, start, end in rows if start <= cursor <= end]
        if not choices:
            raise ValueError("Claimed interval has a gap in its weighted rows")
        end, a = max(choices)
        end = min(end, upper)
        pieces.append((a, cursor, end))
        cursor = end + 1
    return pieces


def shared_interval_source(n, work):
    k, first, count = (int(work[key]) for key in ("k", "first_trace", "cap"))
    if n <= 0 or k <= 0 or count <= 0:
        raise ValueError("Expected a positive input, multiplier and budget")
    if first != isqrt(4*k*n - 1) + 1 or int(work["first_omitted"]) != first + count:
        raise ValueError("Trace endpoints disagree with the public product and budget")

    shared = work["shared"]
    intervals = [(int(lo), int(hi)) for lo, hi in shared["intervals"]]
    rows = [tuple(map(int, row)) for row in shared["interval_rows"]]
    if not intervals or any(lo <= 0 or lo > hi for lo, hi in intervals):
        raise ValueError("Expected at least one nonempty positive interval")
    if any(hi + 1 >= lo for (_, hi), (lo, _) in zip(intervals, intervals[1:])):
        raise ValueError("Expected disjoint merged intervals in increasing order")
    positions = sum(hi - lo + 1 for lo, hi in intervals)
    if positions != int(shared["positions"]):
        raise ValueError("The reported position count differs from the interval union")
    if any(a <= 0 or k % a or lo > hi for a, lo, hi in rows):
        raise ValueError("Invalid oriented multiplier row")
    if any(not any(l <= lo <= hi <= u for l, u in intervals) for _, lo, hi in rows):
        raise ValueError("A measured row extends outside the reported interval union")
    roots = []
    for i in range(count):
        delta = (first + i)**2 - 4*k*n
        r = isqrt(delta)
        if r*r == delta:
            raise ValueError("A square requires a factor or an oriented compatibility check")
        roots.append(r)

    source = [
        "import PrimeFactors.WeightedTracePrefix",
        "",
        "namespace PrimeFactors.Generated",
        "open WeightedTracePrefix",
        "set_option maxRecDepth 16384",
        "set_option maxHeartbeats 2000000",
        "",
        f"def sharedInput : ℕ := {n}",
        f"private abbrev multiplier : ℕ := {k}",
        f"private abbrev first : ℕ := {first}",
        f"private abbrev count : ℕ := {count}",
        "private def floors : List ℕ := [" + ",\n  ".join(map(str, roots)) + "]",
        "",
        "private theorem noSquares : ∀ i<count, ∀ v : ℕ,",
        "    (first+i)^2 ≠ 4*multiplier*sharedInput+v^2 := by",
        "  intro i hi v",
        "  exact brackets_sound (target:=4*multiplier*sharedInput) (first:=first)",
        "    (roots:=floors) (by decide +kernel) (i:=i) hi v",
        "",
        "private theorem minimumTrace : (first-1)^2 < 4*multiplier*sharedInput := by",
        "  decide +kernel",
        "",
        "private abbrev Clear (l u : ℕ) := ∀ x, l≤x → x≤u → ¬x∣sharedInput",
        "",
        "private theorem clearOf {a b l u : ℕ} (weights : a*b=multiplier)",
        "    (ap : 0<a) (lp : 0<l) (left : a*l^2+b*sharedInput<(first+count)*l)",
        "    (right : a*u^2+b*sharedInput<(first+count)*u) : Clear l u :=",
        "  shared_excludes noSquares minimumTrace weights ap lp left right",
        "",
    ]
    for index, (lower, upper) in enumerate(intervals):
        source.extend([
            f"private abbrev lo{index} : ℕ := {lower}",
            f"private abbrev hi{index} : ℕ := {upper}",
            f"private theorem interval{index} : Clear lo{index} hi{index} := by",
        ])
        pieces = _pieces(lower, upper, rows)
        for offset, (a, lo, hi) in enumerate(pieces):
            b = k // a
            for x in (lo, hi):
                if a*x*x + b*n >= (first + count)*x:
                    raise ValueError("Measured endpoints exceed the open trace bound")
            indent = "  "
            if offset < len(pieces) - 1:
                source.append(f"  apply join (split := {hi}) (next := {hi+1}) (by decide +kernel)")
                indent += "· "
            source.append(
                f"{indent}apply clearOf (a := {a}) (b := {b}) <;> decide +kernel"
            )
        source.append("")

    pairs = ", ".join(f"(lo{i}, hi{i})" for i in range(len(intervals)))
    source.extend([
        f"def sharedIntervals : List (ℕ × ℕ) := [{pairs}]",
        "",
        "/-- Every natural number in the reported union is excluded as a divisor. -/",
        "theorem sharedTraceExclusion (d : ℕ) (inside : ∃ row ∈ sharedIntervals,",
        "    row.1 ≤ d ∧ d ≤ row.2) : ¬ d ∣ sharedInput := by",
        "  obtain ⟨row,hr,lo,hi⟩ := inside",
        "  simp only [sharedIntervals,List.mem_cons,List.not_mem_nil,or_false] at hr",
        "  rcases hr with " + " | ".join("rfl" for _ in intervals),
    ])
    prefix = "  · " if len(intervals) > 1 else "  "
    source.extend(f"{prefix}exact interval{i} d lo hi" for i in range(len(intervals)))
    source.extend(["", "#print axioms sharedTraceExclusion", "end PrimeFactors.Generated", ""])
    return "\n".join(source)


def check_shared_interval(n, work, proof):
    proof.write_text(shared_interval_source(n, work))
    started = perf_counter()
    verify_file(proof, THEOREM)
    shared = work["shared"]
    return {
        "method": "shared multiplier interval union",
        "interval_count": len(shared["intervals"]),
        "positions": str(shared["positions"]),
        "proof": f"proofs/{proof.name}",
        "verification_seconds": perf_counter() - started,
    }
