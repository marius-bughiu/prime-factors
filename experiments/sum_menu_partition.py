"""Partition complete CRT menus under a cap on stored right-table positions."""

from math import prod


def prefix_sizes(sizes, visits):
    """Number of choices needed per DFS layer for its first (or last) visits leaves."""
    if visits == 0:
        return [0] * len(sizes)
    suffix = 1
    needed = [0] * len(sizes)
    for i in range(len(sizes)-1, -1, -1):
        needed[i] = min(sizes[i], (visits+suffix-1)//suffix)
        suffix = min(visits, suffix*sizes[i])
    return needed


def partition(halves, lower, cap, folded, budget):
    """Maximize raw right choices among whole-modulus assignments.

    A state stores (raw choices, sign-fixed choices) and one witnessing subset.
    Try divisors of the theoretical maximum first. A complete second pass
    certifies a smaller optimum. A bounded pass always returns a feasible
    incumbent when cap >= 1; the empty right half costs one position.
    """
    if min(cap, budget) < 0:
        raise ValueError('negative partition budget or storage cap')
    groups = sorted(halves[0]+halves[1], key=lambda group: group[0])
    sizes = [len(values) for _, values in groups]
    fixed = [int((-lower) % m in values) + int(m%2 == 0 and (m//2-lower) % m in values)
             for m, values in groups]
    total = prod(sizes)
    limit = min(total, (2 if folded else 1)*cap)
    incumbent = (1, 1, 0)  # raw count, fixed count, bit mask
    transitions = 0
    peak_states = 0
    seeds_tested = 0

    def fits(raw, signs):
        return raw+signs <= 2*cap if folded else raw <= cap

    def record(raw, signs, mask):
        nonlocal incumbent
        if fits(raw, signs) and (raw, -signs) > (incumbent[0], -incumbent[1]):
            incumbent = raw, signs, mask

    # A single descending packing pass remains available at zero DP budget.
    # Replaying the two supplied greedy halves also preserves any feasible
    # incumbent of the previous scheduling rule.
    index = {m: i for i, (m, _) in enumerate(groups)}
    for half in halves:
        indices = [index[m] for m, _ in half]
        record(prod(sizes[i] for i in indices), prod(fixed[i] for i in indices),
               sum(1 << i for i in indices))
        seeds_tested += 1
    raw, signs, mask = 1, 1, 0
    for i in sorted(range(len(groups)), key=lambda j: -sizes[j]):
        seeds_tested += 1
        if fits(raw*sizes[i], signs*fixed[i]):
            raw, signs, mask = raw*sizes[i], signs*fixed[i], mask | (1 << i)
    record(raw, signs, mask)

    def explore(exact):
        nonlocal transitions, peak_states
        states = {(1, 1): 0}
        peak_states = max(peak_states, 1)
        for i, (size, sign_count) in enumerate(zip(sizes, fixed)):
            if size == 1 or (exact and limit % size):
                continue
            additions = {}
            for (raw, signs), mask in states.items():
                if transitions == budget:
                    return False
                transitions += 1
                new_raw = raw*size
                if new_raw > limit or (exact and limit % new_raw):
                    continue
                new_signs = signs*sign_count if folded else 0
                key = new_raw, new_signs
                if key in states or key in additions:
                    continue
                new_mask = mask | (1 << i)
                additions[key] = new_mask
                record(new_raw, new_signs, new_mask)
                peak_states = max(peak_states, len(states)+len(additions))
                if incumbent[0] == limit:
                    return True
            states.update(additions)
        return True

    if cap == 0:
        outcome = 'no_feasible_table'
    elif incumbent[0] == limit:
        outcome = 'upper_bound'
    else:
        explore(True)
        if incumbent[0] == limit:
            outcome = 'upper_bound'
        else:
            complete = explore(False)
            outcome = 'exhaustive' if complete else 'budget'

    raw, _, mask = incumbent
    right = [group for i, group in enumerate(groups) if mask & (1 << i)]
    left = [group for i, group in enumerate(groups) if not mask & (1 << i)]
    raw_fixed = prod(fixed[i] for i in range(len(groups)) if mask & (1 << i))
    stored = (raw+raw_fixed)//2 if folded else raw
    report = dict(outcome=outcome, optimal=outcome in ('upper_bound', 'exhaustive'),
                  transition_budget=budget, transitions=transitions, peak_states=peak_states,
                  seed_checks=seeds_tested, total_choices=total, right_upper_bound=limit,
                  right_choices=raw, right_fixed_points=raw_fixed, stored=stored,
                  left_rows=total//raw, right_moduli=[m for m, _ in right])
    return left, right, report
