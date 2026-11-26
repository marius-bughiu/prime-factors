"""Render the GitHub Pages report from one benchmark run."""

import argparse
import json
import shutil
from html import escape
from math import log2
from pathlib import Path
from string import Template

ROOT = Path(__file__).resolve().parents[1]


def duration(seconds):
    if seconds < 0.01:
        return f'{seconds * 1000:.2f} ms'
    return f'{seconds:.2f} s'


def position_budget(done, required):
    total = int(required)
    if total.bit_length() > 64:
        return f'{done:,} positions evaluated · full sum needs at least 2<sup>{total.bit_length()-1}</sup>'
    return f'{done:,} of {total:,} positions'


def compact_count(value):
    if value.bit_length() <= 64:
        return f'{value:,}'
    return f'<abbr title="{value:,}">about 2<sup>{log2(value):.2f}</sup></abbr>'


def case_row(result):
    checked = result['verified']
    name = escape(result['id'])
    size = result['bits']
    status = 'Lean checked' if checked else 'Partial'
    cls = 'status' if checked else 'status partial'
    factors = ' × '.join(escape(x) for x in result['factors']) or 'None'
    evidence = (f'<a href="{escape(result["certificate"])}">Download Lean certificate</a>' if checked
                else '<span>Remaining cofactor(s)</span> <code>' + ' × '.join(map(escape, result['remaining'])) + '</code>')
    verification = duration(result['verification_seconds']) if checked else 'not run'
    if 'exclusion' in result:
        x = result['exclusion']
        if 'sum_tolerance' in x:
            claim = (f'For two 1,024-bit factors, Lean excludes every sum within '
                     f'{compact_count(int(x["sum_tolerance"]))} of the 647 centers '
                     f'using {x["bands"]} divisor intervals.')
        elif 'radix_exponent' in x:
            claim = (f'When both factors have at most {x["max_factor_bits"]:,} bits, Lean excludes '
                     f'remainder {escape(x["residue"])} modulo 2<sup>{x["radix_exponent"]}</sup>.')
        elif 'lower' in x:
            count = int(x['upper']) - int(x['lower']) + 1
            claim = f'Lean proves that none of the {compact_count(count)} integers in the interval divides the input.'
        else:
            claim = f'Lean excludes every even factor gap through {int(x["max_gap"]):,}.'
        evidence += f'<p>{claim} <a href="{escape(x["proof"])}">Download exclusion proof</a></p>'
        verification = duration(x['verification_seconds']) + ' (exclusion proof)'
    if 'schedule_proof' in result:
        sp = result['schedule_proof']
        if not checked:
            evidence += f'<p><a href="{escape(sp["proof"])}">Download the minimum-schedule proof</a></p>'
            verification = duration(sp['seconds']) + ' (schedule proof)'
        else:
            evidence += '<p>The certificate also proves the stated minimum schedule.</p>'
    if result['method'] == 'subgroup':
        w = result['subgroup']
        unit = 'base' if w['bases_tested'] == 1 else 'bases'
        count = f'Subgroup search · {w["bases_tested"]} {unit} tested · inclusive limit {w["max_base"]}'
        if w['status'] == 'split':
            count += f' · witness {w["witness_base"]}'
    elif result['method'] in ('reduced-order', 'cyclotomic'):
        if result['method'] == 'cyclotomic':
            w = result['cyclotomic']
            label = f'Cyclotomic period search · exponent N^{w["degree"]} − 1'
        else:
            w = result['reduced_order']
            label = 'Reduced-order search'
        count = (f'{label} · base {w["base"]} · {escape(w["outcome"])} · '
                 f'{w["entries_per_table"]} of {w["stride"]} entries built per table · '
                 f'{w["giants_probed"]} giant probes · {w["batch_gcds"]} batch gcds')
        if result['method'] == 'cyclotomic':
            count += f' · {w["halving_gcds"]} halving gcds'
        count += f' · search {duration(result["discovery_seconds"])}'
        if checked:
            verification += f' (certificate generation and replay {duration(result["certificate_seconds"])})'
    elif result['method'] == 'near-smooth-sum':
        w = result['near_smooth_sum']
        ops = w['work']
        count = (f'Sum tolerance {compact_count(int(w["tolerance"]))} · {w["windows_checked"]} of '
                 f'{w["viable_windows"]} candidate bands visited · {ops["geometry_sqrts"]} geometry square roots')
        if ops['trace_windows']:
            count += f' · {ops["trace_windows"]} weighted traces · {ops["square_tests"]} square tests'
        if ops['lll_calls']:
            count += (f' · {ops["lll_calls"]} lattice reductions · {ops["integer_root_nodes"]:,} root nodes'
                      f' · {ops["divisor_tests"]} divisor tests')
        if w['unresolved_windows']:
            count += f' · {len(w["unresolved_windows"])} visited bands unresolved'
        if w['sum_error'] is not None:
            offset = int(w['sum_error'])
            if abs(offset) < 1000:
                count += f' · actual sum offset {offset:,}'
            else:
                count += f' · {abs(offset).bit_length()}-bit difference from the winning center'
    elif result['method'] == 'two-three-sum':
        w = result['two_three_sum']
        count = (f'Factor sums supported on 2 and 3 · {w["exponents_visited"]} exponents visited'
                 f' · {w["square_tests"]} square tests')
        if w['excluded_by_remainder_and_size']:
            count += ' · every such sum excluded by remainder and size'
        elif w['winning_exponent'] is not None:
            count += f' · exponent of 3 at the split {w["winning_exponent"]}'
    elif result['method'] == 'neighbor-smooth-sum':
        w = result['neighbor_smooth_sum']
        count = (f'Inverse difference guess {w["inverse_gap"]} · primes through {w["prime_limit"]:,}'
                 f' · candidate sum {w["smooth_part"]}'
                 f' · {w["remainder_checks"]:,} remainder checks · {w["square_tests"]} square tests')
    elif result['method'] == 'two-draw-sampling':
        w = result['two_draw_sampling']
        scope = 'full period' if w['full_period_scanned'] else 'bounded scan'
        count = (f'Two positive draws · {scope} through length {w["scanned_side"]:,}'
                 f' · {w["sum_gcd_tests"]:,} sum-table gcds · {w["rectangles_tested"]:,} rectangles')
        if w['first_hit_sum'] is not None:
            count += f' · first table factor {w["first_hit_gcd"]:,} at sum {w["first_hit_sum"]:,}'
        if w['best_a'] is not None:
            area = w['best_a'] * w['best_b']
            count += (f' · best lengths {w["best_a"]:,} × {w["best_b"]:,} with {w["best_hits"]:,}/{area:,} hits'
                      f' · cutoff gcd {w["cutoff_gcd"]:,}')
        if w['factor_source'] == 'sum_table':
            count += ' · factor recovered from the sum table'
    elif result['method'] == 'monotone-divisor-sampling':
        w = result['monotone_divisor_sampling']
        count = f'{w["gcd_tests"]:,} gcd tests · {w["proper_hits"]:,} proper hits'
        if w['best_end'] is not None:
            count += (f' · first hit at {w["first_hit"]:,} · best prefix had '
                      f'{w["best_hits"]:,} hits in {w["best_end"]:,} tests')
    elif result['method'] == 'midpoint-weights':
        w = result['midpoint_weights']
        count = (f'Weighted sums · {w["visited_orbits"]:,} of {w["total_orbits"]:,} remainder pairs'
                 f' · {w["candidate_traces"]:,} candidate sums · {w["square_tests"]:,} square tests')
    elif result['method'] == 'complete-offset-search':
        w = result['complete_offset']
        total = w['raw_pairs']
        schedule = f'at least 2<sup>{total.bit_length()-1}</sup>' if total.bit_length() > 64 else f'{total:,}'
        count = (f"Complete offset range · {w['visited_pairs']:,} of {schedule} candidate pairs visited"
                 f" · {w['integer_square_roots']:,} integer square roots")
        if w.get('skipped_pairs'):
            count += f" · {w['skipped_pairs']:,} further pairs skipped by the offset filter"
    elif result['method'] == 'offset-winner-window':
        w = result['offset_winner_window']
        count = (f"Multiplier coordinates · {w['visited_pairs']:,} visits · {w['coordinate_rows']:,} coordinate rows"
                 f" · {w['square_tests']:,} square tests · {w['proper_hits']:,} successful positions")
        if w['exhaustive']:
            count += ' · full coordinate range exhausted'
        else:
            count += (f" · visit budget {w['max_visits']:,}"
                      f" · upper bound on remaining visits {compact_count(w['unvisited_upper'])}")
    elif result['method'] == 'offset-coordinate-gaps':
        w = result['offset_coordinate_gaps']
        band = 'Chord' if w['tilted'] else 'Horizontal'
        scope = 'full coordinate range' if w['all_vectors'] and w['schedule_exhausted'] else 'sampled coordinates'
        candidates = compact_count(w['candidate_lower'])
        if w['candidate_lower'] != w['candidate_upper']:
            candidates += '–' + compact_count(w['candidate_upper'])
        count = (f"{band} intervals · {w['vectors']:,} coordinate pairs ({scope})"
                 f" · {w['empty_intervals']:,} of {w['intervals']:,} intervals empty"
                 f" · {candidates} candidate positions"
                 f" · {w['tested_positions']:,} positions checked with a budget of {w['max_tests']:,}"
                 f" · {w['untested_intervals']:,} intervals still have unchecked positions")
        if 'lift_setup' in w:
            digits = 'original precision' if w['split_only'] else 'lifted precision'
            setup = w['lift_setup']
            count += (f" · {w['classes']:,} residue classes at {digits}"
                      f" · {w['coprime_tests']:,} tested positions passed the gcd check"
                      f" · {setup.get('class_inverses', 0):,} inverses for the divisor classes")
            if setup.get('class_pairs'):
                count += (f" · {setup['class_pairs']:,} class pairs considered"
                          f" · {setup.get('crt_inverses', 0):,} inverses to combine them")
    elif result['method'] == 'offset-arc-lines':
        w = result['offset_arc_lines']
        scope = 'full coordinate range' if w['all_vectors'] and w['schedule_exhausted'] else 'sampled coordinates'
        count = (f"Projected lines · {w['vectors']:,} coordinate pairs ({scope})"
                 f" · {w['tests']:,} of {compact_count(w['scheduled'])} scheduled tests"
                 f" · {w['tested_lines']:,} lines, {w['tested_points']:,} isolated points"
                 f" and {w['tested_vertical']:,} vertical slices"
                 f" · {w['discriminant_roots']:,} discriminant square roots")
    elif result['method'] == 'offset-tangent-cover':
        w = result['offset_tangent_cover']
        scope = 'full coordinate range' if w['all_vectors'] and w['schedule_exhausted'] else 'sampled coordinates'
        count = (f"Tangent arcs · {w['vectors']:,} coordinate pairs ({scope})"
                 f" · {w['visited_arcs']:,} of {compact_count(w['planned_arcs'])} arcs visited"
                 f" · {w['singletons_tested']:,} single positions and {w['line_equations']:,} line equations"
                 f" · {w['epoch_roots']:,} square roots and {w['width_cube_roots']:,} cube roots to plan arcs")
    elif result['method'] == 'weighted-divisor-exclusion':
        w = result['weighted_divisor_exclusion']
        count = (f'Weighted divisor interval · {w["tested_traces"]:,} of {w["total_traces"]:,} weighted sums checked'
                 f' · {w["modular_rejections"]:,} rejected by residues · {w["square_tests"]:,} integer square tests'
                 f' · {w["remaining_traces"]:,} weighted sums untested')
    elif result['method'] == 'adaptive-quartic-cover':
        w = result['adaptive_quartic_cover']
        counts = w['work']
        count = (f'{counts["lll_calls"]:,} lattice reductions covered {counts["covered_chunks"]:,} chunks'
                 f' · {counts["root_polynomials"]:,} polynomials checked for integer roots'
                 f' · {compact_count(w["covered_odd_positions"])} odd positions checked'
                 f' · {compact_count(w["unvisited_odd_positions"])} unvisited')
    elif result['method'] == 'divisor-product-derivative':
        w = result['divisor_product_derivative']
        digit = w['digit']
        count = (f"{digit['products']} product{'s' if digit['products'] != 1 else ''} evaluated modulo a {digit['modulus_bits']:,}-bit integer"
                 f" · {digit['candidates']:,} odd candidates per evaluation"
                 f" · {compact_count(int(digit['remaining']))} unvisited"
                 f" · {w['through_sqrt']['candidates']:,} slots in the capped square-root prefix"
                 f" · {w['trial']['divisions']:,} trial divisions in the comparison")
        if digit['factor_sum'] is not None:
            count += f" · recovered factor sum {escape(digit['factor_sum'])}"
    elif result['method'] == 'paired-divisor-windows':
        w = result['paired_divisor_windows']
        left, right, combined = w['ordinary']
        count = (f"One reduction for both windows · divisors {', '.join(map(str, w['divisors'])) or 'none'}"
                 f" · height {w['height']:,} against bound {w['height_bound']:,}"
                 f" · separate ordinary heights {left['height']:,} and {right['height']:,}"
                 f" · ordinary enclosing-window height {combined['height']:,}")
    elif result['method'] in ('sifted-divisor-window', 'rounded-sifted-window'):
        w = result[result['method'].replace('-', '_')]
        ref = w['reference']
        if w['denominator_gcd'] != 1:
            count = f"Degree-six wheel denominator shares gcd {w['denominator_gcd']:,} with the input"
            if w['denominator_factor']:
                count += f" · proper divisor {w['denominator_factor']:,} recovered before lattice reduction"
        else:
            basis = 'Rounded Chebyshev wheel' if w.get('rounded') else 'Wheel'
            reference = 'ordinary sifted' if w.get('rounded') else 'ordinary centered'
            count = (f"{basis} modulo 105, degree {w['degree']} · {compact_count(w['progression_size'])} odd positions"
                     f" · shift {w['shift']} · sifted height {'passed' if w['short'] else 'missed'}"
                     f" · {reference} height {'passed' if ref['short'] else 'missed'}"
                     f" · {w['work']['lll_swaps']:,} and {ref['work']['lll_swaps']:,} row swaps"
                     f" · {w['work']['modular_evaluations']:,} sifted modular evaluations"
                     f" · {reference} comparison took {duration(w['reference_seconds'])}")
    elif result['method'] == 'binomial-divisor-window':
        w = result['binomial_divisor_window']
        ref = w['reference']
        basis = 'Centered binomial' if w.get('centered', False) else 'One-sided binomial'
        count = (f"{basis}, degree {w['degree']} · {compact_count(w['progression_size'])} odd positions"
                 f" · binomial height {'passed' if w['short'] else 'missed'}"
                 f" · Chebyshev height {'passed' if ref['short'] else 'missed'}"
                 f" · {w['work']['lll_swaps']:,} and {ref['work']['lll_swaps']:,} row swaps"
                 f" · matching Chebyshev comparison took {duration(w['reference_seconds'])}")
    elif result['method'] == 'chebyshev-divisor-window':
        w = result['chebyshev_divisor_window']
        ordinary = w['ordinary']
        count = (f"Two quartic bases on {compact_count(w['progression_size'])} odd positions"
                 f" · Chebyshev height {compact_count(w['height'])} ({'passes' if w['short'] else 'fails'})"
                 f" · ordinary height {compact_count(ordinary['height'])} ({'passes' if ordinary['short'] else 'fails'})"
                 f" · {w['work']['lll_reductions']:,} and {ordinary['work']['lll_reductions']:,} size reductions")
        if 'exclusion' in result:
            count += f" · {result['exclusion']['certified_blocks']} certified polynomial pieces"
    elif result['method'] == 'higher-divisor-window':
        w = result['higher_divisor_window']
        count = (f'Degree {w["degree"]} at a prescribed location · {compact_count(w["progression_size"])} odd positions'
                 f' · {w["work"]["lll_swaps"]:,} row swaps · {w["work"]["lll_reductions"]:,} size reductions')
    elif result['method'] == 'quartic-three-row':
        w = result['quartic_three_row']
        counts = w['work']
        count = (f'Three-row comparison · {w["visited_blocks"]:,} windows visited'
                 f' · {compact_count(w["unvisited_blocks"])} unvisited'
                 f' · {counts["proper_gcds"]:,} hits in {counts["triples_tested"]:,} three-row tests'
                 f' · {counts["four_row_proper_gcds"]:,} hits in {counts["four_row_gcds"]:,} four-row tests')
    elif result['method'] == 'quartic-minor-gcd':
        w = result['quartic_minor_gcd']
        count = (f'Quartic determinant coefficients · {w["visited_blocks"]:,} windows visited'
                 f' · {compact_count(w["unvisited_blocks"])} unvisited · {w["work"]["normalized_minor_gcds"]:,} gcds'
                 f' · {w["work"]["proper_gcds"]:,} proper divisors returned')
    elif result['method'] == 'quartic-basis-translation':
        w = result['quartic_basis_translation']
        count = (f'Translated quartic bases · {w["visited_blocks"]:,} windows visited'
                 f' · {compact_count(w["unvisited_blocks"])} unvisited · {w["work"].get("lll_swaps", 0):,} row swaps'
                 f' · {w["work"].get("joint_mod2_exclusions", 0):,} windows rejected by parity'
                 f' · {w["work"].get("divisor_tests", 0):,} divisibility tests')
    elif result['method'] == 'quartic-window-extension':
        w = result['quartic_window_extension']
        ratio = w['progression_size'] / w['previous_progression_size']
        count = (f'Extended quartic interval · {ratio:.2f}× the original odd positions'
                 f' · {w["initial_lll_calls"]} initial lattice reduction · {w["additional_lll_calls"]} additional'
                 f' · {w["sign_evaluations"]:,} polynomial sign evaluations · {w["certified_blocks"]} certified pieces')
    elif result['method'] == 'quartic-divisor-window':
        w = result['quartic_divisor_window']
        count = (f'Quartic divisor interval · {compact_count(w["progression_size"])} odd positions'
                 f' · {w["lll_reductions"]:,} lattice reductions and {w["lll_swaps"]:,} row swaps'
                 f' · {w["integer_root_nodes"]:,} root-isolation nodes · {w["divisor_tests"]:,} divisibility tests')
    elif result['method'] == 'arbitrary-divisor-window':
        w = result['arbitrary_divisor_window']
        count = (f'Prescribed divisor interval · {compact_count(w["interval_size"])} integers'
                 f' · weighted sums spaced by {w.get("trace_stride", 2)}'
                 f' · {w["convergent_steps"]:,} continued-fraction steps to choose weights'
                 f' · {w["endpoint_tests"]:,} endpoints checked · {w["square_tests"]:,} discriminant square tests'
                 f' · {w["divisor_tests"]:,} direct divisibility checks')
    elif result['method'] == 'offset-factor-blocks':
        w = result['offset_factor_blocks']
        base = 'shifted' if w['shifted'] else 'floor-root'
        count = (f"Smaller-factor intervals · {compact_count(w['visited_blocks'])} of {compact_count(w['total_blocks'])}"
                 f" {base}-base blocks covered (budget {compact_count(w['max_blocks'])})"
                 f" · {compact_count(w['unvisited_blocks'])} blocks unvisited"
                 f" · {w['gauss_iterations']:,} basis reduction steps"
                 f" · {w['scanned_charts']:,} of {w['unique_charts']:,} distinct coordinate pairs scanned"
                 f" · {w['tested_positions']:,} positions tested (budget {w['max_tests']:,})")
        if w.get('coalesce'):
            count += (f" · {w['endpoint_reductions']:,} endpoint reductions"
                      f" · {w['guide_tests']:,} guide tests and {w['guide_interval_roots']:,} guide square roots")
            lower = w['untested_chart_positions_lower']
            upper = w['untested_chart_positions_upper']
            if lower == upper:
                position_count = f"{compact_count(lower)} (exact count)"
            else:
                position_count = f"{compact_count(lower)} to {compact_count(upper)} (lower and upper bounds)"
            count += (f" · {position_count} untested offset positions passing the residue and signed gap-band filters"
                      " across the full scanned coordinate windows")
            if w['max_reductions'] is not None:
                count += f" · endpoint reduction budget {w['max_reductions']:,}"
            if w.get('from_end'):
                count += (" · counted from the end at the integer square root"
                          f" · {compact_count(w['unvisited_prefix_blocks'])} earlier blocks and"
                          f" {compact_count(w['unvisited_suffix_blocks'])} later blocks unvisited")
        if w['untested_intervals']:
            count += f" · {w['untested_intervals']:,} intervals in scanned pairs still have unchecked positions"
    elif result['method'] == 'offset-trace-words':
        w = result['offset_trace_words']
        if w['outcome'] == 'word_cap':
            count = (f"Trace bit masks · required width {compact_count(w['word_bits_required'])} bits"
                     f" exceeds the {w['max_word_bits']:,}-bit cap · no coordinates visited")
        else:
            count = (f"Trace bit masks · {w['raw_pairs']:,} coordinate pairs, {w['parity_positions']:,} parity positions"
                     f" · {w['mask_entries']:,} mask entries prepared · {w['word_intersections']:,} intersections"
                     f" · {w['residue_survivors']:,} survivors · {w['square_tests']:,} square tests")
            if w['unvisited_upper']:
                count += f" · at most {compact_count(w['unvisited_upper'])} coordinate pairs unvisited"
    elif result['method'] == 'offset-crt':
        w = result['offset_crt']
        total = w['total_tuples']
        available = f'at least 2<sup>{total.bit_length()-1}</sup>' if total.bit_length() > 64 else f'{total:,}'
        count = (f"Reconstruction from remainders · {w['visited_tuples']:,} of {available} combinations tried"
                 f" · {w['convergents']:,} continued-fraction steps · {w['square_tests']:,} square tests")
        if 'wheel_work' in w:
            selection = w['wheel_work']
            subsets = selection.get('left_subsets', 0) + selection.get('right_subsets', 0)
            count += f" · prime selection examined {subsets:,} subsets and tried {selection['trial_divisions']} divisors"
    elif result['method'] in ('offset-lattice-batches', 'offset-row-geometry'):
        geometry = result['method'] == 'offset-row-geometry'
        w = result['offset_row_geometry'] if geometry else result['offset_lattice']
        label = 'Lattice search with lifted residues' if geometry else 'Lattice search'
        count = (f"{label} · {w['completed_batches']:,} groups completed"
                 f" · {compact_count(w['unfinished_batches'])} groups unfinished"
                 f" · {w['rows']:,} rows · {w['point_visits']:,} candidate visits · {w['square_tests']:,} square tests")
        if geometry:
            count += (f" · {compact_count(w['total_batches'])} scheduled groups with lifted residues"
                      f" · {compact_count(w['baseline_batches'])} in the original schedule"
                      f" · {w['second_digit_checks']:,} second-digit checks during the scan")
        if 'normalized_mod_tests' in w:
            count += (f" · {w['normalized_mod_tests']:,} normalized-row divisibility checks"
                      f" · {w['determinant_rejections']:,} determinant rejections"
                      f" · {w['valuation_rejections']:,} valuation rejections")
    elif result['method'] in ('offset-dyadic', 'offset-prime-power'):
        dyadic = result['method'] == 'offset-dyadic'
        w = result['offset_dyadic'] if dyadic else result['offset_prime_power']
        total = w['total_tuples']
        available = f'at least 2<sup>{total.bit_length()-1}</sup>' if total.bit_length() > 64 else f'{total:,}'
        visited = w['visited_tuples'] if dyadic else w['visited']
        name_of_search = 'Separate searches by denominator parity' if dyadic else 'Odd prime-power search'
        count = f"{name_of_search} · {visited:,} of {available} combinations · {w['square_tests']:,} square tests"
    elif result['method'] == 'offset-rows':
        w = result['offset_rows']
        tested = w['search']['square_tests']
        count = (f"Grouped offset search · {w['raw']:,} eligible offsets"
                 f" · {w['both_axes']:,} candidates after local tests"
                 f" · {tested:,} discriminants checked")
    elif result['method'] == 'grouped-norm':
        w = result['grouped_norm']
        count = (f"Product-selected multiplier · {w['square_tests']} square tests"
                 f" · {int(w['eligible_multipliers']):,} eligible multipliers"
                 f" · discovery {duration(result['discovery_seconds'])}")
    elif result['method'] == 'projected-level-sieve':
        w = result['projected_levels']
        count = (f'One positive group modulo 2<sup>{int(w["radix"]).bit_length()-1}</sup>'
                 f' · {w["work"]["level_positions_covered"]:,} of {w["total_levels"]:,} trace values checked'
                 f' · {w["work"].get("levels_isolated", 0):,} equations sent to root isolation')
    elif result['method'] in ('unit-quartic', 'centered-quartic'):
        w = result[result['method'].replace('-', '_')]
        if result['method'] == 'centered-quartic':
            label, exponent = 'positive', w['radix_exponent']
        else:
            label, exponent = 'signed', int(w['radix']).bit_length()-1
        count = (f'One {label} remainder group modulo 2<sup>{exponent}</sup>'
                 f' · {w["work"].get("integer_root_nodes", 0):,} root-isolation nodes'
                 f' · search {duration(result["discovery_seconds"])}')
    elif result['method'] == 'quartic-factor-lanes':
        w = result['quartic_factor_lanes']
        total = w['total_orbits']
        available = (f'{total:,}' if total.bit_length() <= 64 else
                     f'at least 2<sup>{total.bit_length()-1}</sup>')
        label = 'sign groups' if w.get('signed') else 'remainder pairs'
        count = (f'Degree {2*w["power"]} equations · {w["visited_orbits"]:,} of {available} {label} searched'
                 f' · {w["work"].get("lll_calls", 0):,} LLL calls'
                 f' · {w["work"].get("integer_root_nodes", 0):,} root-isolation nodes'
                 f' · search {duration(result["discovery_seconds"])}')
        if w.get('signed'):
            count += f' · {w["ordinary_covered_orbits"]:,} ordinary remainder pairs covered'
        if w.get('unit_residue'):
            count += ' · tested factor remainder 1'
        basis_labels = {'newton': 'Newton polynomial', 'gap-newton': 'factor-gap coordinates',
                        'dickson-newton': 'Dickson polynomials in the factor gap'}
        if w.get('basis') in basis_labels:
            count += ' · '+basis_labels[w['basis']]
    elif result['method'] == 'midpoint-slope-batches':
        w = result['midpoint_slope_batches']
        counts = w['work']
        count = (f'CRT half sums · {w["visited_slopes"]:,} slopes searched · '
                 f'{counts.get("candidate_traces", 0):,} candidate sums · '
                 f'{counts.get("square_tests", 0):,} square tests')
        if w.get('geometry') == 'hexagon_slope':
            count += f' · compared {counts["radix_candidates"]} radices by slope count'
        if w.get('curve'):
            count += ' · curved interval'
        if w['outcome'] == 'half_list_limit':
            count += (f' · next list requires {counts["next_half_size"]:,} entries'
                      f' · limit {w["max_half_entries"]:,}')
    elif result['method'] == 'class-orders':
        w = result['class_orders']
        count = (f'Class orders · {w["windows"]:,} interval searches · {w["compositions"]:,} form compositions'
                 f' · {escape(w["outcome"])}')
    elif result['method'] == 'modular-hyperbola':
        w = result['hyperbola']
        radix = f' · radix {w["radix"]:,}' if 'radix' in w else ''
        count = (f'Balanced-interval modular search{radix} · {w["low_classes"]:,} low residue classes'
                 f' · {w["modular_hits"]:,} candidate products · {w["euclidean_steps"]:,} Euclidean steps'
                 f' · search {duration(result["discovery_seconds"])}')
    elif result['method'] == 'quotient-search':
        w = result['quotient_search']
        count = (f'Factor intervals · wheel {w["wheel"]} · {w["blocks"]:,} initial strips · '
                 f'{w["bisected"]:,} bisections · {w["quadratic_solves"]:,} quadratics · '
                 f'{w["euclidean_steps"]:,} Euclidean steps')
    elif result['method'] == 'pell-local-windows':
        w = result['pell_windows']
        count = (f'Continued fractions · {w["steps"]:,} of {w["max_steps"]:,} steps · '
                 f'{w["pairs"]:,} pairs up to {w["depth"]} rows apart · '
                 f'{w["candidates"]:,} candidates · {w["root_tests"]:,} square-root tests')
    elif result['method'] == 'pell-pairs':
        w = result['pell_pairs']
        count = (f'Continued fractions · {w["prime_gcds"]} auxiliary prime checks · '
                 f'{w["walks"]} walks · {w["centers"]} centers · {w["cycles"]} triangles · '
                 f'{w["steps"]:,} of {w["max_steps"]:,} steps')
    elif result['method'] == 'weighted-base':
        w = result['weighted_base']
        selection = w['selection_work']
        count = (f'Base selection · {selection["bases_tested"]:,} of {w["max_primes"]:,} primes tested'
                 f' · combined order {escape(selection["combined_order"])}'
                 f' · {escape(w["outcome"].replace("_", " "))}')
    elif result['method'] == 'trace-cover':
        w = result['trace_cover']
        count = (f'{w["catalogue"]:,} weight pairs · minimum {w["optimum"]:,} blocks · '
                 f'{compact_count(int(w["block"]))} starting powers in the priced table · '
                 f'{w["probes"]:,} weighted test ratios · '
                 f'{"public plan replay" if w.get("replayed_plan") else "planning"} {duration(w["plan_seconds"])}')
        if 'gap_three_blocks' in w:
            count += f' · earlier restricted planner {w["gap_three_blocks"]:,} blocks'
        if w['executed']:
            count += f' · factor search {duration(w["search_seconds"])}'
        else:
            count += ' · planned schedule only'
    elif result['method'] in ('weighted-stride', 'weighted-sparse'):
        w = result['weighted_stride']
        counts = w['work']
        scope = 'all windows generated' if w['schedule_complete'] else (w['limit'] or w['outcome']).replace('_',' ')
        count = (f'Weighted sums · {counts["babies"]:,} starting powers · {counts["giants"]:,} blocks'
                 f' · {counts["labels_covered"]:,} candidate sums · {escape(scope)}'
                 f' · search {duration(result["discovery_seconds"])}')
        if result['method'] == 'weighted-sparse':
            count += (f' · {counts["evaluations"]:,} positions evaluated'
                      f' · {counts["retained_evaluations"]:,} retained in the gcd test')
    elif result['method'] == 'factorial-progressions':
        w = result['factorial_progressions']
        counts = w['work']
        covered = counts.get('batched_candidates', 0) + counts.get('edge_candidates', 0)
        count = (f'Block products · {int(w["span"]):,} integers in budgeted interval'
                 f' · {covered:,} candidates covered · {counts.get("convolutions", 0)} convolutions'
                 f' · search {duration(result["discovery_seconds"])}')
    elif result['method'] == 'extension-trace':
        w = result['extension_trace']
        count = (f'Quadratic-extension sum · {position_budget(w["positions"], w["required_positions"])}'
                 f' · {w["selector_tests"]:,} selector checks · {escape(w["outcome"])}')
    elif result['method'] == 'reciprocal-wheel':
        w = result['reciprocal_wheel']
        count = (f'Paired factor intervals · {w["blocks"]:,} blocks tested'
                 f' · {w["compatible_candidates"]:,} of {w["ordinary_candidates"]:,} candidates retained'
                 f' · {w["evaluations"]:,} polynomial evaluations')
    elif result['method'] == 'local-midpoints':
        w = result['local_midpoints']
        count = (f'Prime-power midpoint tests · {w["range_queries"]} interval counts · '
                 f'{w["square_tests"]} integer square tests')
        if 'survivors' in w:
            count += f' · {int(w["survivors"]):,} possible midpoints remain'
    elif result['method'] == 'quartic-trace':
        w = result['quartic_trace']
        count = (f'Quartic character sums · {w["bits"]+2} bits per residue'
                 f' · {position_budget(w["positions"], w["required_positions"])}'
                 f' · {w["symbol_evaluations"]:,} symbol evaluations')
        if w['vector'] is not None:
            x, y = w['vector']
            count += f' · recovered coordinates ({x}, {y})'
    elif result['method'] == 'norm-band-product':
        w = result['norm_band_product']
        count = (f'Side {int(w["side"]):,} of {int(w["target_side"]):,}'
                 f' · {w["allowed_pairs"]:,} pairs inside the factor interval'
                 f' · {w["evaluations"]:,} polynomial evaluations · one gcd')
        if w.get('canonical'):
            count += ' · unique normalized representation'
    elif result['method'] == 'short-norm-boxes':
        w = result['short_norm_boxes']
        count = (f'Odd-coordinate norm grid · side {int(w["side"]):,} of {int(w["target_side"]):,}'
                 f' · polynomial degree {w["degree"]:,}'
                 f' · {w["evaluations"]:,} of {w["planned_evaluations"]:,} evaluations'
                 f' · {w["pair_values_covered"]:,} coordinate pairs across forms'
                 f' · {w["batch_gcds"]:,} batch gcds')
        if w['row_gcds'] or w['leaf_gcds']:
            count += f' · {w["row_gcds"]:,} row gcds · {w["leaf_gcds"]:,} individual gcds'
    elif result['method'] == 'universal-norms':
        w = result['universal_norms']
        count = f'Norm grid · side {int(w["side"]):,} of {int(w["target_side"]):,}'
        if w['mode'] == 'separating':
            count += f' · {w["selector_tests"]:,} coefficient checks'
            if w['selector'] is not None:
                count += f' · coefficient {w["selector"]:,}'
        else:
            count += f' · {w["forms_tested"]} forms searched · {w["empty_forms"]} excluded by size'
        count += (f' · {w["evaluations"]:,} polynomial evaluations'
                  f' · {w["pair_values_covered"]:,} coordinate pairs across forms'
                  f' · {w["batch_gcds"]:,} batch gcds')
        if w.get('row_gcds') or w.get('leaf_gcds'):
            count += f' · {w["row_gcds"]:,} row gcds · {w["leaf_gcds"]:,} individual gcds'
        if w.get('whole_modulus_batches'):
            count += f' · {w["whole_modulus_batches"]} whole-modulus batch gcds'
    elif result['method'] == 'norm-curves':
        w = result['norm_curves']
        if w['mode'] == 'residues':
            count = (f'Degree {w["degree"]} · {w["blocks"]:,} of {w["max_blocks"]:,} residue classes'
                     f' · {w["auxiliary_equations"]:,} auxiliary equations')
        else:
            count = (f'Degree 2 · {w["blocks"]:,} of {w["max_blocks"]:,} sectors'
                     f' · {w["resultants"]:,} quartics solved')
            if w['reuse_basis']:
                count += f' · {w["reused_bases"]:,} bases reused'
        count += (f' · {w["lll_calls"]:,} lattice reductions · {w["lll_swaps"]:,} swaps'
                  f' · {w["integer_root_nodes"]:,} root-isolation intervals'
                  f' · {w["representations"]:,} representations found')
    elif result['method'] == 'norm-directions':
        w = result['norm_directions']
        count = (f'{w["blocks"]:,} of {w["max_blocks"]:,} ellipse blocks'
                 f' · {w["line_tests"]:,} candidate lines'
                 f' · {w["discriminant_roots"]:,} square-root tests'
                 f' · {w["representations"]:,} representations found')
    elif result['method'] == 'polynomial-packets':
        w = result['polynomial_packet']
        coverage = 'complete height interval' if w['interval_complete'] else 'partial height interval'
        count = (f'All square-root classes at a {int(w["coefficient"]).bit_length():,}-bit coefficient'
                 f' · {w["euclidean_steps"]:,} Euclidean steps'
                 f' · {w["tested_lifts"]:,} of {int(w["possible_lifts"]):,} candidate quadratics checked'
                 f' · small values found {len(w["rows"]):,}'
                 f' · {coverage} · search {duration(result["discovery_seconds"])}')
    elif result['method'] == 'polynomial-relations':
        w = result['polynomial_relations']
        modes = {'single': 'Single interval', 'square': 'Square coefficients', 'edges': 'Shared prime coefficients'}
        count = (f'{modes[w["mode"]]} · {w["positions"]:,} positions · {w["sieve_marks"]:,} sieve marks · '
                 f'{w["smooth_rows"]:,} smooth rows · {w.get("dependencies", 0):,} square relations · '
                 f'{w.get("gcd_tests", 0):,} gcd tests')
        if w['policy'] == 'coefficient':
            count += ' · even row count at each coefficient'
    elif result['method'] == 'seed-gap-sieve':
        w = result['seed_gap_sieve']
        count = (f'Fraction norm at most {w["max_norm"]:,} · wheel modulus {w["modulus"]:,} · '
                 f'{w["entries"]:,} square classes · gap count {w["gaps"]:,} · '
                 f'{w["square_tests"]:,} candidate square roots computed')
    elif result['method'] == 'guided-pairs':
        w = result['guided_pairs']
        count = (f'Fraction norm at most {w["max_norm"]:,} · '
                 f'{w["multipliers"]:,} of {w["max_multipliers"]:,} multiplier roots computed · '
                 f'{w["square_tests"]:,} eligible gaps tested for a square')
    elif result['method'] == 'same-source-pairs':
        w = result['same_source_pairs']
        source = {'unit': 'unit residues', 'square': 'squares of units'}[w['mode']]
        count = (f'Fraction pairs from {source} · {w["draws"]:,} of {w["max_draws"]:,} draws · '
                 f'{w["short_fractions"]:,} short fractions · '
                 f'{w["exact_pair_tests"]:,} of {w["possible_pairs"]:,} possible pairs checked exactly')
    elif result['method'] == 'fraction-chains':
        w = result['fraction_chains']
        count = (f'Euclidean fractions · {w["draws"]:,} of {w["max_draws"]:,} draws · '
                 f'{w["candidates"]:,} fractions tested · {w["accepted_draws"]:,} draws with smooth fractions · '
                 f'{w["smooth_rows"]:,} smooth rows')
    elif result['method'] == 'rational-squares':
        w = result['rational_squares']
        count = (f'{w["mode"].capitalize()} square search · {w["draws"]:,} of {w["max_draws"]:,} draws · '
                 f'{w["euclidean_divisions"]:,} Euclidean divisions · {w["smooth_rows"]:,} smooth rows · '
                 f'{w["tested"]:,} relations tested')
    elif result['method'] == 'scored-multipliers':
        w = result['scored_multipliers']
        count = (f'Continued fraction · multiplier {w["multiplier"]} · {w["candidates"]} choices considered · '
                 f'{w["residue_checks"]} small-prime residue checks · {w["sign_comparisons"]} sign comparisons · '
                 f'{w["steps"]:,} of {w["max_steps"]:,} steps · '
                 f'{w["tested"]:,} relations tested')
    elif result['method'] == 'crt-square-norms':
        w = result['crt_square_norms']
        count = (f'Square-root classes · {w["windows"]:,} of {w["total_windows"]:,} moduli opened · '
                 f'{w["left_size"]:,} left and {w["right_size"]:,} right partial sums in total · '
                 f'{w["visited_hits"]:,} of {w["interval_hits"]:,} window hits checked · '
                 f'{w["private_pruned"]:,} rows excluded · {w["tested"]:,} combined relations tested')
    elif result['method'] == 'partition-recurrence':
        w = result['partition_recurrence']
        count = (f'Sparse partition series · index limit {w["max_index"]:,} · '
                 f'{w["signed_updates"]:,} of {w["possible_updates"]:,} possible additions used')
    elif result['method'] == 'theta-residues':
        w = result['theta_residues']
        count = (f'Power-series coefficient · index limit {w["max_index"]:,} · '
                 f'{w["convolution_terms"]:,} convolution terms · {w["candidates_tested"]:,} candidate divisors')
    elif result['method'] == 'line-powers':
        w = result['line_powers']
        tally = w['work']
        names = {'square-1': 'Dickson polynomial at N² − 1', 'minus': 'Dickson polynomial at N − 1',
                 'plus': 'Dickson polynomial at N + 1', 'monomial-square-1': 'Ordinary power at N² − 1'}
        count = (f'{names[w["exponent"]]} · {tally["labels"]:,} of {w["max_seeds"]:,} labels · '
                 f'{tally["gcds"]:,} gcds · {tally["ladder_steps"]:,} recurrence steps · '
                 f'{tally["modular_powers"]:,} ordinary powers')
    elif result['method'] == 'pooled-relations':
        w = result['pooled_relations']
        count = (f'Continued fractions with multipliers {", ".join(map(str, w["multipliers"]))} · '
                 f'{w["steps"]:,} of {w["max_steps"]:,} steps · '
                 f'{w["distinct_rows"]:,} distinct results · {w["square_tests"]:,} individual square tests · '
                 f'{w["tested"]:,} combined relations tested')
    elif result['method'] == 'pell-relations':
        w = result['pell_relations']
        count = (f'Continued-fraction relations · {w["steps"]:,} of {w["max_steps"]:,} steps · '
                 f'{w["private_pruned"]:,} rows excluded · '
                 f'{w["tested"]:,} of {w["dependencies"]:,} independent combinations tested')
    elif result['method'] == 'four-square-lines':
        w = result['four_square_lines']
        count = (f'Four-square representations · {w["triples"]:,} of {w["max_triples"]:,} triples tested · '
                 f'{w["representations"]:,} representations · {w["finite_labels"]:,} slopes · '
                 f'{w["pair_gcds"]:,} pair comparisons')
    elif result['method'] == 'salie-blocks':
        w = result['salie_blocks']
        outcome = ('sum decoded' if w['outcome'] == 'decoded' else
                   'sum unfinished, factor found in scan' if w['scan_factor'] is not None else 'sum unfinished')
        count = (f'Blocked sum · {outcome} · {w["orbits"]:,} of {w["max_orbits"]:,} orbits · '
                 f'{w["trig_calls"]} trigonometric evaluations · {w["complex_products"]:,} complex products')
    elif result['method'] == 'folded-square':
        w = result['folded_square']
        count = (f'Fixed-frequency sum · {w["sums"]} complete sums · '
                 f'{w["terms"]:,} of {w["max_terms"]:,} unit terms · '
                 f'{w["unit_gcds"]:,} gcd tests')
    elif result['method'] == 'salie-seed':
        w = result['salie_seed']
        count = (f'Shared Salié reading · {w["sums"]} complete sums · '
                 f'{w["terms"]:,} of {w["max_terms"]:,} unit terms · '
                 f'{w["unit_gcds"]:,} gcd tests · {w["certified_cells"]} certified rounding decisions')
    elif result['method'] in ('divisor-samples', 'salie-residues'):
        w = result[result['method'].replace('-', '_')]
        outcome = {'phase_split': 'recovered a root', 'frequency_gcd': 'frequency gcd split',
                   'crt_split': 'reconstructed a root by CRT', 'prime_gcd': 'scheduled prime split',
                   'budget': 'term budget exhausted', 'size_limit': 'size limit reached',
                   'unresolved': 'unresolved'}[w['outcome']]
        count = (f'Salié sums · {outcome} · {w["sums"]:,} distinct sums · '
                 f'{w["terms"]:,} of {w["max_terms"]:,} terms · '
                 f'{w["unit_gcds"]:,} unit tests during setup')
        if result['method'] == 'salie-residues':
            count += f' · {w["prime_count"]} scheduled primes'
    elif result['method'] == 'wide-modulus':
        w = result['wide_modulus']
        order = w['order']
        count = (f'One-interval sieve · modulus {w["m"]:,} · '
                 f'{w["work"].get("baby_powers", 0):,} baby powers · '
                 f'{w["work"].get("giant_powers", 0):,} giant powers · '
                 f'{order["work"]["certificate_gcds"]:,} order checks · '
                 f'{order["work"]["progression_gcds"]:,} progression gcds · '
                 f'search {duration(result["discovery_seconds"])}')
        if not checked:
            count += ' · ' + escape(w['unresolved_stage'].replace('_', ' '))
    elif result['method'] == 'short-basis':
        w = result['short_basis']
        extra = 'on' if w['use_exceptional'] else 'off'
        count = (f'Short lattice weights · {w["sparse_entries"]:,} baby table entries'
                 f' · {w["kept"]:,} ordinary giant records · {w["ordinary_gcds"]:,} ordinary gcds'
                 f' · exceptional search {extra} · {w["exceptional_gcds"]:,} exceptional gcds'
                 f' · {w["fallback_gcds"]:,} fallback gcds · search {duration(result["discovery_seconds"])}')
    elif result['method'] == 'pascal':
        w = result['pascal']
        count = (f'Binomial formula · {escape(w["cutoff"])} cutoff · index {escape(w["index"])}'
                 f' · index budget {w["max_index"]:,} · coefficients evaluated {w["coefficients_evaluated"]}')
        if w['coefficient_bits'] is not None:
            count += f' · exact coefficient size {w["coefficient_bits"]:,} bits · residue {escape(w["residue"])}'
        count += f' · search {duration(result["discovery_seconds"])}'
    elif result['method'] == 'inverse-windows':
        w = result['inverse_windows']
        count = (f'Modular inverses · {w["entries"]:,} table entries · {w["geometric_cells"]:,} rectangle lookups'
                 f' · {w["modular_points"]:,} candidate products · {w["baseline_trial_odds"]:,} divisions in a full trial scan'
                 f' · search {duration(result["discovery_seconds"])}')
    elif result['method'] == 'midpoint-readings':
        w = result['readings']
        count = (f'Jacobi sign checks · {w["midpoints"]:,} initial midpoints'
                 f' · {w["evaluations"]:,} sign evaluations · {w["final_square_tests"]:,} final square tests'
                 f' · search {duration(result["discovery_seconds"])}')
    elif result['method'] == 'continued-square':
        w = result['continued_square']
        cap = f' · cap {w["max_convergents"]}' if w["max_convergents"] is not None else ''
        count = (f'Continued fractions of the square-root residual · {w["convergents"]} convergents'
                 f'{cap} · {w["square_tests"]} square tests after the initial integer square root'
                 f' · search {duration(result["discovery_seconds"])}')
    elif result['method'] == 'square-offset':
        w = result['square_offset']
        count = (f'Corrected totient square · {w["gaps_tested"]} of {w["max_gap"]} index gaps tested'
                 f' · {w["discriminants"]} discriminants · search {duration(result["discovery_seconds"])}')
    elif result['method'] == 'predecessor-square':
        w = result['predecessor_square']
        count = (f'Totient square classes · {w["scales_tested"]} scales tested'
                 f' · inclusive limit {w["max_scale"]} · search {duration(result["discovery_seconds"])}')
    elif result['method'] == 'gap-stride':
        w = result['gap_stride']
        count = (f'Powers of five in the half-gap · exponent {w["exponent"]} of {w["max_exponent"]}'
                 f' · {w["per_root"]} midpoints per root · {w["square_tests"]} square tests'
                 f' · {w["lift_tests"]} modular digit tests · search {duration(result["discovery_seconds"])}')
    elif result['method'] == 'shifted':
        outcome = 'split' if result['shifted']['status'] == 'split' else 'no split'
        count = f'Shifted-square formula · {outcome} · {result["fermat_steps"]} Fermat midpoints'
    else:
        unit = 'midpoint' if result['fermat_steps'] == 1 else 'midpoints'
        count = f'Fermat pipeline · {result["fermat_steps"]} {unit} tested · budget {result["max_steps"]}'
    return f'''<details id="{name}"><summary><span class="case-title">{escape(result['description'])}</span>
<span class="numeric size">{size} bits</span><span class="{cls}">{status}</span>
<span class="numeric time">{duration(result['wall_seconds'])}</span></summary><div class="payload">
<p>{count}</p><p class="label">Input</p><code>{escape(result['n'])}</code>
<p class="label">{'Prime factors' if checked else 'Resolved portion'}</p><code>{factors}</code>
<p>Lean verification {verification}</p><div>{evidence}</div></div></details>'''


def render(out):
    data = json.loads((out / 'results.json').read_text())
    results = sorted(data['results'], key=lambda row: -row['bits'])
    biggest = max((row for row in results if row['verified']), key=lambda row: row['bits'])
    repo = 'https://github.com/' + escape(data['repository'])
    sha = escape(data['commit'])
    complete = sum(row['verified'] for row in results)
    run_link = f' · <a href="{repo}/actions/runs/{escape(data["run_id"])}">Workflow run</a>' if data['run_id'] else ''
    html = Template((ROOT / 'site/index.html').read_text()).substitute(
        repo=repo, tree=f'{repo}/blob/{sha}', commit_url=f'{repo}/commit/{sha}', sha=sha[:7],
        bits=f"{biggest['bits']:,}", largest_desc=escape(biggest['description']), largest_id=escape(biggest['id']),
        count=len(results), complete=complete, partial=len(results) - complete,
        rows='\n'.join(map(case_row, results)), cpu=escape(data['cpu']), python=escape(data['python']),
        lean=escape(data['lean']), date=escape(data['measured_at']), run_link=run_link)
    (out / 'index.html').write_text(html)
    shutil.copyfile(ROOT / 'site/style.css', out / 'style.css')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out', type=Path, default=ROOT / 'build' / 'site')
    render(parser.parse_args().out)
