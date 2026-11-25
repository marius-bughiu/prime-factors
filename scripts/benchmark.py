"""Run the public fixtures from N, check their expected outcomes, and retain proof files."""

import argparse
import json
import os
import platform
import re
import subprocess
import sys
import time
from datetime import datetime, timezone
from functools import partial
from math import isqrt
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from experiments.adaptive_quartic_cover import search as adaptive_quartic_search
from experiments.higher_divisor_window import search as higher_window_search
from experiments.divisor_product_derivative import compare as compare_product_digits
from experiments.paired_divisor_windows import compare as compare_paired_windows
from experiments.arbitrary_divisor_window import quartile_center, search as arbitrary_window_search
from experiments.class_order_search import search as class_order_search
from experiments.complete_offset_search import search as complete_offset_search
from experiments.offset_arc_lines import search as offset_arc_line_search
from experiments.offset_coordinate_gaps import search as offset_coordinate_gap_search
from experiments.offset_crt_reconstruction import search as offset_crt_search
from experiments.offset_dyadic_search import search as offset_dyadic_search
from experiments.offset_factor_blocks import search as offset_factor_block_search
from experiments.offset_lattice_batches import search as offset_lattice_search
from experiments.offset_prime_power_slopes import search as offset_prime_power_search
from experiments.offset_row_geometry import search as offset_row_geometry_search
from experiments.offset_tangent_cover import search as offset_tangent_cover_search
from experiments.offset_trace_words import search as offset_trace_word_search
from experiments.offset_winner_window import search as offset_winner_window_search
from experiments.weighted_divisor_exclusion import search as weighted_divisor_search
from experiments.grouped_offset_frame import choose_frame
from experiments.grouped_offset_rows import bounded_rows
from experiments.midpoint_slope_batches import search as slope_batch_search
from experiments.midpoint_weights import search as weight_orbit_search
from experiments.gap_newton_lanes import search as gap_lane_search
from experiments.quartic_minor_gcd import search as minor_gcd_search
from experiments.quartic_three_row import search as three_row_search
from experiments.quartic_basis_translation import search as translated_window_search
from experiments.quartic_interval_extension import _bernstein_positive, extend as extend_quartic_window
from experiments.quartic_divisor_window import odd_quartile_center, search as quartic_window_search
from experiments.quartic_factor_lanes import search as quartic_lane_search
from experiments.unit_factor_lane import search as unit_lane_search
from experiments.unit_quartic_probe import probe as unit_quartic_probe
from experiments.centered_sum_quartic import probe as centered_quartic_probe
from experiments.projected_level_sieve import centered_search as projected_level_search
from scripts.factor import verify_file
from scripts.higher_window_certificate import check_higher_interval
from experiments.modular_hyperbola import search as hyperbola_search
from experiments.local_midpoint_lanes import search as local_midpoint_search
from experiments.divisor_samples import search as divisor_sample_search
from experiments.salie_residues import search as salie_residue_search
from experiments.salie_seed import search as salie_seed_search
from experiments.midpoint_readings import search as midpoint_readings_search
from experiments.short_basis_sieve import search as short_basis_search
from experiments.wide_modulus import search as wide_modulus_search
from experiments.pascal_readout import search as pascal_search
from experiments.pell_pairs import search as pell_pair_search
from experiments.pell_local_windows import search as pell_window_search
from experiments.pell_relations import search as pell_relation_search
from experiments.pooled_relations import search as pooled_relation_search
from experiments.crt_square_norms import search as crt_square_search
from experiments.partition_recurrence import search as partition_recurrence_search
from experiments.scored_multipliers import search as scored_multiplier_search
from experiments.rational_squares import search as rational_square_search
from experiments.fraction_chains import search as fraction_chain_search
from experiments.pair_class_search import search as same_source_pair_search
from experiments.guided_pairs import cover as guided_pair_cover
from experiments.seed_gap_sieve import search as seed_gap_search
from experiments.polynomial_relations import search as polynomial_relation_search
from experiments.polynomial_packet import search as polynomial_packet_search
from experiments.norm_directions import search as norm_direction_search
from experiments import norm_auxiliary, norm_band_product, norm_residue_curves
from experiments import extension_trace, factorial_progressions, quartic_trace, reciprocal_wheel
from experiments import short_norm_boxes, universal_norm_batch, weighted_base_selection, weighted_stride_search
from experiments.salie_blocks import search as salie_block_search
from experiments.folded_square import direct as fixed_phase_search
from experiments.four_square_lines import search as four_square_line_search
from experiments.line_powers import search as line_power_search
from experiments.theta_residues import search as theta_residue_search
from experiments.quotient_search import search as quotient_search
from experiments.inverse_windows import search_product as inverse_windows_search
from experiments.continued_square import search as continued_square_search
from experiments.predecessor_square import search as predecessor_square_search, search_square_offset
from experiments.gap_stride import search as gap_search
from experiments.cyclotomic_periods import expand_cases, reduced_table_search, search as cyclotomic_search


def cli(args, expected_code=0):
    command = [sys.executable, *map(str, args)]
    proc = subprocess.run(command, cwd=ROOT, text=True, capture_output=True, timeout=900)
    if proc.returncode != expected_code:
        raise RuntimeError(f"{args[0]} exited {proc.returncode}: {proc.stderr}\n{proc.stdout}")
    return json.loads(proc.stdout)


def agree(case, result, keys):
    for key in keys:
        if case[key] != result[key]:
            raise ValueError(f"{case['id']}.{key}: expected {case[key]!r}, got {result[key]!r}")


def period_case(case, method, proof):
    n, base, stride = int(case['n']), case['base'], case['stride']
    work_keys = ['outcome', 'entries_per_table', 'giants_probed', 'batch_gcds']
    if method == 'cyclotomic':
        work = cyclotomic_search(n, base, case['degree'], stride)
        work['degree'] = case['degree']
        work_keys.append('halving_gcds')
        key = 'cyclotomic'
    else:
        work = reduced_table_search(n, base, stride)
        key = 'reduced_order'
    factor = work.pop('factor')
    search_seconds = work.pop('search_nanoseconds') / 1_000_000_000
    agree(case, work, work_keys)
    return certify_split(case, proof, factor, search_seconds, key, dict(work, base=base, stride=stride))


def certify_split(case, proof, factor, search_seconds, key, work):
    n = int(case['n'])
    result = dict(n=case['n'], bits=n.bit_length(), factors=[], remaining=[case['n']],
                  status='partial', verified=False, verification_seconds=None, certificate_seconds=None,
                  discovery_seconds=search_seconds)
    result[key] = work
    if factor is not None:
        certificate_start = time.perf_counter()
        checked = cli(['scripts/factor.py', case['n'], '--factor-hint', factor, '--max-steps', 0,
                       '--verify', '--lean', proof])
        result.update({key: checked[key] for key in
                       ['factors', 'remaining', 'status', 'verified', 'verification_seconds']})
        result['certificate_seconds'] = time.perf_counter() - certificate_start
    return result


def verify_interval(n, work, proof, module, application):
    """Tie the downloaded statement to the measured input and inclusive endpoints."""
    if not work['excluded'] or n % 2 != 1:
        raise ValueError('Expected an exhausted divisor-free interval on an odd input')
    theorem = 'PrimeFactors.Generated.divisor_interval'
    proof.write_text(f"""import PrimeFactors.{module}

set_option exponentiation.threshold 16384
set_option maxRecDepth 10000

theorem {theorem} (d : ℕ) (lo : {work['lower']} ≤ d) (hi : d ≤ {work['upper']}) :
    ¬ d ∣ {n} := by
{application}

#print axioms {theorem}
""")
    return verified_interval(work, proof, theorem)


def verified_interval(work, proof, theorem):
    start = time.perf_counter()
    verify_file(proof, theorem)
    return dict(lower=str(work['lower']), upper=str(work['upper']), proof=f'proofs/{proof.name}',
                verification_seconds=time.perf_counter()-start)


def check_divisor_interval(n, work, first, count, modulus, proof):
    """Check the measured interval and every allowed trace directly in Lean."""
    if modulus < 2:
        raise ValueError('Expected a modulus of at least two')
    if work.get('trace_stride') == 24:
        return verify_interval(n, work, proof, 'UniversalTraceWindow', f"""  apply PrimeFactors.UniversalTraceWindow.excludes_of_modulus
    (c := {work['center']}) (w := {work['radius']}) (a := {work['a']}) (b := {work['b']})
    (t := {first}) {modulus} ?_ ?_ ?_ ?_ ?_ ?_ ?_ d lo hi
  all_goals first
    | (unfold PrimeFactors.UniversalTraceWindow.Curvature; decide +kernel)
    | (unfold PrimeFactors.UniversalTraceWindow.Weights; decide +kernel)
    | decide +kernel""")
    return verify_interval(n, work, proof, 'WeightedDivisorExclusion', f"""  apply PrimeFactors.WeightedDivisorExclusion.excludes
    (a := {work['a']}) (b := {work['b']}) (first := {first}) (count := {count})
    (moduli := [{modulus}]) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ d lo hi
  all_goals first | (unfold PrimeFactors.WeightedDivisorExclusion.Lower; decide +kernel) | decide +kernel""")


def check_quartic_levels(n, sample, proof):
    """Check one entire excluded chunk, including points outside the old height window."""
    center, left, right = sample['center'], sample['left'], sample['right']
    bounds = dict(lower=center+2*left, upper=center+2*right, excluded=True)
    row_terms = []
    for row in sample['rows']:
        coeffs = ', '.join(str(a) for a in row['coefficients'])
        row_terms.append(f"⟨![{coeffs}], ({row['low']}), ({row['high']})⟩")
    cases = ' | '.join('rfl' for _ in row_terms)
    return verify_interval(n, bounds, proof, 'QuarticLevelExclusion', f"""  let rows : List PrimeFactors.QuarticLevelExclusion.Row := [{', '.join(row_terms)}]
  apply PrimeFactors.QuarticLevelExclusion.odd_interval_excludes
    (rows := rows) (c := {center}) (l := ({left})) (u := ({right}))
    (t := ({sample['anchor']})) (m := {sample['modulus']}) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ d lo hi
  all_goals first | decide +kernel | skip
  intro r hr
  simp only [rows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with {cases}
  all_goals constructor
  all_goals first | (unfold PrimeFactors.QuarticDivisorWindow.jets; decide +kernel) | decide +kernel""")


def check_quartic_interval(n, work, proof):
    if work['stride'] != 2 or work['rootless_modulus'] is None:
        raise ValueError('Expected an odd progression and a modular exclusion witness')
    coefficients = ', '.join(str(a) for a in work['coefficients'])
    return verify_interval(n, work, proof, 'QuarticDivisorWindow', f"""  apply PrimeFactors.QuarticDivisorWindow.odd_interval_excludes
    (v := ![{coefficients}]) (c := {work['center']}) (W := {work['radius']})
    (t := ({work['anchor']})) (m := {work['rootless_modulus']})
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ d lo hi
  all_goals first | (unfold PrimeFactors.QuarticDivisorWindow.jets; decide +kernel) | decide +kernel""")


def chebyshev_quartic_cuts(work, limit=64):
    """Cover a measured quartic by bounded Bernstein certificates for both strict margins."""
    if (work['degree'], work['depth']) != (4, 2) or not work['short'] or not work['excluded']:
        raise ValueError('Expected a short exclusion quartic of depth two')
    c, radius = work['center'], work['radius']
    square = [c*c, 4*c, 4, 0, 0]
    margins = [[a+sign*b for a, b in zip(square, work['coefficients'])] for sign in (-1, 1)]
    pending = [(-radius, radius)]
    ends = []
    tests = 0
    while pending:
        left, right = pending.pop()
        tests += 1
        if all(_bernstein_positive(poly, left, right) for poly in margins):
            ends.append(right)
        elif left < right and len(ends)+len(pending)+2 <= limit:
            mid = (left+right)//2
            pending.extend([(mid+1, right), (left, mid)])
        else:
            raise ValueError('Failed to certify both quartic margins within the subdivision budget')
    return ends[:-1], tests


def check_chebyshev_quartic(n, work, proof):
    cuts, tests = chebyshev_quartic_cuts(work)
    coefficients = ', '.join(map(str, work['coefficients']))
    exclusion = verify_interval(n, work, proof, 'QuarticIntervalExtension', f"""  apply PrimeFactors.QuarticIntervalExtension.odd_interval_excludes
    (v := ![{coefficients}]) (c := {work['center']}) (cuts := [{', '.join(map(str,cuts))}])
    (l := (-{work['radius']})) (u := {work['radius']}) (t := ({work['anchor']}))
    (m := {work['rootless_modulus']}) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ d lo hi
  all_goals first | (unfold PrimeFactors.QuarticDivisorWindow.jets; decide +kernel) | decide +kernel""")
    return dict(exclusion, certified_blocks=len(cuts)+1, bernstein_tests=tests)


def check_extended_interval(n, work, proof):
    """Verify both the interval exclusion and the first failing index on each side."""
    if not (work['excluded'] and work['left_neighbor_fails'] and work['right_neighbor_fails']):
        raise ValueError('Expected an empty interval with two confirmed maximal boundaries')
    coeffs = ', '.join(str(a) for a in work['coefficients'])
    cuts = ', '.join(str(x) for x in work['cuts'])
    theorem = 'PrimeFactors.Generated.extended_divisor_interval'
    proof.write_text(f"""import PrimeFactors.QuarticIntervalExtension

open PrimeFactors.QuarticFactorLane PrimeFactors.QuarticDivisorWindow PrimeFactors.QuarticIntervalExtension
set_option maxRecDepth 16384
set_option exponentiation.threshold 16384

private def row : Fin 5 → ℤ := ![{coeffs}]
private def center : ℕ := {work['center']}
private def firstOffset : ℤ := {work['first_offset']}
private def lastOffset : ℤ := {work['last_offset']}
private def cuts : List ℤ := [{cuts}]
private theorem passes : covered row center 2 firstOffset lastOffset cuts = true := by decide +kernel

theorem {theorem} :
    (∀ d : ℕ, {work['lower']} ≤ d → d ≤ {work['upper']} → ¬ d ∣ {n}) ∧
    (∀ x : ℤ, firstOffset≤x → x≤lastOffset → |value (weights row) 1 x| < ((center:ℤ)+2*x)^2) ∧
    (∀ a b : ℤ, a≤firstOffset → lastOffset≤b →
      (∀ x : ℤ, a≤x → x≤b → |value (weights row) 1 x| < ((center:ℤ)+2*x)^2) →
      a=firstOffset ∧ b=lastOffset) := by
  constructor
  · intro d lo hi
    apply PrimeFactors.QuarticIntervalExtension.odd_interval_excludes (v:=row) (c:=center)
      (l:=firstOffset) (u:=lastOffset) (cuts:=cuts) (t:=({work['anchor']})) (m:={work['rootless_modulus']})
      ?_ ?_ ?_ ?_ passes ?_ ?_ ?_ ?_ d lo hi
    all_goals first | (unfold jets; decide +kernel) | decide +kernel
  · exact maximal_component (by decide +kernel) passes (by decide +kernel) (by decide +kernel)

#print axioms {theorem}
""")
    return verified_interval(work, proof, theorem)


def short_basis_case(case, proof):
    start = time.perf_counter()
    run = short_basis_search(int(case['n']), case['m'], case['m0'], case['primes'],
                             case['max_bad'], exceptional=case['use_exceptional'])
    elapsed = time.perf_counter() - start
    ordinary = run['ordinary']
    exceptional = run.get('exceptional', {})
    fallback = run.get('fallback', {})
    hits = [ordinary['first'], *(sweep['power'] for sweep in exceptional.values()), fallback.get('first')]
    factor = next((hit['factor'] for hit in hits if hit is not None), None)
    work = dict(run, ordinary_gcds=ordinary['work'].get('pair_gcds', 0),
                exceptional_gcds=sum(sweep['work']['pair_gcds'] for sweep in exceptional.values()),
                fallback_gcds=fallback.get('work', {}).get('pair_gcds', 0),
                use_exceptional=case['use_exceptional'])
    agree(case, work, ['sparse_entries', 'ordinary_gcds', 'exceptional_gcds', 'fallback_gcds'])
    return certify_split(case, proof, factor, elapsed, 'short_basis', work)


def run_case(case, method, proofs):
    name = case['id']
    if not re.fullmatch(r'[a-zA-Z0-9_-]+', name):
        raise ValueError(f'Invalid benchmark ID {name!r}')
    proof = proofs / f'{name}.lean'
    start = time.perf_counter()
    complete = case['status'] == 'complete'
    if method == 'midpoint-weights':
        work = weight_orbit_search(int(case['n']), case.get('max_orbits'),
                                   reduce_discriminant=case.get('reduce_discriminant', False),
                                   curve=case.get('curve', False))
        elapsed = time.perf_counter() - start
        pairs = work.pop('pairs')
        agree(case, work, ['total_orbits', 'visited_orbits', 'candidate_traces', 'square_tests'])
        result = certify_split(case, proof, pairs[0][0] if pairs else None, elapsed, 'midpoint_weights', work)
    elif method == 'complete-offset-search':
        work = complete_offset_search(int(case['n']), case['max_pairs'],
                                      filter_prime_limit=case.get('filter_prime_limit'))
        elapsed = time.perf_counter() - start
        agree(case, work, ['max_offset', 'raw_pairs', 'loose_raw_pairs', 'visited_pairs',
                           'coprime_pairs', 'negative_discriminants', 'integer_square_roots',
                           'square_hits', 'proper_hits', 'unvisited_pairs'])
        if 'filter_prime_limit' in case:
            agree(case, work, ['covered_pairs', 'skipped_pairs', 'skipped_rows'])
        result = certify_split(case, proof, work.pop('factor'), elapsed, 'complete_offset', work)
    elif method == 'offset-winner-window':
        work = offset_winner_window_search(int(case['n']), case['max_visits'], equal_width=case['equal_width'])
        elapsed = time.perf_counter() - start
        agree(case, work, ['raw_slots', 'coordinate_visits_upper', 'visited_pairs', 'coordinate_rows',
                           'coprime_vectors', 'coprime_slots', 'square_tests', 'square_hits', 'proper_hits',
                           'unvisited_upper', 'exhaustive', 'next_coordinate'])
        result = certify_split(case, proof, work.pop('factor'), elapsed, 'offset_winner_window', work)
    elif method == 'offset-coordinate-gaps':
        work = offset_coordinate_gap_search(int(case['n']), case['parts'], max_vectors=case['max_vectors'],
                                            max_tests=case['max_tests'], all_vectors=case['all_vectors'],
                                            tilted=case['tilted'], lift_cap=case.get('lift_cap', 1),
                                            split_only=case.get('split_only', False),
                                            unit_square=case.get('unit_square', 1),
                                            trace_units=case.get('trace_units', False))
        elapsed = time.perf_counter() - start
        hits = work.pop('hits')
        work['proper_hits'] = len(hits)
        agree(case, work, work.keys())
        factor = int(hits[0][2]) if hits else None
        result = certify_split(case, proof, factor, elapsed, 'offset_coordinate_gaps', work)
    elif method in ('offset-arc-lines', 'offset-tangent-cover'):
        settings = {key: case[key] for key in ('all_vectors', 'max_vectors', 'lift_cap', 'unit_square', 'trace_units')}
        if method == 'offset-arc-lines':
            work = offset_arc_line_search(int(case['n']), case['parts'], max_tests=case['max_tests'],
                                          hybrid=case['hybrid'], **settings)
        else:
            work = offset_tangent_cover_search(int(case['n']), max_arcs=case['max_arcs'],
                                              shifted_base=case.get('shifted_base', False), **settings)
        elapsed = time.perf_counter() - start
        hits = work.pop('hits')
        work.update(proper_hits=len(hits), first_hit=hits[0][:2] if hits else None)
        agree(case, work, work)
        factor = int(hits[0][2]) if hits else None
        result = certify_split(case, proof, factor, elapsed, method.replace('-', '_'), work)
    elif method == 'offset-trace-words':
        work = offset_trace_word_search(int(case['n']), prime_limit=case['prime_limit'],
                                        max_word_bits=case['max_word_bits'], max_pairs=case['max_pairs'])
        elapsed = time.perf_counter() - start
        factor = work.pop('factor')
        agree(case, work, work)
        result = certify_split(case, proof, factor, elapsed, 'offset_trace_words', work)
    elif method == 'offset-factor-blocks':
        from_end = case.get('from_end', False)
        work = offset_factor_block_search(
            int(case['n']), max_blocks=case['max_blocks'], start_block=0 if from_end else case['start_block'],
            from_end=from_end, max_tests=case['max_tests'], shifted=case['shifted'], parity=case['parity'],
            coalesce=case.get('coalesce', False), max_reductions=case.get('max_reductions'))
        elapsed = time.perf_counter() - start
        hits = work.pop('hits')
        work.update(proper_hits=len(hits), first_hit=hits[0][:2] if hits else None)
        agree(case, work, work)
        factor = int(hits[0][2]) if hits else None
        result = certify_split(case, proof, factor, elapsed, 'offset_factor_blocks', work)
    elif method == 'adaptive-quartic-cover':
        n = int(case['n'])
        work = adaptive_quartic_search(n, full=case['full'], mode=case['mode'],
                                      max_reductions=case['max_reductions'], level_cap=case['level_cap'],
                                      chunks_per_basis=case['chunks_per_basis'], sample_certificate=not case['full'])
        elapsed = time.perf_counter() - start
        agree(case, work, ['radius', 'fixed_window_count', 'covered_odd_positions', 'unvisited_prefix_odd',
                           'unvisited_suffix_odd', 'unvisited_odd_positions', 'schedule_exhausted', 'stalled', 'work'])
        sample = work.pop('sample_certificate')
        factor = next((d for d in work['divisors'] if 1 < d < n), None)
        result = certify_split(case, proof, factor, elapsed, 'adaptive_quartic_cover', work)
        if not case['full']:
            result['exclusion'] = check_quartic_levels(n, sample, proof)
    elif method == 'divisor-product-derivative':
        work = compare_product_digits(int(case['n']), case['max_candidates'])
        elapsed = time.perf_counter()-start
        digit = work['digit']
        agree(case, digit, ['outcome', 'candidates', 'full_candidates', 'products', 'product_gcd',
                            'digit0', 'digit1', 'factor_sum', 'work'])
        agree(case, dict(unvisited=digit['remaining'], **work), ['unvisited', 'whole_band', 'through_sqrt', 'trial'])
        result = certify_split(case, proof, digit['factor'], elapsed, 'divisor_product_derivative', work)
    elif method == 'paired-divisor-windows':
        work = compare_paired_windows(int(case['n']), half_separation=case['half_separation'], radius=case['radius'])
        elapsed = time.perf_counter()-start
        agree(case, work, ['center', 'height', 'height_bound', 'relation_verified', 'divisors', 'roots', 'work', 'ordinary'])
        factor = next((d for d in work['divisors'] if 1 < d < int(case['n'])), None)
        result = certify_split(case, proof, factor, elapsed, 'paired_divisor_windows', work)
    elif method == 'chebyshev-divisor-window':
        n = int(case['n'])
        center, radius = odd_quartile_center(n), int(case['radius'])
        parameters = dict(degree=case['degree'], depth=case['depth'], modulus_limit=case['modulus_limit'])
        work = higher_window_search(n, center, radius, chebyshev=True, **parameters)
        ordinary = higher_window_search(n, center, radius, **parameters)
        elapsed = time.perf_counter()-start
        work['ordinary'] = {k: ordinary[k] for k in ('short', 'height', 'rootless_modulus', 'work')}
        agree(case, work, ['center', 'progression_size', 'short', 'height', 'ordinary_height',
                           'rootless_modulus', 'work', 'ordinary'])
        factor = next((d for d in work['divisors'] if 1 < d < n), None)
        result = certify_split(case, proof, factor, elapsed, 'chebyshev_divisor_window', work)
        if work['rootless_modulus'] is not None:
            result['exclusion'] = check_chebyshev_quartic(n, work, proof)
    elif method == 'higher-divisor-window':
        n = int(case['n'])
        work = higher_window_search(n, odd_quartile_center(n), int(case['radius']), degree=case['degree'],
                                    depth=case['depth'], modulus_limit=case['modulus_limit'])
        elapsed = time.perf_counter() - start
        agree(case, work, ['center', 'progression_size', 'short', 'rootless_modulus', 'work'])
        factor = next((d for d in work['divisors'] if 1 < d < n), None)
        result = certify_split(case, proof, factor, elapsed, 'higher_divisor_window', work)
        if work['rootless_modulus'] is not None:
            result['exclusion'] = check_higher_interval(n, work, proof, verify_interval)
    elif method == 'quartic-three-row':
        work = three_row_search(int(case['n']), schedule=case['schedule'], blocks=case['blocks'])
        elapsed = time.perf_counter() - start
        agree(case, work, ['radius', 'first_center', 'max_blocks', 'total_blocks', 'visited_blocks',
                           'unvisited_prefix_blocks', 'unvisited_suffix_blocks', 'unvisited_blocks',
                           'schedule_exhausted', 'work'])
        result = certify_split(case, proof, work['factor'], elapsed, 'quartic_three_row', work)
    elif method == 'quartic-minor-gcd':
        n = int(case['n'])
        work = minor_gcd_search(n, full=case['full'], blocks=case['blocks'])
        elapsed = time.perf_counter()-start
        agree(case, work, ['radius', 'first_center', 'max_blocks', 'visited_blocks', 'total_blocks',
                           'unvisited_prefix_blocks', 'unvisited_suffix_blocks', 'unvisited_blocks',
                           'visited_odd_integers', 'unvisited_odd_integers', 'schedule_exhausted', 'work'])
        result = certify_split(case, proof, work['factor'], elapsed, 'quartic_minor_gcd', work)
    elif method == 'quartic-basis-translation':
        n = int(case['n'])
        work = translated_window_search(n, full=case['full'], blocks=case['blocks'])
        elapsed = time.perf_counter()-start
        agree(case, work, ['radius', 'range_lower', 'range_upper', 'first_odd', 'last_odd',
                           'even_integers', 'first_center', 'available_blocks', 'total_blocks', 'max_blocks',
                           'visited_blocks', 'unvisited_prefix_blocks', 'unvisited_suffix_blocks',
                           'unvisited_blocks', 'visited_odd_integers', 'unvisited_odd_integers',
                           'unresolved_odd_integers', 'exhausted', 'first_swaps', 'later_swaps',
                           'max_later_swaps', 'work'])
        factor = next((d for d in work['divisors'] if 1 < d < n), None)
        result = certify_split(case, proof, factor, elapsed, 'quartic_basis_translation', work)
    elif method == 'quartic-window-extension':
        n = int(case['n'])
        window = quartic_window_search(n, odd_quartile_center(n), int(case['radius']),
                                      modulus_limit=case['modulus_limit'])
        work = extend_quartic_window(window)
        elapsed = time.perf_counter()-start
        agree(case, work, ['lower', 'upper', 'progression_size', 'interval_size', 'previous_progression_size',
                           'certified_blocks', 'bernstein_tests', 'sign_evaluations', 'additional_lll_calls',
                           'integer_root_nodes', 'divisor_tests', 'left_neighbor_fails', 'right_neighbor_fails',
                           'rootless_residue_checks', 'excluded', 'rootless_modulus'])
        work['initial_lll_calls'] = window['lll_calls']
        work['initial_lll_reductions'] = window['lll_reductions']
        work['initial_lll_swaps'] = window['lll_swaps']
        factor = next((d for d in work['divisors'] if 1 < d < n), None)
        result = certify_split(case, proof, factor, elapsed, 'quartic_window_extension', work)
        if work['excluded'] and work['rootless_modulus'] is not None:
            result['exclusion'] = check_extended_interval(n, work, proof)
    elif method == 'quartic-divisor-window':
        n = int(case['n'])
        center = odd_quartile_center(n) if case['use_odd_quartile'] else int(case['center'])
        work = quartic_window_search(n, center, int(case['radius']), stride=case['stride'],
                                    modulus_limit=case['modulus_limit'])
        elapsed = time.perf_counter() - start
        agree(case, work, ['center', 'lower', 'upper', 'interval_size', 'progression_size', 'covers_interval',
                           'height', 'relation_verified', 'anchor_inversions', 'basis_dimension', 'rows_compared',
                           'jet_checks', 'lll_calls', 'lll_reductions', 'lll_swaps', 'integer_root_nodes',
                           'divisor_tests', 'moduli_tested', 'modular_evaluations', 'rootless_modulus',
                           'progression_excluded', 'excluded'])
        factor = next((d for d in work['divisors'] if 1 < d < n), None)
        result = certify_split(case, proof, factor, elapsed, 'quartic_divisor_window', work)
        if 'interval_proof_modulus' in case:
            if work['rootless_modulus'] != case['interval_proof_modulus']:
                raise ValueError('The quartic modular witness did not match the fixture')
            result['exclusion'] = check_quartic_interval(n, work, proof)
    elif method in ('weighted-divisor-exclusion', 'arbitrary-divisor-window'):
        n = int(case['n'])
        if method == 'weighted-divisor-exclusion':
            work = weighted_divisor_search(n, case['a'], case['b'], int(case['radius']),
                                           max_trace_tests=case['max_trace_tests'], modulus=case.get('modulus'))
            counters = ['total_traces', 'tested_traces', 'remaining_traces', 'modular_rejections']
            first, count = work['first_trace'], work['total_traces']
        else:
            center = quartile_center(n) if case['use_quartile'] else int(case['center'])
            work = arbitrary_window_search(n, center, int(case['radius']), mod24=case.get('mod24', False))
            counters = ['convergent_steps', 'endpoint_tests', 'possible_traces', 'candidate_tests', 'divisor_tests']
            if case.get('mod24'):
                counters.append('trace_stride')
            first, count = work['trace'], 1
        elapsed = time.perf_counter() - start
        agree(case, work, ['lower', 'upper', 'square_tests', 'excluded', *counters])
        factor = next((d for d in work['divisors'] if 1 < d < n), None)
        result = certify_split(case, proof, factor, elapsed, method.replace('-', '_'), work)
        if 'interval_proof_modulus' in case:
            result['exclusion'] = check_divisor_interval(n, work, first, count, case['interval_proof_modulus'], proof)
    elif method == 'offset-crt':
        work = offset_crt_search(int(case['n']), case['max_tuples'], exhaust=case['exhaust'],
                                 optimize_wheel=case.get('optimize_wheel', False))
        elapsed = time.perf_counter() - start
        agree(case, work, ['total_tuples', 'visited_tuples', 'unchecked_tuples', 'convergents',
                           'reconstructed', 'square_tests', 'proper_hits', 'raw_slots', 'first_hit'])
        if case.get('optimize_wheel'):
            agree(case, work, ['baseline_tuples', 'wheel_work'])
        result = certify_split(case, proof, work.pop('factor'), elapsed, 'offset_crt', work)
    elif method == 'offset-lattice-batches':
        work = offset_lattice_search(int(case['n']), case['max_batches'], drop=case['drop'],
                                     max_events=case['max_events'], exhaust=case['exhaust'],
                                     dyadic_exponent=case.get('dyadic_exponent'),
                                     primitive_rows=case.get('primitive_rows', False))
        elapsed = time.perf_counter() - start
        agree(case, work, ['raw_slots', 'full_tuples', 'total_batches', 'started_batches',
                           'completed_batches', 'unfinished_batches', 'gauss_iterations', 'rows',
                           'rejected_rows', 'point_visits', 'primitive_points', 'deferred_checks',
                           'pivot_prime_tests', 'row_divisibility_tests', 'square_tests', 'proper_hits',
                           'first_hit', 'deferred_primes', 'wheel_work'])
        if case.get('dyadic_exponent'):
            agree(case, work, ['charts', 'setup', 'odd_only_tuples'])
        if case.get('primitive_rows'):
            agree(case, work, ['normalized_prime_tests', 'normalized_mod_tests',
                               'determinant_rejections', 'valuation_rejections'])
        result = certify_split(case, proof, work.pop('factor'), elapsed, 'offset_lattice', work)
    elif method == 'offset-row-geometry':
        work = offset_row_geometry_search(int(case['n']), case['max_batches'], drop=case['drop'],
                                          reserve_size=case['reserve_size'], max_events=case['max_events'],
                                          exhaust=case['exhaust'])
        elapsed = time.perf_counter() - start
        agree(case, work, ['baseline_batches', 'total_batches', 'started_batches', 'completed_batches',
                           'unfinished_batches', 'full_tuples', 'minimum_modulus', 'raw_slots', 'first_hit',
                           'proper_hits', 'rows', 'rejected_rows', 'point_visits', 'primitive_points',
                           'deferred_checks', 'second_digit_checks', 'square_tests', 'reserve_primes',
                           'work', 'wheel_work'])
        result = certify_split(case, proof, work.pop('factor'), elapsed, 'offset_row_geometry', work)
    elif method == 'offset-dyadic':
        work = offset_dyadic_search(int(case['n']), case['max_per_chart'], max_exponent=case['max_exponent'])
        elapsed = time.perf_counter() - start
        agree(case, work, ['odd_only_tuples', 'total_tuples', 'visited_tuples', 'unchecked_tuples',
                           'reconstructed', 'square_tests', 'proper_hits'])
        for chart, expected in case['charts'].items():
            agree(dict(expected, id=case['id']+'-'+chart), work['charts'][chart], expected)
        result = certify_split(case, proof, work.pop('factor'), elapsed, 'offset_dyadic', work)
    elif method == 'offset-prime-power':
        work = offset_prime_power_search(int(case['n']), case['max_tuples'], exhaust=case['exhaust'])
        elapsed = time.perf_counter() - start
        work['lifts'] = [[p, e] for p, e in work['powers'] if e > 1]
        agree(case, work, ['total_tuples', 'visited', 'unchecked', 'square_tests', 'distinct_count',
                           'selection_queries', 'right_subsets', 'all_powers_lower', 'lifts'])
        result = certify_split(case, proof, work.pop('factor'), elapsed, 'offset_prime_power', work)
    elif method == 'offset-rows':
        n = int(case['n'])
        T = isqrt(n)
        options = {}
        if case.get('choose_frame'):
            selected = choose_frame(T, n-T*T, case['max_offset'])
            options['basis'] = selected['basis']
            if selected['eligible']:
                options['max_prefix'] = selected['cap']
        work = bounded_rows(T, n-T*T, case['max_offset'], None,
                            max_square_tests=case['max_square_tests'], **options)
        elapsed = time.perf_counter()-start
        agree(case, work, ['raw', 'primitive', 'both_axes', 'rows'])
        search = work['search']
        agree(case, search, ['square_tests'])
        result = certify_split(case, proof, search['factor'], elapsed, 'offset_rows', work)
    elif method == 'grouped-norm':
        run = subprocess.run(
            ['lake', 'env', 'lean', '--run', 'experiments/GroupedNormProbe.lean', case['n']],
            cwd=ROOT, text=True, capture_output=True, check=True, timeout=120)
        work = json.loads(run.stdout)
        pair = work.pop('pair')
        elapsed = work.pop('search_ns') / 1_000_000_000
        agree(case, work, ['eligible_multipliers', 'square_tests'])
        if pair is not None and (len(pair) != 2 or int(pair[0]) * int(pair[1]) != int(case['n'])):
            raise ValueError(f"{name}: incorrect product from the Lean probe")
        result = certify_split(case, proof, pair[0] if pair else None, elapsed, 'grouped_norm', work)
    elif method == 'projected-level-sieve':
        run = projected_level_search(int(case['n']), 1 << case['radix_exponent'], int(case['residue']),
                                     max_levels=case['max_levels'])
        pairs = run.pop('pairs')
        elapsed = run.pop('search_seconds')
        agree(case, {'expected_pairs': pairs}, ['expected_pairs'])
        agree(case, run, ['work', 'total_levels', 'unexamined_levels', 'other_positive_groups'])
        result = certify_split(case, proof, pairs[0][0] if pairs else None, elapsed, 'projected_levels', run)
    elif method in ('unit-quartic', 'centered-quartic'):
        n, u = int(case['n']), int(case['residue'])
        if method == 'centered-quartic':
            run = centered_quartic_probe(n, u)
            agree(case, run, ['radix_exponent', 'total_groups', 'unchecked_groups'])
        else:
            run = unit_quartic_probe(n, 1 << case['radix_exponent'], u)
            agree(case, run, ['total_signed_groups', 'unchecked_signed_groups'])
        elapsed = run.pop('search_seconds')
        pairs = run.pop('pairs')
        agree(case, {'expected_pairs': pairs}, ['expected_pairs'])
        agree(case, run, ['work', 'local_remainders'])
        result = certify_split(case, proof, pairs[0][0] if pairs else None, elapsed, method.replace('-', '_'), run)
    elif method == 'quartic-factor-lanes':
        if case.get('unit_residue'):
            work = unit_lane_search(int(case['n']))
        elif case.get('basis') in ('gap-newton', 'dickson-newton'):
            work = gap_lane_search(int(case['n']), case['max_orbits'], power=case['power'],
                                   basis=case['basis'].split('-')[0])
        else:
            work = quartic_lane_search(int(case['n']), case['max_orbits'], power=case['power'],
                                       signed=case.get('signed', False), basis=case.get('basis', 'taylor'))
        elapsed = time.perf_counter() - start
        pairs = work.pop('pairs')
        agree(case, {'expected_pairs': pairs}, ['expected_pairs'])
        agree(case, work, list(work))
        work.update(max_orbits=case['max_orbits'], pairs=pairs)
        result = certify_split(case, proof, pairs[0][0] if pairs else None, elapsed,
                               'quartic_factor_lanes', work)
    elif method == 'midpoint-slope-batches':
        settings = {k: case[k] for k in ('multiplier', 'max_half_entries')}
        settings.update({k: case[k] for k in ('geometry', 'curve') if k in case})
        work = slope_batch_search(int(case['n']), **settings)
        elapsed = time.perf_counter() - start
        pairs = work.pop('pairs')
        agree(case, work, list(work))
        work.update(settings)
        result = certify_split(case, proof, pairs[0][0] if pairs else None, elapsed,
                               'midpoint_slope_batches', work)
    elif method == 'class-orders':
        work = class_order_search(int(case['n']), case['prime_limit'], case['max_compositions'], case['shared'])
        elapsed = time.perf_counter() - start
        factor = work.pop('factor')
        agree(case, work, ['outcome', 'compositions', 'windows'])
        result = certify_split(case, proof, factor, elapsed, 'class_orders', work)
    elif method == 'modular-hyperbola':
        work = hyperbola_search(int(case['n']), radix_policy=case.get('radix_policy', 'binary'))
        elapsed = time.perf_counter() - start
        pairs = work.pop('pairs')
        agree(case, work, ['low_classes', 'modular_hits'])
        if 'radix' in case:
            agree(case, work, ['radix', 'euclidean_steps'])
        factor = pairs[0][0] if pairs else None
        result = certify_split(case, proof, factor, elapsed, 'hyperbola', work)
    elif method == 'quotient-search':
        work = quotient_search(int(case['n']), case['width'], wheel=case['wheel'])
        elapsed = time.perf_counter() - start
        pairs = work.pop('pairs')
        checks = ['blocks', 'initial_strip_points', 'quadratic_solves', 'bisected']
        if 'collinear_beyond_area' in case:
            checks.append('collinear_beyond_area')
        agree(case, work, checks)
        found = work['setup_divisor'] or (pairs[0][0] if pairs else None)
        factor = int(found) if found is not None else None
        result = certify_split(case, proof, factor, elapsed, 'quotient_search', work)
    elif method == 'pell-local-windows':
        work = pell_window_search(int(case['n']), case['max_steps'], case['depth'])
        elapsed = time.perf_counter() - start
        agree(case, work, ['steps', 'pairs', 'candidates', 'root_tests'])
        hits = [hit for hit in (work['ordinary_pair'], work['shifted_pair']) if hit]
        first = min(hits, key=lambda hit: hit['j'], default=None)
        work.update(max_steps=case['max_steps'], depth=case['depth'])
        result = certify_split(case, proof, first['factor'] if first else None, elapsed,
                               'pell_windows', work)
    elif method == 'pell-pairs':
        work = pell_pair_search(int(case['n']), case['max_prime'], case['max_steps'], case['triangles'])
        elapsed = time.perf_counter() - start
        factor = work.pop('factor')
        agree(case, work, ['outcome', 'steps', 'walks', 'centers', 'cycles', 'root'])
        work.update(max_steps=case['max_steps'], max_prime=case['max_prime'], triangles=case['triangles'])
        result = certify_split(case, proof, factor, elapsed, 'pell_pairs', work)
    elif method == 'pell-relations':
        work = pell_relation_search(int(case['n']), case['multiplier'], case['max_steps'])
        elapsed = time.perf_counter() - start
        factor = work.pop('factor')
        agree(case, work, list(work))
        work.update(max_steps=case['max_steps'], multiplier=case['multiplier'])
        result = certify_split(case, proof, factor, elapsed, 'pell_relations', work)
    elif method == 'weighted-base':
        settings = {k: case[k] for k in ('k', 'baby_steps', 'max_giants', 'prime_limit', 'max_primes', 'stride')}
        run = weighted_base_selection.search(int(case['n']), **settings)
        elapsed = time.perf_counter() - start
        selection = run['selection']
        weighted = run['weighted']
        work = dict(outcome=run['outcome'], selection_outcome=selection['outcome'],
                    selected_base=selection['selected_base'], selection_work=selection['work'],
                    weighted_work=weighted['work'] if weighted is not None else None)
        agree(case, work, list(work))
        work.update(settings)
        result = certify_split(case, proof, run['factor'], elapsed, 'weighted_base', work)
    elif method in ('weighted-stride', 'weighted-sparse'):
        settings = {k: case[k] for k in ('k', 'baby_steps', 'max_giants', 'max_slopes', 'beta', 'stride')}
        if method == 'weighted-sparse':
            settings.update(wheel_primes=case['wheel_primes'], max_span=case['max_span'])
        work = weighted_stride_search.search(int(case['n']), **settings)
        elapsed = time.perf_counter() - start
        factor = work.pop('factor')
        agree(case, work, list(work))
        work.update(settings)
        result = certify_split(case, proof, factor, elapsed, 'weighted_stride', work)
    elif method == 'factorial-progressions':
        settings = {k: case[k] for k in ('max_span', 'wheel', 'backend')}
        settings['folded'] = case.get('folded', False)
        work = factorial_progressions.search(int(case['n']), **settings)
        elapsed = time.perf_counter() - start
        factor = work.pop('factor')
        agree(case, work, list(work))
        work.update(settings)
        result = certify_split(case, proof, factor, elapsed, 'factorial_progressions', work)
    elif method == 'extension-trace':
        settings = {k: case[k] for k in ('max_positions', 'max_selector')}
        if case.get('mode', 'smooth') == 'punctured':
            work = extension_trace.punctured_search(int(case['n']), **settings)
        else:
            settings.update(a=case['a'], b=case['b'])
            work = extension_trace.search(int(case['n']), **settings)
        elapsed = time.perf_counter() - start
        factor = work.pop('factor')
        agree(case, work, list(work))
        work.update(settings, mode=case.get('mode', 'smooth'))
        result = certify_split(case, proof, factor, elapsed, 'extension_trace', work)
    elif method == 'local-midpoints':
        work = local_midpoint_search(int(case['n']), case['primes'])
        elapsed = time.perf_counter() - start
        factor = work.pop('factor')
        for key in ('low', 'high', 'candidates', 'survivors'):
            if key in work:
                work[key] = str(work[key])
        agree(case, work, [k for k in ('survivors', 'range_queries', 'square_tests', 'outcome', 'prime_exponent_classes') if k in work])
        result = certify_split(case, proof, factor, elapsed, 'local_midpoints', work)
    elif method == 'quartic-trace':
        settings = {k: case[k] for k in ('max_positions', 'max_selector', 'bits')}
        work = quartic_trace.search(int(case['n']), **settings)
        elapsed = time.perf_counter() - start
        factor = work.pop('factor')
        agree(case, work, list(work))
        work.update(settings)
        result = certify_split(case, proof, factor, elapsed, 'quartic_trace', work)
    elif method == 'reciprocal-wheel':
        settings = {k: case[k] for k in ('wheel', 'width', 'max_blocks')}
        work = reciprocal_wheel.search(int(case['n']), **settings)
        elapsed = time.perf_counter() - start
        factor = work.pop('factor')
        agree(case, work, list(work))
        work.update(settings)
        result = certify_split(case, proof, factor, elapsed, 'reciprocal_wheel', work)
    elif method in ('short-norm-boxes', 'norm-band-product'):
        scan = short_norm_boxes.search if method == 'short-norm-boxes' else norm_band_product.search
        settings = dict(canonical=case.get('canonical', False)) if method == 'norm-band-product' else {}
        work = scan(int(case['n']), case['max_side'], balanced=case['balanced'], **settings)
        elapsed = time.perf_counter() - start
        factor = work.pop('factor')
        agree(case, work, list(work))
        work.update(max_side=case['max_side'], balanced=case['balanced'], **settings)
        result = certify_split(case, proof, factor, elapsed, method.replace('-', '_'), work)
    elif method == 'universal-norms':
        n, cap, mode = int(case['n']), case['max_side'], case['mode']
        if mode == 'universal':
            settings = dict(balanced=case['balanced'])
            work = universal_norm_batch.search(n, cap, **settings)
        elif mode == 'separating':
            settings = dict(max_selector=case['max_selector'])
            work = universal_norm_batch.separating_search(n, cap, **settings)
        else:
            raise ValueError(f"Unknown norm grid mode {mode!r}")
        elapsed = time.perf_counter() - start
        factor = work.pop('factor')
        agree(case, work, list(work))
        work.update(mode=mode, max_side=cap, **settings)
        result = certify_split(case, proof, factor, elapsed, 'universal_norms', work)
    elif method == 'norm-curves':
        n, last_prime, max_blocks = int(case['n']), case['last_prime'], case['max_blocks']
        mode = case['mode']
        if mode == 'residues':
            settings = dict(degree=case['degree'])
            work = norm_residue_curves.search(n, last_prime, max_blocks, **settings)
        elif mode == 'sectors':
            settings = dict(reuse_basis=case['reuse_basis'])
            work = norm_direction_search(n, last_prime, max_blocks,
                                         scanner=partial(norm_auxiliary.scan, **settings),
                                         work_counts=norm_auxiliary.EXTRA_COUNTERS)
        else:
            raise ValueError(f"Unknown norm-curve search mode {mode!r}")
        elapsed = time.perf_counter() - start
        factor = work.pop('factor')
        agree(case, work, list(work))
        work.update(mode=mode, max_blocks=max_blocks, last_prime=last_prime, **settings)
        result = certify_split(case, proof, factor, elapsed, 'norm_curves', work)
    elif method == 'norm-directions':
        work = norm_direction_search(int(case['n']), case['last_prime'], case['max_blocks'])
        elapsed = time.perf_counter() - start
        factor = work.pop('factor')
        agree(case, work, list(work))
        work.update(last_prime=case['last_prime'], max_blocks=case['max_blocks'],
                    coordinate_positions=str(work['coordinate_positions']))
        result = certify_split(case, proof, factor, elapsed, 'norm_directions', work)
    elif method == 'polynomial-packets':
        work = polynomial_packet_search(int(case['n']), int(case['coefficient']),
                                        int(case['max_norm']), case['max_lifts'])
        elapsed = time.perf_counter() - start
        factor = work.pop('factor')
        agree(case, work, list(work))
        work.update(coefficient=case['coefficient'], max_norm=case['max_norm'],
                    max_lifts=case['max_lifts'])
        result = certify_split(case, proof, factor, elapsed, 'polynomial_packet', work)
    elif method == 'polynomial-relations':
        mode, policy = case['mode'], case['policy']
        work = polynomial_relation_search(int(case['n']), mode, case['bound'], case['radius'],
                                          case['max_blocks'], policy=policy)
        elapsed = time.perf_counter() - start
        factor = work.pop('factor')
        stats = work.pop('policies').get(policy)
        if stats is not None:
            work.update({k: v for k, v in stats.items() if k != 'factor'})
        agree(case, work, list(work))
        work.update(mode=mode, policy=policy, bound=case['bound'], radius=case['radius'],
                    max_blocks=case['max_blocks'])
        result = certify_split(case, proof, factor, elapsed, 'polynomial_relations', work)
    elif method == 'seed-gap-sieve':
        work = seed_gap_search(int(case['n']), case['max_norm'], case['last_prime'])
        elapsed = time.perf_counter() - start
        factor = work.pop('factor')
        agree(case, work, list(work))
        work.update(max_norm=case['max_norm'], last_prime=case['last_prime'])
        result = certify_split(case, proof, factor, elapsed, 'seed_gap_sieve', work)
    elif method == 'guided-pairs':
        work = guided_pair_cover(int(case['n']), case['max_norm'], case['max_multipliers'])
        elapsed = time.perf_counter() - start
        factor = work.pop('factor')
        agree(case, work, list(work))
        work.update(max_norm=case['max_norm'], max_multipliers=case['max_multipliers'])
        result = certify_split(case, proof, factor, elapsed, 'guided_pairs', work)
    elif method == 'same-source-pairs':
        work = same_source_pair_search(int(case['n']), case['mode'], case['max_draws'])
        elapsed = time.perf_counter() - start
        factor = work.pop('factor')
        agree(case, work, list(work))
        work.update(mode=case['mode'], max_draws=case['max_draws'])
        result = certify_split(case, proof, factor, elapsed, 'same_source_pairs', work)
    elif method in ('rational-squares', 'fraction-chains'):
        run = rational_square_search if method == 'rational-squares' else fraction_chain_search
        work = run(int(case['n']), case['mode'], case['max_draws'], case['bound'], online=case['online'])
        elapsed = time.perf_counter() - start
        factor = work.pop('factor')
        agree(case, work, list(work))
        work.update(mode=case['mode'], max_draws=case['max_draws'], bound=case['bound'], online=case['online'])
        result = certify_split(case, proof, factor, elapsed, method.replace('-', '_'), work)
    elif method == 'scored-multipliers':
        work = scored_multiplier_search(int(case['n']), case['mode'], case['max_steps'])
        elapsed = time.perf_counter() - start
        factor = work.pop('factor')
        agree(case, work, list(work))
        work.update(mode=case['mode'], max_steps=case['max_steps'])
        result = certify_split(case, proof, factor, elapsed, 'scored_multipliers', work)
    elif method == 'crt-square-norms':
        work = crt_square_search(int(case['n']), case['prime_count'], case['threshold_bits'],
                                 case['hit_cap'], subset_size=case.get('subset_size'))
        elapsed = time.perf_counter() - start
        factor = work.pop('factor')
        agree(case, work, list(work))
        work.update(prime_count=case['prime_count'], threshold_bits=case['threshold_bits'],
                    hit_cap=case['hit_cap'], subset_size=case.get('subset_size'))
        result = certify_split(case, proof, factor, elapsed, 'crt_square_norms', work)
    elif method == 'pooled-relations':
        work = pooled_relation_search(int(case['n']), case['multipliers'], case['max_steps'])
        elapsed = time.perf_counter() - start
        factor = work.pop('factor')
        agree(case, work, list(work))
        work.update(multipliers=case['multipliers'], max_steps=case['max_steps'])
        result = certify_split(case, proof, factor, elapsed, 'pooled_relations', work)
    elif method == 'four-square-lines':
        work = four_square_line_search(int(case['n']), case['max_triples'])
        elapsed = time.perf_counter() - start
        factor = work.pop('factor')
        agree(case, work, list(work))
        work['max_triples'] = case['max_triples']
        result = certify_split(case, proof, factor, elapsed, 'four_square_lines', work)
    elif method == 'line-powers':
        work = line_power_search(int(case['n']), case['exponent'], case['start'], case['max_seeds'])
        elapsed = time.perf_counter() - start
        factor = work.pop('factor')
        agree(case, work, ['outcome', 'seed', 'work'])
        work.update(exponent=case['exponent'], start=case['start'], max_seeds=case['max_seeds'])
        result = certify_split(case, proof, factor, elapsed, 'line_powers', work)
    elif method in ('theta-residues', 'partition-recurrence'):
        search = theta_residue_search if method == 'theta-residues' else partition_recurrence_search
        work = search(int(case['n']), case['max_index'])
        elapsed = time.perf_counter() - start
        factor = work.pop('factor')
        agree(case, work, list(work))
        work['max_index'] = case['max_index']
        result = certify_split(case, proof, factor, elapsed, method.replace('-', '_'), work)
    elif method == 'salie-blocks':
        work = salie_block_search(int(case['n']), case['max_orbits'], case['fractional_bits'])
        elapsed = time.perf_counter() - start
        factor = work.pop('factor')
        agree(case, work, list(work))
        result = certify_split(case, proof, factor, elapsed, 'salie_blocks', work)
    elif method in ('salie-seed', 'folded-square'):
        search = salie_seed_search if method == 'salie-seed' else fixed_phase_search
        work = search(int(case['n']), case['max_terms'])
        elapsed = time.perf_counter() - start
        factor = work.pop('factor')
        agree(case, work, list(work))
        work['max_terms'] = case['max_terms']
        result = certify_split(case, proof, factor, elapsed, method.replace('-', '_'), work)
    elif method in ('divisor-samples', 'salie-residues'):
        search, key = ((salie_residue_search, 'salie_residues') if method == 'salie-residues'
                       else (divisor_sample_search, 'divisor_samples'))
        work = search(int(case['n']), case['max_terms'])
        elapsed = time.perf_counter() - start
        factor = work.pop('factor')
        common = ['outcome', 'root', 'terms', 'sums', 'unit_gcds', 'inverses',
                  'jacobi_evaluations', 'frequency_gcds']
        counters = (['multiplier', 'coefficient', 'prime_gcds', 'frequency_inverses',
                     'crt_updates', 'square_tests', 'prime_count', 'last_prime', 'max_precision_bits']
                    if method == 'salie-residues' else ['anchor'])
        agree(case, work, common + counters)
        work['max_terms'] = case['max_terms']
        result = certify_split(case, proof, factor, elapsed, key, work)
    elif method == 'wide-modulus':
        work = wide_modulus_search(int(case['n']), **case['parameters'])
        elapsed = time.perf_counter() - start
        factor = work.pop('factor')
        work['order_method'] = work['order']['method']
        agree(case, work, ['route', 'order_method'])
        result = certify_split(case, proof, factor, elapsed, 'wide_modulus', work)
    elif method == 'short-basis':
        result = short_basis_case(case, proof)
    elif method == 'pascal':
        work = pascal_search(int(case['n']), case['cutoff'], case['max_index'])
        elapsed = time.perf_counter() - start
        factor = work.pop('factor')
        agree(case, work, ['index', 'coefficients_evaluated', 'coefficient_bits', 'residue'])
        result = certify_split(case, proof, factor, elapsed, 'pascal', work)
    elif method == 'inverse-windows':
        n = int(case['n'])
        bits = (n.bit_length() + 1) // 2
        work = inverse_windows_search(n, bits, case['side_bits'], case['word_bits'])
        elapsed = time.perf_counter() - start
        pairs = work.pop('factor_pairs')
        agree(case, work, ['n', 'entries', 'geometric_cells', 'modular_points', 'baseline_trial_odds'])
        factor = pairs[0][0] if pairs else None
        result = certify_split(case, proof, factor, elapsed, 'inverse_windows', work)
    elif method == 'midpoint-readings':
        work = midpoint_readings_search(int(case['n']), case['tests'], case['seed'])
        elapsed = time.perf_counter() - start
        pairs = work.pop('pairs')
        agree(case, work, ['midpoints', 'evaluations', 'final_square_tests'])
        factor = pairs[0][0] if pairs else None
        result = certify_split(case, proof, factor, elapsed, 'readings', work)
    elif method == 'continued-square':
        work = continued_square_search(int(case['n']), case['max_convergents'])
        elapsed = time.perf_counter() - start
        factor = work.pop('factor')
        work.pop('cofactor')
        if factor is not None:
            work['scale'] = str(work['scale'])
            work['parameter'] = str(work['parameter'])
        agree(case, work, ['convergents', 'square_tests', 'direction_tests'])
        result = certify_split(case, proof, factor, elapsed, 'continued_square', work)
    elif method == 'square-offset':
        work = search_square_offset(int(case['n']), case['max_gap'])
        elapsed = time.perf_counter() - start
        factor = work.pop('factor')
        agree(case, work, ['gaps_tested', 'discriminants'])
        result = certify_split(case, proof, factor, elapsed, 'square_offset', work)
    elif method == 'predecessor-square':
        work = predecessor_square_search(int(case['n']), case['max_scale'])
        elapsed = time.perf_counter() - start
        factor = work.pop('factor')
        agree(case, work, ['scales_tested'])
        result = certify_split(case, proof, factor, elapsed, 'predecessor_square', work)
    elif method == 'gap-stride':
        work = gap_search(int(case['n']), case['max_exponent'], case['per_root'])
        elapsed = time.perf_counter() - start
        factor = work.pop('factor')
        agree(case, work, ['exponent', 'square_tests', 'lift_tests'])
        result = certify_split(case, proof, factor, elapsed, 'gap_stride', work)
    elif method in ('reduced-order', 'cyclotomic'):
        result = period_case(case, method, proof)
    else:
        factor_args = ['scripts/factor.py', case['n'], '--max-steps', case.get('max_steps', 0),
                       '--verify', '--lean', proof, '--method', method]
        if method == 'subgroup' and 'max_base' in case:
            factor_args += ['--max-base', case['max_base']]
        result = cli(factor_args, 0 if complete else 1)
        if method == 'subgroup':
            agree(case, result['subgroup'], ['bases_tested'])
        else:
            agree(case, result, ['fermat_steps'])
    agree(case, result, ['n', 'status', 'factors', 'remaining'])
    if method == 'shifted':
        if result['shifted']['status'] != case['shifted']['status']:
            raise ValueError(f"Unexpected shifted-square result for {name}")
    if result['verified'] != complete or (complete and not proof.is_file()):
        raise ValueError(f'Unexpected proof status for {name}')
    if 'exclusion' in case:
        exclusion = case['exclusion']
        theorem = exclusion['theorem']
        if not re.fullmatch(r'[A-Za-z][A-Za-z_0-9]*', theorem):
            raise ValueError(f'Invalid exclusion theorem name {theorem!r}')
        half_gap = int(exclusion['half_gap_limit'])
        proof.write_text(
            'import PrimeFactors.Fermat\n\n'
            f'example (p d : ℕ) (h : d ≤ {half_gap}) :\n'
            f'    {int(case["n"])} ≠ p * (p + 2 * d) :=\n'
            f'  PrimeFactors.{theorem} p d h\n')
        check_start = time.perf_counter()
        subprocess.run(['lake', 'env', 'lean', '-DwarningAsError=true', str(proof)], cwd=ROOT,
                       check=True, timeout=900)
        result['exclusion'] = dict(max_gap=str(2 * half_gap), proof=f'proofs/{proof.name}',
                                   verification_seconds=time.perf_counter() - check_start)
    if method == 'projected-level-sieve' and case.get('check_exclusion'):
        exponent, residue = int(case['radix_exponent']), int(case['residue'])
        source = ROOT / 'benchmarks' / 'controls' / f'ProjectedLevelFresh{exponent}.lean'
        # Restate the result for the actual benchmark input, modulus and residue.
        # Lean rejects a mismatch between the public experiment and its proof.
        theorem = 'PrimeFactors.Generated.exclusion'
        proof.write_text(source.read_text() + f"""
theorem {theorem} (x y : ℕ) (pair : x*y={int(case['n'])})
    (hx : x<2^1024) (hy : y<2^1024) (lane : (x:ℤ) ≡ {residue} [ZMOD (2:ℤ)^{exponent}]) :
    False := PrimeFactors.Fresh{exponent}Exclusion.excludes_factor x y pair hx hy lane
#print axioms {theorem}
""")
        check_start = time.perf_counter()
        verify_file(proof, theorem)
        result['exclusion'] = dict(residue=str(residue), radix_exponent=exponent, max_factor_bits=1024,
                                   proof=f'proofs/{proof.name}', verification_seconds=time.perf_counter()-check_start)
    elapsed = time.perf_counter() - start
    return dict(result, id=name, description=case['description'],
                method=method, wall_seconds=elapsed,
                certificate=f'proofs/{proof.name}' if complete else None)


def cpu_name():
    proc = Path('/proc/cpuinfo')
    if proc.is_file():
        for line in proc.read_text().splitlines():
            if line.startswith('model name'):
                return line.split(':', 1)[-1].strip()
    if platform.system() == 'Darwin':
        info = subprocess.run(['/usr/sbin/sysctl', '-n', 'machdep.cpu.brand_string'],
                              capture_output=True, text=True)
        if info.returncode == 0 and info.stdout.strip():
            return info.stdout.strip()
    return platform.processor() or platform.machine()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out', type=Path, default=ROOT / 'build' / 'site')
    args = parser.parse_args()
    out = args.out.resolve()
    proofs = out / 'proofs'
    proofs.mkdir(parents=True, exist_ok=True)
    results = []
    for filename, method in [('cases.json', 'fermat'), ('subgroup.json', 'subgroup'),
                             ('shifted.json', 'shifted'), ('reduced-orders.json', 'reduced-order'),
                             ('cyclotomic-periods.json', 'cyclotomic'), ('gap-stride.json', 'gap-stride'),
                             ('predecessor-square.json', 'predecessor-square'),
                             ('square-offset.json', 'square-offset'), ('continued-square.json', 'continued-square'),
                             ('short-basis.json', 'short-basis'), ('wide-modulus.json', 'wide-modulus'),
                             ('pascal.json', 'pascal'), ('midpoint-readings.json', 'midpoint-readings'),
                             ('divisor-samples.json', 'divisor-samples'),
                             ('salie-residues.json', 'salie-residues'),
                             ('salie-seed.json', 'salie-seed'),
                             ('folded-square.json', 'folded-square'),
                             ('salie-blocks.json', 'salie-blocks'),
                             ('pell-pairs.json', 'pell-pairs'),
                             ('pell-local-windows.json', 'pell-local-windows'),
                             ('pell-relations.json', 'pell-relations'),
                             ('pooled-relations.json', 'pooled-relations'),
                             ('scored-multipliers.json', 'scored-multipliers'),
                             ('rational-squares.json', 'rational-squares'),
                             ('fraction-chains.json', 'fraction-chains'),
                             ('same-source-pairs.json', 'same-source-pairs'),
                             ('guided-pairs.json', 'guided-pairs'),
                             ('seed-gap-sieve.json', 'seed-gap-sieve'),
                             ('polynomial-relations.json', 'polynomial-relations'),
                             ('norm-directions.json', 'norm-directions'),
                             ('norm-curves.json', 'norm-curves'),
                             ('universal-norms.json', 'universal-norms'),
                             ('short-norm-boxes.json', 'short-norm-boxes'),
                             ('norm-band-product.json', 'norm-band-product'),
                             ('factorial-progressions.json', 'factorial-progressions'),
                             ('weighted-stride.json', 'weighted-stride'),
                             ('weighted-sparse.json', 'weighted-sparse'),
                             ('weighted-base.json', 'weighted-base'),
                             ('quartic-trace.json', 'quartic-trace'),
                             ('local-midpoints.json', 'local-midpoints'),
                             ('extension-trace.json', 'extension-trace'),
                             ('reciprocal-wheel.json', 'reciprocal-wheel'),
                             ('polynomial-packets.json', 'polynomial-packets'),
                             ('crt-square-norms.json', 'crt-square-norms'),
                             ('four-square-lines.json', 'four-square-lines'),
                             ('line-powers.json', 'line-powers'),
                             ('theta-residues.json', 'theta-residues'),
                             ('partition-recurrence.json', 'partition-recurrence'),
                             ('quotient-search.json', 'quotient-search'),
                             ('inverse-windows.json', 'inverse-windows'),
                             ('modular-hyperbola.json', 'modular-hyperbola'),
                             ('midpoint-weights.json', 'midpoint-weights'),
                             ('midpoint-slope-batches.json', 'midpoint-slope-batches'),
                             ('quartic-factor-lanes.json', 'quartic-factor-lanes'), ('unit-quartic.json', 'unit-quartic'),
                             ('centered-quartic.json', 'centered-quartic'), ('projected-levels.json', 'projected-level-sieve'),
                             ('class-orders.json', 'class-orders'), ('grouped-norm.json', 'grouped-norm'),
                             ('offset-rows.json', 'offset-rows'),
                             ('complete-offset-search.json', 'complete-offset-search'),
                             ('offset-winner-window.json', 'offset-winner-window'),
                             ('offset-coordinate-gaps.json', 'offset-coordinate-gaps'),
                             ('offset-gap-lifts.json', 'offset-coordinate-gaps'),
                             ('offset-arc-lines.json', 'offset-arc-lines'),
                             ('offset-tangent-cover.json', 'offset-tangent-cover'),
                             ('offset-trace-words.json', 'offset-trace-words'),
                             ('offset-factor-blocks.json', 'offset-factor-blocks'),
                             ('weighted-divisor-exclusion.json', 'weighted-divisor-exclusion'),
                             ('arbitrary-divisor-window.json', 'arbitrary-divisor-window'),
                             ('quartic-divisor-window.json', 'quartic-divisor-window'),
                             ('quartic-window-extension.json', 'quartic-window-extension'),
                             ('quartic-basis-translation.json', 'quartic-basis-translation'),
                             ('quartic-minor-gcd.json', 'quartic-minor-gcd'),
                             ('quartic-three-row.json', 'quartic-three-row'),
                             ('adaptive-quartic-cover.json', 'adaptive-quartic-cover'),
                             ('higher-divisor-window.json', 'higher-divisor-window'),
                             ('divisor-product-derivative.json', 'divisor-product-derivative'),
                             ('paired-divisor-windows.json', 'paired-divisor-windows'),
                             ('chebyshev-divisor-window.json', 'chebyshev-divisor-window'),
                             ('offset-crt.json', 'offset-crt'),
                             ('offset-lattice-batches.json', 'offset-lattice-batches'),
                             ('offset-row-norm.json', 'offset-lattice-batches'),
                             ('offset-row-geometry.json', 'offset-row-geometry'),
                             ('offset-dyadic.json', 'offset-dyadic'),
                             ('offset-prime-power.json', 'offset-prime-power')]:
        cases = json.loads((ROOT / 'benchmarks' / filename).read_text())
        if method == 'cyclotomic':
            cases = expand_cases(cases)
        for case in cases:
            result = run_case(case, method, proofs)
            results.append(result)
            print(f"{result['id']}  {result['status']}  {result['wall_seconds']:.3f}s", flush=True)
    if len(results) != len({case['id'] for case in results}):
        raise ValueError('Duplicate benchmark ID')
    sha = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip()
    data = dict(commit=sha, measured_at=datetime.now(timezone.utc).isoformat(timespec='seconds'),
                repository=os.getenv('GITHUB_REPOSITORY', 'marius-bughiu/prime-factors'),
                run_id=os.getenv('GITHUB_RUN_ID'), platform=platform.platform(), cpu=cpu_name(),
                python=platform.python_version(), lean=(ROOT / 'lean-toolchain').read_text().strip(),
                results=results)
    (out / 'results.json').write_text(json.dumps(data, indent=2) + '\n')


if __name__ == '__main__':
    main()
