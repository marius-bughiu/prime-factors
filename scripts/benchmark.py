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

from experiments.class_order_search import search as class_order_search
from experiments.complete_offset_search import search as complete_offset_search
from experiments.offset_arc_lines import search as offset_arc_line_search
from experiments.offset_coordinate_gaps import search as offset_coordinate_gap_search
from experiments.offset_crt_reconstruction import search as offset_crt_search
from experiments.offset_dyadic_search import search as offset_dyadic_search
from experiments.offset_lattice_batches import search as offset_lattice_search
from experiments.offset_prime_power_slopes import search as offset_prime_power_search
from experiments.offset_row_geometry import search as offset_row_geometry_search
from experiments.offset_tangent_cover import search as offset_tangent_cover_search
from experiments.offset_trace_words import search as offset_trace_word_search
from experiments.offset_winner_window import search as offset_winner_window_search
from experiments.grouped_offset_frame import choose_frame
from experiments.grouped_offset_rows import bounded_rows
from experiments.midpoint_slope_batches import search as slope_batch_search
from experiments.midpoint_weights import search as weight_orbit_search
from experiments.gap_newton_lanes import search as gap_lane_search
from experiments.quartic_factor_lanes import search as quartic_lane_search
from experiments.unit_factor_lane import search as unit_lane_search
from experiments.unit_quartic_probe import probe as unit_quartic_probe
from experiments.centered_sum_quartic import probe as centered_quartic_probe
from experiments.projected_level_sieve import centered_search as projected_level_search
from scripts.factor import verify_file
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
