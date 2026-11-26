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
from fractions import Fraction
from functools import partial
from math import isqrt
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from experiments.adaptive_quartic_cover import search as adaptive_quartic_search
from experiments.higher_divisor_window import search as higher_window_search
from experiments.binomial_divisor_window import search as binomial_window_search
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
from experiments.monotone_divisor_sampling import scan as scan_divisor_prefixes, scan_sum_rectangles
from experiments.neighbor_smooth_sum import search as neighbor_smooth_search
from experiments.smooth_factor_sums import scan_two_three
from experiments.near_smooth_sum import search as near_smooth_search
from experiments import carry_interval, geometric_lifted_readout, geometric_readout_blocks
from experiments import geometric_precision_readout, geometric_sum_readout, radix_carries, sum_signature_join
from scripts import near_smooth_certificate, trace_cover_certificate
from scripts.geometric_wheel_benchmark import wheel_readout_case
from scripts.cubic_forced_benchmark import forced_case
from experiments import hasse_hankel_probe
from scripts.hasse_benchmark import hasse_case
from scripts.short_pascal_benchmark import short_case
from scripts.growing_factorial_benchmark import growing_case
from scripts.block_exclusion_benchmark import block_exclusion_case
from scripts.block_subresultant_benchmark import block_subresultant_case
from scripts.adaptive_quartic_benchmark import adaptive_quartic_case
from scripts.power_chain_benchmark import power_chain_case
from scripts.character_column_benchmark import character_column_case
from scripts.reciprocal_sum_lane_benchmark import reciprocal_sum_lane_case
from scripts.reciprocal_sum_slice_benchmark import slice_case as reciprocal_sum_slice_case
from scripts.separating_period_benchmark import period_case as separating_period_case
from scripts.cubic_trace_benchmark import cubic_bases_case, cubic_readout_case, cubic_trace_case
from scripts.streamed_sum_benchmark import streamed_sum_case
from scripts.trace_folded_benchmark import trace_folded_case
from scripts.factor_sum_quantile_benchmark import quantile_case
from experiments.affine_excess import compare as compare_affine_excess
from experiments.weighted_square_pairs import search as weighted_square_pair_search
from experiments.weighted_pair_hybrid import run as weighted_menu_search
from experiments.weighted_square_triples import compare as weighted_triple_comparison
from experiments.weighted_subset_search import relation_certificate, search as weighted_subset_search
from experiments.weighted_subset_witness import certificate as subset_exclusion_certificate
from scripts.memory_partition_benchmark import memory_partition_case
from scripts.cyclotomic_sum_lift_benchmark import cyclotomic_sum_case
from scripts.lifted_period_benchmark import lifted_period_case
from scripts.lifted_period_trace_benchmark import lifted_trace_case
from experiments import trace_cover, trace_cover_transfer
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
from scripts.binomial_window_certificate import check_binomial_interval
from scripts.centered_binomial_certificate import check_centered_binomial_interval
from scripts.sifted_window_certificate import check_sifted_interval
from scripts.rounded_sifted_certificate import check_rounded_interval
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
from experiments.mixed_negative_templates import scan as mixed_template_search
from experiments.mixed_negative_norms import search as mixed_negative_search, witness_lean as mixed_negative_witness
from experiments.multiplier_polynomials import search as multiplier_polynomial_search
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
        certificate_options = (['--certificate-trial-limit', case['certificate_trial_limit']]
                               if 'certificate_trial_limit' in case else [])
        checked = cli(['scripts/factor.py', case['n'], '--factor-hint', factor, '--max-steps', 0,
                       '--verify', '--lean', proof, *certificate_options])
        result.update({key: checked[key] for key in
                       ['factors', 'remaining', 'status', 'verified', 'verification_seconds']})
        if certificate_options:
            result['certificate_trial_limit'] = checked['certificate_trial_limit']
        result['certificate_seconds'] = time.perf_counter() - certificate_start
    return result


def check_carry_probe(n, factor, hit, factor_proof):
    """Replay the reported radix and signed corrections as a public Lean computation."""
    high, low = hit['high'], hit['low']
    if 'radix' in hit:
        radix = hit['radix']
        radix_term = str(radix)
    else:
        radix = 1 << hit['exponent']
        radix_term = f"(2^{hit['exponent']})"
    coefficient = radix_carries.nearest(n, radix*radix) + high
    trace = coefficient*radix + radix_carries.nearest(n, radix) - low
    root = isqrt(trace*trace - 4*coefficient*n)
    theorem = 'PrimeFactors.Generated.radix_carry_probe'
    proof = factor_proof.with_name(f'{factor_proof.stem}-trace.lean')
    proof.write_text(f"""import PrimeFactors.PredictedTraceCarries

set_option exponentiation.threshold 8192
set_option maxRecDepth 8192

theorem {theorem} :
    PrimeFactors.PredictedTraceCarries.probe {n} {radix_term} ({high}) ({low})=some {factor} := by
  apply PrimeFactors.PredictedTraceCarries.probe_of_square
    (c:={coefficient}) (t:={trace}) (r:={root})
  all_goals decide +kernel

#print axioms {theorem}
""")
    start = time.perf_counter()
    verify_file(proof, theorem)
    return dict(proof=f'proofs/{proof.name}', seconds=time.perf_counter()-start)


def check_carry_interval_absence(n, work, proof):
    """Check every direct probe in a measured interval using two nonsquare witnesses."""
    if not work['covered'] or work['status'] != 'two_labels' or work['hits']:
        raise ValueError('Expected a covered low-carry interval with no split')
    exponent, high, budget = work['exponent'], work['high'], int(work['low_budget'])
    center_sum = int(work['center_sum'])
    product = int(work['coefficient'])*n
    center, radius, a, b = (int(work['certificate'][key]) for key in ('center', 'radius', 'a', 'b'))
    first, last = center_sum-budget, center_sum+budget
    if first <= 0 or first*first < 4*product:
        raise ValueError('The interval certificate requires a positive lower trace above the square-root threshold')
    top_floor = isqrt(last*last-4*product)
    bottom_ceil = carry_interval.ceil_sqrt(first*first-4*product)
    final_label = (2*(a*center*center+b*product)+3*center-1)//(2*center)
    radicands = [z*z-4*a*b*product for z in (final_label-1, final_label)]
    roots = [isqrt(max(0, delta)) for delta in radicands]
    theorem = 'PrimeFactors.Generated.noCarryInInterval'
    proof.write_text(f"""import PrimeFactors.CarryInterval

open PrimeFactors.PredictedTraceCarries PrimeFactors.ArbitraryDivisorWindow PrimeFactors.CarryInterval
set_option exponentiation.threshold 16384
set_option maxRecDepth 8192

theorem {theorem} (k : ℤ) (inside : |k| ≤ {budget}) :
    probe {n} (2^{exponent}) ({high}) k = none := by
  apply excludes_of_nonsquares
    (S₀ := {center_sum}) (c := {center}) (w := {radius}) (a := {a}) (b := {b})
    (r₁ := {roots[0]}) (r₂ := {roots[1]}) (budget := {budget})
    (by decide +kernel) (by decide +kernel) ?_ ?_ ?_ ?_ ?_ k inside
  · apply fit_checked (f := {top_floor}) (u := {bottom_ceil}) <;> decide +kernel
  · unfold Curvature
    decide +kernel
  · unfold Weights
    decide +kernel
  all_goals (unfold NotSquareAt; decide +kernel)

#print axioms {theorem}
""")
    start = time.perf_counter()
    verify_file(proof, theorem)
    return dict(low_budget=str(budget), exponent=exponent, high=high,
                proof=f'proofs/{proof.name}', verification_seconds=time.perf_counter()-start)


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


def lifted_readout_case(case, proof):
    n = int(case['n'])
    args = n, case['base'], case['max_block_width'], case['max_quotient']
    start = time.perf_counter()
    run = geometric_lifted_readout.search(*args)
    elapsed = time.perf_counter()-start
    ops = run.get('block_work', {})
    measured = dict(run, signed_targets=list(map(int, run['samples'])),
                    scalar_products=ops.get('scalar_products', 0),
                    root_polynomials=ops.get('root_polynomials', 0),
                    block_evaluations=ops.get('block_evaluations', 0))
    agree(case, measured, ['outcome', 'winning_index', 'total_terms', 'required_width',
                          'signed_targets', 'scalar_products', 'root_polynomials', 'block_evaluations', 'work'])

    if 'reflected' in case:
        start = time.perf_counter()
        reflected = geometric_lifted_readout.search(*args, reflected=True)
        seconds = time.perf_counter()-start
        block = reflected.get('block_work', {})
        counters = {key: block.get('reflected_'+key, 0) for key in
                    ('denominators', 'batch_gcds', 'scan_gcds', 'inversions', 'products', 'mirrors')}
        counters['status'] = block.get('reflected_status', 'unrun')
        if counters != case['reflected']:
            raise ValueError(f"{case['id']}: reflected coefficient work mismatch")
        if counters['status'] == 'proper_divisor':
            factor = reflected['factor']
            if not (1 < factor < n and n % factor == 0):
                raise ValueError(f"{case['id']}: invalid reflected divisor")
        else:
            for key in ('samples', 'linear', 'quadratic', 'outcome', 'factor', 'winning_index'):
                if reflected[key] != run[key]:
                    raise ValueError(f"{case['id']}: tree and reflected {key} disagree")
        run['reflected'] = dict(counters, seconds=seconds, outcome=reflected['outcome'],
                                factor=str(reflected['factor']) if reflected['factor'] else None,
                                scalar_products=block.get('scalar_products', 0),
                                unvisited_terms=reflected['work']['unvisited_terms'])

    start = time.perf_counter()
    eager = geometric_lifted_readout.search(*args, all_targets=True)
    run['eager_seconds'] = time.perf_counter()-start
    for key in ['factor', 'outcome', 'linear_minus', 'linear', 'quadratic', 'winning_index',
                'quotient_hits', 'equal_hits']:
        if eager[key] != run[key]:
            raise ValueError(f"{case['id']}: eager and adaptive lifted {key} disagree")
    if any(eager['samples'][key] != value for key, value in run['samples'].items()):
        raise ValueError(f"{case['id']}: eager and adaptive scalar values disagree")
    run['eager_block_work'] = eager.get('block_work', {})
    run['reference'] = 'unrun'
    if ops:
        count = int(run['total_terms'])
        base, target = run['reduced_base'], run['reduced_target']
        start = time.perf_counter()
        if count <= case['max_direct_terms']:
            run['reference'] = 'direct'
            reference = geometric_sum_readout.coefficients(n, base, target, count)
        else:
            run['reference'] = 'seven_product'
            reference, reference_work = geometric_readout_blocks.blocked_coefficients(n, base, target, count)
            run['reference_block_work'] = reference_work
        run['reference_seconds'] = time.perf_counter()-start
        constant, linear, quadratic = reference
        for key, value in [('constant', constant), ('linear_minus', linear[2]),
                           ('linear', linear), ('quadratic', quadratic)]:
            if run[key] is not None and run[key] != value:
                raise ValueError(f"{case['id']}: lifted {key} disagrees at the transported base")
    agree(case, run, ['reference'])
    return certify_split(case, proof, run.pop('factor'), elapsed, 'geometric_lifted_readout', run)


def compare_adaptive_readings(case, reference):
    comparisons = {}
    saved_fields = ['outcome', 'constant', 'linear', 'quadratic', 'readout_index', 'winning_index',
                    'factor', 'quotient_hits', 'equal_hits']
    for mode in ('cube_first', 'square_first'):
        start = time.perf_counter()
        run = geometric_readout_blocks.search(int(case['n']), case['base'], case['max_block_width'],
                                              case['max_quotient'], mode=mode)
        seconds = time.perf_counter()-start
        for field in saved_fields:
            if field == 'quadratic' and run[field] is None:
                continue
            if run[field] != reference[field]:
                raise ValueError(f"{case['id']}: {mode} and seven-product {field} disagree")
        ops = run.get('block_work', {})
        measured = dict(square_products=ops.get('square_products', 0),
                        cube_products=ops.get('cube_products', 0),
                        root_polynomials=ops.get('root_polynomials', 0),
                        block_evaluations=ops.get('block_evaluations', 0),
                        quadratic_available=run['quadratic'] is not None)
        if measured != case['adaptive_checks'][mode]:
            raise ValueError(f"{case['id']}: unexpected {mode} measurements")
        comparisons[mode] = {key: run[key] for key in saved_fields}
        comparisons[mode].update(seconds=seconds, block_work=ops, work=run['work'],
                                 factor=str(run['factor']) if run['factor'] is not None else None)
    return comparisons


def hankel_probe_case(case, proof):
    n = int(case['n'])
    start = time.perf_counter()
    run = hasse_hankel_probe.search(n)
    rows = run['rows']
    raw = [g for row in rows for g in row['raw']]
    hit = next(((i, j, g) for i, row in enumerate(rows) for j, g in enumerate(row['raw'])
                if 1 < g < n), None)
    control_gcds = sum(len(row[k]) for row in rows for k in ('residual', 'simple'))
    control_gcds += len(run['random']) + len(run['descending_odd'])
    work = dict(shifts_checked=len(rows), raw_gcds=len(raw), comparison_gcds=control_gcds,
                raw_values=[str(g) for g in raw], first_shift=str(rows[hit[0]]['shift']) if hit else None,
                first_start=hit[1] if hit else None)
    elapsed = time.perf_counter() - start
    agree(case, work, work)
    result = certify_split(case, proof, hit[2] if hit else None, elapsed, 'hasse_hankel_probe', work)
    if hit:
        i, j, divisor = hit
        shift = ('2', '3', f'(Nat.sqrt {n} : ℤ)', f'((Nat.sqrt {n} : ℤ) + 1)')[i]
        coefficients = hasse_hankel_probe.POLYNOMIALS[j]
        poly = ' + '.join(f'({a}) * (C^2)^{k} * (B^3)^{len(coefficients)-1-k}'
                          for k, a in enumerate(coefficients))
        prefactor = ('2*B*C^4', 'B*C^8')[j]
        theorem = 'PrimeFactors.Generated.hankelProbeGcd'
        reduce_shift = (f'  rw [show Nat.sqrt {n} = {isqrt(n)} by symm; '
                        'exact Nat.eq_sqrt.mpr (by decide +kernel)]\n' if i >= 2 else '')
        # Bind the actual public shift and signed polynomial to the same divisor
        # used by the factor certificate. This arithmetic replay is outside discovery.
        with proof.open('a') as source:
            source.write(f"""
theorem {theorem} :
    let c : ℤ := {shift}
    let B := 3*c^2-1
    let C := c^3-c
    Nat.gcd {n} (({prefactor}) * ({poly})).natAbs = {divisor} := by
{reduce_shift}  decide +kernel
#print axioms {theorem}
""")
        begin = time.perf_counter()
        verify_file(proof, theorem)
        checked_seconds = time.perf_counter() - begin
        result['verification_seconds'] += checked_seconds
        result['certificate_seconds'] += checked_seconds
    return result


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
    elif method == 'geometric-precision-readout':
        n = int(case['n'])
        start = time.perf_counter()
        run = geometric_precision_readout.search(n, case['base'], case['cap'], case['precision_policy'],
                                                case['max_terms'], case['max_lattice_power'],
                                                wheel=case['wheel'], auto_multiplicity=True)
        elapsed = time.perf_counter()-start
        run['lattice_dimension'] = run['lattice']['dimension'] if run['lattice'] else None
        agree(case, run, ['outcome', 'multiplicity', 'precision', 'roots', 'retained', 'lattice_dimension'])
        result = certify_split(case, proof, run.pop('factor'), elapsed, 'geometric_precision_readout', run)
    elif method == 'geometric-wheel-readout':
        result = wheel_readout_case(case, proof, agree, certify_split)
    elif method == 'geometric-lifted-readout':
        result = lifted_readout_case(case, proof)
    elif method == 'geometric-readout-blocks':
        n = int(case['n'])
        search = geometric_readout_blocks.search(n, case['base'], case['max_block_width'],
                                                 case['max_quotient'])
        elapsed = time.perf_counter() - start
        agree(case, search, ['outcome', 'total_terms', 'required_width', 'winning_index', 'work'])
        if case.get('block_work') != search.get('block_work'):
            raise ValueError(f'{name}: unexpected geometric block work')
        reference_start = time.perf_counter()
        direct = geometric_sum_readout.search(n, case['base'], case['reference_term_cap'],
                                              case['max_quotient'])
        search['direct_seconds'] = time.perf_counter() - reference_start
        search['direct_work'] = direct['work']
        search['direct_outcome'] = direct['outcome']
        compared = search['constant'] is not None and direct['constant'] is not None
        search['matched_readings'] = compared
        if compared:
            keys = ['constant', 'linear', 'quadratic', 'readout_index', 'winning_index', 'outcome',
                    'factor', 'quotient_hits', 'equal_hits']
            if any(search[key] != direct[key] for key in keys):
                raise ValueError(f'{name}: blocked product and direct readout disagree')
        agree(case, search, ['direct_outcome', 'matched_readings'])
        if 'adaptive_checks' in case:
            search['adaptive_comparisons'] = compare_adaptive_readings(case, search)
        result = certify_split(case, proof, search.pop('factor'), elapsed, 'geometric_readout_blocks', search)
    elif method == 'geometric-sum-binary':
        args = int(case['n']), case['base'], case['max_terms'], case['max_quotient']
        search = geometric_sum_readout.search_binary(*args)
        elapsed = time.perf_counter() - start
        agree(case, search, ['outcome', 'dense_terms', 'total_terms', 'accepted_mod_32',
                             'winning_sum', 'winning_lane', 'work'])
        comparison_start = time.perf_counter()
        dense = geometric_sum_readout.search(*args)
        search['dense_seconds'] = time.perf_counter() - comparison_start
        search['dense_comparison'] = dict(outcome=dense['outcome'], work=dense['work'])
        agree(case, search, ['dense_comparison'])
        result = certify_split(case, proof, search.pop('factor'), elapsed, 'geometric_sum_binary', search)
    elif method == 'geometric-sum-readout':
        search = geometric_sum_readout.search(int(case['n']), case['base'], case['max_terms'],
                                              case['max_quotient'])
        elapsed = time.perf_counter() - start
        agree(case, search, ['outcome', 'winning_index', 'quotient_hits', 'equal_hits', 'work'])
        result = certify_split(case, proof, search.pop('factor'), elapsed, 'geometric_sum_readout', search)
    elif method == 'streamed-sum-join':
        result = streamed_sum_case(case, proof, agree, certify_split)
    elif method == 'lifted-period-join':
        result = lifted_period_case(case, proof, agree, certify_split)
    elif method == 'lifted-period-trace':
        result = lifted_trace_case(case, proof, agree, certify_split)
    elif method == 'cyclotomic-sum-lift':
        result = cyclotomic_sum_case(case, proof, agree, certify_split)
    elif method == 'weighted-square-subsets':
        n = int(case['n'])
        tick = time.perf_counter()
        search = weighted_subset_search(n)
        elapsed = time.perf_counter() - tick
        agree(case, search, ['outcome', 'minimum_rows'])
        agree(case, search['work'], ['square_subsets', 'covered_subsets', 'remaining_subsets'])
        result = certify_split(case, proof, None, elapsed, 'weighted_square_subsets', search)
        factor = search['factor']
        if factor is not None:
            cert_start = time.perf_counter()
            source, theorem = relation_certificate(n, search)
            proof.write_text(source)
            check_start = time.perf_counter()
            verify_file(proof, theorem)
            result.update(factors=[str(x) for x in sorted((factor, n//factor))], remaining=[],
                          status='complete', verified=True, verification_seconds=time.perf_counter()-check_start,
                          certificate_seconds=time.perf_counter()-cert_start)
    elif method == 'weighted-square-triples':
        tick = time.perf_counter()
        comparison = weighted_triple_comparison(int(case['n']), all_subsets=True)
        elapsed = time.perf_counter() - tick
        agree(case, comparison['work'], ['initial_tests', 'pair_tests', 'triple_tests',
                                         'extra_single_tests', 'genuine_triple_splits'])
        agree(case, comparison['subsets'], ['square_subsets', 'private_pruned'])
        hit = comparison['genuine_triple']
        factor = int(hit['divisor']) if hit else None
        result = certify_split(case, proof, factor, elapsed, 'weighted_square_triples', comparison)
    elif method == 'weighted-square-menu':
        n = int(case['n'])
        comparisons = {}
        for name_policy in ('ordinary', 'pairs', 'hybrid', 'sieved_ordinary'):
            tick = time.perf_counter()
            run = weighted_menu_search(n, name_policy)
            run['seconds'] = time.perf_counter() - tick
            if run['divisor'] is not None:
                if not (1 < run['divisor'] < n and n % run['divisor'] == 0):
                    raise ValueError('weighted menu returned an invalid divisor')
                run['divisor'] = str(run['divisor'])
            expected = case['checks'][name_policy]
            agree(dict(id=case['id'], **expected), dict(arm=run['arm'], **run['work']), expected)
            comparisons[name_policy] = run
        chosen = comparisons['hybrid']
        factor = int(chosen['divisor']) if chosen['divisor'] else None
        result = certify_split(case, proof, factor, chosen['seconds'], 'weighted_square_menu', comparisons)
    elif method == 'affine-excess':
        run = compare_affine_excess(int(case['n']), case['source_limit'], case['labels_per_source'])
        elapsed = time.perf_counter() - start
        agree(case, run, ['small_baseline_weights', 'remaining_pairs'])
        agree(dict(id=name, **case['checks']), run['work'], case['checks'])
        agree(case, {'hit_arms': sorted(run['hits'])}, ['hit_arms'])
        pair_arms = ('nonsingular', 'zero_slope', 'proportional')
        hit = next((run['hits'][arm] for arm in pair_arms if arm in run['hits']), {})
        factor = hit.get('minus') or hit.get('plus')
        result = certify_split(case, proof, factor, elapsed, 'affine_excess', run)
    elif method == 'weighted-square-pair':
        tick = time.perf_counter()
        work = weighted_square_pair_search(int(case['n']))
        elapsed = time.perf_counter() - tick
        agree(case, work, ['square', 'square_tests', 'gcd_tests'])
        result = certify_split(case, proof, work.pop('factor'), elapsed, 'weighted_square_pair', work)
    elif method == 'memory-partition-sum':
        result = memory_partition_case(case, proof, agree, certify_split)
    elif method == 'factor-sum-quantile':
        result = quantile_case(case, proof, agree, certify_split)
    elif method == 'trace-folded-right':
        result = trace_folded_case(case, proof, agree, certify_split)
    elif method == 'collision-gap-readout':
        n = int(case['n'])
        bases = tuple(map(int, case['bases']))
        start = time.perf_counter()
        if case['require_witness']:
            run = sum_signature_join.witnessed_search(n, bases, case['max_half_entries'],
                                                      case['trial_cap'], case['candidate_cap'])
        else:
            run = sum_signature_join.search(n, bases=bases, max_half_entries=case['max_half_entries'],
                                            incremental=True, gap_trial_cap=case['trial_cap'],
                                            gap_candidate_cap=case['candidate_cap'])
        elapsed = time.perf_counter()-start
        work = run['work']
        gap = work.get('collision_gap', {})
        measured = dict(outcome=run['outcome'], hits=work.get('signature_matches'),
                        listed=[str(work.get(k, 0)) for k in ('left_entries', 'right_entries')],
                        common_gap=gap.get('gap'), projection_gcds=gap.get('projection_gcds', 0),
                        sample_tests=work.get('square_tests', 0), gap_remaining=gap.get('remaining'))
        agree(case, measured, list(measured))
        run.update(list_cap=case['max_half_entries'], trial_cap=case['trial_cap'],
                   candidate_cap=case['candidate_cap'], require_witness=case['require_witness'])
        factor = int(run['factors'][0]) if run['factors'] else None
        result = certify_split(case, proof, factor, elapsed, 'collision_gap_readout', run)
    elif method == 'sum-signature':
        search = sum_signature_join.search(int(case['n']), bases=case.get('input_bases'),
                                           max_half_entries=case['max_half_entries'])
        elapsed = time.perf_counter() - start
        agree(case, search, ['outcome', 'factors'])
        agree(dict(id=name, **case['work_checks']), search['work'], case['work_checks'])
        incremental_start = time.perf_counter()
        incremental = sum_signature_join.search(int(case['n']), bases=case.get('input_bases'),
                                                max_half_entries=case['max_half_entries'], incremental=True)
        incremental_seconds = time.perf_counter() - incremental_start
        agree(case, incremental, ['outcome', 'factors'])
        changed = case['incremental_work']
        expected = {**case['work_checks'], **changed}
        agree(dict(id=name, **expected), incremental['work'], expected)
        factors = search.pop('factors')
        search['max_half_entries'] = case['max_half_entries']
        search['incremental_work'] = incremental['work']
        search['incremental_seconds'] = incremental_seconds
        result = certify_split(case, proof, int(factors[0]) if factors else None,
                               elapsed, 'sum_signature', search)
    elif method == 'carry-interval':
        n = int(case['n'])
        exponent, high, budget = case['exponent'], case['high'], int(case['low_budget'])
        work = carry_interval.search(n, exponent, high, budget)
        elapsed = time.perf_counter() - start
        winning_lows = [hit['low'] for hit in work['hits']]
        agree(case, dict(covered=work['covered'], interval_status=work['status'],
                         work=work['work'], winning_lows=winning_lows),
              ['covered', 'interval_status', 'work', 'winning_lows'])
        if int(work['low_candidates']) != 2*budget+1:
            raise ValueError(f'{name}: incorrect inclusive low-carry count')
        work.update(exponent=exponent, high=high, low_budget=str(budget))
        factor = int(work['hits'][0]['factor']) if work['hits'] else None
        result = certify_split(case, proof, factor, elapsed, 'carry_interval', work)
        if factor is not None:
            hit = dict(exponent=exponent, high=high, low=int(winning_lows[0]))
            result['carry_proof'] = check_carry_probe(n, factor, hit, proof)
        elif case.get('check_empty'):
            result['exclusion'] = check_carry_interval_absence(n, work, proof)
    elif method == 'radix-carries':
        n = int(case['n'])
        high, low = case['high_budget'], case['low_budget']
        if 'max_neighbor_checks' in case:
            factor, work = radix_carries.search_neighbors(n, high, low, case['max_neighbor_checks'])
            agree(case, work, ['neighbor_checks'])
            work['max_neighbor_checks'] = case['max_neighbor_checks']
        else:
            factor, work = radix_carries.search(n, high, low)
        elapsed = time.perf_counter() - start
        agree(case, work, ['radices', 'candidates', 'square_tests', 'square_hits', 'hit'])
        work.update(high_budget=high, low_budget=low)
        result = certify_split(case, proof, factor, elapsed, 'radix_carries', work)
        if factor is not None:
            result['carry_proof'] = check_carry_probe(n, factor, work['hit'], proof)
    elif method == 'near-smooth-sum':
        n = int(case['n'])
        tolerance = int(case['tolerance'])
        witnesses = []
        work = near_smooth_search(n, tolerance, max_windows=case.get('max_windows'),
                                  exclusion_witnesses=witnesses)
        elapsed = time.perf_counter() - start
        factor = work.pop('factor')
        exact = scan_two_three(n)
        work.update(exact_smooth_hit=exact['factor'] is not None,
                    exact_smooth_square_tests=exact['square_tests'],
                    exact_smooth_exponents=exact['exponents_visited'])
        for key in ('tolerance', 'largest_divisor_window', 'direct_mod24_tests', 'direct_even_tests',
                    'winning_center', 'winning_sum', 'sum_error'):
            if work[key] is not None:
                work[key] = str(work[key])
        agree(case, work, work.keys())
        result = certify_split(case, proof, factor, elapsed, 'near_smooth_sum', work)
        if n.bit_length() == 2048:
            checked_at = time.perf_counter()
            if (factor is not None and 0 < abs(int(work['sum_error'])) <= min(tolerance, 2**437)
                    and 2**1024 <= int(work['winning_center']) < 2**1025):
                near_smooth_certificate.check_recovery(proof, factor, n//factor, work)
                result['verification_seconds'] += time.perf_counter() - checked_at
            elif (factor is None and not work['unresolved_windows'] and not work['windows_remaining']
                  and tolerance % 2 == 0 and near_smooth_certificate.covers_public_menu(n, tolerance, witnesses)):
                near_smooth_certificate.check_absence(n, tolerance, witnesses, proof, chebyshev_quartic_cuts)
                result['exclusion'] = dict(sum_tolerance=str(tolerance), bands=len(witnesses),
                                           proof=f'proofs/{proof.name}',
                                           verification_seconds=time.perf_counter() - checked_at)
    elif method == 'two-three-sum':
        work = scan_two_three(int(case['n']))
        elapsed = time.perf_counter() - start
        factor = work.pop('factor')
        agree(case, work, work.keys())
        result = certify_split(case, proof, factor, elapsed, 'two_three_sum', work)
        if factor is not None and work['factor_bits'] == 1024:
            p, q = sorted((factor, int(case['n'])//factor))
            b = work['winning_exponent']
            a = 1025 - (3**b).bit_length()
            theorem = 'PrimeFactors.Generated.smoothSumRecovery'
            source = 'import PrimeFactors.SmoothSumSelector\n' + proof.read_text()
            source += f"""
namespace PrimeFactors.Generated
theorem smoothSumRecovery :
    SmoothSumSelector.recover {case['n']} = some ({p}, {q}) := by
  exact SmoothSumSelector.recover_eq (p := {p}) (q := {q}) (a := {a}) (b := {b})
    prime_{p} prime_{q} (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
#print axioms smoothSumRecovery
end PrimeFactors.Generated
"""
            proof.write_text(source)
            check_start = time.perf_counter()
            verify_file(proof, theorem)
            result['verification_seconds'] += time.perf_counter() - check_start
    elif method == 'neighbor-smooth-sum':
        work = neighbor_smooth_search(int(case['n']), case['prime_limit'], case['inverse_gap'])
        elapsed = time.perf_counter() - start
        factor = work.pop('factor')
        agree(case, work, work.keys())
        result = certify_split(case, proof, factor, elapsed, 'neighbor_smooth_sum', work)
    elif method == 'two-draw-sampling':
        work = scan_sum_rectangles(int(case['n']), case['limit'])
        elapsed = time.perf_counter() - start
        factor = work.pop('factor')
        agree(case, work, work.keys())
        result = certify_split(case, proof, factor, elapsed, 'two_draw_sampling', work)
    elif method == 'monotone-divisor-sampling':
        work = scan_divisor_prefixes(int(case['n']), case['limit'])
        elapsed = time.perf_counter() - start
        factor = work.pop('factor')
        agree(case, work, work.keys())
        result = certify_split(case, proof, factor, elapsed, 'monotone_divisor_sampling', work)
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
    elif method in ('binomial-divisor-window', 'sifted-divisor-window', 'rounded-sifted-window'):
        n, radius = int(case['n']), int(case['radius'])
        center = odd_quartile_center(n)
        first, span = center - 2*radius, 2*radius
        rounded = method == 'rounded-sifted-window'
        sifted = method in ('sifted-divisor-window', 'rounded-sifted-window')
        params = dict(degree=case['degree'], depth=case['depth'], modulus_limit=case['modulus_limit'])
        work = binomial_window_search(n, first, span, centered=case['centered'], sifted=sifted, rounded=rounded, **params)
        elapsed = time.perf_counter()-start
        reference_start = time.perf_counter()
        if sifted:
            reference = binomial_window_search(n, first, span, centered=True, sifted=rounded, **params)
        else:
            reference = higher_window_search(n, center, radius, chebyshev=True, **params)
        reference_seconds = time.perf_counter()-reference_start
        agree(case, work, ['lower', 'upper', 'height', 'height_bound', 'short', 'divisors',
                           'rootless_modulus', 'work'])
        reference_keys = ['height', 'short', 'divisors', 'work']
        if sifted:
            agree(case, work, ['origin', 'shift', 'progression_size', 'denominator', 'denominator_gcd'])
            reference_keys.append('rootless_modulus')
        if rounded:
            agree(case, work, ['corrections', 'weights'])
        work['reference'] = {k: reference.get(k) for k in reference_keys}
        agree(case, work, ['reference'])
        work['reference_seconds'] = reference_seconds
        factor = work['denominator_factor'] or next((d for d in work['divisors'] if 1 < d < n), None)
        result = certify_split(case, proof, factor, elapsed, method.replace('-', '_'), work)
        if work['rootless_modulus'] is not None:
            if rounded:
                checker = check_rounded_interval
            elif sifted:
                checker = check_sifted_interval
            else:
                checker = check_centered_binomial_interval if case['centered'] else check_binomial_interval
            result['exclusion'] = checker(n, work, proof, verify_interval)
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
    elif method == 'trace-transfer':
        n = int(case['n'])
        if n.bit_length() > case['template_bits']:
            raise ValueError(f'{name}: input exceeds the template size')
        template, setup = trace_cover_transfer.ceiling_template(
            case['template_bits'], n % 12, case['k'], case['baby_steps'])
        search_start = time.perf_counter()
        run = weighted_stride_search.search(n, case['k'], case['baby_steps'], case['max_giants'],
                                            record_builder=template.records)
        search_seconds = time.perf_counter() - search_start
        factor = run.pop('factor')
        setup_seconds = setup.pop('prepare_seconds')
        work = dict(run, template=setup, template_bits=case['template_bits'], residue=n % 12,
                    setup_seconds=setup_seconds, search_seconds=search_seconds)
        for key, expected in case['expected'].items():
            if work[key] != expected:
                raise ValueError(f'{name}: unexpected transferred schedule or search count for {key}')
        result = certify_split(case, proof, factor, time.perf_counter()-start, 'trace_transfer', work)
    elif method == 'trace-cover':
        n, block = int(case['n']), int(case['baby_steps'])
        plan, work, factor = trace_cover.compare(n, case['k'], block,
            search_factors=case['execute_search'], equal_width=case['equal_width'], sparse=case['sparse'],
            certificate=ROOT/'research'/case['public_plan'] if 'public_plan' in case else None)
        elapsed = time.perf_counter() - start
        for key, expected in case['expected'].items():
            if work[key] != expected:
                raise ValueError(f'{name}: {key} differs from the expected schedule or measured search')
        result = certify_split(case, proof, factor, elapsed, 'trace_cover', work)
        if case['schedule_certificate']:
            checked_at = time.perf_counter()
            trace_cover_certificate.check_schedule(n, case['k'], block, plan, Fraction(work['right']), proof)
            seconds = time.perf_counter()-checked_at
            result['schedule_proof'] = dict(proof=f'proofs/{proof.name}', seconds=seconds)
            if result['verified']:
                result['verification_seconds'] += seconds
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
    elif method == 'hasse-hankel-probe':
        result = hankel_probe_case(case, proof)
    elif method == 'translated-hasse':
        result = hasse_case(case, proof, agree, certify_split)
    elif method == 'growing-factorial':
        result = growing_case(case, proof, agree, certify_split)
    elif method == 'block-exclusion':
        result = block_exclusion_case(case, proof, agree, certify_split)
    elif method == 'block-subresultant':
        result = block_subresultant_case(case, proof, agree, certify_split)
    elif method == 'adaptive-quartic':
        result = adaptive_quartic_case(case, proof, agree, certify_split)
    elif method == 'power-chain':
        result = power_chain_case(case, proof, agree, certify_split)
    elif method == 'reciprocal-sum-slice':
        result = reciprocal_sum_slice_case(case, proof, agree, certify_split)
    elif method == 'reciprocal-sum-lanes':
        result = reciprocal_sum_lane_case(case, proof, agree, certify_split)
    elif method == 'separating-period':
        result = separating_period_case(case, proof, agree, certify_split)
    elif method == 'character-column':
        result = character_column_case(case, proof, agree, certify_split)
    elif method == 'short-pascal':
        result = short_case(case, proof, agree, certify_split)
    elif method == 'cubic-forced':
        result = forced_case(case, proof, agree, certify_split)
    elif method == 'cubic-trace':
        result = cubic_trace_case(case, proof, agree, certify_split)
    elif method == 'cubic-readout':
        result = cubic_readout_case(case, proof, agree, certify_split)
    elif method == 'cubic-smooth-bases':
        result = cubic_bases_case(case, proof, agree, certify_split)
    elif method == 'mixed-negative-template':
        work = mixed_template_search(int(case['n']), case['max_tests'])
        elapsed = time.perf_counter() - start
        factors = work.pop('factors', [])
        work['candidates_left'] = str(work.pop('remaining'))
        agree(case, work, work.keys())
        result = certify_split(case, proof, factors[0] if factors else None, elapsed,
                               'mixed_negative_template', dict(work, max_tests=case['max_tests']))
    elif method == 'mixed-negative-norms':
        n = int(case['n'])
        work = mixed_negative_search(n, case['width'])
        elapsed = time.perf_counter() - start
        factor = work.pop('factor')
        agree(case, work, ('factor_source', 'work', 'split_witness'))
        result = certify_split(case, proof, factor, elapsed, 'mixed_negative_norms', work)
        if work['split_witness'] is not None:
            relation = proof.with_name(f'{name}-relation.lean')
            relation.write_text(mixed_negative_witness(n, work['split_witness']))
            verify_file(relation, 'PrimeFactors.Generated.MixedNegative.witness')
            result['mixed_relation'] = f'proofs/{relation.name}'
    elif method == 'multiplier-polynomials':
        work = multiplier_polynomial_search(int(case['n']), case['arm'], bound=case['bound'],
                                           radius=case['radius'], blocks=case['blocks'])
        elapsed = time.perf_counter() - start
        factor = work.pop('factor')
        agree(case['expected_work'] | {'id': name}, work, list(work))
        result = certify_split(case, proof, factor, elapsed, 'multiplier_polynomials', work)
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
    if method == 'weighted-square-subsets' and case.get('check_unique_subset'):
        mask = sum(1 << (2*(w-1)+i) for w, i in search['witness']['rows'])
        source, counts = subset_exclusion_certificate(int(case['n']), 'WeightedSubsetControl', allow_pivot=True)
        if counts.get('mask') != mask:
            raise ValueError(f'{name}: character certificate identifies a different subset')
        unique = proofs / f'{name}-unique.lean'
        unique.write_text(source + f"\nexample : PrimeFactors.WeightedSubsetControl.product = {int(case['n'])} := rfl\n")
        check_start = time.perf_counter()
        verify_file(unique, 'PrimeFactors.WeightedSubsetControl.onlySquareSubset')
        result['unique_subset'] = dict(proof=f'proofs/{unique.name}', character_search=counts,
                                       verification_seconds=time.perf_counter()-check_start)
    if method == 'weighted-square-triples' and case.get('check_subset_exclusion'):
        source, counts = subset_exclusion_certificate(int(case['n']), 'WeightedSubsetControl')
        proof.write_text(source + f"\nexample : PrimeFactors.WeightedSubsetControl.product = {int(case['n'])} := rfl\n")
        check_start = time.perf_counter()
        verify_file(proof, 'PrimeFactors.WeightedSubsetControl.noSquareSubset')
        result['exclusion'] = dict(square_subsets_excluded=comparison['subsets']['nonempty_subsets'],
                                   proof=f'proofs/{proof.name}', character_search=counts,
                                   verification_seconds=time.perf_counter()-check_start)
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
                             ('multiplier-polynomials.json', 'multiplier-polynomials'),
                             ('mixed-negative-norms.json', 'mixed-negative-norms'),
                             ('cubic-trace.json', 'cubic-trace'),
                             ('cubic-forced.json', 'cubic-forced'),
                             ('short-pascal.json', 'short-pascal'),
                             ('growing-factorial.json', 'growing-factorial'),
                             ('block-exclusion.json', 'block-exclusion'),
                             ('block-subresultant.json', 'block-subresultant'),
                             ('adaptive-quartic.json', 'adaptive-quartic'),
                             ('power-chain.json', 'power-chain'),
                             ('character-column.json', 'character-column'),
                             ('separating-period.json', 'separating-period'),
                             ('reciprocal-sum-lanes.json', 'reciprocal-sum-lanes'),
                             ('reciprocal-sum-slice.json', 'reciprocal-sum-slice'),
                             ('translated-hasse.json', 'translated-hasse'),
                             ('hasse-hankel-probe.json', 'hasse-hankel-probe'),
                             ('cubic-readout.json', 'cubic-readout'),
                             ('cubic-smooth-bases.json', 'cubic-smooth-bases'),
                             ('mixed-negative-template.json', 'mixed-negative-template'),
                             ('norm-directions.json', 'norm-directions'),
                             ('norm-curves.json', 'norm-curves'),
                             ('universal-norms.json', 'universal-norms'),
                             ('short-norm-boxes.json', 'short-norm-boxes'),
                             ('norm-band-product.json', 'norm-band-product'),
                             ('factorial-progressions.json', 'factorial-progressions'),
                             ('weighted-stride.json', 'weighted-stride'),
                             ('trace-cover.json', 'trace-cover'),
                             ('trace-transfer.json', 'trace-transfer'),
                             ('radix-carries.json', 'radix-carries'),
                             ('carry-interval.json', 'carry-interval'),
                             ('sum-signature.json', 'sum-signature'),
                             ('collision-gap-readout.json', 'collision-gap-readout'),
                             ('streamed-sum-join.json', 'streamed-sum-join'),
                             ('trace-folded-right.json', 'trace-folded-right'),
                             ('factor-sum-quantile.json', 'factor-sum-quantile'),
                             ('weighted-square-pairs.json', 'weighted-square-pair'),
                             ('affine-excess.json', 'affine-excess'),
                             ('weighted-square-menu.json', 'weighted-square-menu'),
                             ('weighted-square-triples.json', 'weighted-square-triples'),
                             ('weighted-square-subsets.json', 'weighted-square-subsets'),
                             ('memory-partition-sum.json', 'memory-partition-sum'),
                             ('cyclotomic-sum-lift.json', 'cyclotomic-sum-lift'),
                             ('lifted-period-join.json', 'lifted-period-join'),
                             ('lifted-period-trace.json', 'lifted-period-trace'),
                             ('geometric-sum-readout.json', 'geometric-sum-readout'),
                             ('geometric-sum-binary.json', 'geometric-sum-binary'),
                             ('geometric-readout-blocks.json', 'geometric-readout-blocks'),
                             ('geometric-lifted-readout.json', 'geometric-lifted-readout'),
                             ('geometric-wheel-readout.json', 'geometric-wheel-readout'),
                             ('geometric-precision-readout.json', 'geometric-precision-readout'),
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
                             ('binomial-divisor-window.json', 'binomial-divisor-window'),
                             ('sifted-divisor-window.json', 'sifted-divisor-window'),
                             ('rounded-sifted-window.json', 'rounded-sifted-window'),
                             ('monotone-divisor-sampling.json', 'monotone-divisor-sampling'),
                             ('two-draw-sampling.json', 'two-draw-sampling'),
                             ('neighbor-smooth-sum.json', 'neighbor-smooth-sum'),
                             ('two-three-sum.json', 'two-three-sum'),
                             ('near-smooth-sum.json', 'near-smooth-sum'),
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
