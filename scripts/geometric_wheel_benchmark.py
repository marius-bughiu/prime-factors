"""Cross-check the shared mod-32 grid against dense and independently regrouped products."""

from time import perf_counter

from experiments import geometric_lifted_readout, geometric_wheel_readout
from experiments.geometric_readout_blocks import _prepare_family, _setup
from experiments.geometric_sum_readout import _binary_classes


def _compressed_reference(n, base, lower, upper, directions):
    """Regroup the absolute roots into maximal power-of-two progressions."""
    modulus = n**3
    lifted = pow(base, n, modulus)
    root = lifted * (1 + n) % modulus
    target = pow(lifted, n + 1 - lower, modulus)
    points = {z: target * (1 + z*n) % modulus for z in directions}
    products = {z: 1 for z in directions}
    _, classes = _binary_classes(n)
    for residue, stride in classes:
        offset = (residue - lower) % stride
        first = lower + offset
        if first > upper:
            continue
        count = (upper - first) // stride + 1
        step = pow(root, stride, modulus)
        start = pow(root, offset, modulus)
        shape, work = _setup(n, step, count, 3)
        evaluate = _prepare_family(step, modulus, *shape, work)
        inverse = pow(start, -1, modulus)
        correction = pow(start, count, modulus)
        for z, point in points.items():
            products[z] = products[z] * evaluate(point * inverse % modulus) * correction % modulus
    return {str(z): value for z, value in products.items()}


def wheel_readout_case(case, proof, agree, certify_split):
    n = int(case['n'])
    args = n, case['base'], case['max_block_width'], case['max_quotient']
    start = perf_counter()
    run = geometric_wheel_readout.search(*args)
    elapsed = perf_counter() - start
    ops = run.get('block_work', {})
    run.update(signed_targets=list(map(int, run['samples'])),
               root_polynomials=ops.get('root_polynomials', 0),
               scalar_products=ops.get('scalar_products', 0),
               block_evaluations=ops.get('block_evaluations', 0))
    agree(case, run, ['outcome', 'winning_index', 'accepted_mod_32', 'dense_terms', 'total_terms',
                      'required_width', 'dense_required_width', 'common_length', 'signed_targets',
                      'scalar_products', 'root_polynomials', 'block_evaluations', 'work', 'wheel_work'])

    start = perf_counter()
    dense = geometric_lifted_readout.search(*args)
    dense_ops = dense.get('block_work', {})
    run.update(dense_seconds=perf_counter() - start, dense_outcome=dense['outcome'],
               dense_winning_index=dense['winning_index'],
               dense_block_evaluations=dense_ops.get('block_evaluations', 0),
               dense_scalar_products=dense_ops.get('scalar_products', 0),
               dense_root_polynomials=dense_ops.get('root_polynomials', 0),
               dense_factor=str(dense['factor']) if dense['factor'] else None)
    agree(case, run, ['dense_outcome', 'dense_winning_index', 'dense_block_evaluations'])
    if run['factor'] and dense['factor']:
        if sorted((run['factor'], n // run['factor'])) != sorted((dense['factor'], n // dense['factor'])):
            raise ValueError(f"{case['id']}: different measured splits")

    run['reference'] = 'unrun'
    if ops:
        start = perf_counter()
        eager = geometric_wheel_readout.search(*args, all_targets=True)
        run['eager_seconds'] = perf_counter() - start
        if (any(eager[key] != run[key] for key in
                ('factor', 'outcome', 'constant', 'linear_minus', 'linear', 'quadratic', 'winning_index'))
                or any(eager['samples'][key] != value for key, value in run['samples'].items())):
            raise ValueError(f"{case['id']}: sampling order changed the measured readings")
        start = perf_counter()
        lower, upper = int(run['origin']), int(run['last_sum'])
        if int(run['total_terms']) <= case['max_direct_terms']:
            run['reference'] = 'direct_filtered_jets'
            constant, linear, quadratic = geometric_wheel_readout.filtered_coefficients(
                n, run['reduced_base'], run['reduced_target'], lower, upper - lower + 1)
            for key, value in [('constant', constant), ('linear_minus', linear[2]),
                               ('linear', linear), ('quadratic', quadratic)]:
                if run[key] is not None and run[key] != value:
                    raise ValueError(f"{case['id']}: transported {key} disagrees with direct jets")
        else:
            run['reference'] = 'compressed_progression_products'
        products = _compressed_reference(n, case['base'], lower, upper, (-1, 0, 1))
        if products != eager['samples']:
            raise ValueError(f"{case['id']}: the three exact lifted products disagree")
        run['reference_seconds'] = perf_counter() - start
    agree(case, run, ['reference'])
    return certify_split(case, proof, run.pop('factor'), elapsed, 'geometric_wheel_readout', run)
