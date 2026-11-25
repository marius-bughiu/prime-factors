"""Affine signed-gap residues at a public divisor of the coordinate product."""

from math import gcd, lcm


UNITS_24 = (1,5,7,11,13,17,19,23)


def _explicit_trace_unit_classes(n, t, s, v, first, length, e, split_only, work):
    """Classify traces by possible units p mod 24; each trace belongs to at most one row."""
    s2,v2 = s*s,v*v
    k = s*v
    K = k*k
    sign = 1-2*e
    H = (s2 + (n%24)*v2) % 24
    coeff = (e//v2 - (n%24)*((1-e)//s2)) % 24
    fibers = {}
    for unit in UNITS_24:
        fibers.setdefault(H*unit % 24,[]).append(unit)
    if work is not None:
        work['trace_unit_images'] = work.get('trace_unit_images',0) + len(UNITS_24)
        work.setdefault('trace_rejected_offsets',0)
        work.setdefault('fiber_gcd_steps',0)
    classes = []
    for start in range(min(12,length)):
        trace = first+2*start+2*t*k
        count = 1+(length-1-start)//12
        units = fibers.get(trace % 24)
        if work is not None:
            work['classes_checked'] += 1
        if units is None:
            if work is not None:
                work['trace_rejected_offsets'] += count
                work['rejected_classes'] += 1
            continue
        if work is not None:
            work['unit_classes'] += 1
        if split_only:
            modulus = 4*K
            residue = s2-v2+sign*(trace-s2-v2)
        else:
            r = units[0]
            common = 24
            for other in units[1:]:
                common = gcd(common,coeff*(other-r))
                if work is not None:
                    work['fiber_gcd_steps'] += 1
            modulus = 2*K*common
            residue = sign*trace+2*K*coeff*r
        classes.append((start,12,count,residue % modulus,24*sign % modulus,modulus))
    return classes


def _trace_unit_classes(n, t, s, v, first, length, e, split_only, work):
    """Combine all admissible trace residues into at most two affine progressions."""
    s2,v2 = s*s,v*v
    k = s*v
    K = k*k
    sign = 1-2*e
    h = (s2 + (n%24)*v2) % 24
    g = gcd(h,24)
    f = 24//g
    L = lcm(2,f)
    coeff = (e//v2 - (n%24)*((1-e)//s2)) % 24
    # S=g*u, gcd(u,f)=1, p=(h/g)^(-1)*u mod f. Units for f|24
    # equal their own inverses. For odd f choose the odd representative.
    a = (h//g) % f
    intercept = 0
    if f%2:
        a += (a%2)*f
        intercept = f
    period = (2 if f%2 == 0 else 1) * (3 if f%3 == 0 else 1)
    unit_starts = {1:(0,),2:(1,),3:(1,2),6:(1,5)}[period]
    trace = first+2*t*k
    trace_step = g*period
    stride = trace_step//2
    classes = []
    for u in unit_starts:
        delta = (g*u-trace) % trace_step
        start = delta//2
        if start >= length:
            continue
        S = trace+delta
        count = 1+(length-1-start)//stride
        if split_only:
            modulus = 4*K
            residue = s2-v2+sign*(S-s2-v2)
            step = sign*trace_step
        else:
            modulus = 2*K*L
            unit = (a*(S//g)+intercept) % L
            residue = sign*S+2*K*coeff*unit
            step = sign*trace_step+2*K*coeff*a*period
        classes.append((start,stride,count,residue%modulus,step%modulus,modulus))
    if work is not None:
        work['trace_image_gcds'] = work.get('trace_image_gcds',0)+1
        work['classes_checked'] += len(unit_starts)
        work['unit_classes'] += len(classes)
        work['trace_rejected_offsets'] = work.get('trace_rejected_offsets',0)+length-sum(row[2] for row in classes)
    return sorted(classes)


def choose_divisor(k, cap, work=None):
    """Largest divisor of k at most cap, by bounded trial division."""
    if min(k, cap) < 1:
        raise ValueError('positive coordinate product and divisor cap required')
    if work is not None:
        work.setdefault('divisor_trials',0)
    for d in range(min(k,cap), 0, -1):
        if work is not None:
            work['divisor_trials'] += 1
        if k % d == 0:
            return d


def affine_classes(n, t, s, v, first, length, divisor, *, split_only=False,
                   square8=False, square24=False, trace_units=False, explicit_trace=False, work=None):
    """Return (start,stride,count,residue,slope,modulus) in parity-index coordinates.

    At position m of an entry, j = first + 2*(start + stride*m).
    Modulo modulus the allowed signed gap is residue + slope*m. With
    trace_units=True the d=1 chart for gcd(N,6)=1 also enforces the
    possible images of the unknown factor units mod 24. On unsupported
    inputs this option falls back to the ordinary divisor lift.
    """
    if n % 2 != 1 or n < 1 or t < 0 or min(s,v,divisor) < 1 or gcd(s,v) != 1:
        raise ValueError('expected odd N, coprime positive coordinates and a positive divisor')
    k = s*v
    if k % divisor or length < 0 or (first-s-v)%2:
        raise ValueError('invalid divisor or parity window')
    if not length:
        return []
    if work is not None:
        for key in ('orientation_inverses','class_gcd_checks','classes_checked','unit_classes',
                    'rejected_classes','nonunit_offsets','class_inverses'):
            work.setdefault(key,0)
    use_units = trace_units and divisor == 1 and n%3 != 0
    if trace_units and work is not None:
        work['trace_unit_fallbacks'] = work.get('trace_unit_fallbacks',0) + int(not use_units)
    odd_trace = not trace_units and (square8 or square24) and k%2 == 0
    self_inverse24 = square24 and odd_trace and divisor == 1 and n%3 != 0
    ds = 1 if split_only else gcd(s,divisor)
    dv = 1 if split_only else divisor//ds
    if self_inverse24 and not split_only:
        # Use the full fourth-power orientation for both precisions in this chart.
        ds,dv = s,v
    s2,v2 = s*s,v*v
    left,right = (s*ds)**2,(v*dv)**2
    # E=1 on the s side, E=0 on the v side, to the precision actually used.
    e = right*pow(right, -1, left) if left > 1 else 0
    sign = 1-2*e
    if work is not None:
        work['orientation_inverses'] += int(left > 1)
    if use_units:
        make_classes = _explicit_trace_unit_classes if explicit_trace else _trace_unit_classes
        return make_classes(n,t,s,v,first,length,e,split_only,work)
    big_k = k*k
    parity = (e//v2 + (e-1)//s2) % 2
    stride = 3 if self_inverse24 else divisor if odd_trace else divisor//gcd(divisor,2)
    gcd_divisor = 3 if self_inverse24 and k%3 == 0 else divisor
    delta = 2*stride
    d2 = divisor*divisor
    modulus = 4*big_k if split_only else 2*big_k*lcm(2,d2)
    if odd_trace and not split_only:
        # Multiplying the signed gap by the trace uses only the public
        # squares of the odd factors modulo 8, namely p²=q²=1 mod 8.
        modulus = 16*big_k*d2
        correction = 2*(e*s2*s2-(1-e)*v2*v2)-2*sign*n*big_k
    classes = []
    for start in range(min(stride,length)):
        j = first+2*start
        count = 1 + (length-1-start)//stride
        if work is not None:
            work['classes_checked'] += 1
            work['class_gcd_checks'] += int(gcd_divisor > 1)
        if gcd_divisor > 1 and gcd(j,gcd_divisor) != 1:
            if work is not None:
                work['nonunit_offsets'] += count
                work['rejected_classes'] += 1
            continue
        trace = j+2*t*k
        if work is not None:
            work['unit_classes'] += 1
        if odd_trace and not split_only:
            period_modulus = modulus
            if divisor == 1:
                if self_inverse24 and trace%3:
                    period_modulus = 48*big_k
                # Each unit is its own inverse modulo both 8 and 24.
                residue = (sign+correction)*trace
                slope = (sign+correction)*delta
            else:
                period = 8*d2
                inverse = pow(trace % period,-1,period)
                if work is not None:
                    work['class_inverses'] += 1
                # Delta=2d. The second difference of the inverse vanishes
                # modulo 8d² since m*(m-1) is even for integer m.
                increment = delta*inverse*inverse*(delta*inverse-1) % period
                residue = sign*trace+correction*inverse
                slope = sign*delta+correction*increment
            classes.append((start,stride,count,residue % period_modulus,slope % period_modulus,period_modulus))
            continue
        if split_only or divisor == 1:
            residue = (s2-v2+sign*(trace-s2-v2)) % modulus
            slope = sign*delta % modulus
            classes.append((start,stride,count,residue,slope,modulus))
            continue
        inverse = pow(trace % d2, -1, d2)
        if work is not None:
            work['class_inverses'] += 1
        if inverse % 2 != parity:
            if d2 % 2 == 0:
                raise ArithmeticError('dyadic orientation parity mismatch')
            inverse += d2
        # (trace + delta*m)^-1 = inverse − delta*m*inverse² (mod d²).
        # delta is even, so the chosen inverse parity stays fixed as well.
        residue = sign*(trace-2*n*big_k*inverse) % modulus
        slope = sign*delta*(1+2*n*big_k*inverse*inverse) % modulus
        classes.append((start,stride,count,residue,slope,modulus))
    return classes


def compare(case, cap=8, unit_square=1, rounds=3, *, trace_units=False):
    """Compare residues at identical coordinates, gcd classes, interval and test budgets."""
    import json
    from pathlib import Path
    from statistics import median
    from time import process_time_ns

    from experiments.offset_coordinate_gaps import search

    ids = {'49':'signed-gap-chords-49','fresh':'signed-gap-fresh-2048',
           'crossed':'signed-gap-crossed-2048'}
    if case not in ids or rounds < 1:
        raise ValueError('expected a published comparison input and at least one round')
    fixture = Path(__file__).resolve().parents[1]/'benchmarks/offset-coordinate-gaps.json'
    row = next(r for r in json.loads(fixture.read_text()) if r['id'] == ids[case])
    # Only public inputs and preregistered budgets are read from the fixture.
    args = dict(all_vectors=row['all_vectors'],max_vectors=row['max_vectors'],max_tests=row['max_tests'],
                lift_cap=cap,unit_square=unit_square,trace_units=trace_units)
    times = {'split':[], 'lift':[]}
    runs = {}
    for i in range(rounds):
        for name in (('split','lift') if i%2==0 else ('lift','split')):
            start = process_time_ns()
            run = search(int(row['n']),row['parts'],split_only=name=='split',**args)
            times[name].append(process_time_ns()-start)
            runs[name] = run
    for name,run in runs.items():
        run['median_cpu_ns'] = median(times[name])
    if runs['split']['hits'] != runs['lift']['hits'] and row['all_vectors']:
        raise AssertionError('complete matched searches disagree on accepted positions')
    for key in ('vectors','parity_positions','classes','eligible_positions','intervals','bound_roots'):
        if runs['split'].get(key) != runs['lift'].get(key):
            raise AssertionError('comparison windows differ at '+key)
    return dict(case=case,rounds=rounds,runs=runs)


if __name__ == '__main__':
    import argparse
    import json

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--case',choices=('49','fresh','crossed'),default='49')
    parser.add_argument('--cap',type=int,default=8)
    parser.add_argument('--unit-square',type=int,choices=(1,8,24),default=1)
    parser.add_argument('--trace-units',action='store_true',
                        help='combine the divisor lift with possible factor residues modulo 24')
    parser.add_argument('--rounds',type=int,default=3)
    args = parser.parse_args()
    print(json.dumps(compare(args.case,args.cap,args.unit_square,args.rounds,trace_units=args.trace_units),indent=2))
