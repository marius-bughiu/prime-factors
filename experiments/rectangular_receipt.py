"""Run a rectangular search and certify its public row and coordinate bounds."""
from math import isqrt
from time import perf_counter

from experiments.rectangular_root_windows import run, targets
from experiments.rectangular_weight_panel import price
from scripts.factor import verify_file


def count_source(n, bits, data):
    b,h,k,cap = (int(data[key]) for key in ('denominator_cap','numerator_cap','rows','allowed_at_most'))
    scale, excess = data['ratio_scale'], data['ratio_excess']
    lower = isqrt(n)
    root_k = isqrt(k)
    root_quarter = isqrt(k//4)
    digits = root_k.bit_length()
    coordinates = int(data['coordinates_at_most'])
    size_lower = (f'exact (Nat.lt_size (m:={digits-1}) (n:={root_k})).mpr (by decide +kernel)'
                  if digits else 'exact Nat.zero_le _')
    return f"""import PrimeFactors.RectangularWeightCost

set_option maxRecDepth 8192
set_option exponentiation.threshold 8192
namespace PrimeFactors.RectangularExample
private abbrev n : ℕ := {n}
private abbrev b : ℕ := {b}
private abbrev h : ℕ := {h}
private abbrev k : ℕ := {k}
private abbrev scale : ℕ := {scale}
private abbrev excess : ℕ := {excess}
private abbrev cap : ℕ := {cap}
private abbrev cells : ℕ := {coordinates}

private theorem sqrtValue {{v s : ℕ}} (low : s^2≤v) (high : v<(s+1)^2) : v.sqrt=s :=
  le_antisymm (Nat.le_of_lt_succ (Nat.sqrt_lt'.mpr high)) (Nat.le_sqrt'.mpr low)

private theorem bounds {{N B H K R e nr kr qr size rowCap cellCap : ℕ}}
    (np : 0<N) (rp : 0<R) (sn : N.sqrt=nr) (sk : K.sqrt=kr) (sq : (K/4).sqrt=qr)
    (digits : kr.size=size)
    (rows : 4*R*((kr+1)/2+qr)+2*e*((kr+1)/2)^2+e*qr*(qr+1)<4*R*(rowCap+1))
    (paired : (4*R*((kr+1)/2+qr)+2*e*((kr+1)/2)^2+e*qr*(qr+1))/(4*R)+
      H^2*(6*R*(size+1)+2*e*((kr+1)/2)+e*qr)/(8*R*nr)≤cellCap) :
    (RectangularMultiplierCount.allowed K R e).card≤rowCap ∧
      RectangularWeightCost.coordinates N B H K R e≤cellCap := by
  constructor
  · apply RectangularMultiplierCount.at_most K R e rowCap
    dsimp only
    rwa [sk,sq]
  · apply (RectangularWeightCost.bound N B H K R e np rp).trans
    unfold RectangularWeightCost.pairCap
    dsimp only
    rwa [sn,sk,sq,digits]

theorem checked :
    n/(b+1)=h ∧ b^2/n=k ∧ h^2<n ∧ b+h<n ∧ h<2^{bits-1} ∧
    {lower}^2≤n ∧ n<({lower}+1)^2 ∧ h<{lower} ∧
    (2^{bits}-1)^2*scale*({lower}+h)≤n*(scale+excess)*({lower}-h) ∧
    (RectangularMultiplierCount.allowed k scale excess).card≤cap ∧
    cap*10000≤{(10000*cap+k-1)//k}*k ∧
    RectangularWeightCost.coordinates n b h k scale excess≤cells ∧
    cells*10000≤{(10000*coordinates+k-1)//k}*k := by
  have sn : n.sqrt={lower} := sqrtValue (v:=n) (s:={lower}) (by decide +kernel) (by decide +kernel)
  have sk : k.sqrt={root_k} := sqrtValue (v:=k) (s:={root_k}) (by decide +kernel) (by decide +kernel)
  have sq : (k/4).sqrt={root_quarter} := sqrtValue (v:=k/4) (s:={root_quarter}) (by decide +kernel) (by decide +kernel)
  have digits : ({root_k}:ℕ).size={digits} := by
    apply le_antisymm ((Nat.size_le (m:={root_k}) (n:={digits})).mpr (by decide +kernel))
    {size_lower}
  have both := bounds (N:=n) (B:=b) (H:=h) (K:=k) (R:=scale) (e:=excess)
    (rowCap:=cap) (cellCap:=cells) (by decide +kernel) (by decide +kernel)
    sn sk sq digits (by decide +kernel) (by decide +kernel)
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, both.1, by decide +kernel, both.2, by decide +kernel⟩
#print axioms checked
end PrimeFactors.RectangularExample
"""


def observation(case):
    n = int(case['n'])
    weights = case['method_rule']=='weights'
    ds = [1] if weights else targets(n,case['method_rule'])
    result = run(n,ds,rows=case['rows'],per_row=case['per_row'],stop=True,
                 factor_bits=case['factor_bits'] if weights else None)
    work = result['work']
    report = dict(targets=ds,first=result['first'], factor=result['factor'], rows=work['rows'],
                  intervals=work['intervals'],coordinates=work['coordinates'],square_tests=work['square_tests'],
                  trimmed_positions=str(work['truncated_positions']), row_limits=result['row_limits'],
                  weight_pairs=work.get('weight_pairs',0),rows_limit=case['rows'],per_row=case['per_row'])
    if weights:
        report['bound'] = price(n,case['factor_bits'])
    return report


def benchmark(case,proof,agree,certify_split):
    start=perf_counter()
    report=observation(case)
    elapsed=perf_counter()-start
    agree(dict(id=case['id'],**case['checks']),report,case['checks'])
    result=certify_split(case,proof,report['factor'],elapsed,'rectangular_windows',report)
    if 'bound' in report:
        check=proof.with_name(proof.stem+'-bound.lean')
        start=perf_counter()
        check.write_text(count_source(int(case['n']),case['factor_bits'],report['bound']))
        verify_file(check,'PrimeFactors.RectangularExample.checked')
        report['proof']='proofs/'+check.name
        report['count_seconds']=perf_counter()-start
    return result
