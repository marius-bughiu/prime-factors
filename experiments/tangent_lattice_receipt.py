"""Generate checked pointwise block budgets for public signed conic charts."""

from collections import Counter
from math import gcd, isqrt
from time import perf_counter

from experiments.mixed_ratio_heights import jacobi
from experiments.phase_interval import cube_radius
from experiments.salie_reference import ceil_div
from experiments.signed_norm_arcs import charts, domain_size, menu, possible, unit_multiplier
from experiments.tangent_lattice_arcs import collect, modulus
from scripts.factor import primes_through, verify_file


def public_charts(n):
    """The normalized full-size receipts currently cover rows with absolute multiplier one."""
    rows = []
    for d in menu(n, "signed"):
        m = unit_multiplier(n,d)
        if m != 1 or any(n % h not in possible(d,h) for h in (16,3)):
            raise ValueError("count receipt requires the locally admitted multiplier +1 in each chart")
        for hyperbolic,a,b,_,x in charts(n,d,m,Counter(),"unit"):
            sign = 1 if hyperbolic else -1
            k = 2 if d==2 else 4 if d==6 else 1
            w = max(1,cube_radius(8*isqrt(b*n)//a))
            h,t,phi = modulus(n,a,b,sign,"through257")
            if not 0<h<=w or not x:
                raise ValueError("positive complete-chart stride is unavailable")
            rows.append(dict(d=d,a=a,b=b,k=k,s=sign,x=x,w=w,h=h,t=t,c=n*pow(b,-1,h)%h,
                             phi=phi,ordinary=ceil_div(x,w),upper=phi*ceil_div(x,h*(w-h+1))))
    return rows


def chart_type(n,r):
    keys = ("a","b","k","x","w","h","phi","ordinary","upper")
    return "Chart "+n+" "+" ".join(str(r[k]) for k in keys)+f' ({r["s"]})'


def count_proof(n, rows):
    targets = menu(n,"signed")
    ordinary = sum(r["ordinary"] for r in rows)
    upper = sum(r["upper"] for r in rows)
    ppm = ceil_div(10**6*upper,ordinary)
    bits = ["import PrimeFactors.ConicTangentReceipt",
            "set_option maxRecDepth 8192", "namespace PrimeFactors.TangentControl",
            "open ConicTangentReceipt", f"private abbrev input : ℕ := {n}",
            "private theorem odd_input : Odd input := Nat.odd_iff.mpr (by decide +kernel)"]
    dlist = [-1,2,-2,3,-3,6,-6]
    for i,d in enumerate(dlist):
        bits.extend([f"private theorem symbol{i} : jacobiSym ({d}) input = {jacobi(d,n)} := by",
                     f"  rw [jacobiSym.mod_right ({d}) odd_input]",
                     f"  change jacobiSym ({d}) {n%(4*abs(d))} = {jacobi(d,n)}", "  norm_num"])
    bits.extend([f"private theorem selected : targets input = {targets} := by",
                 "  simp [targets, "+", ".join(f"symbol{i}" for i in range(len(dlist)))+"]"])
    plan = "["+", ".join(f'({r["a"]},{r["b"]},{r["k"]},1,{r["s"]})' for r in rows)+"]"
    bits.extend([f"private theorem plan : (targets input).flatMap (shapes input) = {plan} := by",
                 "  rw [selected]", "  decide +kernel",
                 "private theorem admitted : ∀ d ∈ targets input, ∃ x y : ℤ, (x^2-d*y^2-input)%48=0 := by",
                 "  intro d hd", "  rw [selected] at hd",
                 "  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd",
                 "  rcases hd with "+"|".join("rfl" for _ in targets)])
    for d in targets:
        u,v = next((x,y) for x in range(48) for y in range(48) if (x*x-d*y*y-n)%48==0)
        bits.append(f"  · exact ⟨{u},{v},by decide +kernel⟩")
    emitted = {1}
    bits.append("private theorem phi1 : Nat.totient 1=1 := by decide +kernel")
    for i, r in enumerate(rows):
        h, a, b, sign, t, c = (r[k] for k in ("h","a","b","s","t","c"))
        prev = phi = 1
        for p in primes_through(257):
            if h % p:
                continue
            if prev*p not in emitted:
                bits.extend([f"private theorem phi{prev*p} : Nat.totient {prev*p}={phi*(p-1)} :=",
                             f"  totient_step (a:={prev}) (p:={p}) phi{prev} (by decide +kernel) (by decide +kernel)"])
                emitted.add(prev*p)
            prev *= p
            phi *= p-1
        if (prev,phi) != (h,r["phi"]):
            raise ArithmeticError("wheel is not the squarefree product recorded")
        bits.extend([f"private theorem chart{i} : {chart_type('input',r)} := by",
                     "  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel,",
                     "    by decide +kernel, by decide +kernel, ?_⟩",
                     f"  apply (physical_count (h:={h}) (b:={b}) (a:=(({sign}:ℤ):ZMod {h})*{a})",
                     f"    (M:=input) (t:={t}) (c:={c}) ?_ ?_ ?_ ?_ ?_ ?_).trans phi{h}"])
        for v in [2,b,t,c]:
            bits.append(f"  · exact (ZMod.isUnit_iff_coprime {v} {h}).mpr (by decide +kernel)")
        bits.extend(["  · decide +kernel", "  · decide +kernel"])
    caps = " + ".join(str(r["upper"]) for r in rows)
    normal = " + ".join(str(r["ordinary"]) for r in rows)
    limits = " → ".join(f'Counted {r["x"]} {r["w"]} {r["h"]} {r["phi"]} b{i}'
                        for i,r in enumerate(rows))
    names = " ".join(f"b{i}" for i in range(len(rows)))
    total = "+".join(names.split())
    bits.extend(["theorem budget :", f"    (targets input).flatMap (shapes input) = {plan} ∧",
                 "    (∀ d ∈ targets input, ∃ x y : ℤ, (x^2-d*y^2-input)%48=0) ∧"])
    bits.extend(f"    {chart_type('input',r)} ∧" for r in rows)
    bits.extend([f"    ({normal} : ℕ) = {ordinary} ∧ ({caps} : ℕ) = {upper} ∧",
                 f"    ({ppm-1} : ℕ)*{ordinary}<1000000*{upper} ∧",
                 f"    (∀ {names} : ℕ, {limits} → {total}≤{upper} ∧ 1000000*({total})≤{ppm}*{ordinary}) := by",
                 "  refine ⟨plan, admitted, "+", ".join(f"chart{i}" for i in range(len(rows)))+
                 ", by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩",
                 f"  intro {names} "+" ".join(f'h{i}' for i in range(len(rows))),
                 *(f"  have cap{i} := chart{i}.counted h{i}" for i in range(len(rows))),
                 f"  have precise : {total}≤{upper} := by omega",
                 f"  exact ⟨precise,(Nat.mul_le_mul_left 1000000 precise).trans (by decide +kernel)⟩",
                 "#print axioms budget", "end PrimeFactors.TangentControl"])
    return "\n".join(bits)+"\n"


def split_points(n, points):
    previous = {}
    for d,m,x,y in points:
        divisor = gcd(n,y)
        if 1<divisor<n:
            return divisor, [[d,m,x,y]]
        if divisor != 1:
            continue
        r = x*pow(y,-1,n)%n
        if d in previous:
            old, witness = previous[d]
            divisor = gcd(r-old,n)
            if 1<divisor<n:
                return divisor, [witness,[d,m,x,y]]
        else:
            previous[d] = (r,[d,m,x,y])
    return None, []


def benchmark_case(case, proof, certify_split):
    n, mode = int(case["n"]), case["mode"]
    start = perf_counter()
    if mode=="scan":
        positions, ordinary = domain_size(n,"unit")
        if positions>case["max_chart_positions"]:
            raise ValueError("complete CRT2 fixture exceeds its position budget")
        points, work = collect(n,"pair")
        factor, witnesses = split_points(n,points)
        work.update(mode=mode,points=len(points),ordinary_blocks=str(ordinary),
                    chart_positions=str(positions),witnesses=witnesses)
    elif mode=="count":
        rows = public_charts(n)
        ordinary = sum(r["ordinary"] for r in rows)
        upper = sum(r["upper"] for r in rows)
        work = dict(mode=mode,ordinary_blocks=str(ordinary),tangent_block_upper=str(upper),
                    upper_ppm=ceil_div(1000000*upper,ordinary),classes=str(sum(r["phi"] for r in rows)),
                    charts=len(rows),scanned_blocks=0)
        factor = None
    else:
        raise ValueError("unknown tangent lattice benchmark")
    elapsed = perf_counter()-start
    if any(work[k]!=v for k,v in case["checks"].items()):
        raise ValueError(f'{case["id"]}: tangent work differs from expectation')
    if mode=="count":
        began = perf_counter()
        proof.write_text(count_proof(n,rows))
        verify_file(proof,"PrimeFactors.TangentControl.budget")
        work.update(proof=f"proofs/{proof.name}",verification_seconds=perf_counter()-began)
    return certify_split(case,proof,factor,elapsed,"tangent_lattice",work)
