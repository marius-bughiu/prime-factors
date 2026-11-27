"""Exhaustive base-2 comparison on distinct pairs of 9-, 10- and 11-bit primes."""
import argparse
from collections import Counter, defaultdict
from hashlib import sha256
from itertools import combinations
import json
from math import gcd, isqrt, lcm
from pathlib import Path

from experiments.weighted_global_trace import schedule
from scripts.factor import primes_through, verify_file

ROOT = Path(__file__).resolve().parents[1]
REPORT = ROOT / "research/wrapped-gap-census.json"
FLAGS = ("precheck", "row_square", "sum_gcd", "alternate_square", "own_trace", "global_trace",
         "ordinary_fermat")
ALGEBRA = ("row_square", "sum_gcd", "alternate_square")
PRIOR = ("precheck", *ALGEBRA, "own_trace")


def scan(n, bits):
    """The complete finite search uses only n and the advertised common prime width."""
    gaps, coords, _ = schedule(n, bits, 64, 2)
    found = {name: set() for name in FLAGS}
    count = Counter()
    def check(name, value):
        g = gcd(value, n)
        count[f"{name}_gcds"] += 1
        if 1 < g < n:
            found[name].add(g)
        return g

    physical = dict.fromkeys((k,y) for k,y,_,_,_ in coords)
    midpoint = isqrt(n-1)+1
    count["ordinary_start_isqrts"] += 1
    for name, rows in (("row_square", physical),
                       ("ordinary_fermat", ((1,t) for t in range(midpoint, midpoint+len(physical))))):
        for k, y in rows:
            z = y*y-k*n
            x = isqrt(z)
            count[name+"_isqrts"] += 1
            if x*x == z:
                check(name, y-x)
                check(name, y+x)
    h = n//2
    right = {}
    by_trace = defaultdict(list)
    for e in gaps:
        v = pow(2, h*e, n)
        trace = (v+pow(v,-1,n))%n
        check("precheck", v*v-1)
        right[e] = v, trace
        by_trace[trace].append(e)
    hits = []
    for k,y,c,s,own in coords:
        x = pow(2, s-(h+1)*c, n)
        trace = (x+pow(x,-1,n))%n
        check("sum_gcd", s)
        if right[own][1] == trace:
            check("own_trace", x-right[own][0])
        for e in by_trace.get(trace, ()):
            v = right[e][0]
            g = check("global_trace", x-v)
            if 1 < g < n:
                hits.append(dict(k=k, y=y, c=c, s=s, own_gap=own, matched_gap=e,
                                 x_power=x, y_power=v, trace=trace, gcd=g))
        for e in gaps:
            z = s*s-(c*c-e*e)*n
            count["alternate_discriminants"] += 1
            if z < 0:
                continue
            count["alternate_square_isqrts"] += 1
            t = isqrt(z)
            if t*t == z:
                check("alternate_square", s-t)
                check("alternate_square", s+t)
    count.update(coordinates=len(coords), right_gaps=len(gaps))
    return found, hits, count


def order_two(p):
    order, value = 1, 2%p
    while value != 1:
        order, value = order+1, 2*value%p
    return order


def verified_pairs(primes, examples):
    ns = "PrimeFactors.WrappedGapCensus"
    members = "[" + ",\n".join(f"⟨{p}, by norm_num⟩" for p in primes) + "]"
    code = ["import PrimeFactors.Certificate", "import Mathlib.Tactic.NormNum.Prime",
            "set_option maxRecDepth 16384", "set_option maxHeartbeats 3000000", f"namespace {ns}",
            f"private def catalog : List {{p : ℕ // Nat.Prime p}} := {members}",
            "private def selected := catalog.map Subtype.val",
            "private theorem prime (p : ℕ) (h : p ∈ selected) : Nat.Prime p := by",
            "  obtain ⟨u, _, rfl⟩ := List.mem_map.mp h",
            "  exact u.property",
            "theorem panel (p q : ℕ) (hp : p ∈ selected) (hq : q ∈ selected) :",
            "    ExactFactorization (p*q) [p,q] := by",
            "  apply ExactFactorization.cons (n := q) (prime p hp)",
            "  simpa using (ExactFactorization.cons (n := 1) (prime q hq) exactFactorization_nil)",
            "#print axioms panel"]
    for n, p, q in examples:
        code.extend([f"example : ExactFactorization {n} [{p},{q}] :=",
                     f"  panel {p} {q} (by decide +kernel) (by decide +kernel)"])
    code.extend([f"end {ns}", ""])
    path = ROOT / "build/WrappedGapCensus.lean"
    path.parent.mkdir(exist_ok=True)
    path.write_text("\n".join(code))
    verify_file(path, ns+".panel")
    return dict(theorem=ns+".panel", distinct_primes=len(primes), examples=len(examples),
                sha256=sha256(path.read_bytes()).hexdigest())


def census(verify=False):
    groups, examples, selected = [], [], []
    for bits in (9,10,11):
        primes = [p for p in primes_through((1<<bits)-1) if p >= 1<<(bits-1)]
        trial_primes = [p for p in range(1<<(bits-1), 1<<bits)
                        if all(p%d for d in range(2,isqrt(p)+1))]
        if primes != trial_primes:
            raise ArithmeticError("the sieve and trial-division prime lists disagree")
        selected.extend(primes)
        orders = {p:order_two(p) for p in primes}  # Retrospective labels, never passed to scan.
        for length in (2*bits-1, 2*bits):
            groups.append(dict(prime_bits=bits, product_bits=length, primes=len(primes),
                               totals=Counter(), joint=Counter(), work=Counter(), examples=[]))
        digests = [sha256(), sha256()]
        for p,q in combinations(primes, 2):
            n = p*q
            high = n.bit_length()-(2*bits-1)
            cell = groups[-2+high]
            found, hits, work = scan(n, bits)
            if any(g not in (p,q) or n%g for gs in found.values() for g in gs):
                raise ArithmeticError("a product-only gcd was inconsistent with the census input")
            if not found["own_trace"] <= found["global_trace"]:
                raise ArithmeticError("a full lookup dropped an own-gap factor")
            cell["work"].update(work)
            mask = sum(1<<i for i,key in enumerate(FLAGS) if found[key])
            cell["joint"][str(mask)] += 1
            tot = cell["totals"]
            tot["products"] += 1
            for key in FLAGS:
                tot[key] += bool(found[key])
            prior = any(found[k] for k in PRIOR)
            alg = any(found[k] for k in ALGEBRA)
            full = bool(found["global_trace"])
            setup = bool(found["precheck"])
            tot["own_with_setup"] += bool(found["own_trace"] or setup)
            tot["global_with_setup"] += full or setup
            tot["any_scalar_check"] += alg
            tot["any_prior"] += prior
            tot["off_gap_beyond_own_and_setup"] += full and not (found["own_trace"] or setup)
            tot["global_beyond_scalar_and_setup"] += full and not (alg or setup)
            tot["global_beyond_prior"] += full and not prior
            tot["global_beyond_prior_and_ordinary"] += full and not (prior or found["ordinary_fermat"])
            digest = [n, [sorted(found[k]) for k in FLAGS]]
            digests[high].update(json.dumps(digest, separators=(",",":")).encode()+b"\n")
            if not full or prior:
                continue
            m, j, order = (p+q)//2, (q-p)//2, lcm(orders[p],orders[q])
            for hit in hits:
                c,s,e = hit["c"],hit["s"],hit["matched_gap"]
                if hit["own_gap"] == e or gcd(hit["y_power"]**2-1,n) != 1:
                    raise ArithmeticError("a strongest gain was not a clear off-gap hit")
                multiples = [(s-value)//order for value in (m*c+j*e,m*c-j*e)
                             if (s-value)%order == 0]
                if not multiples or 0 in multiples:
                    raise ArithmeticError("a gain escaped the wrapped-sum identity")
                tot["wrapped_hit_coordinates_beyond_prior"] += 1
                if len(cell["examples"]) < 3 and (not cell["examples"] or cell["examples"][-1]["n"] != str(n)):
                    examples.append((n,p,q))
                    cell["examples"].append(dict(n=str(n), factors=[str(p),str(q)], hit=hit,
                                                 base_order=order, wrap_multiples=multiples,
                                                 alternate_discriminant=s*s-(c*c-e*e)*n,
                                                 ordinary_fermat_split=bool(found["ordinary_fermat"])))
        if sum(g["totals"]["products"] for g in groups[-2:]) != len(primes)*(len(primes)-1)//2:
            raise ArithmeticError("the two product widths did not partition the prime pairs")
        for group, digest in zip(groups[-2:], digests):
            group["outcomes_sha256"] = digest.hexdigest()
    return dict(base=2, multiplier_limit=64, coordinates_per_row=2,
                population="All p<q among primes with the same indicated factor width.",
                joint_definition="Mask bit i records any proper gcd from flag_bits[i], excluding setup from both trace flags.",
                alternate_definition="For every coordinate and every scheduled gap e, if s²−(c²−e²)N is a nonnegative integer square t², check both gcd(s−t,N) and gcd(s+t,N).",
                ordinary_definition="Consecutive Fermat midpoints from ceil(sqrt(N)), one per distinct scheduled (k,y).",
                wrap_definition="Signed quotient (s−(c(p+q)/2 ± e(q−p)/2))/ord_N(2), measured only after a public split.",
                checks="The sieve and independent trial division agree on the complete prime list. The Python search verifies every returned proper gcd equals one of the enumeration primes. The Lean certificate proves primality for the entire enumerated prime list and verifies the factorization of any product from that list.",
                flag_bits=list(FLAGS), prior_union=list(PRIOR), cells=groups,
                certificate=verified_pairs(selected,examples) if verify else None)


if __name__ == "__main__":
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument("--write", action="store_true")
    cli.add_argument("--verify", action="store_true")
    args = cli.parse_args()
    result = census(args.verify)
    output = json.dumps(result, indent=2) + "\n"
    if args.write:
        REPORT.write_text(output)
    else:
        print(output, end="")
