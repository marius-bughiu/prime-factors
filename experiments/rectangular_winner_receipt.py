"""Check complete winning-row classifications against the published prime certificates."""
import json
from math import isqrt
from pathlib import Path

from experiments.certified_control import lean_source
from experiments.offset_tangent_cover import cube_root
from experiments.offset_winner_positions import published_controls
from experiments.rectangular_winning_rows import report
from scripts.factor import render_certificate, verify_file

ROOT = Path(__file__).resolve().parents[1]


def source(label, p, q, r):
    n = p*q
    if label == 'fresh':
        control = json.loads((ROOT/'research/certified-control.json').read_text())
        primes = lean_source(control, include_signature=False)
    elif label == 'crossed':
        primes = render_certificate(n, [p,q])
    else:
        raise ValueError('this receipt requires two full-size winning rows')
    wins = sorted((s for s in r['neighbors'] if s['inside']), key=lambda s: int(s['multiplier']))
    if len(wins) != 2:
        raise ValueError('expected two primitive witnesses in the recorded rectangle')
    start, second = (s['multiplier'] for s in wins)
    t = cube_root(n-1)+1
    ws = []
    for i, w in enumerate(wins):
        ws.append(f"""private theorem win{i} : Hit n b h {w['multiplier']} true :=
  ⟨by decide +kernel, {w['x']}, {w['y']}, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    fun _ => by decide +kernel⟩""")
    witnesses = '\n'.join(ws)
    return 'import PrimeFactors.RectangularRowNormalization\nimport PrimeFactors.RectangularDistinctProducts\n' + primes + f"""
set_option maxRecDepth 8192
set_option exponentiation.threshold 8192
namespace PrimeFactors.RectangularWinners
open RectangularRowNormalization RectangularFullWidth
private abbrev p : ℕ := {p}
private abbrev q : ℕ := {q}
private abbrev n : ℕ := {n}
private abbrev b : ℕ := {r['denominator_cap']}
private abbrev h : ℕ := {r['numerator_cap']}
private abbrev last : ℕ := {r['last_multiplier']}

private theorem dimensionsFromBounds {{N T S box height cap : ℕ}}
    (tl : (T-1)^3<N) (tu : N≤T^3) (sl : S^2≤N) (su : N<(S+1)^2)
    (bin : max (N/T) (S+1)=box) (hin : N/(box+1)=height) (kin : box^2/N=cap) :
    B N=box ∧ H N=height ∧ K N=cap := by
  have cube := CubicForcedParameters.ceilCube_eq tl tu
  have root : N.sqrt=S := le_antisymm (Nat.le_of_lt_succ (Nat.sqrt_lt'.mpr su)) (Nat.le_sqrt'.mpr sl)
  have eq : B N=box := by rw [B,cube,root,bin]
  exact ⟨eq,by rw [H,eq,hin],by rw [K,eq,kin]⟩

private theorem dimensionsCheck : B n=b ∧ H n=h ∧ K n=last := by
  apply dimensionsFromBounds (N:=n) (T:={t}) (S:={isqrt(n)}) (box:=b) (height:=h) (cap:=last)
  all_goals decide +kernel

private theorem relax {{N B H k : ℕ}} (hit : Hit N B H k true) : Hit N B H k false := by
  obtain ⟨kp,x,y,yp,yb,xh,eq,_⟩ := hit
  exact ⟨kp,x,y,yp,yb,xh,eq,fun bad => Bool.noConfusion bad⟩

{witnesses}

theorem checked :
    (∀ k≤K n, Hit n (B n) (H n) k false ↔ k={start} ∨ k={second}) ∧
    2^681<{start} ∧ {start}<{second} ∧
    2^501 ≤ ((RectangularSearchFloor.emitted (K n) 1024 (excess n)).filter (· < {start})).card := by
  have pp : p.Prime := Generated.factorization.2 p (by decide +kernel)
  have qp : q.Prime := Generated.factorization.2 q (by decide +kernel)
  have prod : p*q=n := by decide +kernel
  have two := only_two (i:={start}) (j:={second}) (B:=b) (H:=h) (K:=last) pp qp (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by rw [prod]; exact win0) (by rw [prod]; exact win1) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  rw [prod] at two
  obtain ⟨bb,hh,kk⟩ := dimensionsCheck
  rw [bb,hh,kk]
  have pos := RectangularSearchFloor.positive_excess (p:=p) (q:=q)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  rw [prod] at pos
  refine ⟨?_,by decide +kernel,by decide +kernel,
    RectangularDistinctProducts.prefix_visits (limit:=last) (stop:={start}) (e:=excess n) (by decide +kernel) (by decide +kernel) pos⟩
  intro k cap
  refine ⟨two k cap,?_⟩
  rintro (rfl|rfl)
  · exact relax win0
  · exact relax win1
#print axioms checked
end PrimeFactors.RectangularWinners
"""


def verify():
    data = report()
    if data != json.loads((ROOT/'research/rectangular-winning-rows.json').read_text()):
        raise ValueError('stored diagnostic differs from the recomputed records')
    by_name = {r['id']: r for r in data['controls']}
    for label, _, p, q in published_controls():
        if label == 'small':
            continue
        out = ROOT/'build/site/proofs'/f'rectangular-exact-{label}-2048.lean'
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_text(source(label,p,q,by_name[label]))
        verify_file(out, 'PrimeFactors.RectangularWinners.checked')
        print(f'{label} exact row classification passed', flush=True)


if __name__ == '__main__':
    verify()
