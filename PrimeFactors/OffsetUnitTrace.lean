import PrimeFactors.OffsetGapLift

namespace PrimeFactors.OffsetUnitTrace

/-- Unit squares determine both residues, even when the trace itself is
a nonunit. Only the smaller factor's square condition is used. -/
theorem unit_trace {p q N S e u w s v m : ℤ}
    (prod : N=p*q) (trace : S=p*s^2+q*v^2) (ev : e=v^2*u) (es : 1-e=s^2*w)
    (unit : m ∣ p^2-1) :
    m ∣ S-(s^2+N*v^2)*p ∧
    2*m*(s*v)^2 ∣ (p*s^2-q*v^2) -
      ((1-2*e)*S+2*(s*v)^2*(u-N*w)*p) := by
  obtain ⟨a,ha⟩ := unit
  constructor
  · refine ⟨-q*v^2*a,?_⟩
    rw [trace,prod]
    linear_combination -q*v^2*ha
  · refine ⟨q*w*a,?_⟩
    calc _ = 2*e*p*s^2-2*(1-e)*q*v^2-2*(s*v)^2*(u-N*w)*p := by rw [trace]; ring
         _ = 2*(s*v)^2*q*w*(p^2-1) := by rw [es,ev,prod]; ring
         _ = _ := by rw [ha]; ring

/-- H and B have a publicly known Bézout identity. -/
theorem projector_identity {s v N e u w : ℤ} (ev : e=v^2*u) (es : 1-e=s^2*w) :
    v^2*(u-N*w)+w*(s^2+N*v^2)=1 := by linear_combination -ev-es

/-- Exact elimination of the hidden residue x, including its unit condition.
Given a proposed trace and normalized gap digit R, the inverse coordinate
a*R+b*S supplies the missing label. -/
theorem eliminate_label {m S R H B a b : ℤ} (bez : a*B+b*H=1) :
    (∃ x : ℤ, m ∣ S-H*x ∧ m ∣ R-B*x ∧ IsCoprime x m) ↔
    m ∣ H*R-B*S ∧ IsCoprime (a*R+b*S) m := by
  constructor
  · rintro ⟨x,⟨c,hc⟩,⟨d,hd⟩,⟨u,v,uv⟩⟩
    refine ⟨⟨H*d-B*c,?_⟩,u,v-u*(a*d+b*c),?_⟩
    · linear_combination H*hd-B*hc
    · linear_combination u*a*hd + u*b*hc + u*x*bez + uv
  · rintro ⟨⟨c,hc⟩,unit⟩
    refine ⟨a*R+b*S,⟨-a*c,?_⟩,⟨b*c,?_⟩,unit⟩
    · linear_combination -a*hc-S*bez
    · linear_combination b*hc-R*bez

/-- In the original variables the determinant congruence becomes one
linear relation between S and z. -/
theorem gap_equation {p q N S s v m : ℤ} (prod : N=p*q) (trace : S=p*s^2+q*v^2)
    (unit : m ∣ p^2-1) :
    2*m*(s*v)^2 ∣ (s^2+N*v^2)*(p*s^2-q*v^2)-(s^2-N*v^2)*S := by
  obtain ⟨a,ha⟩ := unit
  refine ⟨q*a,?_⟩
  rw [trace,prod]
  linear_combination 2*(s*v)^2*q*ha

/-- Divide the trace and modulus by g and invert only the remaining unit.
A Bézout coefficient of h=H/g gives the affine representative. -/
theorem reduced_trace {S H m g f t h x a b : ℤ} (gp : g≠0)
    (tr : S=g*t) (hh : H=g*h) (mod : m=g*f) (inverse : a*h+b*f=1) :
    m ∣ S-H*x ↔ f ∣ x-a*t := by
  constructor
  · rintro ⟨w,hw⟩
    have eq : t-h*x=f*w := by
      apply mul_left_cancel₀ gp
      rw [tr,hh,mod] at hw
      linear_combination hw
    exact ⟨b*x-a*w,by linear_combination -a*eq-x*inverse⟩
  · rintro ⟨w,hw⟩
    refine ⟨b*t-h*w,?_⟩
    rw [tr,hh,mod]
    linear_combination -g*h*hw-g*t*inverse

/-- If the normalized digit uses a unit multiplier on the unresolved
quotient of the modulus, whole label classes map onto whole digit classes. -/
theorem digit_class {B R y L F : ℤ} (cop : IsCoprime B F) :
    (∃ x : ℤ, L ∣ x-y ∧ L*F ∣ R-B*x) ↔ L ∣ R-B*y := by
  constructor
  · rintro ⟨x,⟨a,ha⟩,⟨b,hb⟩⟩
    exact ⟨F*b+B*a,by linear_combination hb+B*ha⟩
  · rintro ⟨a,ha⟩
    obtain ⟨u,v,uv⟩ := cop
    refine ⟨y+L*u*a,⟨u*a,by ring⟩,⟨a*v,?_⟩⟩
    linear_combination ha - L*a*uv

/-- If 3 is delegated to the unresolved quotient, a single missing
digit class enforces the remaining condition on factor labels. -/
theorem veto_three {B R x m : ℤ} (mod : (3:ℤ) ∣ m)
    (unit : IsCoprime (3:ℤ) B) (digit : m ∣ R-B*x) : (3:ℤ) ∣ R ↔ (3:ℤ) ∣ x := by
  have eq := mod.trans digit
  constructor
  · intro yes
    have product : (3:ℤ) ∣ B*x := by simpa using dvd_sub yes eq
    exact unit.dvd_of_dvd_mul_left product
  · intro yes
    simpa using dvd_add eq (dvd_mul_of_dvd_right yes B)

/-- Compatibility of two affine predictions for the signed gap is one
linear congruence on their common trace index. -/
theorem affine_compatible {g l r a A b B t z : ℤ}
    (one : g*l ∣ z-(a+A*t)) (two : g*r ∣ z-(b+B*t)) :
    g ∣ (b-a)+(B-A)*t := by
  obtain ⟨x,hx⟩ := one
  obtain ⟨y,hy⟩ := two
  exact ⟨l*x-r*y,by linear_combination hx-hy⟩

/-- On a compatible trace progression write Y-X=g*h, with h affine
in its index. The combined residue X+g*l*u*h is again affine, now
at the least common multiple when g is the gcd of the old moduli. -/
theorem join_affine {g l r X Y z h u v : ℤ} (bez : l*u+r*v=1) (diff : Y-X=g*h) :
    (g*l ∣ z-X ∧ g*r ∣ z-Y) ↔ g*l*r ∣ z-(X+g*l*u*h) := by
  constructor
  · rintro ⟨⟨a,ha⟩,⟨b,hb⟩⟩
    refine ⟨v*a+u*b,?_⟩
    calc _ = r*v*(z-X)+l*u*(z-Y) := by linear_combination -(z-X)*bez+l*u*diff
         _ = _ := by rw [ha,hb]; ring
  · rintro ⟨w,hw⟩
    refine ⟨⟨r*w+u*h,by linear_combination hw⟩,⟨l*w-v*h,?_⟩⟩
    linear_combination hw-diff+g*h*bez

/-- Finite representatives of all compatible normalized digits at fixed
H, B and trace, including nonunit traces. -/
noncomputable def labels (H B S : ℕ) : List ℕ :=
  ((List.range 24).filter (fun x => x.Coprime 24 && (H*x)%24 == S%24)).map (fun x => (B*x)%24)

def unitLabels : List ℕ := [1,5,7,11,13,17,19,23]

theorem unit_labels_spec : ∀ x : Fin 24, x.val∈unitLabels ↔ x.val.Coprime 24 := by decide +kernel

/-- Public feasibility for each of the 24 residue classes of the trace.
An image exists exactly when H and S have the same gcd with 24. -/
theorem trace_feasible : ∀ H S : Fin 24,
    unitLabels.any (fun x => (H.val*x)%24 == S.val) = true ↔ H.val.gcd 24=S.val.gcd 24 := by
  decide +kernel

/-- Digits at a nonempty trace whose factor labels equal x modulo f. -/
noncomputable def digitFibre (f x B : ℕ) : List ℕ :=
  (unitLabels.filter (fun p => p%f == x%f)).map (fun p => (B*p)%24)

/-- The length of the smallest positive gap around a circle of size 24.
A singleton returns the full circumference. -/
noncomputable def minimumSpacing (digits : List ℕ) : ℕ :=
  (digits.flatMap (fun a => digits.map (fun b => if a=b then 24 else (b+24-a)%24))).foldl min 24

private noncomputable def fibreChecks (f x B : ℕ) : Bool :=
  let digits := digitFibre f x B
  let unitCount := ((List.range f).filter (fun n => n.Coprime f)).length
  decide (digits.length*unitCount=8 ∧ minimumSpacing digits=Nat.lcm 2 f)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem table_checks :
    ([1,2,3,4,6,8,12,24] : List ℕ).all (fun f =>
      unitLabels.all (fun x => (List.range 24).all (fun B =>
      !(B.Coprime (24/f)) || fibreChecks f x B)))=true := by decide +kernel

/-- For every possible reduced modulus and unit label, the exact count
and the smallest positive cyclic spacing are independent of B. -/
theorem fibre_count_and_spacing {f x B : ℕ} (hf : f∈([1,2,3,4,6,8,12,24] : List ℕ))
    (hx : x∈unitLabels) (bound : B<24) (unit : B.Coprime (24/f)) :
    (digitFibre f x B).length*((List.range f).filter (fun n => n.Coprime f)).length=8 ∧
    minimumSpacing (digitFibre f x B)=Nat.lcm 2 f := by
  have row := List.all_eq_true.mp (List.all_eq_true.mp
    (List.all_eq_true.mp table_checks f hf) x hx) B (List.mem_range.mpr bound)
  simpa [unit,fibreChecks] using row

/-- Two different label residues and a noninvertible trace on a proper
primitive offset of 2501 = 41 * 61. -/
theorem example2501 :
    let p : ℕ := 41
    let q : ℕ := 61
    let s : ℕ := 5
    let v : ℕ := 4
    let N := p*q
    let S := p*s^2+q*v^2
    let H := s^2+N*v^2
    let B := 17518
    N=2501 ∧ S=2001 ∧ S.gcd 24=3 ∧ (p*s^2-q*v^2)=49 ∧
    labels H B S=[22,14] := by decide +kernel

/-- The exact divisibility of traces can still help when the only common
digit progression has parity precision. -/
theorem example527 :
    let S := 17+31
    let H := 1+527
    S%24=0 ∧ (labels H 1 S)=[1,5,7,11,13,17,19,23] ∧
    labels H 1 (S+2)=[] := by decide +kernel

end PrimeFactors.OffsetUnitTrace
