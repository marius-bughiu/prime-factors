import PrimeFactors.TraceCoverCertificate
import PrimeFactors.WeightedStride

namespace PrimeFactors.TraceCoverCertificate

/-- The literal progression starts at the first residue at or above
the geometric minimum. Verifying its two adjacent squares avoids a root oracle. -/
def validStart (n : ℕ) (s : Slope) : Bool :=
  decide (0<s.step ∧ s.step=weightedStride n s.a s.b ∧
    s.start ≡ s.a+s.b*n [MOD s.step] ∧ 4*s.a*s.b*n≤s.start^2 ∧
    (s.start<s.step ∨ (s.start-s.step)^2<4*s.a*s.b*n))

/-- Reduced slopes in [1,2] with denominator at most k, in denominator order. -/
noncomputable def catalogueCoordinates (k : ℕ) : List (ℕ × ℕ) :=
  (List.range k).flatMap fun i =>
    let b := i+1
    ((List.range (b+1)).filter fun j => (b+j).Coprime b).map fun j => (b+j,b)

/-- All progressions are validated, and every catalogue coordinate occurs. -/
noncomputable def fullCatalogue (n k : ℕ) (rows : List Slope) : Bool :=
  let coordinates := rows.map fun s => (s.a,s.b)
  rows.all (validStart n) && decide (coordinates.toFinset = (catalogueCoordinates k).toFinset)

theorem coordinate_mem {k a b : ℕ} : (a,b) ∈ catalogueCoordinates k ↔
    0<b ∧ b≤k ∧ b≤a ∧ a≤2*b ∧ a.Coprime b := by
  simp only [catalogueCoordinates,List.mem_flatMap,List.mem_range,List.mem_map,
    List.mem_filter,decide_eq_true_eq,Prod.mk.injEq]
  constructor
  · rintro ⟨i,hi,j,⟨hj,cop⟩,ha,hb⟩
    subst a; subst b
    exact ⟨by omega,by omega,by omega,by omega,cop⟩
  · rintro ⟨pos,bound,lo,hi,cop⟩
    refine ⟨b-1,by omega,a-b,⟨by omega,?_⟩,by omega,by omega⟩
    simpa only [show b-1+1=b by omega, Nat.add_sub_of_le lo] using cop

private theorem center_covered {n m g : ℕ} {s : Slope} {x : Point}
    (a : 0<s.a) (b : 0<s.b) (ok : covers n m s g x) : covers n m s g ⟨s.a,s.b⟩ := by
  change decide (_ < _) = true at ok ⊢
  apply decide_eq_true
  have h := of_decide_eq_true ok
  change n*(s.a*x.den+s.b*x.num)^2 < x.num*x.den*(cutoff m s g)^2 at h
  have am : 4*s.a*s.b*(x.num*x.den) ≤ (s.a*x.den+s.b*x.num)^2 := by
    nlinarith only [sq_nonneg ((s.a*x.den:ℤ)-s.b*x.num)]
  have bounds := (Nat.mul_le_mul_left n am).trans_lt h
  have common : x.num*x.den*(4*s.a*s.b*n) < x.num*x.den*(cutoff m s g)^2 := by
    convert bounds using 1
    ring
  have strict := Nat.lt_of_mul_lt_mul_left common
  have mult := Nat.mul_lt_mul_of_pos_left strict (Nat.mul_pos a b)
  change n*(s.a*s.b+s.b*s.a)^2<s.a*s.b*(cutoff m s g)^2
  convert mult using 1
  ring

/-- Moving to the right toward the slope preserves coverage. -/
theorem of_left {n m g : ℕ} {s : Slope} {x y : Point} (a : 0<s.a) (b : 0<s.b)
    (xd : 0<x.den) (yd : 0<y.den) (xy : before x y) (side : before y ⟨s.a,s.b⟩)
    (ok : covers n m s g x) : covers n m s g y :=
  segment xd yd b xy side ok (center_covered a b ok)

/-- Moving to the left toward the slope preserves coverage. -/
theorem of_right {n m g : ℕ} {s : Slope} {x y : Point} (a : 0<s.a) (b : 0<s.b)
    (xd : 0<x.den) (yd : 0<y.den) (xy : before x y) (side : before ⟨s.a,s.b⟩ x)
    (ok : covers n m s g y) : covers n m s g x :=
  segment b xd yd side xy (center_covered a b ok) ok

/-- An actual covered pair occurs at a searched label. The product and
coprimality alone determine the stride. -/
theorem actual_index {n m g p q : ℕ} {s : Slope} (prod : p*q=n)
    (cop : p.Coprime 6) (start : validStart n s) (covered : covers n m s g ⟨q,p⟩) :
    ∃ j<m*g, s.start+s.step*j=s.a*p+s.b*q := by
  obtain ⟨pos,step,first,_,prev⟩ := of_decide_eq_true start
  let z := s.a*p+s.b*q
  have modz : s.start ≡ z [MOD s.step] := by
    apply first.trans
    rw [step,←prod]
    exact (weighted_sum_congruent cop s.a s.b q).symm
  have sq : 4*s.a*s.b*n≤z^2 := by
    rw [←prod]; dsimp [z]; nlinarith only [sq_nonneg ((s.a*p:ℤ)-s.b*q)]
  have atMost : s.start≤z := by
    by_contra! h
    have diff : s.step ∣ s.start-z := Nat.modEq_iff_dvd' h.le |>.mp modz.symm
    have le := Nat.le_of_dvd (Nat.sub_pos_of_lt h) diff
    rcases prev with small | lower
    · omega
    · have := Nat.pow_le_pow_left (show z≤s.start-s.step by omega) 2
      omega
  obtain ⟨j,hj⟩ := Nat.modEq_iff_dvd' atMost |>.mp modz
  have hit : s.start+s.step*j=z := by omega
  have limit := at_product prod covered
  change z<s.start+s.step*m*g at limit
  have head : s.step*j<s.step*(m*g) := by rw [←Nat.mul_assoc]; omega
  exact ⟨j,Nat.lt_of_mul_lt_mul_left head,hit⟩

end PrimeFactors.TraceCoverCertificate
