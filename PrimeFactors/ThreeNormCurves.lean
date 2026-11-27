import PrimeFactors.ThreeTargetRepresentations
import PrimeFactors.NormUnitInterval
import PrimeFactors.ShortRootNorm

/-! Reduce the signed three-target menu to one norm equation per target. -/
namespace PrimeFactors.ThreeNormCurves

open SmallDiscriminantLattice

/-- Signed multiplier determined by the target and N modulo three. -/
def multiplier (N : ℕ) (D : ℤ) : ℤ :=
  if D = -6 then (if N%3=1 then 1 else 2)
  else if D=3 ∨ D=6 then (if N%3=1 then 1 else -1)
  else 1

/-- Positive targets use the real part of their smallest positive norm-one
unit. For negative targets the original ellipse already has fixed height. -/
def heightFactor (N : ℕ) (D : ℤ) : ℤ :=
  if D=2 then 3 else if D=3 then 2 else if D=6 then 5 else multiplier N D

structure Point (N : ℕ) (D : ℤ) (r : ZMod N) where
  x : ℤ
  y : ℤ
  norm : x^2-D*y^2=multiplier N D*N
  height : x^2+abs D*y^2≤heightFactor N D*N
  root : (x:ZMod N)=r*y
  primitive : IsCoprime x y
  unit : IsUnit (y:ZMod N)

/-- The public endpoints can be tested with integer arithmetic. -/
theorem interval {N : ℕ} {D : ℤ} {r : ZMod N} (w : Point N D r) (dp : 0<D) :
    -(multiplier N D*N)≤D*w.y^2 ∧ 2*D*w.y^2≤(heightFactor N D-multiplier N D)*N := by
  have h := w.height
  rw [abs_of_pos dp] at h
  constructor <;> nlinarith only [w.norm,h,sq_nonneg w.x]

private theorem classify {N : ℕ} (np : ¬3∣N) {D m x y : ℤ} (three : (D:ZMod 3)=0)
    (norm : x^2-D*y^2=m*N) (cases : m=1 ∨ m= -1 ∨ m=2) : m=1 ↔ N%3=1 := by
  have n3 : (N:ZMod 3)≠0 := fun h => np ((ZMod.natCast_zmod_eq_zero_iff_dvd ..).mp h)
  have eq := congrArg (fun z : ℤ => (z:ZMod 3)) norm
  push_cast at eq
  rw [three,zero_mul,sub_zero] at eq
  have n1 : (N:ZMod 3)=1 ↔ N%3=1 := ZMod.natCast_eq_natCast_iff N 1 3
  rw [←n1]
  rcases cases with e|e|e <;> subst m <;> norm_num at eq ⊢
  · exact (by decide : ∀ a n : ZMod 3, n≠0 → a^2=n → n=1) _ _ n3 eq
  · exact (by decide : ∀ a n : ZMod 3, n≠0 → a^2= -n → n≠1) _ _ n3 eq
  · exact (by decide : ∀ a n : ZMod 3, n≠0 → a^2=2*n → n≠1) _ _ n3 eq

private theorem two_normalize {N : ℕ} (np : 0<N) (odd : Odd N) {r : ZMod N}
    (rr : r^2=(2:ℤ)) (u : Representation N 2 r) :
    ∃ a b : ℤ, a^2-2*b^2=N ∧ (a:ZMod N)=r*b := by
  have m := ThreeTargetRepresentations.small_multiplier np odd (by decide : abs (2:ℤ)≤3) u
  rcases (show u.m=1 ∨ u.m= -1 by omega) with e|e
  · exact ⟨_,_,by simpa [e] using u.norm,u.point⟩
  have h := u.norm
  rw [e] at h
  refine ⟨u.x+2*u.y,u.x+u.y,by nlinarith only [h],?_⟩
  push_cast
  rw [u.point]
  norm_num at rr
  linear_combination -(u.y:ZMod N)*rr

private theorem six_normalize {N : ℕ} (odd : Odd N) {r : ZMod N}
    (rr : r^2=(6:ℤ)) (u : Representation N 6 r) :
    ∃ m a b : ℤ, (m=1 ∨ m= -1) ∧ a^2-6*b^2=m*N ∧ (a:ZMod N)=r*b := by
  obtain ⟨nz,cap⟩ := u.multiplier
  by_cases one : u.m=1 ∨ u.m= -1
  · exact ⟨u.m,u.x,u.y,one,u.norm,u.point⟩
  have two : u.m=2 ∨ u.m= -2 := by omega
  have mod2 := congrArg (fun z : ℤ => (z:ZMod 2)) u.norm
  push_cast at mod2
  have mz : (u.m:ZMod 2)=0 := by
    rcases two with e|e <;> rw [e] <;> decide
  have even : (u.x:ZMod 2)^2=0 := by
    simpa only [mz,show (6:ZMod 2)=0 from rfl,zero_mul,sub_zero] using mod2
  have dvd := (ZMod.intCast_zmod_eq_zero_iff_dvd ..).mp (pow_eq_zero even)
  obtain ⟨a,xa⟩ := dvd
  norm_num at xa
  have rel := congrArg (fun z : ℤ => (z:ZMod N)) xa
  push_cast at rel
  have half : (2:ZMod N)*a=r*u.y := rel.symm.trans u.point
  have invertible : IsUnit (2:ZMod N) := by
    exact_mod_cast (ZMod.isUnit_iff_coprime 2 N).mpr
      (Nat.prime_two.coprime_iff_not_dvd.mpr (fun h => odd.not_two_dvd_nat h))
  have mixed : r*(a:ZMod N)=3*u.y := by
    apply invertible.mul_right_inj.mp
    norm_num at rr
    linear_combination r*half+(u.y:ZMod N)*rr
  have pt : ((u.x+3*u.y:ℤ):ZMod N)=r*((a+u.y:ℤ):ZMod N) := by
    push_cast; rw [u.point,mul_add,mixed,add_comm]
  have h := u.norm
  rw [xa] at h
  rcases two with e|e <;> rw [e] at h
  · exact ⟨-1,_,_,Or.inr rfl,by rw [xa]; nlinarith only [h],pt⟩
  · exact ⟨1,_,_,Or.inl rfl,by rw [xa]; nlinarith only [h],pt⟩

private theorem primitive_exact {N D : ℕ} (np : 0<N) {r : ZMod N} (rr : r^2=D)
    {x y : ℤ} (pt : (x:ZMod N)=r*y) (norm : x^2-D*y^2=N ∨ x^2-D*y^2= -(N:ℤ)) :
    IsCoprime x y ∧ IsUnit (y:ZMod N) := by
  letI : NeZero N := ⟨np.ne'⟩
  have R : ((r.val:ℕ):ZMod N)^2=D := by simpa using rr
  have forNat {a : ℤ} {b : ℕ} (h : (a:ZMod N)=r*b)
      (n : a^2-D*(b:ℤ)^2=N ∨ a^2-D*(b:ℤ)^2= -(N:ℤ)) :
      IsCoprime a (b:ℤ) ∧ IsUnit (b:ZMod N) := by
    obtain ⟨prim,unit⟩ := ShortRootNorm.primitive_of_norm np R (by simpa using h) n
    exact ⟨prim,(ZMod.isUnit_iff_coprime ..).mpr unit⟩
  cases y with
  | ofNat b =>
    obtain ⟨prim,unit⟩ := forNat (a := x) (b := b) (by simpa using pt) norm
    exact ⟨prim,by simpa using unit⟩
  | negSucc b =>
    have yp : (Int.negSucc b : ℤ) = -(↑(b+1):ℤ) := by rfl
    rw [yp] at pt norm ⊢
    have pair := forNat (a := -x) (b := b+1) (by push_cast at pt ⊢; rw [pt]; ring)
      (by simpa only [neg_sq] using norm)
    exact ⟨by simpa using pair.1.neg_neg,by simpa using pair.2.neg⟩

private theorem positive_point {N D : ℕ} (np : 0<N) (dp : 0<D)
    {r : ZMod N} (rr : r^2=D) {m a b U V : ℤ} (m1 : m=1 ∨ m= -1)
    (chosen : m=multiplier N D) (hf : U=heightFactor N D)
    (up : 0<U) (vp : 0<V) (pell : U^2-(D:ℤ)*V^2=1)
    (norm : a^2-D*b^2=m*N) (pt : (a:ZMod N)=r*b) : Nonempty (Point N D r) := by
  have dr : r^2=((D:ℤ):ZMod N) := by simpa using rr
  obtain ⟨x,y,n,point,height⟩ := NormUnitInterval.reduce (by exact_mod_cast dp) up vp pell m1 dr norm pt
  have normalized : x^2-D*y^2=N ∨ x^2-D*y^2= -(N:ℤ) := by
    rcases m1 with e|e
    · exact Or.inl (by simpa [e] using n)
    · exact Or.inr (by simpa [e] using n)
  obtain ⟨prim,unit⟩ := primitive_exact np rr point normalized
  refine ⟨⟨x,y,chosen ▸ n,?_,point,prim,unit⟩⟩
  simpa [abs_of_nonneg (Int.natCast_nonneg D),hf] using height


private theorem negative_point {N : ℕ} (np : 0<N) (odd : Odd N) (no3 : ¬3∣N)
    {D : ℤ} (neg : D<0) (targets : abs D≤3 ∨ D= -6) {r : ZMod N} (u : Representation N D r) :
    Nonempty (Point N D r) := by
  have npos : 0<(N:ℤ) := by exact_mod_cast np
  have pos : 0<u.m := by
    have n : 0≤u.m*N := by
      rw [←u.norm]
      exact sub_nonneg.mpr ((mul_nonpos_of_nonpos_of_nonneg neg.le (sq_nonneg _)).trans (sq_nonneg _))
    have nn := nonneg_of_mul_nonneg_left n npos
    obtain ⟨nz,_⟩ := u.multiplier
    omega
  have chosen : u.m=multiplier N D := by
    rcases targets with small|rfl
    · have h := ThreeTargetRepresentations.small_multiplier np odd small u
      have a : D≠ -6 := by intro e; subst D; norm_num at small
      simpa [multiplier,a,show D≠3 by omega,show D≠6 by omega] using (show u.m=1 by omega)
    · obtain ⟨nz,lim⟩ := u.multiplier
      have h := classify no3 (by decide : ((-6:ℤ):ZMod 3)=0) u.norm (by omega)
      by_cases n : N%3=1 <;> simp [multiplier,n] <;> omega
  have hf : heightFactor N D=multiplier N D := by
    simp [heightFactor,show D≠2 by omega,show D≠3 by omega,show D≠6 by omega]
  refine ⟨⟨u.x,u.y,chosen ▸ u.norm,?_,u.point,u.primitive,u.unit⟩⟩
  rw [abs_of_neg neg,hf,←chosen]
  nlinarith only [u.norm]

private theorem selected_sign {N : ℕ} (no3 : ¬3∣N) {D m a b : ℤ}
    (d : D=3 ∨ D=6) (m1 : m=1 ∨ m= -1) (n : a^2-D*b^2=m*N) :
    m=multiplier N D := by
  have z : (D:ZMod 3)=0 := by rcases d with rfl|rfl <;> decide
  have c := classify no3 z n (m1.imp_right Or.inl)
  rcases d with rfl|rfl <;> by_cases one : N%3=1 <;> simp [multiplier,one] <;> omega

/-- Each signed target uses exactly one public equation. Every modular root
with an initial short representation retains a primitive representative there. -/
theorem normalize {N : ℕ} (np : 0<N) (odd : Odd N) (no3 : ¬3∣N) {D : ℤ}
    (values : D∈([-1,2,-2,3,-3,6,-6]:List ℤ)) {r : ZMod N} (rr : r^2=D)
    (w : Representation N D r) : Nonempty (Point N D r) := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at values
  rcases values with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact negative_point np odd no3 (by decide) (Or.inl (by decide)) w
  · obtain ⟨a,b,n,pt⟩ := two_normalize np odd rr w
    exact positive_point (D:=2) (U:=3) (V:=2) (m:=1) np (by decide) (by simpa using rr)
      (Or.inl rfl) (by simp [multiplier]) (by simp [heightFactor]) (by decide) (by decide) (by decide)
      (by simpa using n) pt
  · exact negative_point np odd no3 (by decide) (Or.inl (by decide)) w
  · have h := ThreeTargetRepresentations.small_multiplier np odd (by decide : abs (3:ℤ)≤3) w
    have m1 : w.m=1 ∨ w.m= -1 := by omega
    exact positive_point (D:=3) (U:=2) (V:=1) np (by decide) (by simpa using rr) m1
      (selected_sign no3 (Or.inl rfl) m1 w.norm) (by simp [heightFactor]) (by decide) (by decide)
      (by decide) w.norm w.point
  · exact negative_point np odd no3 (by decide) (Or.inl (by decide)) w
  · obtain ⟨m,a,b,m1,n,pt⟩ := six_normalize odd rr w
    exact positive_point (D:=6) (U:=5) (V:=2) np (by decide) (by simpa using rr) m1
      (selected_sign no3 (Or.inr rfl) m1 n) (by simp [heightFactor]) (by decide) (by decide)
      (by decide) n pt
  · exact negative_point np odd no3 (by decide) (Or.inr rfl) w

/-- Each pair in the public list is the equation x²−Dy²=mN. -/
noncomputable def curves (N : ℕ) : List (ℤ × ℤ) :=
  (ThreeRootTargets.menu N ThreeRootTargets.signed).map fun D => (D,multiplier N D)

theorem length_le (N : ℕ) : (curves N).length≤3 := by
  simp only [curves,ThreeRootTargets.menu,List.length_map]
  change (List.take 3 _).length≤3
  simp

/-- Two inequivalent modular roots on one reduced curve split the product. -/
theorem factor {N : ℕ} [NeZero N] {D : ℤ} {r t : ZMod N}
    (u : Point N D r) (v : Point N D t) (rr : r^2=D) (tr : t^2=D)
    (diff : r≠t) (opposite : r≠-t) :
    let g := ((u.x:ZMod N)*v.y-(v.x:ZMod N)*u.y).val.gcd N
    1<g ∧ g<N ∧ g∣N := by
  let w := (u.unit.mul v.unit).unit
  have wz : (w:ZMod N)=(u.y:ZMod N)*v.y := (u.unit.mul v.unit).unit_spec
  have eq : (u.x:ZMod N)*v.y-(v.x:ZMod N)*u.y=(w:ZMod N)*r-w*t := by
    rw [u.root,v.root,wz]
    ring
  have split := maskedRelations_split (rr.trans tr.symm) diff opposite
  dsimp only
  rw [eq,maskedRelations_unit_gcd]
  exact ⟨split.1, split.2, Nat.gcd_dvd_right ..⟩

/-- For every pair of distinct primes larger than three, one of the at most
three public curves has two reduced representatives whose cross determinant
reveals a proper factor. -/
theorem semiprime {p q : ℕ} (pp : p.Prime) (pq : q.Prime) (ne : p≠q) (lp : 3<p) (lq : 3<q) :
    ∃ D, (D,multiplier (p*q) D)∈curves (p*q) ∧ ∃ r t : ZMod (p*q),
      ∃ u : Point (p*q) D r, ∃ v : Point (p*q) D t,
        r^2=D ∧ t^2=D ∧ r≠t ∧ r≠-t ∧
        let g := ((u.x:ZMod (p*q))*v.y-(v.x:ZMod (p*q))*u.y).val.gcd (p*q)
        1<g ∧ g<p*q ∧ g∣p*q := by
  obtain ⟨D,mem,r,t,u,v,rr,tr,diff,opposite,_⟩ := ThreeTargetRepresentations.semiprime pp pq ne lp lq
  have val := (ThreeRootTargets.signed_values (p*q)).subset mem
  have positive := Nat.mul_pos pp.pos pq.pos
  letI : NeZero (p*q) := ⟨positive.ne'⟩
  have odd := (pp.odd_of_ne_two (by omega)).mul (pq.odd_of_ne_two (by omega))
  have no3 : ¬3∣p*q := by
    intro h
    rcases Nat.prime_three.dvd_mul.mp h with h|h
    · have eq := (Nat.prime_dvd_prime_iff_eq Nat.prime_three pp).mp h; omega
    · have eq := (Nat.prime_dvd_prime_iff_eq Nat.prime_three pq).mp h; omega
  obtain ⟨a⟩ := normalize positive odd no3 val rr u
  obtain ⟨b⟩ := normalize positive odd no3 val tr v
  exact ⟨D,List.mem_map.mpr ⟨D,mem,rfl⟩,r,t,a,b,rr,tr,diff,opposite,factor a b rr tr diff opposite⟩

end PrimeFactors.ThreeNormCurves
