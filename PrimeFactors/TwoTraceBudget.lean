import PrimeFactors.TraceCoverCertificate

/-! A constant-size certificate for the optimal allocation between the
ordinary sum and twice the first factor plus the second factor. It prices
complete coverage of every rational ratio from one through two. -/

namespace PrimeFactors.TwoTraceBudget

open TraceCoverCertificate

/-- The intersection numerator times denominator, using signed arithmetic
so the same quadratic applies beyond the allowed allocations. -/
def score (s t α β G x : ℤ) : ℤ :=
  let T := s+α*x
  let U := t+β*(G-x)
  (2*T-U)*(U-T)

/-- For this integer concave quadratic, comparison with just the two
in-range neighbors certifies its maximum over all G+1 choices. -/
theorem bounded_max {s t α β G j x : ℤ} (ha : 0≤α) (hb : 0≤β) (xlo : 0≤x) (xhi : x≤G)
    (left : j=0 ∨ score s t α β G (j-1)≤score s t α β G j)
    (right : j=G ∨ score s t α β G (j+1)≤score s t α β G j) :
    score s t α β G x ≤ score s t α β G j := by
  let f := score s t α β G
  let k := (2*α+β)*(α+β)
  have hk : 0≤k := by dsimp [k]; positivity
  change f x≤f j
  rcases lt_trichotomy x j with h|h|h
  · have near : f (j-1)≤f j := left.resolve_left (by omega)
    have step : 0≤j-x-1 := by omega
    have dg : 0≤j-x := by omega
    have id : f x-f j=(j-x)*(f (j-1)-f j)-k*(j-x)*(j-x-1) := by
      dsimp [f,k,score]; ring
    linarith only [id,mul_nonpos_of_nonneg_of_nonpos dg (sub_nonpos.mpr near),
      mul_nonneg (mul_nonneg hk dg) step]
  · rw [h]
  · have near : f (j+1)≤f j := right.resolve_left (by omega)
    have step : 0≤x-j-1 := by omega
    have dg : 0≤x-j := by omega
    have id : f x-f j=(x-j)*(f (j+1)-f j)-k*(x-j)*(x-j-1) := by
      dsimp [f,k,score]; ring
    linarith only [id,mul_nonpos_of_nonneg_of_nonpos dg (sub_nonpos.mpr near),
      mul_nonneg (mul_nonneg hk dg) step]

/-- The fixed two-slope schedule with the given numbers of blocks covers
the complete balanced rational interval. A ratio need not occur at N. -/
def Covers (n m s t step₁ step₂ u v : ℕ) : Prop :=
  ∀ r : Point, 0<r.den → r.den≤r.num → r.num≤2*r.den →
    covers n m ⟨1,1,s,step₁⟩ u r ∨ covers n m ⟨2,1,t,step₂⟩ v r

def intersection (T U : ℕ) : Point := ⟨2*T-U,U-T⟩

/-- At the rational crossing both normalized trace tests reduce to a single
integer comparison. A smaller second cutoff is also excluded. -/
theorem crossing_miss {n m s t step₁ step₂ u v v' T U : ℕ}
    (first : T=s+step₁*m*u) (second : U=t+step₂*m*v') (sp : 0<s)
    (vle : v≤v') (left : 2*U≤3*T) (right : 4*T≤3*U)
    (area : (2*(T:ℤ)-U)*(U-T)≤n) :
    let r := intersection T U
    0<r.den ∧ r.den≤r.num ∧ r.num≤2*r.den ∧
    covers n m ⟨1,1,s,step₁⟩ u r=false ∧ covers n m ⟨2,1,t,step₂⟩ v r=false := by
  let A := 2*T-U
  let B := U-T
  have tp : 0<T := by omega
  have xyz : 0<B ∧ B≤A ∧ A≤2*B ∧ B+A=T ∧ 2*B+A=U := by dsimp [A,B]; omega
  have aZ : (A:ℤ)=2*(T:ℤ)-U := by dsimp [A]; omega
  have bZ : (B:ℤ)=(U:ℤ)-T := by dsimp [B]; omega
  rw [←aZ,←bZ] at area
  have ar : A*B≤n := by exact_mod_cast area
  have low : t+step₂*m*v≤U := by rw [second]; exact Nat.add_le_add_left (Nat.mul_le_mul_left _ vle) t
  change 0<B ∧ B≤A ∧ A≤2*B ∧ decide (_ < _)=false ∧ decide (_ < _)=false
  refine ⟨xyz.1,xyz.2.1,xyz.2.2.1,decide_eq_false_iff_not.mpr ?_,decide_eq_false_iff_not.mpr ?_⟩
  · change ¬ n*(1*B+1*A)^2<A*B*(s+step₁*m*u)^2
    rw [one_mul,one_mul,xyz.2.2.2.1,←first]
    exact Nat.not_lt_of_ge (Nat.mul_le_mul_right _ ar)
  · change ¬ n*(2*B+1*A)^2<A*B*(t+step₂*m*v)^2
    rw [one_mul,xyz.2.2.2.2]
    exact Nat.not_lt_of_ge (Nat.mul_le_mul ar (Nat.pow_le_pow_left low 2))

/-- Extremal endpoint checks imply the linear inequalities that keep every
intersection inside the balanced interval. -/
theorem endpoint_guards {n s t A B : ℕ} (own₁ : 4*n≤s^2) (own₂ : 8*n≤t^2)
    (opposite₁ : 2*A^2≤9*n) (opposite₂ : B^2≤9*n) : 2*B≤3*s ∧ 4*A≤3*t := by
  constructor
  · apply (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp
    nlinarith only [own₁,opposite₂]
  · apply (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp
    nlinarith only [own₂,opposite₁]

/-- All allocations of at most G blocks miss a rational profile when a
single checked integer vertex falls below the required product. -/
theorem budget {n m s t step₁ step₂ G j : ℕ}
    (sp : 0<s) (guard₁ : 2*(t+step₂*m*G)≤3*s) (guard₂ : 4*(s+step₁*m*G)≤3*t)
    (left : j=0 ∨ score s t (step₁*m) (step₂*m) G ((j:ℤ)-1)≤score s t (step₁*m) (step₂*m) G j)
    (right : j=G ∨ score s t (step₁*m) (step₂*m) G ((j:ℤ)+1)≤score s t (step₁*m) (step₂*m) G j)
    (cut : score s t (step₁*m) (step₂*m) G j≤n) :
    ∀ u v, u+v≤G → ¬ Covers n m s t step₁ step₂ u v := by
  intro u v spent cov
  let w := G-u
  let T := s+step₁*m*u
  let U := t+step₂*m*w
  have wu : (w:ℤ)=(G:ℤ)-u := by dsimp [w]; omega
  have wu' : w≤G := Nat.sub_le ..
  have upperT := Nat.mul_le_mul_left (step₁*m) (by omega : u≤G)
  have upperU := Nat.mul_le_mul_left (step₂*m) wu'
  have atU := bounded_max (s:=(s:ℤ)) (t:=(t:ℤ)) (α:=(step₁*m:ℤ)) (β:=(step₂*m:ℤ))
    (j:=(j:ℤ)) (G:=(G:ℤ)) (x:=(u:ℤ)) (by positivity) (by positivity)
    (by positivity) (by omega) (by exact_mod_cast left) (by exact_mod_cast right)
  have h := atU.trans cut
  unfold score at h
  rw [←wu] at h
  have ar : (2*(T:ℤ)-U)*(U-T)≤n := by simpa only [T,U,Nat.cast_add,Nat.cast_mul] using h
  have miss := crossing_miss (n:=n) (T:=T) (U:=U) (v:=v) (v':=w) rfl rfl sp
    (by dsimp [w]; omega) (by dsimp [T,U]; omega) (by dsimp [T,U]; omega) ar
  rcases cov _ miss.1 miss.2.1 miss.2.2.1 with ok|ok
  · simp [miss.2.2.2.1] at ok
  · simp [miss.2.2.2.2] at ok

/-- The optimum in this coverage model uses exactly total blocks. -/
def IsMinimum (n m s t step₁ step₂ total : ℕ) : Prop :=
  (∃ u v, u+v=total ∧ Covers n m s t step₁ step₂ u v) ∧
  ∀ u v, u+v<total → ¬ Covers n m s t step₁ step₂ u v

/-- Check the two upper-cover pieces at their common rational crossing. -/
noncomputable def upper (n m s t step₁ step₂ u v : ℕ) : Bool :=
  let r := intersection (s+step₁*m*u) (t+step₂*m*v)
  upperCheck n m [(⟨1,1,s,step₁⟩,u),(⟨2,1,t,step₂⟩,v)] ⟨1,1⟩ ⟨2,1⟩ [(r,0),(⟨2,1⟩,1)]

theorem upper_covers {n m s t step₁ step₂ u v : ℕ} (accepted : upper n m s t step₁ step₂ u v) :
    Covers n m s t step₁ step₂ u v := by
  intro r hd lo hi
  obtain ⟨row,mem,hit⟩ := upper_sound (x:=r) hd accepted
    (by simpa [before] using lo) (by simpa [before] using hi)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
  rcases mem with rfl|rfl
  · exact Or.inl hit
  · exact Or.inr hit

/-- This certificate reads one maximizing point of the lower-budget quadratic
and one feasible split of the next budget. No table indexed by G is evaluated. -/
noncomputable def check (n m s t step₁ step₂ G j u v : ℕ) : Bool :=
  let f := score s t (step₁*m) (step₂*m) G
  decide (0<s ∧ 2*(t+step₂*m*G)≤3*s ∧ 4*(s+step₁*m*G)≤3*t ∧
    (j=0 ∨ f ((j:ℤ)-1)≤f j) ∧ (j=G ∨ f ((j:ℤ)+1)≤f j) ∧ f j≤n ∧ u+v=G+1) &&
    upper n m s t step₁ step₂ u v

theorem check_sound {n m s t step₁ step₂ G j u v : ℕ}
    (accepted : check n m s t step₁ step₂ G j u v) : IsMinimum n m s t step₁ step₂ (G+1) := by
  unfold check at accepted
  simp only [Bool.and_eq_true,decide_eq_true_eq] at accepted
  obtain ⟨⟨pos,guard₁,guard₂,left,right,atTop,total⟩,cover⟩ := accepted
  exact ⟨⟨u,v,total,upper_covers cover⟩,fun i k h =>
    budget pos guard₁ guard₂ left right atTop i k (by omega)⟩

end PrimeFactors.TwoTraceBudget
