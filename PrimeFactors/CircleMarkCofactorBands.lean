import PrimeFactors.CircleMarkSmallTargets
import PrimeFactors.Fermat

/-! For a positive remainder, a mark places the remainder in an integer
multiple of the interval known to contain both prime factors. -/
namespace PrimeFactors.CircleMarkCofactorBands

open Finset CircleBranchCount

/-- A necessary interval condition on a positive remainder. -/
def inBands (P H y : ℕ) : Prop := ∃ k : ℕ, 0<k ∧ k*P≤y ∧ y≤k*H

/-- Only the largest potential cofactor needs to be checked. -/
theorem inBands_iff {P H y : ℕ} (pos : 0<P) (yp : 0<y) :
    inBands P H y ↔ y≤(y/P)*H := by
  constructor
  · rintro ⟨k,_,lo,hi⟩
    exact hi.trans (Nat.mul_le_mul_right H ((Nat.le_div_iff_mul_le pos).mpr lo))
  · intro hi
    have k : 0<y/P := Nat.pos_of_ne_zero fun zero => by
      rw [zero,zero_mul] at hi
      omega
    exact ⟨y/P,k,by simpa only [Nat.mul_comm P] using Nat.mul_div_le y P,hi⟩

private theorem multiple {P H r y : ℕ} (lo : P≤r) (hi : r≤H) (yp : 0<y) (dvd : r∣y) :
    inBands P H y := by
  obtain ⟨k,e⟩ := dvd
  have kp : 0<k := Nat.pos_of_ne_zero fun z => by simp [e,z] at yp
  rw [e,mul_comm r]
  exact ⟨k,kp,Nat.mul_le_mul_left k lo,Nat.mul_le_mul_left k hi⟩

private theorem nonunit {n a x y : ℕ} [NeZero n] (eqn : x^2=a+y) :
    (x:ZMod n)∈marked n a ↔ ¬n.Coprime y := by
  have ez : (x:ZMod n)^2=(a:ZMod n)+(y:ZMod n) := by
    simpa only [Nat.cast_pow,Nat.cast_add] using congrArg (fun u : ℕ => (u:ZMod n)) eqn
  have difference : ((a:ℤ):ZMod n)-(x:ZMod n)^2= -(y:ZMod n) := by
    rw [Int.cast_natCast,ez]
    abel
  have iu : IsUnit (-(y:ZMod n)) ↔ IsUnit (y:ZMod n) := ⟨fun h => by simpa using h.neg,IsUnit.neg⟩
  simp only [marked,mem_filter,mem_univ,true_and,difference,iu,ZMod.isUnit_iff_coprime]
  exact not_congr Nat.coprime_comm

/-- Removing a known factor coprime to N leaves the same necessary condition
on the reduced remainder. In particular one can remove any power of two for
odd N. -/
theorem reduced {p q P H c z a x : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (pl : P≤p) (ql : P≤q) (pu : p≤H) (qu : q≤H) (unit : (p*q).Coprime c)
    (pos : 0<z) (form : x^2=a+c*z) (hit : (x:ZMod (p*q))∈marked (p*q) a) :
    inBands P H z := by
  have nc := (nonunit form).mp hit
  rw [Nat.coprime_mul_iff_right,and_iff_right unit,Nat.coprime_mul_iff_left,
    hp.out.coprime_iff_not_dvd,hq.out.coprime_iff_not_dvd] at nc
  by_cases dv : p∣z
  · exact multiple pl pu pos dv
  · exact multiple ql qu pos (by tauto)

theorem marked_band {p q P H a x : ℕ} [Fact p.Prime] [Fact q.Prime]
    (pl : P≤p) (ql : P≤q) (pu : p≤H) (qu : q≤H)
    (pos : a<x^2) (hit : (x:ZMod (p*q))∈marked (p*q) a) : inBands P H (x^2-a) := by
  apply reduced pl ql pu qu (c:=1) (Nat.coprime_one_right _) (by omega) _ hit
  omega

/-- At a small Jacobi-negative target, every actual mark has a *positive*
integer remainder, so the cofactor condition applies to all marked coordinates. -/
theorem positive_of_marked {p q P a x : ℕ} [Fact p.Prime] [Fact q.Prime]
    (neg : jacobiSym a (p*q)= -1) (pl : P≤p) (ql : P≤q) (small : a<P)
    (hit : (x:ZMod (p*q))∈marked (p*q) a) : a<x^2 := by
  by_contra! bad
  exact (CircleMarkSmallTargets.initial neg pl ql small (Nat.le_sqrt'.mpr (by omega))) hit

/-- The first coordinate whose squared remainder reaches the next lower
endpoint. It can overshoot the next band when adjacent squares are far apart. -/
def jump (a P x : ℕ) : ℕ := ceilSqrt (a+((x^2-a)/P+1)*P)

theorem jump_le_iff {a P x z : ℕ} :
    jump a P x≤z ↔ a+((x^2-a)/P+1)*P≤z^2 := ceilSqrt_le_iff

theorem progress {a P x : ℕ} (pos : 0<P) (above : a≤x^2) : x<jump a P x := by
  have next := Nat.lt_mul_div_succ (x^2-a) pos
  rw [Nat.mul_comm P] at next
  exact lt_of_not_ge (fun stop => by have h := jump_le_iff.mp stop; omega)

/-- Every intervening integer coordinate is a certified miss. The endpoint
itself is retained for testing, even if the jump goes directly to a mark. -/
theorem skip {p q P H a x z : ℕ} [Fact p.Prime] [Fact q.Prime]
    (pl : P≤p) (ql : P≤q) (pu : p≤H) (qu : q≤H)
    (above : a<x^2) (gap : ((x^2-a)/P)*H<x^2-a) (fromX : x≤z)
    (before : z<jump a P x) : (z:ZMod (p*q))∉marked (p*q) a := by
  intro hit
  have monotone := Nat.pow_le_pow_left fromX 2
  obtain ⟨k,_,lo,hi⟩ := marked_band pl ql pu qu (above.trans_le monotone) hit
  have stop : z^2<a+((x^2-a)/P+1)*P := lt_of_not_ge (fun past =>
    (not_le_of_gt before) (jump_le_iff.mpr past))
  by_cases left : k≤(x^2-a)/P
  · have h := Nat.mul_le_mul_right H left
    omega
  · have h := Nat.mul_le_mul_right P (show (x^2-a)/P+1≤k by omega)
    omega

/-- Replacing the left endpoint of any finite scan by the jump keeps exactly
the same successful coordinates, including its first success when one exists. -/
theorem hits_preserved {p q P H a x : ℕ} [Fact p.Prime] [Fact q.Prime] (finish : ℕ)
    (pos : 0<P) (pl : P≤p) (ql : P≤q) (pu : p≤H) (qu : q≤H)
    (above : a<x^2) (gap : ((x^2-a)/P)*H<x^2-a) :
    (Icc x finish).filter (fun z : ℕ => (z:ZMod (p*q))∈marked (p*q) a) =
    (Icc (jump a P x) finish).filter (fun z : ℕ => (z:ZMod (p*q))∈marked (p*q) a) := by
  ext z
  simp only [mem_filter,mem_Icc]
  constructor
  · rintro ⟨⟨start,stop⟩,hit⟩
    exact ⟨⟨le_of_not_gt (fun early => skip pl ql pu qu above gap start early hit),stop⟩,hit⟩
  · rintro ⟨⟨start,stop⟩,hit⟩
    exact ⟨⟨(progress pos above.le).le.trans start,stop⟩,hit⟩

/-- The k-th upper endpoint and next lower endpoint touch or overlap on
the integer line exactly at this threshold. -/
theorem touch_iff {P H k : ℕ} (width : P≤H) :
    (k+1)*P≤k*H+1 ↔ P-1≤k*(H-P) := by
  have form : k*H=k*P+k*(H-P) := by rw [←Nat.mul_add]; congr 1; omega
  rw [form,Nat.add_mul,one_mul]
  omega

/-- From the first touching pair of bands on, every integer remainder passes
the interval test. -/
theorem continuous {P H k y : ℕ} (pos : 0<P) (width : P≤H) (kp : 0<k)
    (touch : P-1≤k*(H-P)) (above : k*P≤y) : inBands P H y := by
  have jl : k≤y/P := (Nat.le_div_iff_mul_le pos).mpr above
  have joined := (touch_iff (k:=y/P) width).mpr (touch.trans (Nat.mul_le_mul_right (H-P) jl))
  have next := Nat.lt_mul_div_succ y pos
  rw [Nat.mul_comm P] at next
  exact ⟨y/P,kp.trans_le jl,by simpa only [Nat.mul_comm P] using Nat.mul_div_le y P,by omega⟩

/-- Six-bit factor bounds give P=49 and H=63. The endpoint of this
two-coordinate skip has a nontrivial gcd at the target three. -/
theorem control : 3127/64+1=49 ∧ jump 3 49 9=11 ∧
    (∀ z : ℕ, 9≤z → z<11 → (z:ZMod 3127)∉marked 3127 3) ∧
    (11:ZMod 3127)∈marked 3127 3 ∧ Nat.gcd (11^2-3) 3127=59 := by
  letI : Fact (Nat.Prime 53) := ⟨by decide⟩
  letI : Fact (Nat.Prime 59) := ⟨by decide⟩
  have next : jump 3 49 9=11 := by decide
  refine ⟨by decide,next,fun z lo hi =>
    skip (p:=53) (q:=59) (a:=3) (H:=63) (x:=9) (by decide : 49≤53) (by decide)
      (by decide) (by decide) (by decide) (by decide) lo (by rwa [next]),?_,by decide⟩
  exact (nonunit (n:=3127) (x:=11) (a:=3) (y:=118) (by decide)).mpr (by decide)

end PrimeFactors.CircleMarkCofactorBands
