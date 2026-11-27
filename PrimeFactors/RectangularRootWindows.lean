import PrimeFactors.RootIntervalSlope
import PrimeFactors.MaskedRelations
import PrimeFactors.ThreeTargetRepresentations
import Mathlib.Tactic.LinearCombination

/-! A narrow rectangle for every prescribed modular root gives short intervals
on rows indexed by a multiple of the input. The rectangle can be searched
from N alone. -/
namespace PrimeFactors.RectangularRootWindows

/-- Dirichlet approximation confines the numerator and denominator representing
any modular residue. Inverting the denominator reconstructs the residue;
a nonunit denominator below N already shares a proper divisor with N. -/
theorem rectangle {N B : ℕ} (np : 0<N) (bp : 0<B) (r : ZMod N) :
    ∃ (y : ℕ) (x : ℤ), 0<y ∧ y≤B ∧ x.natAbs≤N/(B+1) ∧ (x : ZMod N)=r*y := by
  letI : NeZero N := ⟨np.ne'⟩
  obtain ⟨y,yp,yb,j,h⟩ := boundedSlope_exists N B (r.val : ℤ) np bp
  let x := (y : ℤ)*r.val-(N : ℤ)*j
  have h' : ((x.natAbs : ℤ) * (B+1)) ≤ N := by
    rw [Int.natCast_natAbs]
    exact h
  have h'' : x.natAbs*(B+1) ≤ N := by exact_mod_cast h'
  refine ⟨y,x,yp,yb,(Nat.le_div_iff_mul_le (by omega)).mpr h'',?_⟩
  dsimp [x]
  push_cast
  simp [mul_comm]

/-- On a balanced large-prime input a short, nonzero numerator forces
the denominator to be a unit at every prime of N. -/
theorem coprime_denominator {N B H y : ℕ} [NeZero N] {x : ℤ} {r : ZMod N}
    (yp : 0<y) (yb : y≤B) (bn : B<N) (xh : x.natAbs≤H)
    (large : ∀ l : ℕ, l.Prime → l∣N → H<l)
    (unit : IsUnit r) (ratio : (x:ZMod N)=r*y) : y.Coprime N := by
  have nz : x≠0 := by
    intro z
    have eq : r*(y:ZMod N)=r*0 := by rw [←ratio,z,Int.cast_zero,mul_zero]
    have dy := (ZMod.natCast_zmod_eq_zero_iff_dvd ..).mp (unit.mul_right_inj.mp eq)
    exact (not_le_of_gt (lt_of_le_of_lt yb bn)) (Nat.le_of_dvd yp dy)
  apply Nat.coprime_of_dvd
  intro l lp ly ln
  have eq := congrArg (ZMod.castHom ln (ZMod l)) ratio
  simp only [map_intCast,map_mul,map_natCast,
    (ZMod.natCast_zmod_eq_zero_iff_dvd ..).mpr ly,mul_zero] at eq
  have dv := Int.natCast_dvd.mp ((ZMod.intCast_zmod_eq_zero_iff_dvd ..).mp eq)
  exact (not_le_of_gt (large l lp ln)) ((Nat.le_of_dvd (Int.natAbs_pos.mpr nz) dv).trans xh)

/-- Make both coordinates primitive if the denominator is invertible.
Scaling down preserves the modular ratio and its rectangular bounds. -/
theorem primitive {N H B y : ℕ} [NeZero N] {x : ℤ} {r : ZMod N}
    (yp : 0<y) (byBound : y≤B) (bx : x.natAbs≤H) (unit : y.Coprime N)
    (ratio : (x:ZMod N)=r*y) :
    ∃ (v : ℕ) (u : ℤ), 0<v ∧ v≤B ∧ u.natAbs≤H ∧ u.natAbs.Coprime v ∧
      v.Coprime N ∧ (u:ZMod N)=r*v := by
  let g := x.natAbs.gcd y
  have gp : 0<g := Nat.gcd_pos_of_pos_right _ yp
  have gx : g ∣ x.natAbs := Nat.gcd_dvd_left ..
  have gy : g ∣ y := Nat.gcd_dvd_right ..
  have gx' : (g:ℤ) ∣ x := Int.natCast_dvd.mpr gx
  obtain ⟨u,hu⟩ := gx'
  obtain ⟨v,hv⟩ := gy
  have ux : x.natAbs=g*u.natAbs := by rw [hu,Int.natAbs_mul,Int.natAbs_natCast]
  have uq : u.natAbs=x.natAbs/g := by rw [ux,Nat.mul_div_cancel_left _ gp]
  have vq : v=y/g := by rw [hv,Nat.mul_div_cancel_left _ gp]
  have cop : u.natAbs.Coprime v := by rw [uq,vq]; exact Nat.coprime_div_gcd_div_gcd gp
  have gn : g.Coprime N := unit.coprime_dvd_left (Nat.gcd_dvd_right ..)
  have vn : v.Coprime N := unit.coprime_dvd_left ⟨g,by rw [hv,Nat.mul_comm]⟩
  have gu : IsUnit (g : ZMod N) := (ZMod.isUnit_iff_coprime g N).mpr gn
  refine ⟨v,u,by by_contra! z; simp [show v=0 by omega] at hv; omega,
    (vq ▸ Nat.div_le_self ..).trans byBound,(uq ▸ Nat.div_le_self ..).trans bx,cop,vn,?_⟩
  apply gu.mul_left_inj.mp
  rw [hu,hv] at ratio
  push_cast at ratio
  convert ratio using 1 <;> ring

/-- The small numerator places a positive target above the multiple kN, or
a negative target below it. Only a globally trivial positive square may
have k=0. -/
theorem row {N B H y : ℕ} {x D : ℤ} {r : ZMod N} (np : 0<N) (yp : 0<y)
    (yb : y≤B) (xh : x.natAbs≤H) (short : H^2<N)
    (root : r^2=(D : ZMod N)) (ratio : (x:ZMod N)=r*y)
    (ns : ¬ IsSquare (D:ℚ)) :
    ∃ k : ℕ, 0<k ∧
      (0<D → D*(y:ℤ)^2-(k:ℤ)*N=x^2 ∧ k*N≤D.natAbs*B^2) ∧
      (D<0 → (k:ℤ)*N- (D.natAbs:ℤ)*y^2=x^2 ∧ k*N≤D.natAbs*B^2+H^2) := by
  have div : (N:ℤ) ∣ D*(y:ℤ)^2-x^2 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [ratio,mul_pow,root,sub_self]
  obtain ⟨m,hm⟩ := div
  have yn : (y:ℚ)≠0 := by exact_mod_cast yp.ne'
  have mn : m≠0 := by
    intro h
    rw [h,mul_zero,sub_eq_zero] at hm
    apply ns
    apply (isSquare_iff_exists_sq _).mpr
    refine ⟨(x:ℚ)/y,?_⟩
    have hh : (D:ℚ)*(y:ℚ)^2=(x:ℚ)^2 := by exact_mod_cast hm
    field_simp
    linear_combination hh
  have hsq : x^2≤(H:ℤ)^2 := by
    have h := Nat.pow_le_pow_left xh 2
    have eq : ((x.natAbs:ℤ)^2)≤(H:ℤ)^2 := by exact_mod_cast h
    simpa only [Int.natCast_natAbs,sq_abs] using eq
  have small : (H:ℤ)^2<N := by exact_mod_cast short
  have bn : (y:ℤ)^2≤(B:ℤ)^2 := by exact_mod_cast Nat.pow_le_pow_left yb 2
  have nz : (0:ℤ)<N := by exact_mod_cast np
  refine ⟨m.natAbs,Int.natAbs_pos.mpr mn,?_,?_⟩
  · intro pos
    have mp : 0<m := by
      rcases lt_or_gt_of_ne mn with neg|good
      · have mul := mul_le_mul_of_nonneg_left (show m≤ -1 by omega) nz.le
        nlinarith only [hm,hsq,small,mul,mul_nonneg pos.le (sq_nonneg (y:ℤ))]
      · exact good
    have eq : (m.natAbs:ℤ)=m := by rw [Int.natCast_natAbs,abs_of_pos mp]
    have de : (D.natAbs:ℤ)=D := by rw [Int.natCast_natAbs,abs_of_pos pos]
    constructor
    · rw [eq]; linarith [mul_comm (N:ℤ) m]
    · have h := mul_le_mul_of_nonneg_left bn pos.le
      exact_mod_cast (show (m.natAbs:ℤ)*N≤(D.natAbs:ℤ)*(B:ℤ)^2 by
        rw [eq,de,mul_comm m]; linarith [sq_nonneg x])
  · intro neg
    have yn' : (0:ℤ)<y := by exact_mod_cast yp
    have mp : m<0 := by
      rcases lt_or_gt_of_ne mn with good|bad
      · exact good
      · nlinarith only [hm,mul_nonneg nz.le bad.le,mul_neg_of_neg_of_pos neg (sq_pos_of_pos yn'),sq_nonneg x]
    have eq : (m.natAbs:ℤ)= -m := by rw [Int.natCast_natAbs,abs_of_neg mp]
    have de : (D.natAbs:ℤ)= -D := by rw [Int.natCast_natAbs,abs_of_neg neg]
    constructor
    · rw [eq,de]; linear_combination hm
    · have h := mul_le_mul_of_nonneg_left bn (neg_nonneg.mpr neg.le)
      exact_mod_cast (show (m.natAbs:ℤ)*N≤(D.natAbs:ℤ)*(B:ℤ)^2+(H:ℤ)^2 by
        rw [eq,de]; nlinarith only [hm,h,hsq])

/-- A prime dividing a primitive represented row must admit the target as
a square, except when it divides the denominator (which is ruled out by
primitivity). -/
theorem prime_screen {k N y l : ℕ} (lp : l.Prime) (lk : l∣k) {D x m : ℤ}
    (norm : x^2-D*(y:ℤ)^2=m*k*N) (prim : x.natAbs.Coprime y) :
    IsSquare (D : ZMod l) := by
  letI : Fact l.Prime := ⟨lp⟩
  have kz : (k:ZMod l)=0 := (ZMod.natCast_zmod_eq_zero_iff_dvd ..).mpr lk
  have e := congrArg (fun z:ℤ => (z:ZMod l)) norm
  push_cast at e
  rw [kz,mul_zero,zero_mul,sub_eq_zero] at e
  have ynz : (y:ZMod l)≠0 := by
    intro z
    have xz : (x:ZMod l)^2=0 := by simp [e,z]
    have xd : (l:ℤ) ∣ x := (ZMod.intCast_zmod_eq_zero_iff_dvd ..).mp (pow_eq_zero xz)
    have divides := Nat.dvd_gcd (Int.natCast_dvd.mp xd) ((ZMod.natCast_zmod_eq_zero_iff_dvd ..).mp z)
    rw [prim.gcd_eq_one,Nat.dvd_one] at divides
    exact lp.ne_one divides
  apply (isSquare_iff_exists_sq _).mpr
  refine ⟨(x:ZMod l)/y,?_⟩
  field_simp
  linear_combination -e

/-- Every root of a unit nonsquare is represented in a primitive row
within the scanner's two unsigned integer endpoints. Large is automatic
for the motivating balanced inputs at the cube-root numerator cutoff. -/
theorem cover {N B : ℕ} [NeZero N] {D : ℤ} (bp : 0<B) (bn : B<N)
    (short : (N/(B+1))^2<N) (ns : ¬IsSquare (D:ℚ)) (r : ZMod N)
    (large : ∀ l : ℕ, l.Prime → l∣N → N/(B+1)<l)
    (unit : IsUnit r) (root : r^2=(D:ZMod N)) :
    ∃ (k y : ℕ) (x : ℤ), 0<k ∧ 0<y ∧ y≤B ∧ x.natAbs≤N/(B+1) ∧
      x.natAbs.Coprime y ∧ y.Coprime N ∧ (x:ZMod N)=r*y ∧
      (0<D → D*(y:ℤ)^2-(k:ℤ)*N=x^2 ∧ k*N≤D.natAbs*B^2) ∧
      (D<0 → (k:ℤ)*N-(D.natAbs:ℤ)*y^2=x^2 ∧ k*N≤D.natAbs*B^2+(N/(B+1))^2) := by
  obtain ⟨y,x,yp,yb,xh,ratio⟩ := rectangle (NeZero.pos N) bp r
  have yn := coprime_denominator yp yb bn xh large unit ratio
  obtain ⟨v,u,vp,vb,uh,prim,vn,eq⟩ := primitive yp yb xh yn ratio
  obtain ⟨k,kp,pos,neg⟩ := row (NeZero.pos N) vp vb uh short root eq ns
  exact ⟨k,v,u,kp,vp,vb,uh,prim,vn,eq,pos,neg⟩

/-- An exact spacing bound for any two denominators tested on the same row.
This counts both signs of the target without a real square root. -/
theorem spacing {d L u v H : ℕ} (low : L≤u) (ord : u≤v)
    (band : d*v^2≤d*u^2+H^2) : d*(2*L)*(v-u)≤H^2 := by
  obtain ⟨w,rfl⟩ := Nat.exists_eq_add_of_le ord
  simp only [Nat.add_sub_cancel_left]
  nlinarith only [band,Nat.mul_le_mul_right (2*d*w) low,Nat.zero_le (d*w^2)]

end PrimeFactors.RectangularRootWindows
