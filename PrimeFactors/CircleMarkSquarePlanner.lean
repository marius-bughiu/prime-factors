import PrimeFactors.Fermat
import PrimeFactors.RecognizingQuarticProducts
import PrimeFactors.CircleMarkRationalMixedBoundary
import PrimeFactors.CircleMarkFirstTarget
import PrimeFactors.SmallJacobiNonresidue
import PrimeFactors.LeastPrimeBoundInterface

/-! Cost of the ordinary Fermat comparison when just one factor is in the
shortfall band for a square chosen from the product's fourth root. -/
namespace PrimeFactors.CircleMarkSquarePlanner

open RecognizingQuarticProducts

/-- If one factor is close to the public ceiling square root, this bounds the
actual midpoint index without first estimating the other factor. -/
private theorem midpoint_bound {p q k : ℕ}
    (near : ((q:ℤ)-(ceilSqrt (p*q):ℤ))^2 < 2*(k+1:ℕ)*(q:ℤ)) :
    (p+q)/2 ≤ ceilSqrt (p*q)+k := by
  let R := ceilSqrt (p*q)
  change ((q:ℤ)-(R:ℤ))^2 < _ at near
  have sq : p*q≤R^2 := ceilSqrt_le_iff.mp le_rfl
  have sq' : (p:ℤ)*q≤(R:ℤ)^2 := by exact_mod_cast sq
  by_contra! late
  have bound : 2*(R+k+1)≤p+q := by dsimp only [R] at *; omega
  have mul := Nat.mul_le_mul_right q bound
  have mul' : 2*((R:ℤ)+k+1)*q≤((p:ℤ)+q)*q := by exact_mod_cast mul
  push_cast at near
  nlinarith only [near,sq',mul']

/-- Take H=D=h=floor(N^(1/4)). If q is in the small-deficit regime
for that square, the true midpoint occurs among the first five. -/
theorem upper_square {p q s : ℕ} (order : p≤q) (sp : 0<s)
    (small : s≤fourthRoot (p*q)) (area : q=(fourthRoot (p*q)+1)^2+s) :
    (p+q)/2 ≤ ceilSqrt (p*q)+4 := by
  let h := fourthRoot (p*q)
  let R := ceilSqrt (p*q)
  change s≤h at small
  change q=(h+1)^2+s at area
  have hp := (fourthRoot_eq_iff.mp (show fourthRoot (p*q)=h from rfl)).1
  have low : h^2≤R := by
    apply Nat.mul_self_le_mul_self_iff.mp
    have sq : p*q≤R^2 := ceilSqrt_le_iff.mp le_rfl
    nlinarith only [hp,sq]
  have up : R≤q := ceilSqrt_le_iff.mpr (by simpa only [sq] using Nat.mul_le_mul_right q order)
  have bound : q≤h^2+3*h+1 := by nlinarith only [area,small]
  apply midpoint_bound
  change ((q:ℤ)-(R:ℤ))^2 < 10*(q:ℤ)
  have delta : (q:ℤ)-R≤3*h+1 := by
    have b : (q:ℤ)≤3*h+1+R := by exact_mod_cast (show q≤3*h+1+R by omega)
    linarith
  have nn : 0≤(q:ℤ)-R := sub_nonneg.mpr (by exact_mod_cast up)
  have ss := sq_le_sq' (by linarith : -(3*(h:ℤ)+1)≤(q:ℤ)-R) delta
  have high : (h:ℤ)^2+2*h+1≤q := by exact_mod_cast (show h^2+2*h+1≤q by nlinarith only [area,Nat.zero_le s])
  nlinarith only [ss,high,sq_nonneg (h:ℤ),Int.natCast_nonneg h]

/-- In this family the five-test public check necessarily succeeds. At a
specific tested index, taking the integer square root recovers the two
original odd factors in increasing order. -/
theorem five_tests {p q s : ℕ} (op : Odd p) (oq : Odd q) (order : p≤q) (sp : 0<s)
    (small : s≤fourthRoot (p*q)) (area : q=(fourthRoot (p*q)+1)^2+s) :
    fermatWindowMiss (p*q) 5=false ∧ ∃ i<5,
      let m := ceilSqrt (p*q)+i
      let d := (m^2-p*q).sqrt
      m-d=p ∧ m+d=q := by
  let m := (p+q)/2
  let d := (q-p)/2
  let R := ceilSqrt (p*q)
  obtain ⟨x,hx⟩ := op
  obtain ⟨y,hy⟩ := oq
  have mid : m=p+d := by dsimp [m,d]; omega
  have larger : q=p+2*d := by dsimp [d]; omega
  have hit : m^2=p*q+d^2 := by rw [mid,larger]; ring
  have low : R≤m := ceilSqrt_le_iff.mpr (by omega)
  have cap : m≤R+4 := upper_square order sp small area
  let i := m-R
  have ind : i<5 := by dsimp [i]; omega
  have atIndex : ceilSqrt (p*q)+i=m := by change R+i=m; dsimp [i]; omega
  have delta : m^2-p*q=d^2 := by omega
  constructor
  · cases e : fermatWindowMiss (p*q) 5
    · rfl
    · have bad := List.all_eq_true.mp e i (List.mem_range.mpr ind)
      change decide ((((ceilSqrt (p*q)+i)^2-p*q).sqrt)^2 ≠ (ceilSqrt (p*q)+i)^2-p*q)=true at bad
      simp only [atIndex,delta,Nat.sqrt_eq',ne_self_iff_false,decide_false,Bool.false_eq_true] at bad
  · refine ⟨i,ind,?_⟩
    dsimp only
    rw [atIndex,delta,Nat.sqrt_eq']
    omega

set_option exponentiation.threshold 4096 in
/-- Conditional on the analytic least-prime estimate at the supplied modulus. The least negative target actually selected
from N attains a proper gcd throughout the full-width upper-square band. -/
theorem first_target {p q s : ℕ} [pp : Fact p.Prime] [qp : Fact q.Prime]
    (pl : 2^1023≤p) (ord : p<q) (width : p*q<2^2048)
    (least : 3000≤p*q → (∀ r : ℕ, r.Prime → r∣p*q → Real.log (p*q:ℕ)^2≤(r:ℝ)) →
      LeastPrimeBoundInterface.RealOutside (p*q) (Real.log (p*q:ℕ)^2)) (sp : 0<s)
    (small : s≤fourthRoot (p*q)) (area : q=(fourthRoot (p*q)+1)^2+s) :
    ∃ a≤2015165, CircleMarkFirstTarget.First (p*q) a ∧
      let h := fourthRoot (p*q)
      let g := (CircleMarkRationalProduct.product a h h).gcd (p*q)
      g=p ∨ g=q := by
  classical
  let h := fourthRoot (p*q)
  change q=(h+1)^2+s at area
  have limits := fourthRoot_eq_iff.mp (show fourthRoot (p*q)=h from rfl)
  have short : h<p := by
    by_contra! large
    have big := Nat.pow_le_pow_left (pl.trans large) 4
    have lim : 2^2048 ≤ ((2:ℕ)^1023)^4 := by decide +kernel
    omega
  have below : p<(h+1)*(h+1) := by
    by_contra! large
    have mult := Nat.mul_le_mul large (show (h+1)*(h+1)≤q by nlinarith only [area,Nat.zero_le s])
    nlinarith only [limits.2,mult]
  have enough : 2015165≤h := le_fourthRoot.mpr
    ((by decide +kernel : (2015165:ℕ)^4≤2^1023).trans (pl.trans (Nat.le_mul_of_pos_right p qp.out.pos)))
  have oq : q≠2 := by have := (by decide +kernel : 2<2^1023).trans_le pl; omega
  have outside := LeastPrimeBoundInterface.full_size pp.out qp.out pl (pl.trans ord.le) width least
  obtain ⟨l,lim,_,_,neg⟩ := SmallJacobiNonresidue.exists_prime pp.out qp.out ord.ne oq outside
  have ex : ∃ a : ℕ, jacobiSym (a:ℤ) (p*q)= -1 := ⟨l,neg⟩
  let a := Nat.find ex
  have first : CircleMarkFirstTarget.First (p*q) a := ⟨Nat.find_spec ex,fun _ n => Nat.find_min' ex n⟩
  have bound := (first.2 l neg).trans lim
  have ap := (CircleMarkFirstTarget.prime (pp.out.one_lt.trans_le (Nat.le_mul_of_pos_right _ qp.out.pos)) first).pos
  exact ⟨a,bound,first,CircleMarkRationalMixedBoundary.side_target short below sp small
    (by simpa only [pow_two] using area) first.1 ap (bound.trans enough)⟩

attribute [local irreducible] fourthRoot ceilSqrt fermatWindowMiss

/-- A balanced, full-width example where the fifth midpoint is necessary. -/
theorem five_needed : (1489:ℕ).Prime ∧ (1721:ℕ).Prime ∧ 1489*1721=2562569 ∧
    fourthRoot 2562569=40 ∧ (40+1)^2+40=1721 ∧ ceilSqrt 2562569=1601 ∧
    fermatWindowMiss 2562569 4=true ∧ 1605^2=2562569+116^2 ∧
    (1605-116,1605+116)=(1489,1721) := by
  have r : ceilSqrt 2562569=1601 := by
    have hi := (ceilSqrt_le_iff (n:=2562569) (a:=1601)).mpr (by decide)
    have lo : ¬ ceilSqrt 2562569 ≤ 1600 := by rw [ceilSqrt_le_iff]; decide
    omega
  refine ⟨by norm_num,by norm_num,by decide,fourthRoot_eq_iff.mpr ⟨by decide,by decide⟩,
    by decide,r,?_,by decide,by decide⟩
  rw [fermatWindowMiss,r,show List.range 4=[0,1,2,3] from rfl]
  norm_num

end PrimeFactors.CircleMarkSquarePlanner
