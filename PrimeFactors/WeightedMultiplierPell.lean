import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.NumberTheory.Divisors
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Exact Pell equations for the product of two weighted square excesses.
All sign and integrality statements use integer arithmetic. Separation at positive norm counts integer coordinates directly. -/
namespace PrimeFactors.WeightedMultiplierPell

/-- A square product of excesses gives a norm whose right side is a square. -/
theorem norm_identity {A B N r s D E z f t : ℤ}
    (first : D=A^2-4*r*N) (second : E=B^2-4*s*N)
    (joint : z^2=D*E) (radical : r*s=t*f^2) :
    (s*D+r*E)^2-t*(2*f*z)^2=(s*A^2-r*B^2)^2 := by
  have diff : s*D-r*E=s*A^2-r*B^2 := by rw [first,second]; ring
  rw [←diff]
  linear_combination -4*r*s*joint+4*z^2*radical

/-- With both labels and multipliers fixed, the first Pell coordinate
determines the original product since its coefficient is 8rs. -/
theorem recover_product {A B N r s D E : ℤ}
    (first : D=A^2-4*r*N) (second : E=B^2-4*s*N) :
    8*r*s*N = s*A^2+r*B^2-(s*D+r*E) := by rw [first,second]; ring

private theorem zero_square {A B N r s D E z : ℤ}
    (first : D=A^2-4*r*N) (second : E=B^2-4*s*N) (joint : z^2=D*E)
    (same : s*A^2=r*B^2) (nonneg : 0≤A*B*z) (nonnegD : 0≤D) :
    (A*B-z)^2=16*r*s*N^2 := by
  have cross : B^2*D=A^2*E := by rw [first,second]; linear_combination 4*N*same
  have center : A*B*z=B^2*D := by
    apply (sq_eq_sq₀ nonneg (mul_nonneg (sq_nonneg _) nonnegD)).mp
    calc (A*B*z)^2 = A^2*B^2*z^2 := by ring
         _ = B^2*(A^2*E)*D := by rw [joint]; ring
         _ = (B^2*D)^2 := by rw [←cross]; ring
  calc
    (A*B-z)^2 = A^2*B^2-2*(A*B*z)+z^2 := by ring
    _ = _ := by rw [center,joint,first,second]; linear_combination -4*N*same

/-- At C=0 the minus-sign gcd is exactly N. This includes zero excesses. -/
theorem zero_gcd {A B N r s D E z : ℕ}
    (first : A^2=D+4*r*N) (second : B^2=E+4*s*N)
    (joint : z^2=D*E) (same : s*A^2=r*B^2) :
    (A*B-z).gcd N=N := by
  have eq1 : (A:ℤ)^2=D+4*(r:ℤ)*N := by exact_mod_cast first
  have eq2 : (B:ℤ)^2=E+4*(s:ℤ)*N := by exact_mod_cast second
  have prod : (z:ℤ)^2=(D:ℤ)*E := by exact_mod_cast joint
  have rel : (s:ℤ)*(A:ℤ)^2=(r:ℤ)*(B:ℤ)^2 := by exact_mod_cast same
  have diff := zero_square (sub_eq_iff_eq_add.mpr eq1).symm
    (sub_eq_iff_eq_add.mpr eq2).symm prod rel (by positivity) (by positivity)
  have below : z≤A*B := by
    apply (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp
    rw [joint,mul_pow]
    exact Nat.mul_le_mul (by omega) (by omega)
  have div : (N:ℤ)^2 ∣ ((A*B-z:ℕ):ℤ)^2 := by
    rw [Nat.cast_sub below,Nat.cast_mul,diff]
    exact ⟨16*(r:ℤ)*s,by ring⟩
  apply Nat.gcd_eq_right
  exact_mod_cast (Int.pow_dvd_pow_iff (by decide : 2≠0)).mp div

/-- Before dividing the Pell coordinates by a common factor g, its square
divides C². Thus g divides C itself, for every solution of the norm equation. -/
theorem common_dvd {x y t g C : ℕ} (norm : x^2=t*y^2+C^2)
    (left : g∣x) (right : g∣y) : g∣C := by
  apply (Nat.pow_dvd_pow_iff (by decide : 2≠0)).mp
  have a := pow_dvd_pow_of_dvd left 2
  have b := dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd right 2) t
  rw [norm] at a
  exact (Nat.dvd_add_iff_right b).mpr a

/-- Division by a common factor preserves the square shape of the norm. -/
theorem normalize {x y t C g : ℕ} (norm : x^2=t*y^2+C^2) (hg : 0<g)
    (left : g∣x) (right : g∣y) :
    (x/g)^2 = t*(y/g)^2+(C/g)^2 := by
  have cdvd := common_dvd norm left right
  apply mul_left_cancel₀ (pow_ne_zero 2 hg.ne')
  calc
    _ = (g*(x/g))^2 := (mul_pow ..).symm
    _ = x^2 := by rw [Nat.mul_div_cancel' left]
    _ = t*y^2+C^2 := norm
    _ = t*(g*(y/g))^2+(g*(C/g))^2 := by
      rw [Nat.mul_div_cancel' right,Nat.mul_div_cancel' cdvd]
    _ = _ := by ring

/-- Primitive coordinate pairs select exactly one slope modulo the entire norm. -/
theorem primitive_class {x y d t : ℤ} (norm : x^2-t*y^2=d) (cop : IsCoprime y x) :
    ∃ R : ℤ, d ∣ R^2-t ∧ d ∣ x-R*y ∧ ∀ S : ℤ, d ∣ x-S*y → d ∣ R-S := by
  obtain ⟨a,b,bezout⟩ := cop
  let k := a^2*y + 2*a*b*x + t*b^2*y
  have inv : k*y+d*b^2=1 := by
    dsimp [k]
    linear_combination (a*y+b*x+1)*bezout-b^2*norm
  refine ⟨x*k, ⟨k^2-t*b^2*(k*y+1),?_⟩, ⟨x*b^2,?_⟩,?_⟩
  · linear_combination k^2*norm+t*(k*y+1)*inv
  · linear_combination -x*inv
  · rintro s ⟨z,hz⟩
    refine ⟨k*z-s*b^2,?_⟩
    linear_combination k*hz+s*inv

/-- Each natural solution of positive first coordinate therefore supplies a
divisor g of C and one root class modulo (C/g)². -/
theorem normalized_class {x y t C : ℕ} (norm : x^2=t*y^2+C^2) (xp : 0<x) :
    let g := x.gcd y
    g∣C ∧ ∃ R : ℤ, ((C/g:ℕ):ℤ)^2 ∣ R^2-t ∧
      ((C/g:ℕ):ℤ)^2 ∣ ((x/g:ℕ):ℤ)-R*(y/g:ℕ) ∧
      ∀ S : ℤ, ((C/g:ℕ):ℤ)^2 ∣ ((x/g:ℕ):ℤ)-S*(y/g:ℕ) →
        ((C/g:ℕ):ℤ)^2 ∣ R-S := by
  let g := x.gcd y
  have gp : 0<g := Nat.gcd_pos_of_pos_left _ xp
  have cop : (x/g).Coprime (y/g) := Nat.coprime_div_gcd_div_gcd gp
  have X : g∣x := Nat.gcd_dvd_left ..
  have Y : g∣y := Nat.gcd_dvd_right ..
  have nc : ((x/g:ℕ):ℤ)^2=(t:ℤ)*((y/g:ℕ):ℤ)^2+((C/g:ℕ):ℤ)^2 := by
    exact_mod_cast normalize norm gp X Y
  exact ⟨common_dvd norm X Y,primitive_class (by linarith only [nc]) cop.symm.isCoprime⟩

/-- Integer coordinates of the quotient in a single slope class. -/
theorem quotient {x y w v d t R : ℤ} (hd : d≠0)
    (first : x^2-t*y^2=d) (second : w^2-t*v^2=d)
    (root : d ∣ R^2-t) (left : d ∣ x-R*y) (right : d ∣ w-R*v) :
    ∃ a b : ℤ, d*a=x*w-t*y*v ∧ d*b=x*v-w*y ∧ a^2-t*b^2=1 ∧
      x*a+t*y*b=w ∧ x*b+y*a=v := by
  obtain ⟨e, he⟩ := root
  obtain ⟨s, hs⟩ := left
  obtain ⟨z, hz⟩ := right
  let a := s*w+R*y*z+e*y*v
  let b := s*v-z*y
  have ha : d*a=x*w-t*y*v := by
    dsimp [a]
    linear_combination -w*hs-R*y*hz-y*v*he
  have hb : d*b=x*v-w*y := by
    dsimp [b]
    linear_combination -v*hs+y*hz
  refine ⟨a,b,ha,hb,?_,?_,?_⟩
  · apply mul_left_cancel₀ (pow_ne_zero 2 hd)
    calc
      d^2*(a^2-t*b^2) = (d*a)^2-t*(d*b)^2 := by ring
      _ = (x^2-t*y^2)*(w^2-t*v^2) := by rw [ha,hb]; ring
      _ = d^2*1 := by rw [first,second]; ring
  · apply mul_left_cancel₀ hd
    calc
      d*(x*a+t*y*b) = x*(d*a)+t*y*(d*b) := by ring
      _ = d*w := by rw [ha,hb]; linear_combination w*first
  · apply mul_left_cancel₀ hd
    calc
      d*(x*b+y*a) = x*(d*b)+y*(d*a) := by ring
      _ = d*v := by rw [ha,hb]; linear_combination v*first

/-- In a positive norm equation with positive first and nonnegative second
coordinates, the first coordinate at least doubles from one solution to the
next in a fixed class. This uses only integer inequalities. -/
theorem separation {x y w v d t R : ℤ} (hd : 0<d) (ht : 0<t)
    (first : x^2-t*y^2=d) (second : w^2-t*v^2=d)
    (root : d ∣ R^2-t) (left : d ∣ x-R*y) (right : d ∣ w-R*v)
    (xp : 0<x) (yp : 0≤y) (vp : 0≤v) (order : x<w) : 2*x≤w := by
  obtain ⟨a,b,ha,hb,norm,wa,_⟩ := quotient hd.ne' first second root left right
  have wp : 0<w := xp.trans order
  have inc : 0<v^2-y^2 := by
    apply pos_of_mul_pos_right (a:=t) _ ht.le
    nlinarith only [first,second,mul_pos (sub_pos.mpr order) (by omega : 0<w+x)]
  have cross : (x*v-w*y)*(x*v+w*y)=d*(v^2-y^2) := by
    linear_combination v^2*first-y^2*second
  have bp : 0<b := by
    apply pos_of_mul_pos_right (a:=d) _ hd.le
    rw [hb]
    apply pos_of_mul_pos_left (b:=x*v+w*y) _ (by positivity)
    rw [cross]
    exact mul_pos hd inc
  have diag : (x*w-t*y*v)*(x*w+t*y*v)=d*(x^2+t*v^2) := by
    linear_combination x^2*second+t*v^2*first
  have ap : 0<a := by
    apply pos_of_mul_pos_right (a:=d) _ hd.le
    rw [ha]
    apply pos_of_mul_pos_left (b:=x*w+t*y*v) _ (by positivity)
    rw [diag]
    positivity
  have an : a≠1 := by
    rintro rfl
    have prod : 0<t*b^2 := by positivity
    nlinarith only [norm,prod]
  have two : 2≤a := by omega
  calc 2*x ≤ a*x := mul_le_mul_of_nonneg_right two xp.le
       _ ≤ w := by rw [←wa,mul_comm a x]; exact le_add_of_nonneg_right (by positivity)

private theorem band {x : ℤ} (positive : 0<x) (K : ℕ) (top : x<2^K) :
    ∃ j<K, 2^j≤x ∧ x<2^(j+1) := by
  induction K with
  | zero => simp at top; omega
  | succ K ih =>
    by_cases inside : x<2^K
    · obtain ⟨j,hj,lo,hi⟩ := ih inside
      exact ⟨j,by omega,lo,hi⟩
    · exact ⟨K,by omega,le_of_not_gt inside,top⟩

/-- Bound the number of pairs in one class solely by the bit bound for their
first coordinate, with either sign of the underlying two-trace difference. -/
theorem class_card {d t R : ℤ} (hd : 0<d) (ht : 0<t) (root : d ∣ R^2-t)
    (S : Finset (ℤ×ℤ)) (K : ℕ)
    (points : ∀ z∈S, z.1^2-t*z.2^2=d ∧ d ∣ z.1-R*z.2 ∧
      0<z.1 ∧ 0≤z.2 ∧ z.1<2^K) : S.card≤K := by
  classical
  have room (z : S) : ∃ j<K, 2^j≤z.val.1 ∧ z.val.1<2^(j+1) :=
    band (points z z.property).2.2.1 K (points z z.property).2.2.2.2
  choose j hj bot top using room
  let bin (x : S) : Fin K := ⟨j x,hj x⟩
  have diff (a b : S) (ord : a.val.1<b.val.1) : j a≠j b := by
    intro same
    obtain ⟨na,ra,ax,ay,_⟩ := points a a.property
    obtain ⟨nb,rb,_,bypos,_⟩ := points b b.property
    have twice := separation hd ht na nb root ra rb ax ay bypos ord
    have lower : (2:ℤ)^(j b+1)≤b.val.1 := by
      rw [←same,pow_succ,mul_comm]
      exact (mul_le_mul_of_nonneg_left (bot a) (by decide)).trans twice
    exact (not_lt_of_ge lower) (top b)
  have inj : Function.Injective bin := by
    intro a b eq
    have same : j a=j b := congrArg Fin.val eq
    rcases lt_trichotomy a.val.1 b.val.1 with ab|ab|ba
    · exact (diff a b ab same).elim
    · apply Subtype.ext
      apply Prod.ext ab
      obtain ⟨na,_,_,ay,_⟩ := points a a.property
      obtain ⟨nb,_,_,bypos,_⟩ := points b b.property
      apply (sq_eq_sq₀ ay bypos).mp
      apply mul_left_cancel₀ ht.ne'
      rw [ab] at na
      omega
    · exact (diff b a ba same.symm).elim
  simpa only [Fintype.card_coe,Fintype.card_fin] using Fintype.card_le_of_injective bin inj

/-- A prime dividing the squarefree radicand prevents a square root modulo
its square. The argument includes the dyadic prime. -/
theorem ramified_no_root {t l R : ℤ} (prime : Prime l) (sf : Squarefree t) (rad : l∣t) :
    ¬l^2 ∣ R^2-t := by
  rintro ⟨z,hz⟩
  obtain ⟨w,hw⟩ := rad
  have hit : l∣R^2 := ⟨w+l*z,by linear_combination hz+hw⟩
  obtain ⟨b,hb⟩ := prime.dvd_of_dvd_pow hit
  exact prime.not_unit (sf l ⟨b^2-z,by rw [hb] at hz; linear_combination -hz⟩)

/-- The split-radicand case uses the ordinary factors x−y and x+y of C².
The smaller factor determines (x,y) uniquely. -/
theorem split_card {C : ℕ} (pos : 0<C) (S : Finset (ℕ×ℕ))
    (points : ∀ z∈S, z.1^2=z.2^2+C^2) : S.card≤(C^2).divisors.card := by
  have data (z : ℕ×ℕ) (hz : z∈S) : z.2<z.1 ∧ (z.1-z.2)*(z.1+z.2)=C^2 := by
    have eq := points z hz
    have yx : z.2<z.1 := (Nat.pow_lt_pow_iff_left (by decide : 2≠0)).mp
      (by rw [eq]; exact Nat.lt_add_of_pos_right (pow_pos pos 2))
    refine ⟨yx,?_⟩
    obtain ⟨k,hk⟩ := Nat.exists_eq_add_of_le yx.le
    rw [hk] at eq ⊢
    rw [Nat.add_sub_cancel_left]
    nlinarith only [eq]
  apply Finset.card_le_card_of_injOn (fun z => z.1-z.2)
  · intro z hz
    exact Nat.mem_divisors.mpr ⟨⟨z.1+z.2,(data z hz).2.symm⟩,pow_ne_zero 2 pos.ne'⟩
  · intro u hu v hv same
    obtain ⟨up,ue⟩ := data u hu
    obtain ⟨vp,ve⟩ := data v hv
    change u.1-u.2=v.1-v.2 at same
    have eq : u.1+u.2=v.1+v.2 := by
      apply mul_left_cancel₀ (Nat.sub_pos_of_lt up).ne'
      rw [ue, same,ve]
    exact Prod.ext (by omega) (by omega)

end PrimeFactors.WeightedMultiplierPell
