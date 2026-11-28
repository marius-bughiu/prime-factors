import PrimeFactors.CircleMarkRationalFrequency
import PrimeFactors.CircleMarkRationalTwoHoles

/-! Fixed-semiprime hit frequencies near the rectangular coverage threshold. -/
namespace PrimeFactors.CircleMarkRationalTargetCount

open Finset CircleMarkRationalFrequency CircleMarkRationalCover CircleMarkRationalTwoHoles
open CircleMarkTargetFrequency
open private PrimeFactors.CircleMarkRationalFrequency.point
  PrimeFactors.CircleMarkRationalFrequency.local_point
  PrimeFactors.CircleMarkRationalFrequency.clear_point from PrimeFactors.CircleMarkRationalFrequency
open private PrimeFactors.CircleMarkTargetFrequency.plus PrimeFactors.CircleMarkTargetFrequency.squares
  PrimeFactors.CircleMarkTargetFrequency.local_cards PrimeFactors.CircleMarkTargetFrequency.covered_sub
  from PrimeFactors.CircleMarkTargetFrequency

private theorem local_test {n p : ℕ} [NeZero n] [Fact p.Prime] (dv : p∣n)
    (a : ZMod p) (z : ℕ×ℕ) (cop : z.2.Coprime n) :
    ((PrimeFactors.CircleMarkRationalFrequency.point n z).val : ZMod p)^2=a ↔
      (z.1:ZMod p)^2=a*(z.2:ZMod p)^2 := by
  rw [PrimeFactors.CircleMarkRationalFrequency.local_point dv z cop]
  have cleared := congrArg (fun x : ZMod p => x^2)
    (PrimeFactors.CircleMarkRationalFrequency.clear_point z (cop.of_dvd_right dv))
  simp only [mul_pow] at cleared
  constructor
  · rintro rfl
    exact cleared.symm
  · intro eqn
    exact mul_right_cancel₀ (pow_ne_zero 2 (isUnit_iff_ne_zero.mp
      ((ZMod.isUnit_iff_coprime ..).mpr (cop.of_dvd_right dv)))) (cleared.trans eqn)

private theorem menu_hit {n p H D : ℕ} [NeZero n] [Fact p.Prime] (dv : p∣n)
    (units : ∀ z∈rectangle H D, z.2.Coprime n) {a : ZMod p} (nz : a≠0) :
    a∈covered p (menu n H D) ↔ SquareHit p (a.val:ℤ) H D := by
  simp only [covered,mem_erase,and_iff_right nz,SquareHit,Int.cast_natCast,ZMod.natCast_zmod_val]
  constructor
  · intro m
    obtain ⟨x,xm,eqn⟩ := mem_image.mp m
    obtain ⟨z,zm,rfl⟩ := mem_image.mp xm
    obtain ⟨im,jm⟩ := mem_product.mp zm
    exact ⟨z.1,im,z.2,jm,(local_test dv a z (units z zm)).mp eqn⟩
  · rintro ⟨i,im,j,jm,eqn⟩
    have zm : (i,j)∈rectangle H D := mem_product.mpr ⟨im,jm⟩
    exact mem_image.mpr ⟨_,mem_image.mpr ⟨(i,j),zm,rfl⟩,(local_test dv a (i,j) (units _ zm)).mpr eqn⟩

/-- At one prime, the covered nonzero squares and the exceptional square for
each positive divisor of the deficit exhaust the nonzero quadratic residues. -/
theorem local_count {n p H D s : ℕ} [NeZero n] [Fact p.Prime] (dv : p∣n) (odd : p≠2)
    (units : ∀ z∈rectangle H D, z.2.Coprime n) (sp : 0<s) (sh : s≤H) (sd : s≤D)
    (area : p=(H+1)*(D+1)+s) :
    (covered p (menu n H D)).card+s.divisors.card=(p-1)/2 := by
  have complement : PrimeFactors.CircleMarkTargetFrequency.plus p \ covered p (menu n H D)=missingSquares p H D := by
    ext a
    have missing := mem_missingSquares (p:=p) (H:=H) (D:=D) (a:=(a.val:ℤ))
    simp only [Int.cast_natCast,ZMod.natCast_zmod_val] at missing
    rw [mem_sdiff,missing]
    simp only [PrimeFactors.CircleMarkTargetFrequency.plus,PrimeFactors.CircleMarkTargetFrequency.squares,mem_erase,mem_filter,
      mem_univ,true_and]
    by_cases nz : a=0
    · simp [nz]
    · rw [menu_hit dv units nz]
      tauto
  have total := card_sdiff_add_card_eq_card (PrimeFactors.CircleMarkTargetFrequency.covered_sub p (menu n H D))
  rw [complement,(missing_counts sp sh sd area).2,(PrimeFactors.CircleMarkTargetFrequency.local_cards p odd).1] at total
  omega

private theorem side_bounds {r H D s : ℕ} (sp : 0<s) (sh : s≤H) (sd : s≤D)
    (area : r=(H+1)*(D+1)+s) : D<r ∧ r≠2 := by
  have := Nat.mul_le_mul_right (D+1) (by omega : 2≤H+1)
  omega

private theorem contribution {r c e : ℕ} [hr : Fact r.Prime] (odd : r≠2) (total : c+e=(r-1)/2) :
    (c:ℚ)/(r-1)=1/2-(e:ℚ)/(r-1) := by
  obtain ⟨k,hk⟩ := hr.out.odd_of_ne_two odd
  have eqn : 2*(c+e)+1=r := by omega
  have eqn' : 2*((c:ℚ)+e)+1=r := by exact_mod_cast eqn
  have nz : (r:ℚ)-1≠0 := (sub_pos.mpr (by exact_mod_cast hr.out.one_lt)).ne'
  rw [eq_sub_iff_add_eq,←add_div,div_eq_div_iff nz (by norm_num)]
  linarith

/-- Among the uniformly chosen negative-Jacobi targets at this fixed product,
each local exceptional square removes precisely one reciprocal prime-width
share. The rectangle and the product are fixed before choosing a target. -/
theorem coverage {p q H D s t : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime] (diff : p≠q)
    (sp : 0<s) (sh : s≤H) (sd : s≤D) (pa : p=(H+1)*(D+1)+s)
    (tp : 0<t) (th : t≤H) (td : t≤D) (qa : q=(H+1)*(D+1)+t) :
    rate (p*q) (menu (p*q) H D)=1-(s.divisors.card:ℚ)/(p-1)-(t.divisors.card:ℚ)/(q-1) := by
  obtain ⟨ps,op⟩ := side_bounds sp sh sd pa
  obtain ⟨qs,oq⟩ := side_bounds tp th td qa
  have unitAt {r j : ℕ} [hr : Fact r.Prime] (bound : D<r) (m : j∈Icc 1 D) : j.Coprime r :=
    (hr.out.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (mem_Icc.mp m).1
      ((mem_Icc.mp m).2.trans_lt bound))).symm
  have units (z : ℕ×ℕ) (m : z∈rectangle H D) : z.2.Coprime (p*q) :=
    (unitAt ps (mem_product.mp m).2).mul_right (unitAt qs (mem_product.mp m).2)
  rw [rate_eq diff op oq,
    contribution op (local_count (dvd_mul_right p q) op units sp sh sd pa),
    contribution oq (local_count (dvd_mul_left q p) oq units tp th td qa)]
  ring

/-- The 3-by-3 grid hits 119 of the 144 negative-Jacobi targets at 17 times
19. Its two local deficits are one and three. -/
theorem control : (targets 323).card=144 ∧ (hits 323 (menu 323 3 3)).card=119 ∧
    rate 323 (menu 323 3 3)=119/144 := by
  letI : Fact (Nat.Prime 17) := ⟨by decide⟩
  letI : Fact (Nat.Prime 19) := ⟨by decide⟩
  have rate' := coverage (p:=17) (q:=19) (H:=3) (D:=3) (s:=1) (t:=3)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  have total := (counts (p:=17) (q:=19) (by decide) (by decide) (by decide) (menu 323 3 3)).1
  change (targets 323).card=144 at total
  have result : rate 323 (menu 323 3 3)=119/144 := by
    change rate (17*19) (menu (17*19) 3 3)=_
    rw [rate',show (1:ℕ).divisors.card=1 by decide,show (3:ℕ).divisors.card=2 by decide]
    norm_num
  refine ⟨total,?_,result⟩
  rw [rate,total] at result
  exact_mod_cast (show ((hits 323 (menu 323 3 3)).card:ℚ)=119 by linarith)

end PrimeFactors.CircleMarkRationalTargetCount
