import PrimeFactors.CircleMarkRationalMixedBoundary
import PrimeFactors.RecognizingQuarticProducts
import PrimeFactors.CircleMarkPrimitiveDensity

/-! Count hits among all negative-Jacobi targets separately for each fixed
balanced product. The square grid is set by the product. The subrectangle
used in the counting proof may depend on the larger prime. -/
namespace PrimeFactors.CircleMarkPublicGridRate

open Finset CircleMarkTargetFrequency CircleMarkRationalFrequency RecognizingQuarticProducts
open private PrimeFactors.CircleMarkRationalTargetCount.contribution from PrimeFactors.CircleMarkRationalTargetCount

abbrev side (p q : ℕ) := fourthRoot (p*q)

/-- Width of the collision-free subrectangle used for counting at q. -/
abbrev thin (p q : ℕ) := (q-1)/(2*side p q)

structure Bounds (p q h d : ℕ) : Prop where
  side_three : 3≤h
  side_short : h<p
  smaller_full : p<(h+1)*(h+1)
  square_le : h^2≤q
  thin_pos : 0<d
  thin_le : d≤h
  collision_free : 2*(h*d)<q
  rounded : q≤2*h*(d+1)

/-- The smaller prime sees every nonzero square. Near half the larger prime
in cell area fits inside a subrectangle with distinct primitive fractions. -/
theorem geometry {p q : ℕ} (big : 9≤p) (order : p<q) (balance : q<2*p) :
    Bounds p q (side p q) (thin p q) := by
  let h := side p q
  let d := thin p q
  have bounds := fourthRoot_eq_iff.mp (show fourthRoot (p*q)=h from rfl)
  have hpq := Nat.mul_le_mul_left p order.le
  have hqq := Nat.mul_le_mul_right q order.le
  have h3 : 3≤h := le_fourthRoot.mpr (by nlinarith only [hpq,Nat.pow_le_pow_left big 2])
  have sq_le : h^2≤q := by
    apply Nat.mul_self_le_mul_self_iff.mp
    nlinarith only [bounds.1,hqq]
  have full : p<(h+1)*(h+1) := by
    apply Nat.mul_self_lt_mul_self_iff.mp
    nlinarith only [hpq,bounds.2]
  have short : h<p := by
    by_contra! l
    nlinarith only [sq_le,balance,l,Nat.pow_le_pow_left l 2,
      Nat.mul_le_mul_right p big]
  have top : q<2*h*(h+1) := by
    have x := Nat.mul_lt_mul_of_pos_right balance (by omega : 0<q)
    have y := Nat.mul_lt_mul_of_pos_left bounds.2 (by decide : 0<2)
    have size : (h+1)^2≤2*h^2 := by
      have a := Nat.mul_le_mul_right h h3
      nlinarith only [h3,a]
    have lim := Nat.mul_le_mul_right ((h+1)^2) size
    apply Nat.mul_self_lt_mul_self_iff.mp
    nlinarith only [x,y,lim]
  have pos : 0<2*h := by omega
  have qp : q-1+1=q := by omega
  have dpos : 0<d := Nat.div_pos (show 2*h ≤ q-1 by nlinarith only [sq_le,h3,Nat.mul_le_mul_right h h3,qp]) pos
  have dshort : d≤h := by
    have t : (q-1)/(2*h)<h+1 := (Nat.div_lt_iff_lt_mul pos).mpr (by nlinarith only [top,Nat.sub_le q 1])
    exact Nat.le_of_lt_succ t
  have db : d*(2*h)≤q-1 := Nat.div_mul_le_self ..
  have up : q-1<(d+1)*(2*h) := (Nat.div_lt_iff_lt_mul pos).mp (Nat.lt_succ_self d)
  change Bounds p q h d
  exact ⟨h3,short,full,sq_le,dpos,dshort,by nlinarith only [db,qp],by nlinarith only [up,qp]⟩

/-- The public square contains the floor of 21/25 times the square root
of q on each side. This integer form avoids rounding a real radius. -/
theorem disk_room {p q : ℕ} (order : p<q) (balance : q<2*p) (big : 2000≤side p q) :
    21^2*q < 25^2*(side p q)^2 := by
  let h := side p q
  change 2000≤h at big
  change 21^2*q < 25^2*h^2
  have upper := (fourthRoot_eq_iff.mp (show fourthRoot (p*q)=h from rfl)).2
  have qsq : q^2<2*(h+1)^4 := by
    nlinarith only [Nat.mul_lt_mul_of_pos_right balance (by omega : 0<q),Nat.mul_lt_mul_of_pos_left upper (by decide : 0<2)]
  have little : 2000*(h+1)≤2001*h := by omega
  have scale := Nat.pow_le_pow_left little 4
  rw [mul_pow,mul_pow] at scale
  have cutoff : (21^2*q)^2*2000^4 < (25^2*h^2)^2*2000^4 := calc
    _ = (21^4*2000^4)*q^2 := by ring
    _ < (21^4*2000^4)*(2*(h+1)^4) := Nat.mul_lt_mul_of_pos_left qsq (by norm_num)
    _ = (2*21^4)*(2000^4*(h+1)^4) := by ring
    _ ≤ (2*21^4)*(2001^4*h^4) := Nat.mul_le_mul_left _ scale
    _ = (2*21^4*2001^4)*h^4 := by ring
    _ ≤ (25^4*2000^4)*h^4 := Nat.mul_le_mul_right _ (by decide)
    _ = _ := by ring
  have squares := Nat.lt_of_mul_lt_mul_right cutoff
  exact Nat.mul_self_lt_mul_self_iff.mp (by simpa only [sq] using squares)

private theorem rectangle_sub {h d : ℕ} (le : d≤h) : rectangle h d⊆rectangle h h :=
  product_subset_product_right (Icc_subset_Icc_right le)

private theorem covered_subgrid (n q h d : ℕ) (le : d≤h) :
    covered q (menu n h d) ⊆ covered q (menu n h h) :=
  erase_subset_erase _ (image_subset_image (image_subset_image (rectangle_sub le)))

theorem units {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (big : 9≤p) (order : p<q) (balance : q<2*p) (z : ℕ×ℕ)
    (m : z∈rectangle (side p q) (side p q)) : z.2.Coprime (p*q) := by
  have info := geometry big order balance
  have unitAt {r : ℕ} [hr : Fact r.Prime] (bound : side p q<r) : z.2.Coprime r := by
    obtain ⟨jp,jh⟩ := mem_Icc.mp (mem_product.mp m).2
    exact (hr.out.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt jp (jh.trans_lt bound))).symm
  exact (unitAt info.side_short).mul_right (unitAt (info.side_short.trans order))

/-- Exactly half of all target classes are squares at the smaller prime,
and every one of these is hit by the public fourth-root square. -/
theorem rate_split {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (big : 9≤p) (order : p<q) (balance : q<2*p) :
    rate (p*q) (menu (p*q) (side p q) (side p q)) =
      1/2+((covered q (menu (p*q) (side p q) (side p q))).card:ℚ)/(q-1) := by
  have info := geometry big order balance
  have full := CircleMarkRationalMixedBoundary.full_count (H:=side p q) (dvd_mul_right p q)
    (by omega) (units big order balance) ((by decide : 0<3).trans_le info.side_three)
    info.side_short info.smaller_full
  rw [rate_eq order.ne (by omega) (by omega),PrimeFactors.CircleMarkRationalTargetCount.contribution
    (r:=p) (e:=0) (by omega) (by simpa using full)]
  norm_num

/-- Every primitive fraction in the collision-free subrectangle contributes
one distinct target square at q. The smaller-prime contribution is exactly half. -/
theorem mass {p q : ℕ} [Fact p.Prime] [hq : Fact q.Prime]
    (big : 9≤p) (order : p<q) (balance : q<2*p) :
    1/2+((primitive (side p q) (thin p q)).card:ℚ)/(q-1) ≤
      rate (p*q) (menu (p*q) (side p q) (side p q)) := by
  have info := geometry big order balance
  have local_q := cover_count (n:=p*q) (dvd_mul_left q p) info.collision_free
    (fun z m => units big order balance z (rectangle_sub info.thin_le m))
  have count := card_le_card (covered_subgrid (p*q) q _ _ info.thin_le)
  rw [local_q] at count
  rw [rate_split big order balance]
  apply add_le_add_left
  exact div_le_div_of_nonneg_right (by exact_mod_cast count) (sub_nonneg.mpr (by exact_mod_cast hq.out.one_le))

/-- Transfer any proven lower density of primitive cells to a target hit rate.
The rounding loss comes from the final incomplete column. -/
theorem density_bound {p q : ℕ} [Fact p.Prime] [hq : Fact q.Prime]
    (big : 9≤p) (order : p<q) (balance : q<2*p) {c : ℚ} (cp : 0<c)
    (density : c*(side p q)*(thin p q)≤((primitive (side p q) (thin p q)).card:ℚ)) :
    (1+c)/2-c*(side p q)/(q-1)<rate (p*q) (menu (p*q) (side p q) (side p q)) := by
  apply lt_of_lt_of_le _ (mass big order balance)
  have near : (q:ℚ)≤2*(side p q)*((thin p q)+1) := by exact_mod_cast (geometry big order balance).rounded
  have pos : (0:ℚ)<q-1 := sub_pos.mpr (by exact_mod_cast hq.out.one_lt)
  apply (mul_lt_mul_iff_of_pos_right pos).mp
  simp only [sub_mul,add_mul,div_mul_cancel₀ _ pos.ne']
  nlinarith only [density,mul_le_mul_of_nonneg_left near cp.le,cp]

set_option exponentiation.threshold 8192

/-- In the full-size cohort, both dimensions of the subrectangle are large
and the incomplete-column error is below 2⁻⁵¹¹. -/
theorem full_dimensions {p q : ℕ} (lo : 2^1023≤p) (order : p<q) (hi : q<2^1024) :
    2^511≤side p q ∧ side p q<2^512 ∧ 2^20≤thin p q ∧
      (side p q:ℚ)/(q-1)<1/(2:ℚ)^511 := by
  let h := side p q
  have lower : 2^511≤h := le_fourthRoot.mpr
    ((by decide +kernel : ((2:ℕ)^511)^4 ≤ 2^1023*2^1023).trans (Nat.mul_le_mul lo (lo.trans order.le)))
  have pq := (Nat.mul_le_mul_right q (order.trans hi).le).trans_lt
    (Nat.mul_lt_mul_of_pos_left hi (by decide +kernel : 0<2^1024))
  have upper : h<2^512 := by
    apply lt_of_not_ge
    intro bad
    have large := le_fourthRoot.mp bad
    change (2^512)^4≤p*q at large
    rw [show (2^512:ℕ)^4=2^1024*2^1024 by decide +kernel] at large
    omega
  have qfloor : 2^1023≤q-1 := by omega
  have cap : 2^20≤thin p q := by
    apply (Nat.le_div_iff_mul_le (show 0<2*h by have := (by decide +kernel : 0<2^511).trans_le lower; omega)).mpr
    exact (Nat.mul_le_mul_left (2^20) (Nat.mul_le_mul_left 2 upper.le)).trans
      ((by decide +kernel : (2:ℕ)^20*(2*2^512)≤2^1023).trans qfloor)
  refine ⟨lower,upper,cap,?_⟩
  have qpos : (0:ℚ)<q-1 := sub_pos.mpr (by exact_mod_cast (show 1<q by omega))
  apply (div_lt_div_iff₀ qpos (by positivity)).mpr
  rw [one_mul]
  have bound := (Nat.mul_lt_mul_of_pos_right upper (by decide +kernel : 0<2^511)).trans_le
    ((by decide +kernel : (2:ℕ)^512*2^511≤2^1023).trans qfloor)
  change (h:ℚ)*2^511 < (q:ℚ)-1
  rw [←Nat.cast_one (R:=ℚ),←Nat.cast_sub (by omega : 1≤q)]
  exact_mod_cast bound

/-- With any supplied primitive density, this bound holds separately at every
full-width input. No distributional assumption on the primes is needed. -/
theorem full_density {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (lo : 2^1023≤p) (order : p<q) (hi : q<2^1024) {c : ℚ} (cp : 0<c)
    (density : c*(side p q)*(thin p q)≤((primitive (side p q) (thin p q)).card:ℚ)) :
    (1+c)/2-c/(2:ℚ)^511 < rate (p*q) (menu (p*q) (side p q) (side p q)) := by
  have bal : q<2*p := hi.trans_le ((by decide +kernel : (2:ℕ)^1024≤2*2^1023).trans
    (Nat.mul_le_mul_left _ lo))
  have out := density_bound ((by decide +kernel : 9≤2^1023).trans lo) order bal cp density
  have ratio := mul_lt_mul_of_pos_left (full_dimensions lo order hi).2.2.2 cp
  rw [←mul_div_assoc,←mul_div_assoc,mul_one] at ratio
  linarith only [ratio,out]

/-- A baseline from the elementary majority of primitive pairs. -/
theorem three_quarters {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (lo : 2^1023≤p) (order : p<q) (hi : q<2^1024) :
    3/4-1/(2:ℚ)^512 < rate (p*q) (menu (p*q) (side p q) (side p q)) := by
  obtain ⟨a,_,d,_⟩ := full_dimensions lo order hi
  have m := majority (by omega : 0<side p q) (by omega : 0<thin p q)
  have cast : (side p q:ℚ)*(thin p q) < 2*((primitive (side p q) (thin p q)).card:ℚ) := by exact_mod_cast m
  have out := full_density lo order hi (c:=1/2) (by norm_num) (by linarith)
  norm_num at out ⊢
  exact out

/-- More than four fifths of all negative-Jacobi target classes are hit,
uniformly over pairs of distinct full-width primes. -/
theorem four_fifths {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (lo : 2^1023≤p) (order : p<q) (hi : q<2^1024) :
    4/5 < rate (p*q) (menu (p*q) (side p q) (side p q)) := by
  obtain ⟨h,_,d,_⟩ := full_dimensions lo order hi
  have count := CircleMarkPrimitiveDensity.large_rectangle ((by decide +kernel : 2^20≤2^511).trans h) d
  have cast : 601*((side p q:ℚ)*(thin p q:ℚ)) < 1000*((primitive (side p q) (thin p q)).card:ℚ) := by
    exact_mod_cast count
  have out := full_density lo order hi (c:=601/1000) (by norm_num) (by linarith)
  exact lt_trans (by norm_num) out

end PrimeFactors.CircleMarkPublicGridRate
