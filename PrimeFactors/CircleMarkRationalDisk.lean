import PrimeFactors.CircleMarkRationalFrequency

/-! Squaring modular fractions can identify opposite slopes. A Euclidean norm
bound controls both signs of the cross-products simultaneously. -/
namespace PrimeFactors.CircleMarkRationalDisk

open Finset CircleMarkRationalFrequency CircleMarkTargetFrequency
open private PrimeFactors.CircleMarkRationalFrequency.point
  PrimeFactors.CircleMarkRationalFrequency.clear_point
  PrimeFactors.CircleMarkRationalFrequency.local_point
  PrimeFactors.CircleMarkRationalFrequency.reduced_unique
  PrimeFactors.CircleMarkRationalFrequency.in_rect from PrimeFactors.CircleMarkRationalFrequency

open CircleMarkRationalFrequency (point in_rect clear_point reduced_unique local_point)

private theorem cross_small {a b c d q : ℕ} (left : a^2+b^2<q) (right : c^2+d^2<q) :
    a*d+c*b<q := by
  have cs : (a*d+c*b)^2≤(a^2+b^2)*(c^2+d^2) := by
    exact_mod_cast (show ((a:ℤ)*d+c*b)^2≤((a:ℤ)^2+b^2)*((c:ℤ)^2+d^2) by
      nlinarith only [sq_nonneg ((a:ℤ)*c-b*d)])
  have bound := (Nat.mul_le_mul_right (c^2+d^2) left.le).trans_lt
    (Nat.mul_lt_mul_of_pos_left right (by omega))
  exact Nat.mul_self_lt_mul_self_iff.mp (by simpa only [sq] using cs.trans_lt bound)

private theorem disk_inj {q : ℕ} [Fact q.Prime] {z w : ℕ×ℕ}
    (zp : 0<z.1) (wp : 0<w.2) (zc : z.1.Coprime z.2) (wc : w.1.Coprime w.2)
    (zd : z.2.Coprime q) (wd : w.2.Coprime q)
    (zs : z.1^2+z.2^2<q) (ws : w.1^2+w.2^2<q)
    (eqn : (point q z)^2=(point q w)^2) : z=w := by
  have cross : ((z.1*w.2 : ℕ):ZMod q)^2=((w.1*z.2 : ℕ):ZMod q)^2 := by
    rw [Nat.cast_mul,Nat.cast_mul,←clear_point z zd,←clear_point w wd]
    simp only [mul_pow]
    linear_combination (z.2:ZMod q)^2*(w.2:ZMod q)^2*eqn
  have short := cross_small zs ws
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp cross with same|opp
  · have ordinary := congrArg ZMod.val same
    rw [ZMod.val_natCast_of_lt (by omega : z.1*w.2<q),
      ZMod.val_natCast_of_lt (by omega : w.1*z.2<q)] at ordinary
    exact reduced_unique zc wc zp ordinary
  · have zero : ((z.1*w.2+w.1*z.2:ℕ):ZMod q)=0 := by
      rw [Nat.cast_add,opp,neg_add_cancel]
    have pos := Nat.mul_pos zp wp
    have bad := congrArg ZMod.val zero
    rw [ZMod.val_natCast_of_lt short,ZMod.val_zero] at bad
    omega

/-- Each reduced positive fraction inside the open disk contributes a different
nonzero square to the product-selected grid, even if the full grid has collisions. -/
theorem disk_count {n q h : ℕ} [NeZero n] [Fact q.Prime] (dv : q∣n)
    (S : Finset (ℕ×ℕ)) (sub : S⊆rectangle h h)
    (shape : ∀z∈S,z.1^2+z.2^2<q) (units : ∀z∈rectangle h h,z.2.Coprime n) :
    (S.filter fun z=>z.1.Coprime z.2).card ≤ (covered q (menu n h h)).card := by
  classical
  apply card_le_card_of_injOn (fun z => (point q z)^2)
  · intro z hz
    obtain ⟨zm,_⟩ := mem_filter.mp hz
    have u := units z (sub zm)
    obtain ⟨⟨zp,_⟩,_⟩ := in_rect.mp (sub zm)
    have lo : z.1≤z.1^2 := by simpa only [sq] using Nat.le_mul_of_pos_right z.1 zp
    have norm := shape z zm
    apply mem_erase.mpr
    refine ⟨?_,mem_image.mpr ⟨(point n z).val,mem_image.mpr ⟨z,sub zm,rfl⟩,?_⟩⟩
    · intro zero
      have bad := clear_point z (u.of_dvd_right dv)
      rw [sq_eq_zero_iff.mp zero,zero_mul] at bad
      have val := congrArg ZMod.val bad
      rw [ZMod.val_zero,ZMod.val_natCast_of_lt (by omega : z.1<q)] at val
      omega
    · rw [local_point dv z u]
  · intro z hz w hw eqn
    obtain ⟨zm,zc⟩ := mem_filter.mp hz
    obtain ⟨wm,wc⟩ := mem_filter.mp hw
    exact disk_inj (in_rect.mp (sub zm)).1.1 (in_rect.mp (sub wm)).2.1 zc wc
      ((units z (sub zm)).of_dvd_right dv) ((units w (sub wm)).of_dvd_right dv)
      (shape z zm) (shape w wm) eqn

end PrimeFactors.CircleMarkRationalDisk
