import PrimeFactors.TwelveResidueCollision

namespace PrimeFactors.TwelveRectangle
open TwelveResidueCollision

set_option maxHeartbeats 900000

/-- Each positive odd offset has this baby representative. -/
def representative (a : ℕ) := if a=3 then 1 else if a=9 then 5 else a

/-- The two exact rational coincidences are polynomial identities, including
after reduction modulo an arbitrary composite. -/
theorem representative_key {R : Type*} [CommRing R] (a : ℕ) :
    num (representative a:R)*den (a:R) = num (a:R)*den (representative a:R) := by
  by_cases h : a=3
  · subst a
    norm_num [representative,num,den,sextic]
  by_cases k : a=9
  · subst a
    norm_num [representative,num,den,sextic]
  simp [representative,h,k]

/-- A signed interval hit is preserved by its representative's raw key. -/
theorem signed_key {R : Type*} [CommRing R] (a : ℕ) {g : R}
    (matchAt : g=(a:R) ∨ g=-(a:R)) :
    num (representative a:R)*den g = num g*den (representative a:R) := by
  rcases matchAt with rfl|rfl
  · exact representative_key _
  · have d : den (-(a:R))=den (a:R) := by unfold den; ring
    have n : num (-(a:R))=num (a:R) := by unfold num sextic; ring
    rw [d,n]
    exact representative_key _

noncomputable def Offset (radius : ℕ) := (Finset.range radius).image (fun i => 2*i+1)

/-- H baby slots cover H+2 distinct positive odd offsets. -/
theorem representative_count {h : ℕ} (enough : 3≤h) :
    ((Offset (h+2)).image representative).card=h := by
  classical
  let s := Offset (h+2)
  have contains (i : ℕ) (hi : i<h+2) : 2*i+1∈s :=
    Finset.mem_image.mpr ⟨i,Finset.mem_range.mpr hi,rfl⟩
  have one : 1∈s := contains 0 (by omega)
  have three : 3∈s := contains 1 (by omega)
  have five : 5∈s := contains 2 (by omega)
  have nine : 9∈s := contains 4 (by omega)
  have eq : s.image representative = (s.erase 3).erase 9 := by
    ext z
    simp only [Finset.mem_image,Finset.mem_erase]
    constructor
    · rintro ⟨x,hx,rfl⟩
      by_cases a : x=3
      · simp_all [representative]
      by_cases b : x=9 <;> simp_all [representative]
    · rintro ⟨h9,h3,hz⟩
      exact ⟨z,hz,by simp [representative,h3,h9]⟩
  have count : s.card=h+2 := by
    unfold s Offset
    rw [Finset.card_image_of_injective _ (by intro a b hab; change 2*a+1=2*b+1 at hab; omega),
      Finset.card_range]
  change (s.image representative).card=_
  rw [eq,Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨by decide,nine⟩),
    Finset.card_erase_of_mem three,count]
  omega

/-- An integer in each row of 2R candidate odd divisors equals the center
plus or minus an odd baby. The first center is L+2R-1. -/
theorem signed_row (L j : ℤ) {R k : ℕ} (hi : k<2*R) :
    ∃ a ∈ Offset R, ((L+2*R-1+4*R*j) - (L+2*(k:ℤ)+4*R*j) = (a:ℤ)) ∨
      ((L+2*R-1+4*R*j) - (L+2*(k:ℤ)+4*R*j) = -(a:ℤ)) := by
  by_cases left : k<R
  · refine ⟨2*(R-1-k)+1, Finset.mem_image.mpr ⟨R-1-k,Finset.mem_range.mpr (by omega),rfl⟩,
      Or.inl ?_⟩
    omega
  · refine ⟨2*(k-R)+1, Finset.mem_image.mpr ⟨k-R,Finset.mem_range.mpr (by omega),rfl⟩,
      Or.inr ?_⟩
    omega

/-- When a candidate equals a prime p, resolving the representative with
the actual signed branches produces p or 2p as an integer witness. -/
theorem represented_comparison (p g : ℤ) (a : ℕ) (hit : g-p=(a:ℤ) ∨ g-p=-(a:ℤ)) :
    let b : ℤ := representative a
    ∃ z ∈ [g-b,g+b,b*g-3,b*g+3,(b-3)*g-(3*b+3),(b-3)*g+(3*b+3)], z=p ∨ z=2*p := by
  by_cases h : a=3
  · subst a
    simp only [representative,if_false,if_true,Nat.cast_one,List.mem_cons,List.not_mem_nil,or_false]
    rcases hit with h|h
    · exact ⟨g-3,by simp,Or.inl (by omega)⟩
    · exact ⟨g+3,by simp,Or.inl (by omega)⟩
  by_cases h' : a=9
  · subst a
    norm_num [representative] at hit ⊢
    omega
  simp [representative,h,h']
  omega

private theorem nonintegral {d t s e : ℤ} (pos : 0<d) (nonzero : e≠0) (small : |e|<d) :
    d*t ≠ s*d+e := by
  obtain ⟨lower,upper⟩ := abs_lt.mp small
  rcases lt_trichotomy t s with lt|eq|gt
  · have h := mul_le_mul_of_nonneg_left (show t≤s-1 by omega) pos.le
    nlinarith
  · subst t
    intro eq
    apply nonzero
    nlinarith
  · have h := mul_le_mul_of_nonneg_left (show s+1≤t by omega) pos.le
    nlinarith

private theorem cast_small {p : ℕ} {z : ℤ} (nonzero : z≠0) (small : |z|<p) :
    (z:ZMod p)≠0 := by
  rw [Ne,ZMod.intCast_zmod_eq_zero_iff_dvd]
  intro divides
  have hd : (p:ℤ)∣|z| := (dvd_abs _ _).mpr divides
  exact (not_lt_of_ge (Int.le_of_dvd (abs_pos.mpr nonzero) hd)) small

private theorem pair_outside {p : ℕ} [Fact p.Prime] {B t d a s e : ℤ}
    (size : (B+3)*|t|+3*B+3 < (p:ℤ))
    (pos : 0<d) (hi : d≤B+3) (anum : |a|≤3*B+3)
    (repr : a=s*d+e) (nz : e≠0) (small : |e|<d) :
    pair (a:ZMod p) (d:ZMod p) (t:ZMod p)≠0 := by
  have bd : |d*t|+|a| < (p:ℤ) := by
    rw [abs_mul,abs_of_pos pos]
    linarith [mul_le_mul_of_nonneg_right hi (abs_nonneg t)]
  have sub : d*t-a≠0 := sub_ne_zero.mpr (repr ▸ nonintegral pos nz small)
  have add : d*t+a≠0 := by
    intro eq
    apply nonintegral (t:= -t) pos nz small
    rw [←repr]
    nlinarith
  have h := mul_ne_zero
    (cast_small sub ((abs_sub (d*t) a).trans_lt bd))
    (cast_small add ((abs_add_le (d*t) a).trans_lt bd))
  simpa [pair] using h

/-- A giant within this distance of any multiple of p can only collide via
the two signed identity branches. The bound is independent of the multiple. -/
theorem near_multiple {p : ℕ} [Fact p.Prime] {B b t k : ℤ} (pbig : 108<p)
    (lo : 16≤b) (hi : b≤B) (size : (B+3)*|t|+3*B+3 < (p:ℤ)) :
    let g : ZMod p := ((k*(p:ℤ)+t:ℤ):ZMod p)
    num (b:ZMod p)*den g = num g*den (b:ZMod p) ↔
      g=(b:ZMod p) ∨ g=-(b:ZMod p) := by
  simp only [Int.cast_add,Int.cast_mul,Int.cast_natCast,ZMod.natCast_self,mul_zero,zero_add]
  have r := @pair_outside p _ B t
  have h₂ := r (d:=b+3) (a:=3*b-3) (s:=3) (e:= -12) size (by omega) (by omega)
    (abs_le.mpr (by omega)) (by ring) (by decide) (abs_lt.mpr (by omega))
  have h₃ := r (d:=b+1) (a:=b-3) (s:=1) (e:= -4) size (by omega) (by omega)
    (abs_le.mpr (by omega)) (by ring) (by decide) (abs_lt.mpr (by omega))
  have h₄ := r (d:=b) (a:= -3) (s:=0) (e:= -3) size (by omega) (by omega)
    (abs_le.mpr (by omega)) (by ring) (by decide) (abs_lt.mpr (by omega))
  have h₅ := r (d:=b-1) (a:= -b-3) (s:= -1) (e:= -4) size (by omega) (by omega)
    (abs_le.mpr (by omega)) (by ring) (by decide) (abs_lt.mpr (by omega))
  have h₆ := r (d:=b-3) (a:= -3*b-3) (s:= -3) (e:= -12) size (by omega) (by omega)
    (abs_le.mpr (by omega)) (by ring) (by decide) (abs_lt.mpr (by omega))
  push_cast at h₂ h₃ h₄ h₅ h₆
  have base : (108:ZMod p)≠0 := by
    exact_mod_cast (show ((108:ℕ):ZMod p)≠0 by
      rw [Ne,ZMod.natCast_zmod_eq_zero_iff_dvd]
      exact Nat.not_dvd_of_pos_of_lt (by decide) pbig)
  rw [←sub_eq_zero,difference]
  simp only [mul_eq_zero,neg_eq_zero,base,h₂,h₃,h₄,h₅,h₆,false_or,or_false]
  simp only [pair,one_mul,mul_eq_zero,sub_eq_zero,add_eq_zero_iff_eq_neg]

/-- Over the rationals the smaller odd offsets have just these two mergers.
The integer cross differences are small enough that the same classification
holds for the eight offsets at every 1024-bit prime. -/
theorem first_eight : ∀ i j : Fin 8,
    let a : ℕ := 2*i.val+1
    let b : ℕ := 2*j.val+1
    let z : ℤ := num (a:ℤ)*den (b:ℤ) - num (b:ℤ)*den (a:ℤ)
    (z=0 ↔ representative a=representative b) ∧ |z|<2^120 := by decide +kernel

/-- The finite rational classification transfers to large prime fields. -/
theorem first_eight_mod {p : ℕ} [Fact p.Prime] (large : 2^120<p) (i j : Fin 8) :
    let a : ℕ := 2*i.val+1
    let b : ℕ := 2*j.val+1
    num (a:ZMod p)*den (b:ZMod p)=num (b:ZMod p)*den (a:ZMod p) ↔
      representative a=representative b := by
  let a : ℕ := 2*i.val+1
  let b : ℕ := 2*j.val+1
  let z : ℤ := num (a:ℤ)*den (b:ℤ)-num (b:ℤ)*den (a:ℤ)
  obtain ⟨classify,bound⟩ := first_eight i j
  change z=0 ↔ representative a=representative b at classify
  change |z|<(2:ℤ)^120 at bound
  have eq : ((z:ℤ):ZMod p) = num (a:ZMod p)*den (b:ZMod p)-num (b:ZMod p)*den (a:ZMod p) := by
    simp [z,num,den,sextic]
  change num (a:ZMod p)*den (b:ZMod p)=num (b:ZMod p)*den (a:ZMod p) ↔ _
  rw [←sub_eq_zero,←eq,←classify]
  refine ⟨fun h => by_contra (fun ne => cast_small ne (bound.trans (by exact_mod_cast large)) h),?_⟩
  intro h
  rw [h,Int.cast_zero]

/-- Above fifteen, if both positive offsets fit the no-wrap bound then a
key equality is ordinary equality. No choice of rational representatives
can merge two unequal keys on this interval. -/
theorem distinct_large_offsets {p : ℕ} [Fact p.Prime] {B a b : ℕ}
    (pbig : 108<p) (large : 16≤b) (positive : 0<a) (ua : a≤B) (ub : b≤B)
    (small : (B+3)*B+3*B+3<p) :
    num (b:ZMod p)*den (a:ZMod p)=num (a:ZMod p)*den (b:ZMod p) ↔ a=b := by
  have bound : ((B:ℤ)+3)*|(a:ℤ)|+3*B+3 < (p:ℤ) := by
    rw [abs_of_nonneg (by positivity)]
    exact_mod_cast (show (B+3)*a+3*B+3<p by
      exact (by gcongr : (B+3)*a+3*B+3≤(B+3)*B+3*B+3).trans_lt small)
  have iff := near_multiple (b:=(b:ℤ)) (t:=(a:ℤ)) (k:=0) pbig (by exact_mod_cast large)
    (by exact_mod_cast ub) bound
  simp only [zero_mul,zero_add,Int.cast_natCast] at iff
  have sum_lt : a+b<p := by nlinarith
  rw [iff]
  constructor
  · rintro (eq|eq)
    · have out := congrArg ZMod.val eq
      simpa [ZMod.val_natCast_of_lt (show a<p by omega),ZMod.val_natCast_of_lt (show b<p by omega)]
        using out
    · have h : ((a+b:ℕ):ZMod p)=0 := by rw [Nat.cast_add,eq,neg_add_cancel]
      exact False.elim ((Nat.not_dvd_of_pos_of_lt (by omega) sum_lt)
        ((ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mp h))
  · rintro rfl
    exact Or.inl rfl

end PrimeFactors.TwelveRectangle
