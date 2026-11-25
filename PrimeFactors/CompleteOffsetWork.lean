import PrimeFactors.CompleteOffsetSearch
import PrimeFactors.FareyWork
import Mathlib.Algebra.BigOperators.Intervals

namespace PrimeFactors.CompleteOffsetWork
open Finset FareyWork

def height (h : ℕ) := (4*h/3).sqrt

/-- Twice the enclosing rectangle area always exceeds the integer square root
of the product. The case h = 2 attains the weaker small-height ratio h = 2J². -/
theorem rectangle_threshold {T h : ℕ} (hp : 0<h) :
    let J := height h
    T < 2*J*(T*J/h+1) := by
  intro J
  have jp : 1≤J := Nat.le_sqrt'.mpr ((Nat.le_div_iff_mul_le (by decide : 0<3)).mpr (by omega))
  have upper : 4*h<(J+1)^2*3 := (Nat.div_lt_iff_lt_mul (by decide : 0<3)).mp (Nat.lt_succ_sqrt' _)
  have fit : h ≤ 2*J^2 := by
    by_cases one : J=1
    · rw [one] at upper ⊢
      omega
    · obtain ⟨a,ha⟩ := Nat.exists_eq_add_of_le (show 2≤J by omega)
      rw [ha] at upper ⊢
      nlinarith only [upper,Nat.zero_le (a*a),Nat.zero_le a]
  have roundUp : T*J < (T*J/h+1)*h :=
    (Nat.div_lt_iff_lt_mul hp).mp (Nat.lt_succ_self _)
  apply (Nat.mul_lt_mul_right hp).mp
  calc T*h ≤ T*(2*J^2) := Nat.mul_le_mul_left T fit
       _ = 2*J*(T*J) := by ring
       _ < 2*J*((T*J/h+1)*h) := Nat.mul_lt_mul_of_pos_left roundUp (by omega)
       _ = _ := by ring

noncomputable def rawSlots (T h : ℕ) : Finset (ℕ × ℕ) :=
  (Icc 1 (height h)).biUnion fun j => (Icc 1 (T*j/h+1)).image (Prod.mk j)

noncomputable def slots (T h : ℕ) : Finset (ℕ × ℕ) := (rawSlots T h).filter fun x => x.1.Coprime x.2

theorem mem_slots {T h j k : ℕ} : (j,k) ∈ slots T h ↔
    (1≤j ∧ j≤height h) ∧ (1≤k ∧ k≤T*j/h+1) ∧ j.Coprime k := by
  constructor
  · intro hx
    obtain ⟨raw,cop⟩ := mem_filter.mp hx
    obtain ⟨a,ha,point⟩ := mem_biUnion.mp raw
    obtain ⟨b,hb,eq⟩ := mem_image.mp point
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj eq
    exact ⟨mem_Icc.mp ha,mem_Icc.mp hb,cop⟩
  · rintro ⟨hj,hk,cop⟩
    exact mem_filter.mpr ⟨mem_biUnion.mpr ⟨j,mem_Icc.mpr hj,mem_image.mpr ⟨k,mem_Icc.mpr hk,rfl⟩⟩,cop⟩

/-- The counted set is exactly the reduced-form theorem's sharp primitive schedule. -/
theorem sharp_iff {T h j k : ℕ} : (j,k) ∈ slots T h ↔
    3*j^2≤4*h ∧ CompleteOffsetSearch.InSchedule T h j k := by
  rw [mem_slots, height,Nat.le_sqrt',Nat.le_div_iff_mul_le (by decide : 0<3)]
  unfold CompleteOffsetSearch.InSchedule
  rw [Nat.le_sqrt']
  omega

private theorem parameters {U a b : ℕ} (mem : (a,b) ∈ primitiveOffsets U) :
    0<a ∧ 0<b ∧ a≤b ∧ b≤U ∧ a.Coprime b := by
  obtain ⟨pair,order,cop⟩ := mem_filter.mp mem
  obtain ⟨ha,hb⟩ := mem_product.mp pair
  exact ⟨(mem_Icc.mp ha).1,(mem_Icc.mp hb).1,order,(mem_Icc.mp hb).2,cop⟩

private theorem mass {h : ℕ} (hp : 0<h) : h≤8*(primitiveOffsets (height h)).card := by
  let J := height h
  have jp : 1≤J := Nat.le_sqrt'.mpr ((Nat.le_div_iff_mul_le (by decide : 0<3)).mpr (by omega))
  have upper : 4*h<(J+1)^2*3 := (Nat.div_lt_iff_lt_mul (by decide : 0<3)).mp (Nat.lt_succ_sqrt' _)
  by_cases large : 7≤J
  · have slope : (J+1)^2*3≤4*J^2 := by
      obtain ⟨a,ha⟩ := Nat.exists_eq_add_of_le large
      rw [ha]
      nlinarith only [Nat.zero_le (a*a),Nat.zero_le a]
    have enough : h≤J^2 := by omega
    exact enough.trans (primitive_count J)
  · have finite : ∀ i ∈ List.range 7, 1 ≤ i → (i+1)^2*3 ≤ 32*(primitiveOffsets i).card := by decide +kernel
    have := finite J (List.mem_range.mpr (by omega)) jp
    change h≤8*(primitiveOffsets J).card
    omega

private def pack (w : ℕ × (ℕ × ℕ)) := (w.2.2, w.2.1+w.1*w.2.2)
private def unpack (w : ℕ × ℕ) := ((w.2-1)/w.1, (w.2-1)%w.1+1,w.1)

private theorem unpack_pack {U t a b : ℕ} (h : (a,b) ∈ primitiveOffsets U) :
    unpack (pack (t,a,b))=(t,a,b) := by
  obtain ⟨ap,bp,ab,_,_⟩ := parameters h
  have lt : a-1<b := by omega
  simp [pack,unpack,show a+t*b-1=(a-1)+t*b by omega,Nat.add_mul_div_right _ _ bp,
    Nat.div_eq_of_lt lt,Nat.mod_eq_of_lt lt,Nat.sub_add_cancel ap]

private theorem packed_count {T h : ℕ} (hp : 0<h) :
    T/h*(primitiveOffsets (height h)).card ≤ (slots T h).card := by
  let domain := range (T/h) ×ˢ primitiveOffsets (height h)
  have h : domain.card ≤ (slots T h).card := by
    apply card_le_card_of_injOn pack
    · rintro ⟨t,a,b⟩ hx
      obtain ⟨ht,mem⟩ := mem_product.mp hx
      have tr := mem_range.mp ht
      obtain ⟨ap,bp,ab,bh,cop⟩ := parameters mem
      have lim := (Nat.le_div_iff_mul_le hp).mp (show t+1≤T/h by omega)
      have kth : (a+t*b)*h ≤ T*b := calc
        _ ≤ (b+t*b)*h := Nat.mul_le_mul_right h (by omega)
        _ = ((t+1)*h)*b := by ring
        _ ≤ _ := Nat.mul_le_mul_right b lim
      change (b,a+t*b) ∈ slots T h
      apply mem_slots.mpr
      exact ⟨⟨bp,bh⟩,⟨by omega,((Nat.le_div_iff_mul_le hp).mpr kth).trans (by omega)⟩,
        (Nat.coprime_add_mul_right_right b a t).mpr cop.symm⟩
    · rintro ⟨t,a,b⟩ hx ⟨t',a',b'⟩ hy same
      have l := unpack_pack (t:=t) (mem_product.mp hx).2
      have r := unpack_pack (t:=t') (mem_product.mp hy).2
      exact l.symm.trans ((congrArg unpack same).trans r)
  simpa [domain,card_product] using h

private def reflect (z : ℕ × ℕ) : (ℕ × ℕ) × Bool :=
  if z.2=1 ∨ 2*z.1≤z.2 then ((z.2,z.1),false) else ((z.2,z.2-z.1),true)

private def unreflect (w : (ℕ × ℕ) × Bool) : ℕ × ℕ :=
  (if w.2 then w.1.1-w.1.2 else w.1.2,w.1.1)

private theorem unreflect_reflect {U a b : ℕ} (mem : (a,b) ∈ primitiveOffsets U) :
    unreflect (reflect (a,b))=(a,b) := by
  have ab := (parameters mem).2.2.1
  unfold reflect
  split <;> simp [unreflect,Nat.sub_sub_self ab]

private theorem reflection_count {T h : ℕ} (hp : 0<h) (bound : h≤2*T) :
    (primitiveOffsets (height h)).card ≤ 2*(slots T h).card := by
  let target := slots T h ×ˢ (univ : Finset Bool)
  have h : (primitiveOffsets (height h)).card ≤ target.card := by
    apply card_le_card_of_injOn reflect
    · rintro ⟨a,b⟩ mem
      obtain ⟨ap,bp,ab,bh,cop⟩ := parameters mem
      have half (k : ℕ) (lim : 2*k≤b) : k≤T*b/h+1 := by
        have ok : k*h≤T*b := calc
          _ ≤ k*(2*T) := Nat.mul_le_mul_left k bound
          _ = (2*k)*T := by ring
          _ ≤ b*T := Nat.mul_le_mul_right _ lim
          _ = _ := Nat.mul_comm ..
        exact ((Nat.le_div_iff_mul_le hp).mpr ok).trans (by omega)
      unfold reflect
      split
      next low =>
        apply mem_product.mpr
        refine ⟨mem_slots.mpr ⟨⟨bp,bh⟩,⟨ap,?_⟩,cop.symm⟩,mem_univ _⟩
        change a≤T*b/h+1
        change b=1 ∨ 2*a≤b at low
        rcases low with eq|lim
        · have := Nat.zero_le (T*b/h)
          omega
        · exact half _ lim
      next high =>
        change ¬(b=1 ∨ 2*a≤b) at high
        have lt : a<b := by
          rcases eq_or_lt_of_le ab with eq|lt
          · subst b
            exact (high (Or.inl ((Nat.coprime_self a).mp cop))).elim
          · exact lt
        change ((b,b-a),true) ∈ target
        exact mem_product.mpr ⟨mem_slots.mpr ⟨⟨bp,bh⟩,⟨by omega,half _ (by omega)⟩,
          (Nat.coprime_self_sub_right ab).mpr cop.symm⟩,mem_univ _⟩
    · rintro ⟨a,b⟩ hx ⟨a',b'⟩ hy same
      exact (unreflect_reflect hx).symm.trans ((congrArg unreflect same).trans (unreflect_reflect hy))
  simpa [target,card_product,Nat.mul_comm] using h

/-- A full sweep has strictly more than T/16 primitive slots even before a
particular factor pair is specified. Only the floor-root range 0<h≤2T is used. -/
theorem primitive_work {T h : ℕ} (hp : 0<h) (bound : h≤2*T) : T<16*(slots T h).card := by
  have amount := mass hp
  by_cases wide : h≤T
  · let m := T/h
    have mp : 0<m := Nat.div_pos wide hp
    have cost := packed_count (T:=T) hp
    have cap : T<(m+1)*h := by simpa only [Nat.mul_comm h] using Nat.lt_mul_div_succ T hp
    have twice := Nat.mul_le_mul_right h (show m+1≤2*m by omega)
    have gain := Nat.mul_le_mul_left m amount
    change m*(primitiveOffsets (height h)).card≤(slots T h).card at cost
    nlinarith only [cap,twice,gain,cost]
  · have cost := reflection_count hp bound
    omega

private theorem row_sum (J T h : ℕ) :
    2*h*(∑ j ∈ Icc 1 J, T*j/h)≤T*J*(J+1) := by
  induction J with
  | zero => simp
  | succ J ih =>
    have step : Icc 1 (J+1)=insert (J+1) (Icc 1 J) := by
      ext x
      simp only [mem_Icc,mem_insert]
      omega
    have absent : J+1 ∉ Icc 1 J := by simp
    rw [step,sum_insert absent]
    have next := Nat.mul_div_le (T*(J+1)) h
    nlinarith only [ih,next]

/-- Even before removing nonprimitive choices the complete schedule has at
most 2T slots. This is a candidate count and does not price individual tests. -/
theorem raw_work {T h : ℕ} (hp : 0<h) (bound : h≤2*T) : (rawSlots T h).card≤2*T := by
  let J := height h
  have total : (rawSlots T h).card ≤ ∑ j ∈ Icc 1 J, (T*j/h+1) := by
    apply card_biUnion_le.trans (sum_le_sum _)
    intro j _
    exact card_image_le.trans_eq (by rw [Nat.card_Icc, Nat.add_sub_cancel])
  rw [sum_add_distrib] at total
  simp only [sum_const,nsmul_eq_mul,mul_one,Nat.card_Icc,Nat.add_sub_cancel] at total
  have square : J^2*3≤4*h := (Nat.le_div_iff_mul_le (by decide : 0<3)).mp (Nat.sqrt_le' _)
  have jj : J*(J+1)≤2*h := by
    rcases lt_or_ge J 2 with small|large
    · interval_cases J <;> omega
    · have scale := Nat.mul_le_mul_right J large
      nlinarith only [square,scale]
  have bounded : J≤T := by
    apply le_of_not_gt
    intro bad
    have too := Nat.pow_le_pow_left (show T+1≤J from bad) 2
    nlinarith only [too,square,bound,Nat.le_mul_self T]
  have sum_bound := row_sum J T h
  have weighted := Nat.mul_le_mul_left T jj
  have below : (∑ j ∈ Icc 1 J, T*j/h)≤T := by
    apply Nat.le_of_mul_le_mul_left (c:=2*h) _ (by positivity)
    nlinarith only [sum_bound,weighted]
  change (rawSlots T h).card ≤ (∑ j ∈ Icc 1 J, T*j/h) + J at total
  exact total.trans ((Nat.add_le_add below bounded).trans_eq (by omega))

/-- A 2,048-bit nonsquare needs more than 2^1019 distinct primitive slots
for this complete schedule, independently of finding an earlier factor. -/
theorem target_work {N : ℕ} (size : 2^2047≤N) (nonsquare : N.sqrt^2<N) :
    2^1019 < (slots N.sqrt (N-N.sqrt^2)).card := by
  let T := N.sqrt
  let h := N-T^2
  have hp : 0<h := Nat.sub_pos_of_lt nonsquare
  have full : h+T^2=N := Nat.sub_add_cancel nonsquare.le
  have next : N<(T+1)^2 := Nat.lt_succ_sqrt' _
  have bound : h≤2*T := by nlinarith only [full,next]
  have floor : 2^1023≤T := Nat.le_sqrt'.mpr ((show ((2:ℕ)^1023)^2≤2^2047 by decide +kernel).trans size)
  have cost := primitive_work hp bound
  have scale : 16*(2:ℕ)^1019=2^1023 := by decide +kernel
  change 2^1019<(slots T h).card
  omega

end PrimeFactors.CompleteOffsetWork
