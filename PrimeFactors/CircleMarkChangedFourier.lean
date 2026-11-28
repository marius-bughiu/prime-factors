import PrimeFactors.CircleMarkSingletonChanges
import PrimeFactors.DivisorSample

/-! The unnormalized discrete Fourier transform of changes caused by the
singleton mask. At unit frequencies the two complete CRT lines cancel and
the remaining phase is exactly the four-square-root trace at half frequency. -/
namespace PrimeFactors.CircleMarkChangedFourier

open Finset CircleMarkSingletonChanges
open scoped Classical
open private PrimeFactors.punctured_character_sum from PrimeFactors.FourierAccess
open PrimeFactors (punctured_character_sum)

noncomputable def wave {n : ℕ} [NeZero n] (k t : ZMod n) : ℂ :=
  ZMod.stdAddChar (-(t*k))

noncomputable def coefficient (n : ℕ) [NeZero n] (k : ZMod n) : ℂ :=
  ZMod.dft (fun t : ZMod n => if t∈changes n then (1:ℂ) else 0) k

noncomputable def rootTrace (n : ℕ) [NeZero n] (s : ZMod n) : ℂ :=
  ∑ w : ZMod n, if w^2=1 then wave s w else 0

private theorem wave_add {n : ℕ} [NeZero n] (k x y : ZMod n) :
    wave k (x+y)=wave k x*wave k y := by
  simp only [wave,add_mul,neg_add,AddChar.map_add_eq_mul]

private theorem at_zero {n : ℕ} [NeZero n] (k : ZMod n) : wave k 0=1 := by
  simp [wave,AddChar.map_zero_eq_one]

private theorem weighted {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (cop : p.Coprime q) (f : ZMod (p*q) → ℂ) :
    let e := ZMod.chineseRemainder cop
    (∑ t : ZMod (p*q), if t∈changes (p*q) then f t else 0) =
      (∑ x : ZMod p, f (e.symm (x,1))) + (∑ y : ZMod q, f (e.symm (1,y)))
      - f 1 - f (e.symm (1,0)) - f (e.symm (0,1)) := by
  let e := ZMod.chineseRemainder cop
  let G (x : ZMod p) (y : ZMod q) := f (e.symm (x,y))
  let R (x : ZMod p) (y : ZMod q) :=
    (if y=1 then G x 1 else 0) + (if x=1 then G 1 y else 0)
    - (if x=1 then if y=1 then G 1 1 else 0 else 0)
    - (if x=1 then if y=0 then G 1 0 else 0 else 0)
    - (if x=0 then if y=1 then G 0 1 else 0 else 0)
  have point (t : ZMod (p*q)) : (if t∈changes (p*q) then f t else 0)=R (e t).1 (e t).2 := by
    have eqn : e t = (t.val : ℕ) := by rw [←map_natCast e,ZMod.natCast_zmod_val]
    have membership : t∈changes (p*q) ↔ (e t).1≠0 ∧ (e t).2≠0 ∧ ((e t).1=1 ∨ (e t).2=1) := by
      rw [eqn]; exact mem_changes t
    have ft : f t=G (e t).1 (e t).2 := by simp [G]
    rw [if_congr membership rfl rfl,ft]
    dsimp only [R]
    by_cases a : (e t).1=0 <;> by_cases b : (e t).2=0 <;>
      by_cases c : (e t).1=1 <;> by_cases d : (e t).2=1 <;> simp_all
  rw [Fintype.sum_equiv e.toEquiv _ (fun z => R z.1 z.2) point,Fintype.sum_prod_type]
  simp only [R,sum_add_distrib,sum_sub_distrib,sum_ite_irrel,sum_const_zero,sum_ite_eq',mem_univ,if_true]
  simp [G,e.symm.map_one]
  rfl

private theorem whole {r : ℕ} [Fact r.Prime] (ψ : AddChar (ZMod r) ℂ)
    (inj : Function.Injective ψ) (k : ZMod r) :
    (∑ x : ZMod r, ψ (-(x*k))) = if k=0 then (r:ℂ) else 0 := by
  have h := punctured_character_sum ψ inj k
  have split (x : ZMod r) : ψ (-(x*k)) =
      (if x=0 then 0 else ψ (-(x*k))) + (if x=0 then 1 else 0) := by
    by_cases z : x=0 <;> simp [z,AddChar.map_zero_eq_one]
  calc _ = ∑ x : ZMod r, ((if x=0 then 0 else ψ (-(x*k))) + (if x=0 then 1 else 0)) :=
          sum_congr rfl (fun x _ => split x)
       _ = _ := by rw [sum_add_distrib,h]; simp

private theorem coordinate_waves {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (cop : p.Coprime q) (k : ℕ) :
    let e := ZMod.chineseRemainder cop
    let w := wave (n:=p*q) k
    ((∑ x : ZMod p, w (e.symm (x,1))) = (if p∣k then (p:ℂ) else 0)*w 1) ∧
    ((∑ y : ZMod q, w (e.symm (1,y))) = (if q∣k then (q:ℂ) else 0)*w 1) ∧
    (p∣k → w (e.symm (1,0))=1 ∧ w (e.symm (0,1))=w 1) ∧
    (q∣k → w (e.symm (0,1))=1 ∧ w (e.symm (1,0))=w 1) := by
  let e := ZMod.chineseRemainder cop
  let ψ : AddChar (ZMod (p*q)) ℂ := ZMod.stdAddChar
  let ψp := ψ.compAddMonoidHom (e.symm.toAddMonoidHom.comp (AddMonoidHom.inl (ZMod p) (ZMod q)))
  let ψq := ψ.compAddMonoidHom (e.symm.toAddMonoidHom.comp (AddMonoidHom.inr (ZMod p) (ZMod q)))
  have pinj : Function.Injective ψp := fun _ _ h =>
    congrArg Prod.fst (e.symm.injective (ZMod.injective_stdAddChar h))
  have qinj : Function.Injective ψq := fun _ _ h =>
    congrArg Prod.snd (e.symm.injective (ZMod.injective_stdAddChar h))
  let wp (x : ZMod p) := ψp (-(x*k))
  let wq (y : ZMod q) := ψq (-(y*k))
  have split (x : ZMod p) (y : ZMod q) :
      wave (k : ZMod (p*q)) (e.symm (x,y)) = wp x * wq y := by
    change ψ (-(e.symm (x,y)*k)) = ψ (e.symm (-(x*k),0)) * ψ (e.symm (0,-(y*k)))
    rw [←AddChar.map_add_eq_mul,←map_add]
    apply congrArg ψ
    apply e.injective
    rw [map_neg,map_mul,e.apply_symm_apply,map_natCast,e.apply_symm_apply]
    ext <;> simp
  have one : wave (k : ZMod (p*q)) 1 = wp 1 * wq 1 := by
    simpa only [show e.symm (1,1)=(1:ZMod (p*q)) from map_one e.symm] using split 1 1
  have sumP : (∑ x, wp x) = if p∣k then (p:ℂ) else 0 := by
    simpa only [ZMod.natCast_zmod_eq_zero_iff_dvd] using whole ψp pinj (k:ZMod p)
  have sumQ : (∑ y, wq y) = if q∣k then (q:ℂ) else 0 := by
    simpa only [ZMod.natCast_zmod_eq_zero_iff_dvd] using whole ψq qinj (k:ZMod q)
  have zp (h : p∣k) : wp 1=1 := by simp [wp,(ZMod.natCast_zmod_eq_zero_iff_dvd ..).mpr h,AddChar.map_zero_eq_one]
  have zq (h : q∣k) : wq 1=1 := by simp [wq,(ZMod.natCast_zmod_eq_zero_iff_dvd ..).mpr h,AddChar.map_zero_eq_one]
  have zeroP : wp 0=1 := by simp [wp,AddChar.map_zero_eq_one]
  have zeroQ : wq 0=1 := by simp [wq,AddChar.map_zero_eq_one]
  dsimp only
  simp only [e] at split
  simp only [split,one,←sum_mul,←mul_sum,sumP,sumQ,zeroP,zeroQ,one_mul,mul_one]
  refine ⟨?_,?_,fun h => by simp [zp h],fun h => by simp [zq h]⟩
  · by_cases h : p∣k <;> simp [h,zp]
  · by_cases h : q∣k <;> simp [h,zq,mul_comm]

/-- Two complete lines, with their intersection counted once and both
nonunit mixed idempotents removed. -/
theorem lines {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (cop : p.Coprime q) (k : ℕ) :
    let e := ZMod.chineseRemainder cop
    let w := wave (n:=p*q) k
    coefficient (p*q) k =
      ((if p∣k then (p:ℂ) else 0)+(if q∣k then (q:ℂ) else 0))*w 1
      - w 1 - w (e.symm (1,0)) - w (e.symm (0,1)) := by
  let w := wave (n:=p*q) k
  have dft : coefficient (p*q) k = ∑ t : ZMod (p*q), if t∈changes (p*q) then w t else 0 := by
    simp only [coefficient,ZMod.dft_apply,smul_eq_mul,w,wave,mul_ite,mul_one,mul_zero]
  obtain ⟨a,b,_⟩ := coordinate_waves cop k
  dsimp only
  rw [dft,weighted cop w,a,b,add_mul]

/-- The half-frequency is specified by the odd public modulus alone. -/
noncomputable def halfFrequency (n k : ℕ) : ZMod n := ((n+1)/2*k : ℕ)

private theorem twice {n : ℕ} (odd : Odd n) (k : ℕ) :
    (2:ZMod n)*halfFrequency n k=(k:ZMod n) := by
  have eqn : 2*((n+1)/2)=n+1 := by obtain ⟨a,ha⟩ := odd; omega
  rw [halfFrequency,Nat.cast_mul,←mul_assoc,←Nat.cast_ofNat (R:=ZMod n) (n:=2),
    ←Nat.cast_mul,eqn,Nat.cast_add,Nat.cast_one,ZMod.natCast_self,zero_add,one_mul]

private theorem trace_shift {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (cop : p.Coprime q) (op : p≠2) (oq : q≠2) (k : ℕ) :
    let e := ZMod.chineseRemainder cop
    let s := halfFrequency (p*q) k
    wave s 1 * rootTrace (p*q) s =
      wave (k:ZMod (p*q)) 1 + 1 + wave (k:ZMod (p*q)) (e.symm (1,0)) +
        wave (k:ZMod (p*q)) (e.symm (0,1)) := by
  let e := ZMod.chineseRemainder cop
  let s := halfFrequency (p*q) k
  let h := divisorSampleMixed cop
  have double : (2:ZMod (p*q))*s=k := twice ((hp.out.odd_of_ne_two op).mul (hq.out.odd_of_ne_two oq)) k
  have wp (x : ZMod (p*q)) : wave s (2*x)=wave (k:ZMod (p*q)) x := by
    unfold wave
    congr 2
    rw [←double]
    ring
  have hm : e h=(1,-1) := e.apply_symm_apply _
  have plus : 1+h=2*e.symm (1,0) := by
    apply e.injective
    rw [map_add,map_one,hm,map_mul,map_ofNat,e.apply_symm_apply]
    ext <;> norm_num
  have minus : 1+(-h)=2*e.symm (0,1) := by
    apply e.injective
    rw [map_add,map_one,map_neg,hm,map_mul,map_ofNat,e.apply_symm_apply]
    ext <;> norm_num
  change wave s 1 * rootTrace (p*q) s=_
  rw [rootTrace,divisorSample_four_roots hp.out hq.out cop op oq]
  simp only [mul_add,←wave_add]
  change wave s (1+1)+wave s (1+ -1)+wave s (1+h)+wave s (1+ -h)=_
  rw [plus,minus,wp,wp,add_neg_cancel,at_zero,show (1+1:ZMod (p*q))=2*1 by ring,wp]

/-- The frequency-divisibility contributions and a four-root trace give the
whole coefficient in the same unnormalized convention as mathlib's DFT. -/
theorem coefficient_eq {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (cop : p.Coprime q)
    (op : p≠2) (oq : q≠2) (k : ℕ) :
    let s := halfFrequency (p*q) k
    coefficient (p*q) k =
      ((if p∣k then (p:ℂ) else 0)+(if q∣k then (q:ℂ) else 0))*wave (k:ZMod (p*q)) 1
        +1-wave s 1*rootTrace (p*q) s := by
  dsimp only
  rw [lines cop,trace_shift cop op oq k]
  ring

theorem unit_frequency {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (cop : p.Coprime q)
    (op : p≠2) (oq : q≠2) (k : ℕ) (kp : ¬p∣k) (kq : ¬q∣k) :
    let s := halfFrequency (p*q) k
    coefficient (p*q) k = 1-wave s 1*rootTrace (p*q) s := by
  simpa only [kp,kq,if_false,zero_add,zero_mul] using coefficient_eq cop op oq k

private theorem wave_norm {n : ℕ} [NeZero n] (k t : ZMod n) : ‖wave k t‖=1 := by
  simp [wave,ZMod.stdAddChar_apply]

/-- Converting a supplied trace approximation z to a coefficient reading
preserves its absolute error exactly. -/
theorem unit_error {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (cop : p.Coprime q)
    (op : p≠2) (oq : q≠2) (k : ℕ) (kp : ¬p∣k) (kq : ¬q∣k) (z : ℂ) :
    let s := halfFrequency (p*q) k
    ‖(1-wave s 1*z)-coefficient (p*q) k‖ = ‖z-rootTrace (p*q) s‖ := by
  let s := halfFrequency (p*q) k
  rw [unit_frequency cop op oq k kp kq]
  change ‖(1-wave s 1*z)-(1-wave s 1*rootTrace (p*q) s)‖=_
  rw [show (1-wave s 1*z)-(1-wave s 1*rootTrace (p*q) s)=
    wave s 1*(rootTrace (p*q) s-z) by ring,norm_mul,wave_norm,one_mul,norm_sub_rev]

/-- The exact coefficient reading also returns the trace using the public phase. -/
theorem read_trace {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (cop : p.Coprime q)
    (op : p≠2) (oq : q≠2) (k : ℕ) (kp : ¬p∣k) (kq : ¬q∣k) :
    let s := halfFrequency (p*q) k
    rootTrace (p*q) s = (1-coefficient (p*q) k)/wave s 1 := by
  let s := halfFrequency (p*q) k
  have nz : wave s 1≠0 := fun z => by simpa [z] using wave_norm s 1
  change rootTrace (p*q) s = (1-coefficient (p*q) k)/wave s 1
  rw [eq_div_iff nz,unit_frequency cop op oq k kp kq]
  change rootTrace (p*q) s*wave s 1=1-(1-wave s 1*rootTrace (p*q) s)
  ring

/-- Zero frequency recovers the ordinary unsigned count. -/
theorem zero_frequency {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (cop : p.Coprime q) :
    coefficient (p*q) 0 = (p:ℂ)+q-3 := by
  have h := lines cop 0
  norm_num [wave,AddChar.map_zero_eq_one,sub_sub] at h
  exact h

/-- At a nonzero frequency divisible by just one prime, the indicated
divisor is already accessible as a gcd with the frequency. -/
theorem prime_frequencies {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (cop : p.Coprime q) (k : ℕ) :
    (p∣k → ¬q∣k → coefficient (p*q) k=((p:ℂ)-2)*wave (k:ZMod (p*q)) 1-1) ∧
    (q∣k → ¬p∣k → coefficient (p*q) k=((q:ℂ)-2)*wave (k:ZMod (p*q)) 1-1) := by
  obtain ⟨_,_,a,b⟩ := coordinate_waves cop k
  constructor
  · intro dp dq
    obtain ⟨left,right⟩ := a dp
    rw [lines cop,if_pos dp,if_neg dq,left,right,add_zero]
    ring
  · intro dq dp
    obtain ⟨left,right⟩ := b dq
    rw [lines cop,if_pos dq,if_neg dp,left,right,zero_add]
    ring

end PrimeFactors.CircleMarkChangedFourier
