import PrimeFactors.PrimeSquareSumWeights

/-! Multiplicity of the sum of a known local pair modulo an odd prime
power, determined by the divisibility of its difference. -/

open private PrimeFactors.two_unit from PrimeFactors.PrimePowerCount

namespace PrimeFactors.PrimePowerPairWeight

open PrimeSquareSumWeights
open scoped Classical

/-- In the multiples of d, prescribe the quotient modulo k. Each eligible
residue of that quotient occurs l times in the interval of length d*k*l. -/
private theorem scaled_fiber {m k : ℕ} [NeZero m] [NeZero k] (d l : ℕ)
    (pos : 0<d) (size : m=d*(k*l)) (P : ZMod k → Prop) :
    Nat.card {s : ZMod m // d∣s.val ∧ P ((s.val/d : ℕ) : ZMod k)} =
      Nat.card {z : ZMod k // P z}*l := by
  let encode (r : ZMod k) (j : Fin l) := d*(r.val+k*j.val)
  have small (r : ZMod k) (j : Fin l) : encode r j<m := by
    rw [size]
    apply Nat.mul_lt_mul_of_pos_left _ pos
    calc
      r.val+k*j.val < k*(j.val+1) := by rw [Nat.mul_succ]; have := r.val_lt; omega
      _ ≤ k*l := Nat.mul_le_mul_left _ j.isLt
  let f (z : {r : ZMod k // P r} × Fin l) :
      {s : ZMod m // d∣s.val ∧ P ((s.val/d : ℕ) : ZMod k)} :=
    ⟨(encode z.1.val z.2 : ℕ),by
      rw [ZMod.val_natCast_of_lt (small ..)]
      refine ⟨dvd_mul_right _ _,?_⟩
      simp only [encode,Nat.mul_div_cancel_left _ pos,Nat.cast_add,Nat.cast_mul,
        ZMod.natCast_self,zero_mul,add_zero,ZMod.natCast_zmod_val]
      exact z.1.property⟩
  have inj : Function.Injective f := by
    rintro ⟨⟨r,hr⟩,i⟩ ⟨⟨s,hs⟩,j⟩ eq
    have h := congrArg (fun a => a.val.val) eq
    change ((encode r i : ℕ) : ZMod m).val=((encode s j : ℕ) : ZMod m).val at h
    rw [ZMod.val_natCast_of_lt (small ..),ZMod.val_natCast_of_lt (small ..)] at h
    have h' := Nat.mul_left_cancel pos h
    have modEq := congrArg (fun z => z%k) h'
    change (r.val+k*i.val)%k=(s.val+k*j.val)%k at modEq
    simp only [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt r.val_lt,Nat.mod_eq_of_lt s.val_lt] at modEq
    obtain rfl : r=s := ZMod.val_injective _ modEq
    exact Prod.ext rfl (Fin.ext (Nat.mul_left_cancel (NeZero.pos k) (Nat.add_left_cancel h')))
  have onto : Function.Surjective f := by
    rintro ⟨s,hd,hp⟩
    let v := s.val/d
    have rep : d*v=s.val := (Nat.mul_comm d v).trans (Nat.div_mul_cancel hd)
    have lt : v<k*l := by
      apply Nat.lt_of_mul_lt_mul_left (a:=d)
      rw [rep,←size]; exact s.val_lt
    let j : Fin l := ⟨v/k,(Nat.div_lt_iff_lt_mul (NeZero.pos k)).mpr (by simpa [Nat.mul_comm] using lt)⟩
    refine ⟨(⟨(v : ZMod k),hp⟩,j),Subtype.ext ?_⟩
    change ((d*((v : ZMod k).val+k*(v/k)) : ℕ) : ZMod m)=s
    rw [ZMod.val_natCast,Nat.mod_add_div,rep,ZMod.natCast_zmod_val]
  rw [←Nat.card_congr (Equiv.ofBijective f ⟨inj,onto⟩),Nat.card_prod]
  simp

variable {p : ℕ} [Fact p.Prime]

/-- Removing 2t powers of p reduces the root equation and leaves t free
digits. This identity includes nonsquares and zero on the reduced side. -/
theorem roots_scaled (e t k u : ℕ) (split : e=2*t+k) :
    Nat.card {s : ZMod (p^e) // s^2=((p^t : ℕ) : ZMod (p^e))^2*(u : ZMod (p^e))} =
      Nat.card {r : ZMod (p^k) // r^2=(u : ZMod (p^k))}*p^t := by
  let d := p^t
  have pd : 0<d := pow_pos (Fact.out : p.Prime).pos _
  have size : p^e=d^2*p^k := by rw [split,pow_add]; dsimp [d]; rw [←pow_mul]; congr 2; omega
  have cancel (w : ℕ) : ((d*w : ℕ) : ZMod (p^e))^2=((d^2*u : ℕ) : ZMod (p^e)) ↔
      (w : ZMod (p^k))^2=(u : ZMod (p^k)) := by
    rw [←Nat.cast_pow,←Nat.cast_pow,mul_pow,ZMod.natCast_eq_natCast_iff,
      ZMod.natCast_eq_natCast_iff,size]
    exact ⟨Nat.ModEq.mul_left_cancel' (pow_ne_zero 2 pd.ne'),fun h => h.mul_left' _⟩
  have same (s : ZMod (p^e)) : s^2=((d^2*u : ℕ) : ZMod (p^e)) ↔
      d∣s.val ∧ ((s.val/d : ℕ) : ZMod (p^k))^2=u := by
    have rep (h : d∣s.val) : ((d*(s.val/d) : ℕ) : ZMod (p^e))=s := by
      rw [Nat.mul_comm d,Nat.div_mul_cancel h,ZMod.natCast_zmod_val]
    constructor
    · intro h
      have con : s.val^2 ≡ d^2*u [MOD p^e] := (ZMod.natCast_eq_natCast_iff ..).mp (by
        rw [Nat.cast_pow,ZMod.natCast_zmod_val]; exact h)
      have hd := (Nat.pow_dvd_pow_iff (by decide : 2≠0)).mp
        ((con.dvd_iff (size ▸ dvd_mul_right _ _)).mpr (dvd_mul_right _ _))
      exact ⟨hd,(cancel _).mp (by rw [rep hd]; exact h)⟩
    · rintro ⟨hd,h⟩
      exact (rep hd) ▸ (cancel _).mpr h
  change Nat.card {s : ZMod (p^e) // s^2=(d : ZMod (p^e))^2*(u : ZMod (p^e))}=_
  rw [←Nat.cast_pow,←Nat.cast_mul,Nat.card_congr (Equiv.subtypeEquivRight same)]
  exact scaled_fiber d d pd (by rw [size]; ring) (fun s : ZMod (p^k) => s^2=u)

private theorem zero_iff (e v : ℕ) :
    p^e∣v^2 ↔ p^((e+1)/2)∣v := by
  by_cases h : v=0
  · simp [h]
  · have prime := (Fact.out : p.Prime)
    rw [prime.pow_dvd_iff_le_factorization (pow_ne_zero 2 h),
      prime.pow_dvd_iff_le_factorization h,Nat.factorization_pow]
    simp only [Finsupp.coe_smul,Pi.smul_apply,smul_eq_mul]
    omega

/-- The roots of zero are exactly the multiples of p^ceil(e/2). -/
theorem roots_zero (e : ℕ) : Nat.card {s : ZMod (p^e) // s^2=0}=p^(e/2) := by
  let d := p^((e+1)/2)
  have pos : 0<d := pow_pos (Fact.out : p.Prime).pos _
  have exactSize : p^e=d*(1*p^(e/2)) := by
    rw [one_mul,←pow_add]; congr 1; omega
  have equiv (s : ZMod (p^e)) : s^2=0 ↔
      d∣s.val ∧ (fun _ : ZMod 1 => True) ((s.val/d : ℕ) : ZMod 1) := by
    rw [and_true,←zero_iff,←ZMod.natCast_zmod_eq_zero_iff_dvd,Nat.cast_pow,ZMod.natCast_zmod_val]
  rw [Nat.card_congr (Equiv.subtypeEquivRight equiv),scaled_fiber _ _ pos exactSize (fun _ : ZMod 1 => True)]
  simp

private theorem weight_as_roots {e n : ℕ} (odd : p≠2) {x y : ZMod (p^e)}
    (prod : x*y=(n : ZMod (p^e))) :
    weight n (x+y)=Nat.card {s : ZMod (p^e) // s^2=(x-y)^2} := by
  rw [weight_roots (PrimeFactors.two_unit odd e),←prod,show (x+y)^2-4*(x*y)=(x-y)^2 by ring]

/-- An exact p-adic order t of the known difference gives two roots after
removing p^(2t). Each root admits p^t lifts. -/
theorem weight_of_exact {e n t u : ℕ} (odd : p≠2) {x y : ZMod (p^e)}
    (prod : x*y=(n : ZMod (p^e))) (diff : x-y=((p^t*u : ℕ) : ZMod (p^e)))
    (unit : ¬p∣u) (small : 2*t<e) : weight n (x+y)=2*p^t := by
  let k := e-(2*t+1)
  have split : e=2*t+(k+1) := by dsimp [k]; omega
  rw [weight_as_roots odd prod,diff,Nat.cast_mul,mul_pow,←Nat.cast_pow u 2,
    roots_scaled (p:=p) e t (k+1) (u^2) split]
  have z : (u : ZMod p)≠0 := (ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mp.mt unit
  have nz : (((u:ℤ)^2 : ℤ) : ZMod p)≠0 := by push_cast; exact pow_ne_zero _ z
  have sq : IsSquare (((u:ℤ)^2 : ℤ) : ZMod p) := by push_cast; exact ⟨_,pow_two _⟩
  have count := (primitiveNorm_odd_root_count odd ((u:ℤ)^2) nz k).trans (if_pos sq)
  push_cast at count ⊢
  rw [count]

/-- The exact-order formula directly in terms of two divisibility tests
on the least nonnegative representative of the observed difference. -/
theorem weight_of_shell {e n t : ℕ} (odd : p≠2) {x y : ZMod (p^e)}
    (prod : x*y=(n : ZMod (p^e))) (hit : p^t∣(x-y).val)
    (miss : ¬p^(t+1)∣(x-y).val) (small : 2*t<e) : weight n (x+y)=2*p^t := by
  obtain ⟨u,h⟩ := hit
  apply weight_of_exact (u:=u) odd prod
  · rw [←h,ZMod.natCast_zmod_val]
  · rintro ⟨v,rfl⟩
    exact miss ⟨v,by rw [h,pow_succ,mul_assoc]⟩
  · exact small

/-- Beyond the halfway valuation threshold the squared difference is zero.
The boundary, including equal residues, contributes exactly p^floor(e/2). -/
theorem weight_of_deep {e n : ℕ} (odd : p≠2) {x y : ZMod (p^e)}
    (prod : x*y=(n : ZMod (p^e))) (deep : p^((e+1)/2)∣(x-y).val) :
    weight n (x+y)=p^(e/2) := by
  have zero := (ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mpr ((zero_iff _ _).mpr deep)
  rw [Nat.cast_pow,ZMod.natCast_zmod_val] at zero
  rw [weight_as_roots odd prod,zero,roots_zero]

/-- The p-adic valuation of the residue representative, capped at e.
The zero residue has capped valuation e. -/
noncomputable def cappedOrder (p e v : ℕ) : ℕ := if v=0 then e else min e (v.factorization p)

/-- Combined local weight formula for every observed pair and exponent.
It applies in particular when the two coordinates are units. -/
theorem weight_of_pair {e n : ℕ} (odd : p≠2) {x y : ZMod (p^e)}
    (prod : x*y=(n : ZMod (p^e))) :
    let t := cappedOrder p e (x-y).val
    weight n (x+y)=if 2*t<e then 2*p^t else p^(e/2) := by
  dsimp only
  by_cases zero : (x-y).val=0
  · rw [cappedOrder,if_pos zero,if_neg (by omega : ¬2*e<e)]
    exact weight_of_deep odd prod (by rw [zero]; exact dvd_zero _)
  · let v := (x-y).val
    let t := min e (v.factorization p)
    have valEq : cappedOrder p e v=t := if_neg zero
    change weight n (x+y)=if 2*cappedOrder p e v<e then 2*p^(cappedOrder p e v) else p^(e/2)
    rw [valEq]
    have prime := (Fact.out : p.Prime)
    have le : t ≤ v.factorization p := min_le_right _ _
    split_ifs with low
    · have eq : t=v.factorization p := by dsimp [t] at *; omega
      apply weight_of_shell odd prod ((prime.pow_dvd_iff_le_factorization zero).mpr le) _ low
      exact fun h => (by omega : ¬t+1≤v.factorization p)
        ((prime.pow_dvd_iff_le_factorization zero).mp h)
    · have deep : (e+1)/2≤v.factorization p := by omega
      exact weight_of_deep odd prod ((prime.pow_dvd_iff_le_factorization zero).mpr deep)

end PrimeFactors.PrimePowerPairWeight
