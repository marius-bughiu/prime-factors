import PrimeFactors.CircleMarkMaskDigitReadout
import PrimeFactors.CircleMarkSharedScores

/-! A block coordinate deliberately supplies the evaluation point for an
offset mask. Opposite parity excludes repeated coordinates. A vanishing
score identifies the row containing the unique complementary offset, and
the gcd of the mask value in that row already equals the smaller prime. -/
namespace PrimeFactors.CircleMarkDirectedDigitQueries

open Finset Polynomial CircleMarkDigitCoordinates CircleMarkMaskDigitReadout
open CircleMarkJacobiMask CircleMarkMidcutReadout CircleMarkSharedScores
open scoped Classical
open private PrimeFactors.CircleMarkDigitCoordinates.block_mem
  PrimeFactors.CircleMarkDigitCoordinates.offset_mem from PrimeFactors.CircleMarkDigitCoordinates
open CircleMarkDigitCoordinates (block_mem offset_mem)

noncomputable abbrev rows (n : ℕ) := blocks (cutoff n) (base n) (range (base n))
noncomputable abbrev columns (n : ℕ) (I : Finset ℕ) := offsets (cutoff n) I

/-- The sample is the chosen block coordinate squared modulo the input. -/
noncomputable def rowScore (n : ℕ) [NeZero n] (I : Finset ℕ) (x : ℕ) : ℤ :=
  score n (columns n I) ((x^2 : ℕ) : ZMod n)

noncomputable def rowGcd (n : ℕ) (I : Finset ℕ) (x : ℕ) : ℕ :=
  (((squareMask (columns n I)).eval ((x : ℤ)^2)).natAbs).gcd n

private theorem geometry {p q x : ℕ} [Fact p.Prime] [Fact q.Prime]
    (order : p<q) (bal : q<2*p) (op : p≠2) (oq : q≠2)
    (row : x ∈ rows (p*q)) (I : Finset ℕ) :
    (0<x ∧ x<p) ∧ ∀y∈columns (p*q) I, y<p ∧ x≠y ∧ x+y<q := by
  obtain ⟨low,_,hi⟩ := CircleMarkJacobiMaskEdge.bounds order bal op oq
  obtain ⟨j,_,short,eqn⟩ := block_mem row
  refine ⟨by omega,?_⟩
  intro y hy
  obtain ⟨i,_,_,off⟩ := offset_mem hy
  omega

private theorem dvd_value {r x : ℕ} [Fact r.Prime] (C : Finset ℕ) :
    r ∣ ((squareMask C).eval ((x : ℤ)^2)).natAbs ↔
      ∃y∈C, (x:ZMod r)^2=(y:ZMod r)^2 := by
  rw [←Int.natCast_dvd,←ZMod.intCast_zmod_eq_zero_iff_dvd]
  simp only [squareMask,eval_prod,eval_sub,eval_X,eval_C,Int.cast_prod,Int.cast_sub,Int.cast_pow,
    Int.cast_natCast,prod_eq_zero_iff,sub_eq_zero]

/-- One public gcd per row. The larger prime never divides the value,
and the smaller prime divides it exactly when a complementary offset exists. -/
theorem gcd_eq {p q x : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (order : p<q) (bal : q<2*p) (op : p≠2) (oq : q≠2)
    (row : x ∈ rows (p*q)) (I : Finset ℕ) :
    rowGcd (p*q) I x = if ∃y∈columns (p*q) I, x+y=p then p else 1 := by
  let C := columns (p*q) I
  let v := ((squareMask C).eval ((x : ℤ)^2)).natAbs
  obtain ⟨⟨pos,xp⟩,safe⟩ := geometry order bal op oq row I
  have atP : p∣v ↔ ∃y∈C, x+y=p := by
    rw [dvd_value]
    apply exists_congr
    intro y
    apply and_congr_right
    intro hy
    obtain ⟨yp,ne,_⟩ := safe y hy
    rw [CircleMarkSparseMaskProbe.square_eq pos xp yp,or_iff_right ne]
  have atQ : ¬q∣v := by
    rintro h
    obtain ⟨y,hy,eqn⟩ := (dvd_value C).mp h
    obtain ⟨yp,ne,short⟩ := safe y hy
    exact ((CircleMarkSparseMaskProbe.square_eq pos (xp.trans order) (yp.trans order)).mp eqn).elim ne short.ne
  change v.gcd (p*q) = if ∃y∈C, x+y=p then p else 1
  split_ifs with hit
  · exact NormBatchGCD.one_batch hq.out (atP.mpr hit) atQ
  · exact Nat.coprime_mul_iff_right.mpr
      ⟨(hp.out.coprime_iff_not_dvd.mpr (fun h => hit (atP.mp h))).symm,
        (hq.out.coprime_iff_not_dvd.mpr atQ).symm⟩

/-- A deliberately sampled square has score zero on a matching row and one elsewhere. -/
theorem score_eq {p q x : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (order : p<q) (bal : q<2*p) (op : p≠2) (oq : q≠2)
    (row : x ∈ rows (p*q)) (I : Finset ℕ) :
    rowScore (p*q) I x = if ∃y∈columns (p*q) I, x+y=p then 0 else 1 := by
  obtain ⟨⟨pos,xp⟩,_⟩ := geometry order bal op oq row I
  have bound : x^2 < p*q := by
    rw [sq]
    exact Nat.mul_lt_mul_of_lt_of_le xp (xp.trans order).le (by omega)
  have cop : x.Coprime (p*q) :=
    Nat.coprime_mul_iff_right.mpr
      ⟨(hp.out.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt pos xp)).symm,
       (hq.out.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt pos (xp.trans order))).symm⟩
  rw [rowScore,CircleMarkSharedScores.score_eq,ZMod.val_natCast_of_lt bound,Nat.cast_pow]
  have one : jacobiSym ((x:ℤ)^2) (p*q)=1 := jacobiSym.sq_one' (by simpa using cop.gcd_eq_one)
  have gr := gcd_eq order bal op oq row I
  change rowGcd (p*q) I x = _ at gr
  change (if rowGcd (p*q) I x=1 then jacobiSym ((x:ℤ)^2) (p*q) else 0) = _
  rw [gr,one]
  split_ifs <;> simp_all [hp.out.ne_one]

private theorem full_pair {p q : ℕ} [hp : Fact p.Prime] [Fact q.Prime]
    (order : p<q) (bal : q<2*p) (op : p≠2) (oq : q≠2) :
    ∃! z : ℕ×ℕ, z.1 ∈ rows (p*q) ∧ z.2 ∈ columns (p*q) (range (base (p*q))) ∧ z.1+z.2=p := by
  let k := cutoff (p*q)
  let m := base (p*q)
  let s := (2*k+1-p)/2
  obtain ⟨lo,hi,_⟩ := CircleMarkJacobiMaskEdge.bounds order bal op oq
  obtain ⟨code,jl,il⟩ := digits lo hi (hp.out.odd_of_ne_two op)
  change p+2*s=2*k+1 at code
  change s/m<m at jl
  change s%m<m at il
  change k+1<p at lo
  have recombine : s%m+m*(s/m)=s := Nat.mod_add_div ..
  have blockBound : 2*(m*(s/m))<k := by omega
  have offBound : 2*(s%m)<k+1 := by omega
  let x := k-2*(m*(s/m))
  let y := k+1-2*(s%m)
  refine ⟨(x,y),⟨mem_image.mpr ⟨s/m,mem_filter.mpr ⟨mem_range.mpr jl,blockBound⟩,rfl⟩,
    mem_image.mpr ⟨s%m,mem_filter.mpr ⟨mem_range.mpr il,offBound⟩,rfl⟩,?_⟩,?_⟩
  · change x+y=p
    dsimp only [x,y]
    omega
  · rintro ⟨x',y'⟩ ⟨xb,yo,sum⟩
    obtain ⟨j,_,_,ex⟩ := block_mem xb
    obtain ⟨i,inside,_,ey⟩ := offset_mem yo
    change x'+2*(m*j)=k at ex
    change y'+2*i=k+1 at ey
    change x'+y'=p at sum
    have small : i<m := mem_range.mp inside
    have pos : 0<m := Nat.succ_pos _
    have digits : s=i+m*j := by omega
    have qd : s/m=j := by rw [digits,Nat.add_mul_div_left _ _ pos,Nat.div_eq_of_lt small,zero_add]
    have rd : s%m=i := by rw [digits,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt small]
    apply Prod.ext
    · change x'=k-2*(m*(s/m))
      rw [qd]
      omega
    · change y'=k+1-2*(s%m)
      rw [rd]
      omega

/-- With both public index sets full, exactly one row gives zero. The matching
offset is unique there, and that row's gcd yields p directly. -/
theorem unique_hit {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (order : p<q) (bal : q<2*p) (op : p≠2) (oq : q≠2) :
    let I := range (base (p*q))
    ∃! x, x ∈ rows (p*q) ∧ rowScore (p*q) I x=0 := by
  let I := range (base (p*q))
  obtain ⟨⟨x,y⟩,⟨xb,yo,hxy⟩,uniq⟩ := full_pair order bal op oq
  refine ⟨x,⟨xb,?_⟩,?_⟩
  · rw [score_eq order bal op oq xb,if_pos ⟨y,yo,hxy⟩]
  · rintro x' ⟨xb',hit⟩
    rw [score_eq order bal op oq xb'] at hit
    split_ifs at hit with pair
    · obtain ⟨y',yo',sum⟩ := pair
      exact congrArg Prod.fst (uniq (x',y') ⟨xb',yo',sum⟩)
    · contradiction

theorem hit_offset {p q x : ℕ} [Fact p.Prime] [Fact q.Prime]
    (order : p<q) (bal : q<2*p) (op : p≠2) (oq : q≠2)
    (row : x ∈ rows (p*q)) (I : Finset ℕ) (hit : rowScore (p*q) I x=0) :
    (∃! y, y∈columns (p*q) I ∧ x+y=p) ∧ rowGcd (p*q) I x=p := by
  rw [score_eq order bal op oq row] at hit
  split_ifs at hit with pair
  · obtain ⟨y,yo,sum⟩ := pair
    exact ⟨⟨y,⟨yo,sum⟩,fun z h => by omega⟩,
      (gcd_eq order bal op oq row I).trans (if_pos ⟨y,yo,sum⟩)⟩
  · contradiction

/-- The direct evaluation uses at most m row probes, each with at most m
linear factors. This counts scalar root terms for the specified evaluation. -/
theorem work (n : ℕ) :
    (rows n).card ≤ base n ∧ (columns n (range (base n))).card ≤ base n ∧
      (rows n).card*(columns n (range (base n))).card ≤ (base n)^2 := by
  have a : (rows n).card ≤ base n := card_image_le.trans ((card_filter_le ..).trans_eq (card_range _))
  have b : (columns n (range (base n))).card ≤ base n :=
    card_image_le.trans ((card_filter_le ..).trans_eq (card_range _))
  exact ⟨a,b,(Nat.mul_le_mul a b).trans_eq (sq _).symm⟩

/-- At two 1024-bit primes these coarse counts are bounded by 2⁵¹² rows
and 2¹⁰²⁴ scalar root terms in total. -/
theorem full_width {p q : ℕ} (order : p<q) (upper : q<2^1024) :
    (rows (p*q)).card ≤ 2^512 ∧ (columns (p*q) (range (base (p*q)))).card ≤ 2^512 ∧
      (rows (p*q)).card*(columns (p*q) (range (base (p*q)))).card ≤ 2^1024 := by
  obtain ⟨a,b,total⟩ := work (p*q)
  have size := full_dimensions order upper
  exact ⟨a.trans size,b.trans size,total.trans ((Nat.pow_le_pow_left size 2).trans_eq
    (show ((2:ℕ)^512)^2=2^1024 by rw [←pow_mul]))⟩

end PrimeFactors.CircleMarkDirectedDigitQueries
