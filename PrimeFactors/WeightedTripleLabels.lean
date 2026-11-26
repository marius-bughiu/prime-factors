import PrimeFactors.WeightedMultiplierLabels
import PrimeFactors.WeightedTriplePopulation
import PrimeFactors.WeightedTripleReduction
import PrimeFactors.WeightedTripleSupport

/-! An executable square comparison on three nonsquare remainders has
negligible coverage in the balanced 2,048-bit population, even if the
product itself chooses three weights and ranks from the tested menu. -/

namespace PrimeFactors.WeightedTripleLabels
open Finset WeightedMultiplierLabels WeightedMultiplierPopulation WeightedTriplePopulation
set_option exponentiation.threshold 4096
set_option maxRecDepth 4096

def excessAt (n w i : ℕ) : ℕ := (labelAt n w i)^2-4*w*n

def Found (n : ℕ) : Prop :=
  ∃ r∈Icc 1 8, ∃ s∈Icc 1 8, ∃ v∈Icc 1 8, ∃ i<2, ∃ j<2, ∃ k<2,
    let d := excessAt n r i
    let e := excessAt n s j
    let f := excessAt n v k
    d.sqrt^2≠d ∧ e.sqrt^2≠e ∧ f.sqrt^2≠f ∧ (d*e*f).sqrt^2=d*e*f

private theorem nonsquare {d : ℕ} (h : d.sqrt^2≠d) : 0<d ∧ ¬IsSquare d := by
  refine ⟨Nat.pos_of_ne_zero (fun he => h (by simp [he])),?_⟩
  rintro ⟨u,rfl⟩
  exact h (by rw [←pow_two,Nat.sqrt_eq'])

private theorem row_eq (n w i : ℕ) : (labelAt n w i)^2=excessAt n w i+4*w*n :=
  (Nat.sub_add_cancel (above n w i)).symm

theorem implies_reached {n : ℕ} (top : Real.sqrt n≤2*(2:ℝ)^1023) (hit : Found n) :
    Reached n := by
  obtain ⟨r,hr,s,hs,v,hv,i,hi,j,hj,k,hk,nd,ne,nf,hz⟩ := hit
  let d := excessAt n r i
  let e := excessAt n s j
  let f := excessAt n v k
  let z := (d*e*f).sqrt
  have square : d*e*f=z^2 := hz.symm
  obtain ⟨dp,notD⟩ := nonsquare nd
  obtain ⟨ep,notE⟩ := nonsquare ne
  obtain ⟨fp,notF⟩ := nonsquare nf
  have a := row_eq n r i
  have b := row_eq n s j
  have c := row_eq n v k
  have al := inside hi (n:=n) (w:=r)
  have bl := inside hj (n:=n) (w:=s)
  have cl := inside hk (n:=n) (w:=v)
  have af : d*f*e=z^2 := by rw [←square]; ac_rfl
  have bf : e*f*d=z^2 := by rw [←square]; ac_rfl
  refine ⟨r,hr,s,hs,v,hv,_,_,_,top,al,bl,cl,
    WeightedTripleReduction.positive_difference a b dp ep square notF,
    WeightedTripleReduction.positive_difference a c dp fp af notE,
    WeightedTripleReduction.positive_difference b c ep fp bf notD,?_⟩
  obtain ⟨m,u,_,_,de,_,support⟩ := WeightedTripleSupport.triple a b c dp ep fp square
  obtain ⟨rp,rk⟩ := mem_Icc.mp hr
  obtain ⟨sp,sk⟩ := mem_Icc.mp hs
  let X : ℕ := 2^1023
  have bound := first_coordinate_lt rp sp rk sk (by decide : 8≤3^2)
    (by decide +kernel : 24*2≤3*X) (Real.sqrt_nonneg _) (by exact_mod_cast top : Real.sqrt n≤2*(X:ℝ))
    al bl (Real.sq_sqrt (Nat.cast_nonneg n)) a b
  exact ⟨m,support.trans (Nat.lcm_dvd (dvd_mul_right ..) (dvd_mul_left ..)),
    d,e,u,a,b,de,bound.trans_le (by decide +kernel)⟩

/-- Even counting every square match before testing a gcd, fewer than one in
2^475 eligible prime pairs admits any three individually nonsquare rows in
the sixteen-label menu whose product is a square. -/
theorem population : 2^475*(MixedPrefixSample.sample Found).card <
    MixedPrefixSample.eligible.card :=
  sample_coverage Found (fun _ _ h => implies_reached h)

end PrimeFactors.WeightedTripleLabels
