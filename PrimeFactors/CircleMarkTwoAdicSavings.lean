import PrimeFactors.CircleMarkBandSavings
import PrimeFactors.DyadicSumPeak

/-! The cofactor-band filter after dividing the positive remainder by its
entire power of two. Every positive coordinate up to a marked stop belongs
to the ordinary scan. A discarded coordinate belongs to one valuation range;
its square root class controls how many such coordinates fit before the bands join. -/
namespace PrimeFactors.CircleMarkTwoAdicSavings

open Finset MixedPrefixSample CircleMarkBandSavings CircleMarkCofactorBands
open scoped Classical
open private PrimeFactors.CircleMarkBandSavings.away PrimeFactors.CircleMarkBandSavings.stop_data
  from PrimeFactors.CircleMarkBandSavings

set_option exponentiation.threshold 8192
set_option maxRecDepth 8192
attribute [local irreducible] eligible primes

/-- Count all skips, including the initial prefix where the remainder is nonpositive. -/
noncomputable def stripped (n a stop : ℕ) : Finset ℕ :=
  (Icc 1 stop).filter fun x => ¬inBands (lower n) (U-1) (ordCompl[2] (x^2-a))

private noncomputable def congruentBelow (e a B : ℕ) :=
  (range B).filter fun x => x^2 ≡ a [MOD 2^e]

/-- Exact periods avoid any endpoint correction in the lower valuation ranges. -/
private theorem blocks (e a b : ℕ) :
    (congruentBelow e a (2^e*b)).card ≤ 2^((e+1)/2)*b := by
  let s := (univ : Finset (ZMod (2^e))).filter fun x => x^2=(a:ZMod (2^e))
  have size : s.card≤2^((e+1)/2) := by
    simpa only [s,DyadicSumPeak.roots,Nat.card_eq_fintype_card,Fintype.card_subtype] using
      DyadicSumPeak.roots_le e (a:ZMod (2^e))
  let key (x : ℕ) := ((x:ZMod (2^e)),x/2^e)
  apply le_trans _ (Nat.mul_le_mul_right b size)
  rw [←show (s ×ˢ range b).card=s.card*b by simp]
  apply card_le_card_of_injOn key
  · intro x hx
    obtain ⟨ix,root⟩ := mem_filter.mp hx
    apply mem_product.mpr
    refine ⟨mem_filter.mpr ⟨mem_univ _,?_⟩,mem_range.mpr ?_⟩
    · change (x : ZMod (2^e))^2=(a:ZMod (2^e))
      simpa only [Nat.cast_pow] using (ZMod.natCast_eq_natCast_iff _ _ _).mpr root
    · exact (Nat.div_lt_iff_lt_mul (by positivity : 0<(2:ℕ)^e)).mpr
        (by simpa only [Nat.mul_comm b] using mem_range.mp ix)
  · intro x hx y hy hv
    have lo : x ≡ y [MOD 2^e] := (ZMod.natCast_eq_natCast_iff _ _ _).mp (congrArg Prod.fst hv)
    have hi : x/2^e=y/2^e := congrArg Prod.snd hv
    rw [←Nat.mod_add_div x (2^e),show x%2^e=y%2^e from lo,hi,Nat.mod_add_div]

private theorem residue {a x e : ℕ} (small : e≤(x^2-a).factorization 2) :
    x^2 ≡ a [MOD 2^e] := by
  by_cases sa : a≤x^2
  · apply ((Nat.modEq_iff_dvd' sa).mpr ?_).symm
    exact (pow_dvd_pow 2 small).trans (Nat.ordProj_dvd (x^2-a) 2)
  · have z : x^2-a=0 := by omega
    simp [z] at small
    simp [small,Nat.ModEq,Nat.mod_one]

private theorem limit {n a x G k C j : ℕ} (width : lower n≤U-G) (gap : 0<G) (gu : G≤U)
    (kp : 0<k) (touch : U-G-1≤k*(G-1)) (scale : k*(U-G)≤4*C^2)
    (small : a≤C^2) (miss : ¬inBands (lower n) (U-1) (ordCompl[2] (x^2-a)))
    (val : (x^2-a).factorization 2≤2*j+1) : x<3*C*2^j := by
  let y := x^2-a
  let z := ordCompl[2] y
  have under : z<k*(U-G) := by
    by_contra! past
    apply miss (continuous (by simp [lower]) (by omega) kp ?_ ?_)
    · exact (Nat.sub_le_sub_right width 1).trans
        (touch.trans (Nat.mul_le_mul_left k (by omega)))
    · exact (Nat.mul_le_mul_left k width).trans past
  have yl : y<2^(2*j+1)*(4*C^2) := calc
    y = 2^(y.factorization 2)*z := (Nat.ordProj_mul_ordCompl_eq_self y 2).symm
    _ < 2^(y.factorization 2)*(4*C^2) :=
      Nat.mul_lt_mul_of_pos_left (under.trans_le scale) (by positivity)
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) val)
  rw [pow_succ,show (2:ℕ)^(2*j)=((2:ℕ)^j)^2 by rw [←pow_mul,Nat.mul_comm j 2]] at yl
  have npos : 0<(2:ℕ)^j := by positivity
  have mag := Nat.le_mul_of_pos_right (C^2) (show 0<((2:ℕ)^j)^2 by positivity)
  have xy : x^2≤a+y := by dsimp [y]; omega
  by_contra! large
  have sq := Nat.pow_le_pow_left large 2
  nlinarith only [sq,xy,small,yl,mag]

private theorem valuation_pair (c j a : ℕ) (fits : j≤c) :
    (congruentBelow (2*j) a (3*2^c*2^j)).card≤3*2^c := by
  have exp : 2*j+(c-j)=c+j := by omega
  have len : 3*2^c*2^j = 2^(2*j)*(3*2^(c-j)) := by
    calc _ = 3*2^(c+j) := by rw [pow_add]; ring
         _ = 2^(2*j)*(3*2^(c-j)) := by rw [←exp,pow_add]; ring
  rw [len]
  have bound := blocks (2*j) a (3*2^(c-j))
  rw [show (2*j+1)/2=j by omega] at bound
  calc _ ≤ _ := bound
       _ = 3*2^(j+(c-j)) := by rw [pow_add]; ring
       _ = _ := by rw [show j+(c-j)=c by omega]

/-- The finite bound covers every valuation. The last term is the residual
class count beyond valuation 1,024 and includes the final incomplete period. -/
theorem count {n a stop G k c : ℕ} (width : lower n≤U-G) (gap : 0<G) (gu : G≤U)
    (kp : 0<k) (touch : U-G-1≤k*(G-1)) (scale : k*(U-G)≤4*(2^c)^2)
    (small : a≤(2^c)^2) (fit : 511≤c) :
    (stripped n a stop).card≤512*(3*2^c)+2^512*(stop/2^1024+1) := by
  let bin (j : ℕ) := congruentBelow (2*j) a (3*2^c*2^j)
  let tail := congruentBelow 1024 a (2^1024*(stop/2^1024+1))
  have cover : stripped n a stop⊆(range 512).biUnion bin ∪ tail := by
    intro x hx
    obtain ⟨iv,miss⟩ := mem_filter.mp hx
    let v := (x^2-a).factorization 2
    by_cases early : v<1024
    · let j := v/2
      have pair : 2*j≤v ∧ v≤2*j+1 := by dsimp [j]; omega
      have lo := limit width gap gu kp touch scale small miss pair.2
      exact mem_union_left _ (mem_biUnion.mpr ⟨j,mem_range.mpr (by dsimp [j]; omega),
        mem_filter.mpr ⟨mem_range.mpr lo,residue pair.1⟩⟩)
    · have lim := Nat.lt_mul_div_succ stop (by decide +kernel : 0<(2:ℕ)^1024)
      exact mem_union_right _ (mem_filter.mpr ⟨mem_range.mpr ((mem_Icc.mp iv).2.trans_lt lim),
        residue (show 1024≤v by omega)⟩)
  have first : ((range 512).biUnion bin).card≤512*(3*2^c) := by
    have h := card_biUnion_le_card_mul (range 512) bin (3*2^c) (fun j hj =>
      valuation_pair c j a (by have := mem_range.mp hj; omega))
    simpa only [card_range] using h
  have last := blocks 1024 a (stop/2^1024+1)
  exact (card_le_card cover).trans ((card_union_le ..).trans (Nat.add_le_add first last))

private theorem relative {d b saved stop : ℕ} (late : 2^900<stop)
    (bound : saved≤b+2^512*(stop/2^1024+1))
    (low : 8*d*b≤6*2^900) (per : 8*d*2^512≤2^1024) (tail : 8*d*2^512≤2^900) :
    d*saved<stop := by
  have front := low.trans_lt (Nat.mul_lt_mul_of_pos_left late (by decide : 0<6))
  have many : 8*d*2^512*(stop/2^1024)≤stop :=
    (Nat.mul_le_mul_right _ per).trans (by
      simpa only [Nat.mul_comm (2^1024)] using (Nat.div_mul_le_self stop (2^1024)))
  apply Nat.lt_of_mul_lt_mul_left (a:=8)
  calc
    _ = 8*d*saved := by ring
    _ ≤ 8*d*(b+2^512*(stop/2^1024+1)) := Nat.mul_le_mul_left _ bound
    _ = 8*d*b+(8*d*2^512*(stop/2^1024)+8*d*2^512) := by ring
    _ < 6*stop+(stop+stop) := Nat.add_lt_add_of_lt_of_le front
      (Nat.add_le_add many (tail.trans late.le))
    _ = _ := by ring

/-- Removing every factor of two can discard less than a 2^-350 share of
the positive-coordinate walk. The same exception set as the raw-band proof
has share less than 2^-85 among eligible prime pairs. -/
theorem broad_fraction {v : ℕ×ℕ} (member : v∈eligible) (good : v∉exceptional (2^968))
    {a stop : ℕ} (target : a∈Icc 1 CircleMarkSmallTargetPopulation.A)
    (neg : jacobiSym a (v.1*v.2)= -1) (start : 0<stop)
    (hit : ¬(v.1*v.2).Coprime (CircleMarkSmallTargetPopulation.magnitude a stop 1)) :
    2^350*(stripped (v.1*v.2) a stop).card<stop := by
  obtain ⟨sep,late⟩ := PrimeFactors.CircleMarkBandSavings.stop_data member good target neg start hit
  have geom := count (stop:=stop) (k:=2^56) (c:=539) (PrimeFactors.CircleMarkBandSavings.away member sep)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    ((mem_Icc.mp target).2.trans (by decide +kernel)) (by decide)
  exact relative late geom (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Away from the larger upper-end exception, of share less than 2^-23,
the relative bound improves to 2^-366. -/
theorem far_fraction {v : ℕ×ℕ} (member : v∈eligible) (good : v∉exceptional (2^1000))
    {a stop : ℕ} (target : a∈Icc 1 CircleMarkSmallTargetPopulation.A)
    (neg : jacobiSym a (v.1*v.2)= -1) (start : 0<stop)
    (hit : ¬(v.1*v.2).Coprime (CircleMarkSmallTargetPopulation.magnitude a stop 1)) :
    2^366*(stripped (v.1*v.2) a stop).card<stop := by
  obtain ⟨sep,late⟩ := PrimeFactors.CircleMarkBandSavings.stop_data member good target neg start hit
  have geom := count (stop:=stop) (k:=2^24) (c:=523) (PrimeFactors.CircleMarkBandSavings.away member sep)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    ((mem_Icc.mp target).2.trans (by decide +kernel)) (by decide)
  exact relative late geom (by decide +kernel) (by decide +kernel) (by decide +kernel)

end PrimeFactors.CircleMarkTwoAdicSavings
