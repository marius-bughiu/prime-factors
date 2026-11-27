import PrimeFactors.PublicWheelLookupCosts
import PrimeFactors.PrimePowerCount

/-! Exact counts over a complete period and bounds over the two published
factor-width intervals after replacing the seven odd primes by their squares. -/
namespace PrimeFactors.PublicPrimeSquareCounts

set_option maxRecDepth 8192
set_option exponentiation.threshold 4096

open LocalSumMenu PublicWheelWidthControls
open ChebyshevQuarticScale (fresh crossed)

def modulus : ℕ := 4 * 9 * 25 * 49 * 121 * 169 * 289 * 361
def squares : List ℕ := [9,25,49,121,169,289,361]

private theorem second_count {p n : ℕ} (hp : p.Prime) (odd : p ≠ 2) (nd : ¬p ∣ n) :
    count n (p^2) =
      (letI : NeZero p := ⟨hp.ne_zero⟩
       primePowerSumCount p (decide (∃ x : ZMod p, x*x=(n : ZMod p))) 2) := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : NeZero p := ⟨hp.ne_zero⟩
  have nz := (ZMod.natCast_zmod_eq_zero_iff_dvd n p).mp.mt nd
  have nonzero : firstPrimeDigit p 1 (n : ZMod (p^2)) ≠ 0 := by simpa only [map_natCast] using nz
  have ok : IsSquare (n : ZMod p) ↔ ∃ x : ZMod p, x*x=(n : ZMod p) := by
    constructor <;> rintro ⟨x,e⟩ <;> exact ⟨x,e.symm⟩
  simpa only [count,map_natCast,ok] using card_primePower_admissibleSum odd 1 (n : ZMod (p^2)) nonzero

private theorem components (n : ℕ) (odd : ¬2 ∣ n) :
    count n modulus = (squares.map (count n)).prod := by
  have crt {a b : ℕ} (cop : a.Coprime b) : count n (a*b) = count n a * count n b :=
    card_admissibleSum_crt cop n
  simp (disch := decide) only [modulus,crt,IntervalWheelResidues.count_four odd,squares,
    List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,one_mul,mul_one,Nat.mul_assoc]

theorem local_counts {n : ℕ} (cop : IntervalWheelResidues.modulus.Coprime n) :
    squares.map (count n) = [3,5,7,11,13,17,19].map (fun p =>
      let modp := n%p
      let hasSquare := (List.range p).any fun x => x*x%p=modp
      primePowerSumCount p hasSquare 2) := by
  have digit (p : ℕ) (hp : p.Prime) (odd : p≠2) (div : p ∣ IntervalWheelResidues.modulus) :
      count n (p^2) = primePowerSumCount p
        ((List.range p).any fun x => x*x%p=n%p) 2 := by
    letI : NeZero p := ⟨hp.ne_zero⟩
    rw [second_count hp odd (hp.coprime_iff_not_dvd.mp (cop.of_dvd_left div))]
    congr 1
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq,List.any_eq_true,List.mem_range]
    constructor
    · rintro ⟨x,eq⟩
      exact ⟨x.val,ZMod.val_lt _,by simpa only [ZMod.val_mul,ZMod.val_natCast] using congrArg ZMod.val eq⟩
    · rintro ⟨x,_,eq⟩
      refine ⟨x,?_⟩
      rw [←Nat.cast_mul]
      exact (ZMod.natCast_eq_natCast_iff' ..).mpr eq
  change [3,5,7,11,13,17,19].map (fun p => count n (p^2)) = _
  apply List.map_congr_left
  intro p hp
  apply digit
  all_goals simp only [List.mem_cons,List.not_mem_nil,or_false] at hp; rcases hp with h|h|h|h|h|h|h <;> subst p <;> decide

theorem fresh_components : squares.map (count fresh) = [2,7,21,55,78,136,171] := by
  rw [local_counts (by decide +kernel)]
  decide +kernel

theorem crossed_components : squares.map (count crossed) = [2,7,16,55,78,136,154] := by
  rw [local_counts (by decide +kernel)]
  decide +kernel

/-- These period counts need only the public product residues. -/
theorem fresh_period : count fresh modulus = 29331862560 := by
  rw [components _ (by decide +kernel),fresh_components]
  decide +kernel

theorem crossed_period : count crossed modulus = 20126346240 := by
  rw [components _ (by decide +kernel),crossed_components]
  decide +kernel

def Summary (n bits oldLo oldHi rawLo rawHi : ℕ) : Prop :=
  let stronger := tests n modulus
  let earlier := tests n IntervalWheelResidues.modulus
  2^bits ≤ stronger ∧ stronger < 2^(bits+1) ∧
    oldLo*stronger ≤ 100*earlier ∧ 100*earlier ≤ oldHi*stronger ∧
    rawLo*stronger ≤ 100*raw n ∧ 100*raw n ≤ rawHi*stronger

private theorem certify {n a b lo hi bits l h r s : ℕ}
    (range : lo ≤ width n ∧ width n ≤ hi)
    (oldCount : count n IntervalWheelResidues.modulus = a) (newCount : count n modulus = b)
    (arithmetic :
      let oldL := lo/IntervalWheelResidues.modulus*a
      let oldH := (hi/IntervalWheelResidues.modulus+1)*a
      let newL := lo/modulus*b
      let newH := (hi/modulus+1)*b
      2^bits ≤ newL ∧ newH < 2^(bits+1) ∧ l*newH ≤ 100*oldL ∧ 100*oldH ≤ h*newL ∧
      r*newH ≤ 100*(lo/4) ∧ 100*(hi/4+1) ≤ s*newL) : Summary n bits l h r s := by
  have bounds (m c : ℕ) (pos : 0<m) (eq : count n m=c) :
      lo/m*c ≤ tests n m ∧ tests n m ≤ (hi/m+1)*c := by
    obtain ⟨x,y⟩ := period_bounds n m pos
    rw [eq] at x y
    exact ⟨(Nat.mul_le_mul_right _ (Nat.div_le_div_right range.1)).trans x,
      y.trans (Nat.mul_le_mul_right _ (Nat.succ_le_succ (Nat.div_le_div_right range.2)))⟩
  obtain ⟨ol,oh⟩ := bounds _ a (by decide) oldCount
  obtain ⟨nl,nh⟩ := bounds _ b (by decide) newCount
  have rawR : lo/4 ≤ raw n ∧ raw n ≤ hi/4+1 := by
    rw [raw_eq]
    have x : lo/4 ≤ width n/4 := Nat.div_le_div_right range.1
    have y : width n/4 ≤ hi/4 := Nat.div_le_div_right range.2
    split_ifs <;> omega
  obtain ⟨wl,wh,l₁,h₁,l₂,h₂⟩ := arithmetic
  exact ⟨wl.trans nl, nh.trans_lt wh, (Nat.mul_le_mul_left _ nh).trans (l₁.trans (Nat.mul_le_mul_left _ ol)),
    (Nat.mul_le_mul_left _ oh).trans (h₁.trans (Nat.mul_le_mul_left _ nl)),
    (Nat.mul_le_mul_left _ nh).trans (l₂.trans (Nat.mul_le_mul_left _ rawR.1)),
    (Nat.mul_le_mul_left _ rawR.2).trans (h₂.trans (Nat.mul_le_mul_left _ nl))⟩

theorem fresh_summary : Summary fresh 1006 642 643 80189 80190 := by
  refine certify (n:=fresh) (lo:=2557561*10^300) (hi:=2557562*10^300) ?_ IntervalWheelControls.fresh_count fresh_period ?_
  · exact PrimeFactors.PublicWheelLookupCosts.width_between (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · decide +kernel

theorem crossed_summary : Summary crossed 1007 1387 1388 116866 116867 := by
  refine certify (n:=crossed) (lo:=11130366*10^300) (hi:=11130367*10^300) ?_ IntervalWheelControls.crossed_count crossed_period ?_
  · exact PrimeFactors.PublicWheelLookupCosts.width_between (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · decide +kernel

open PersistentLocalSurvivors (smallPrimes period minPerPeriod persistent_interval)
open private PrimeFactors.PersistentLocalSurvivors.discard_midpoint from PrimeFactors.PersistentLocalSurvivors

/-- Midpoint index i corresponds to the sum 2·(ceil(start/2)+i). -/
def sumAt (n i : ℕ) := 2*((start n+1)/2+i)

theorem sumAt_injective (n : ℕ) : Function.Injective (sumAt n) := by
  intro i j eq
  unfold sumAt at eq
  omega

theorem sumAt_in_window {n i : ℕ} (inside : i < width n/2) :
    start n ≤ sumAt n i ∧ sumAt n i ≤ stop n := by
  unfold sumAt
  unfold width at inside
  omega

abbrev Permanent (n exclude : ℕ) := {i : Fin (width n/2) //
  sumAt n i.val ≠ exclude ∧ ∀ p ∈ smallPrimes 19, ∀ e : ℕ,
    AdmissibleSum (n : ZMod (p^e)) (sumAt n i.val : ZMod (p^e))}

private theorem from_midpoint {n h m : ℕ}
    (sq : IsSquare ((((h:ℕ):ℤ)^2-n : ℤ) : ZMod m)) :
    AdmissibleSum (n : ZMod m) ((2*h:ℕ) : ZMod m) := by
  push_cast at sq ⊢
  obtain ⟨t,eq⟩ := sq
  refine ⟨(h:ZMod m)+t,(h:ZMod m)-t,?_,by ring⟩
  linear_combination eq

private theorem permanent_lower {n low : ℕ}
    (sz : low ≤ width n) (units : ∀ i : Fin 20, i.val.Prime → ¬i.val ∣ n)
    (exclude : ℕ) :
    low/2/period 19*minPerPeriod 19 ≤ Nat.card (Permanent n exclude)+1 := by
  let a := (start n+1)/2
  let W := width n/2
  let P (i : Fin W) := ∀ p ∈ smallPrimes 19, ∀ e : ℕ,
    IsSquare ((((a+i.val : ℕ):ℤ)^2-n : ℤ) : ZMod (p^e))
  have cop (p : ℕ) (hp : p ∈ smallPrimes 19) : ¬p∣n := by
    obtain ⟨le,prime⟩ := Finset.mem_filter.mp hp
    exact units ⟨p,Finset.mem_range.mp le⟩ prime
  have cnt := persistent_interval 19 a W n cop
  have disc := PrimeFactors.PersistentLocalSurvivors.discard_midpoint P a exclude
  let transport (i : {j : Fin W // P j ∧ 2*(a+j.val) ≠ exclude}) : Permanent n exclude :=
    ⟨i.val,i.property.2,fun p hp e => from_midpoint (i.property.1 p hp e)⟩
  have inj : Function.Injective transport := fun _ _ eq =>
    Subtype.ext (congrArg (fun k : Permanent n exclude => k.val) eq)
  exact (Nat.mul_le_mul_right _ (Nat.div_le_div_right (Nat.div_le_div_right sz))).trans
    (cnt.trans (disc.trans (Nat.succ_le_succ (Nat.card_le_card_of_injective transport inj))))

/-- Even unlimited precision at these primes leaves many false sums in the
actual width-clipped interval. Any one sum, such as the true one, may be excluded. -/
theorem permanent_controls (exclude : ℕ) :
    2^998 < Nat.card (Permanent fresh exclude) ∧ 2^1000 < Nat.card (Permanent crossed exclude) := by
  have a : 2557561*10^300 ≤ width fresh ∧ width fresh ≤ 2557562*10^300 :=
    PrimeFactors.PublicWheelLookupCosts.width_between (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have b : 11130366*10^300 ≤ width crossed ∧ width crossed ≤ 11130367*10^300 :=
    PrimeFactors.PublicWheelLookupCosts.width_between (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have hl := permanent_lower a.1 (by decide +kernel) exclude
  have hr := permanent_lower b.1 (by decide +kernel) exclude
  have xl : 2^998+1 < 2557561*10^300/2/period 19*minPerPeriod 19 := by decide +kernel
  have xr : 2^1000+1 < 11130366*10^300/2/period 19*minPerPeriod 19 := by decide +kernel
  exact ⟨Nat.lt_of_succ_lt_succ (xl.trans_le hl),Nat.lt_of_succ_lt_succ (xr.trans_le hr)⟩

end PrimeFactors.PublicPrimeSquareCounts
