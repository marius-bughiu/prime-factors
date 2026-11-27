import PrimeFactors.ChebyshevPrimeSample
import PrimeFactors.WeakPhase

/-! A finite upper tail for the common divisor of the two prime predecessors
in the project's actual 2048-bit sample. No independence of residue classes
or asymptotic prime distribution is assumed. -/
namespace PrimeFactors.CommonPredecessorTail

open Finset MixedPrefixSample

set_option exponentiation.threshold 4096

/-- Exceptional members of the existing sample, counted once per unordered pair. -/
noncomputable def exceptional (T : ℕ) :=
  eligible.filter fun z => T<(z.1-1).gcd (z.2-1)

/-- The possible shifted multiples for a fixed common divisor. -/
private def lane (f : ℕ → ℕ) (U d : ℕ) := (Icc 1 (U/d)).image fun k => f (d*k)

private theorem lane_mem (f : ℕ → ℕ) {x U d : ℕ} (xp : 0<x) (bound : x≤U)
    (dp : 0<d) (dv : d∣x) : f x ∈ lane f U d := by
  obtain ⟨k,rfl⟩ := dv
  refine mem_image.mpr ⟨k,mem_Icc.mpr ⟨?_,?_⟩,rfl⟩
  · by_contra! bad
    have : k=0 := by omega
    simp [this] at xp
  · exact (Nat.le_div_iff_mul_le dp).mpr ((Nat.mul_comm k d) ▸ bound)

private theorem lane_card (f : ℕ → ℕ) (U d : ℕ) : (lane f U d).card≤U/d := by
  apply Finset.card_image_le.trans
  simp [Nat.card_Icc]

/-- For pairs of positive coordinates at most U, even after applying a
common function to both coordinates, a gcd above T costs at most U²/T. -/
theorem image_tail (f : ℕ → ℕ) {T U : ℕ} (tp : 0<T) (S : Finset (ℕ×ℕ))
    (covered : ∀ z∈S, ∃ x y, z=(f x,f y) ∧ 0<x ∧ x≤U ∧ 0<y ∧ y≤U ∧ T<x.gcd y) :
    T*S.card≤U^2 := by
  let box (i : ℕ) := (lane f U (T+i+1)) ×ˢ (lane f U (T+i+1))
  have sub : S ⊆ (range U).biUnion box := by
    intro z hz
    obtain ⟨x,y,rfl,xp,xu,yp,yu,larger⟩ := covered z hz
    let d := x.gcd y
    have upper : d≤U := (Nat.gcd_le_left y xp).trans xu
    have low : T<d := larger
    let i := d-(T+1)
    have id : T+i+1=d := by dsimp [i]; omega
    apply mem_biUnion.mpr
    refine ⟨i,mem_range.mpr (by dsimp [i]; omega),?_⟩
    dsimp only [box]
    rw [id]
    exact mem_product.mpr ⟨lane_mem f xp xu (by omega) (Nat.gcd_dvd_left ..),
      lane_mem f yp yu (by omega) (Nat.gcd_dvd_right ..)⟩
  have total : S.card≤∑ i∈range U,(U/(T+i+1))^2 := by
    apply (card_le_card sub).trans (card_biUnion_le.trans (sum_le_sum ?_))
    intro i _
    dsimp only [box]
    rw [card_product,←pow_two]
    exact Nat.pow_le_pow_left (lane_card ..) 2
  have realTotal : (S.card:ℝ)≤∑ i∈range U,((U/(T+i+1):ℕ):ℝ)^2 := by exact_mod_cast total
  have cmp (i : ℕ) : ((U/(T+i+1):ℕ):ℝ)^2 ≤ (U:ℝ)^2*(1/((T:ℝ)+i+1)^2) := by
    have round := Nat.cast_div_le (α:=ℝ) (m:=U) (n:=T+i+1)
    push_cast at round
    calc
      _ ≤ ((U:ℝ)/((T:ℝ)+i+1))^2 := pow_le_pow_left₀ (by positivity) round _
      _ = _ := by rw [div_pow]; ring
  have cost := realTotal.trans (sum_le_sum (fun i _ => cmp i))
  rw [←mul_sum] at cost
  have tail := weakPhase_square_tail tp U
  have nz : 0≤1/((T:ℝ)+U) := by positivity
  have tail' := tail.trans (sub_le_self _ nz)
  have upper := cost.trans (mul_le_mul_of_nonneg_left tail' (sq_nonneg (U:ℝ)))
  have rp : (0:ℝ)<T := by exact_mod_cast tp
  rw [←div_eq_mul_one_div,le_div_iff₀ rp,mul_comm] at upper
  exact_mod_cast upper

private theorem prime_half {p : ℕ} (inP : p∈primes) :
    ∃ x, p=2*x+1 ∧ 0<x ∧ x≤2^1023 := by
  obtain ⟨range,pP⟩ := mem_filter.mp inP
  have ⟨left,right⟩ := mem_Ico.mp range
  change 2^1023≤p at left
  change p<2*2^1023 at right
  obtain ⟨x,hx⟩ := pP.odd_of_ne_two (by omega)
  exact ⟨x,hx,by omega,by omega⟩

attribute [local irreducible] eligible sample ordered primes exceptional

private theorem data {T : ℕ} {z : ℕ×ℕ} (mem : z∈exceptional (2*T)) :
    z.1<z.2 ∧ ∃ x y, z=(2*x+1,2*y+1) ∧ 0<x ∧ x≤2^1023 ∧ 0<y ∧ y≤2^1023 ∧ T<x.gcd y := by
  rw [exceptional,mem_filter] at mem
  obtain ⟨elig,large⟩ := mem
  rw [eligible,sample,mem_filter] at elig
  obtain ⟨inputs,sorted⟩ := elig
  obtain ⟨xp,yp,_,_,_⟩ := (mem_ordered (E:=fun _ => True) (z:=z)).mp inputs
  obtain ⟨x,px,xpos,xu⟩ := prime_half xp
  obtain ⟨y,qy,ypos,yu⟩ := prime_half yp
  rw [px,qy,Nat.add_sub_cancel,Nat.add_sub_cancel,Nat.gcd_mul_left] at large
  exact ⟨sorted,x,y,Prod.ext px qy,xpos,xu,ypos,yu,by omega⟩

/-- Use both orientations without double counting them and divide the even
predecessors by two before summing over the possible gcds. -/
theorem tail (T : ℕ) (tp : 0<T) : 2*T*(exceptional (2*T)).card≤(2^1023)^2 := by
  let A := exceptional (2*T)
  let B := A.image Prod.swap
  have disj : Disjoint A B := by
    apply disjoint_left.mpr
    intro z za zb
    obtain ⟨w,wa,rfl⟩ := mem_image.mp zb
    have a := (data (T:=T) za).1
    have b := (data (T:=T) wa).1
    exact (not_lt_of_ge b.le) a
  have size := image_tail (fun x => 2*x+1) tp (U:=2^1023) (A∪B) (by
    intro z hz
    rcases mem_union.mp hz with za|zb
    · exact (data (T:=T) za).2
    · obtain ⟨w,wa,rfl⟩ := mem_image.mp zb
      obtain ⟨x,y,rfl,xp,xu,yp,yu,large⟩ := (data (T:=T) wa).2
      exact ⟨y,x,rfl,yp,yu,xp,xu,Nat.gcd_comm x y ▸ large⟩)
  rw [card_union_of_disjoint disj,show B.card=A.card from card_image_of_injective _ Prod.swap_injective] at size
  change 2*T*A.card≤_
  calc
    2*T*A.card=T*(A.card+A.card) := by ring
    _ ≤ _ := size

/-- Fewer than one in 2^55 eligible products has a common predecessor
divisor above 2^80. The eligible sample represents each product once. -/
theorem rare55 : 2^55*(exceptional (2^80)).card<eligible.card := by
  have h := tail (2^79) (by positivity)
  rw [show 2*2^79=2^80 by decide +kernel] at h
  apply Nat.lt_of_mul_lt_mul_left (a:=21000000)
  have coef : 21000000*2^55≤2^80 := by decide +kernel
  have scaled := (Nat.mul_le_mul_right (exceptional (2^80)).card coef).trans h
  rw [Nat.mul_assoc] at scaled
  exact scaled.trans_lt (by simpa only [←pow_mul] using ChebyshevPrimeSample.eligible_count)

theorem rare : 2^53*(exceptional (2^80)).card<eligible.card :=
  (Nat.mul_le_mul_right _ (by decide +kernel : 2^53≤2^55)).trans_lt rare55

end PrimeFactors.CommonPredecessorTail
