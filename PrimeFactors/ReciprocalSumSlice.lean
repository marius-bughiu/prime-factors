import PrimeFactors.ReciprocalSumLanes
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.NormNum.Prime

/-! Near the square root, directly decode the few possible sums modulo 211.
Their two modular roots replace enumeration of all 210 unit lanes. -/
namespace PrimeFactors.ReciprocalSumSlice

open Finset ReciprocalSumLanes

set_option maxRecDepth 4096

local instance : Fact (Nat.Prime 211) := ⟨by norm_num⟩

/-- The two quadratic-formula residues, with the square-root check included.
Since 211≡3 mod 4, one fixed exponent extracts a root whenever it exists. -/
noncomputable def fromSum (n z : ZMod 211) : Finset (ZMod 211) :=
  let d := (z^2-4*n)^53
  if d^2 = z^2-4*n then {(z+d)/2, (z-d)/2} else ∅

private theorem sqrt_sign (u : ZMod 211) : (u^2)^53=u ∨ (u^2)^53= -u := by
  apply sq_eq_sq_iff_eq_or_eq_neg.mp
  by_cases z : u=0
  · simp [z]
  · have fermat : u^210=1 := ZMod.pow_card_sub_one_eq_one z
    calc
      ((u^2)^53)^2 = u^(210+2) := by rw [←pow_mul, ←pow_mul]
      _ = u^2 := by rw [pow_add,fermat,one_mul]

private theorem quadratic_pair {F : Type*} [Field F] [DecidableEq F] (n z x d : F)
    (two : (2:F)≠0) (sign : ∀ u : F, u^2=z^2-4*n → d=u ∨ d= -u) :
    x∈(if d^2=z^2-4*n then {(z+d)/2,(z-d)/2} else (∅ : Finset F)) ↔ x*(z-x)=n := by
  constructor
  · intro inside
    split at inside
    · rename_i square
      rcases mem_insert.mp inside with eq | eq
      · rw [eq]; field_simp; linear_combination -square
      · rw [mem_singleton.mp eq]; field_simp; linear_combination -square
    · simp at inside
  · intro prod
    have delta : (2*x-z)^2=z^2-4*n := by linear_combination -4*prod
    have signed := sign (2*x-z) delta
    have square : d^2=z^2-4*n := by rcases signed with h|h <;> simp only [h,even_two.neg_pow,delta]
    rw [if_pos square]
    rcases signed with h|h
    · apply mem_insert.mpr; left; apply (eq_div_iff two).mpr; rw [h]; ring
    · apply mem_insert.mpr; right; apply mem_singleton.mpr; apply (eq_div_iff two).mpr; rw [h]; ring

theorem mem_fromSum (n z x : ZMod 211) : x ∈ fromSum n z ↔ x*(z-x)=n := by
  refine quadratic_pair n z x _ (by decide +kernel) ?_
  intro u hu
  rw [←hu]
  exact sqrt_sign u

theorem fromSum_card (n z : ZMod 211) : (fromSum n z).card ≤ 2 := by
  dsimp only [fromSum]
  split
  · exact (card_insert_le ..).trans (by simp)
  · simp

noncomputable def lower (n b : ℤ) := b+⌈(n:ℝ)/b⌉
noncomputable def upper (n a : ℤ) := a+⌊(n:ℝ)/a⌋

/-- The near-endpoint condition 2401 n ≤ 2500 a² means a≥0.98√n. -/
theorem span {n a b : ℤ} (ap : 0<a) (order : a≤b) (near : 2401*n≤2500*a^2)
    (width : b-a≤843) : upper n a - lower n b < 35 := by
  have A : (0:ℝ)<a := by exact_mod_cast ap
  have B : (0:ℝ)<b := by exact_mod_cast ap.trans_le order
  have dx : (0:ℝ)≤(b:ℝ)-a := by exact_mod_cast sub_nonneg.mpr order
  have close : (2401:ℝ)*n≤2500*(a:ℝ)^2 := by exact_mod_cast near
  have diff : (b:ℝ)-a≤843 := by exact_mod_cast width
  have ab := mul_pos A B
  have ratio : (2401:ℝ)*((n:ℝ)-a*b) ≤ 99*(a*b) := by nlinarith only [close,mul_nonneg A.le dx]
  have lim := mul_le_mul_of_nonneg_left ratio dx
  have bound : 2401*(factorSum n a-factorSum n b)≤99*((b:ℝ)-a) := by
    apply le_of_mul_le_mul_right (a:=(a:ℝ)*b) _ ab
    rw [mul_assoc, difference _ A.ne' B.ne']
    linarith only [show ((b:ℝ)-a)*(2401*((n:ℝ)-a*b))=2401*((b-a)*(n-a*b)) by ring,
      show ((b:ℝ)-a)*(99*(a*b))=99*(b-a)*(a*b) by ring, lim]
  have hi := Int.floor_le ((n:ℝ)/a)
  have lo := Int.le_ceil ((n:ℝ)/b)
  have rounded : ((upper n a:ℤ):ℝ)-((lower n b:ℤ):ℝ)<35 := by
    unfold upper lower; push_cast; unfold factorSum at bound
    linarith only [hi,lo,bound,diff]
  exact_mod_cast rounded

/-- The integer j denotes sum n+1+4j. -/
noncomputable def indices (n L U : ℤ) := Ioc ((L-1-(n+1))/4) ((U-(n+1))/4)

noncomputable def lanes (n L U : ℤ) : Finset (ZMod 211) :=
  (indices n L U).biUnion fun j => fromSum n ((n+1+4*j:ℤ):ZMod 211)

theorem indices_bound {n L U : ℤ} (narrow : U-L<35) : (indices n L U).card ≤ 9 := by
  rw [indices,Int.card_Ioc]
  omega

theorem lanes_bound {n L U : ℤ} (narrow : U-L<35) : (lanes n L U).card ≤ 18 :=
  (card_biUnion_le_card_mul _ _ 2 (fun _ _ => fromSum_card ..)).trans <|
    Nat.mul_le_mul_right 2 (indices_bound narrow)

theorem all_integer_sums {n L U : ℤ} (narrow : U-L<35) :
    ((Icc L U).biUnion fun z => fromSum n (z:ZMod 211)).card ≤ 70 := by
  have h : (Icc L U).card ≤ 35 := by rw [Int.card_Icc]; omega
  exact (card_biUnion_le_card_mul _ _ 2 (fun _ _ => fromSum_card ..)).trans (Nat.mul_le_mul_right 2 h)

theorem covers {n a b p q : ℤ} (ap : 0<a) (left : a≤p) (right : p≤b) (small : b^2≤n)
    (near : 2401*n≤2500*a^2) (prod : p*q=n) (oddp : Odd p) (oddq : Odd q) :
    (p:ZMod 211) ∈ lanes n (lower n b) (upper n a) := by
  have balanced : n≤2*a^2 := by nlinarith only [near,sq_nonneg a]
  obtain ⟨lo,hi⟩ := sum_survives ap left right small balanced prod
  obtain ⟨v,hv⟩ := oddp
  obtain ⟨w,hw⟩ := oddq
  have rep : n+1+4*(-v*w)=p+q := by rw [←prod,hv,hw]; ring
  apply mem_biUnion.mpr
  refine ⟨-v*w, mem_Ioc.mpr ((slot_index (by decide : (0:ℤ)<4) _ _ _ _).mp ?_), ?_⟩
  · simpa only [rep,lower,upper] using And.intro lo hi
  · rw [rep,mem_fromSum]
    push_cast
    simpa only [Int.cast_mul,add_sub_cancel_left] using congrArg (fun z : ℤ => (z:ZMod 211)) prod

/-- Integer sites retained by any chosen set of residues in a directed band. -/
noncomputable def oddSites (a b : ℤ) (S : Finset (ZMod 211)) : Finset ℤ :=
  (Icc a b).filter fun x => x%2=1 ∧ (x:ZMod 211)∈S

theorem oddSites_card (a b : ℤ) (S : Finset (ZMod 211)) (width : b-a≤843) :
    (oddSites a b S).card≤2*S.card := by
  let code (x : ℤ) : Bool × ZMod 211 := (decide (x<a+422), x)
  have inside : ∀ x∈oddSites a b S, code x∈(univ : Finset Bool) ×ˢ S := by
    intro x hx
    exact mem_product.mpr ⟨mem_univ _,(mem_filter.mp hx).2.2⟩
  have inj : Set.InjOn code (oddSites a b S : Set ℤ) := by
    intro x hx y hy eq
    obtain ⟨xb,xodd,_⟩ := mem_filter.mp hx
    obtain ⟨yb,yodd,_⟩ := mem_filter.mp hy
    obtain ⟨xa,xend⟩ := mem_Icc.mp xb
    obtain ⟨ya,yend⟩ := mem_Icc.mp yb
    have same : x<a+422 ↔ y<a+422 := by
      simpa only [code,decide_eq_decide] using congrArg Prod.fst eq
    have modEq := (ZMod.intCast_eq_intCast_iff x y 211).mp (congrArg Prod.snd eq)
    obtain ⟨t,dt⟩ := Int.modEq_iff_dvd.mp modEq
    have close : -422 < y-x ∧ y-x < 422 := by omega
    omega
  simpa only [card_product, card_univ, Fintype.card_bool] using card_le_card_of_injOn code inside inj

theorem position_bound {n a b : ℤ} (ap : 0<a) (order : a≤b) (near : 2401*n≤2500*a^2)
    (width : b-a≤843) :
    (oddSites a b (lanes n (lower n b) (upper n a))).card ≤ 36 :=
  (oddSites_card a b _ width).trans <|
    Nat.mul_le_mul_left 2 (lanes_bound (span ap order near width))

/-- Ordinary wheel positions of the same parity as the unknown odd prime. -/
noncomputable def ordinary (a b : ℤ) := oddSites a b (univ.erase 0)

theorem ordinary_full (a : ℤ) : (ordinary a (a+843)).card=420 := by
  have total : 422 ≤ (oddSites a (a+843) univ).card := by
    let pick (i : ℕ) : ℤ := a+(a+1)%2+2*i
    have inside (i : ℕ) (hi : i∈range 422) : pick i∈oddSites a (a+843) univ := by
      have bound := mem_range.mp hi
      apply mem_filter.mpr
      dsimp [pick]
      exact ⟨mem_Icc.mpr ⟨by omega,by omega⟩,by omega,mem_univ _⟩
    have inj : Set.InjOn pick (range 422 : Set ℕ) := by
      intro i _ j _ eq
      dsimp [pick] at eq
      omega
    simpa only [card_range] using card_le_card_of_injOn pick inside inj
  have zero := oddSites_card a (a+843) ({0} : Finset (ZMod 211)) (by omega)
  rw [card_singleton,Nat.mul_one] at zero
  have allSites : oddSites a (a+843) univ ⊆ ordinary a (a+843) ∪ oddSites a (a+843) {0} := by
    intro x hx
    obtain ⟨inrange,odd,_⟩ := mem_filter.mp hx
    by_cases eq : (x:ZMod 211)=0
    · exact mem_union_right _ (mem_filter.mpr ⟨inrange,odd,mem_singleton.mpr eq⟩)
    · exact mem_union_left _ (mem_filter.mpr ⟨inrange,odd,mem_erase.mpr ⟨eq,mem_univ _⟩⟩)
  have both := (card_le_card allSites).trans (card_union_le ..)
  have bound := oddSites_card a (a+843) (univ.erase (0:ZMod 211)) (by omega)
  have digits : (univ.erase (0:ZMod 211)).card=210 := by
    rw [card_erase_of_mem (mem_univ _),card_univ,ZMod.card]
  rw [digits] at bound
  change (ordinary a (a+843)).card≤2*210 at bound
  omega

/-- The complete 844-site blocks ending at t, starting from the high end. -/
def blockCount (t : ℤ) : ℕ := (t/42200).toNat
def blockStart (t : ℤ) (i : ℕ) := t+1-844*((i:ℤ)+1)

noncomputable def dropped (n t : ℤ) (i : ℕ) : Finset ℤ :=
  let a := blockStart t i
  ordinary a (a+843) \ oddSites a (a+843) (lanes n (lower n (a+843)) (upper n a))

noncomputable def removed (n t : ℤ) := (range (blockCount t)).biUnion (dropped n t)

private theorem block_geometry {n t : ℤ} (large : 2^24≤t) (top : n<(t+1)^2)
    {i : ℕ} (within : i<blockCount t) :
    0<blockStart t i ∧ blockStart t i+843≤t ∧ 2401*n≤2500*(blockStart t i)^2 := by
  have low : 49*(t+1)≤50*blockStart t i := by unfold blockStart blockCount at *; omega
  have pos : 0<blockStart t i := by omega
  have sq := pow_le_pow_left₀ (by omega : 0≤49*(t+1)) low 2
  exact ⟨pos,by unfold blockStart; omega,by nlinarith only [top,sq]⟩

private theorem odd_budget {a b : ℤ} (ordered : a≤b) :
    2*((ordinary a b).card:ℤ)≤b-a+3 := by
  let pick (x : ℤ) := x/2
  have inside : ∀ x∈ordinary a b, pick x∈Icc (a/2) (b/2) := by
    intro x hx
    obtain ⟨lo,hi⟩ := mem_Icc.mp (mem_filter.mp hx).1
    exact mem_Icc.mpr ⟨Int.ediv_le_ediv (by decide) lo,Int.ediv_le_ediv (by decide) hi⟩
  have inj : Set.InjOn pick (ordinary a b : Set ℤ) := by
    intro x hx y hy eq
    have h := (mem_filter.mp hx).2.1
    have g := (mem_filter.mp hy).2.1
    dsimp [pick] at eq
    omega
  have count := card_le_card_of_injOn pick inside inj
  rw [Int.card_Icc] at count
  omega

theorem removed_count {n t : ℤ} (large : 2^24≤t) (top : n<(t+1)^2) :
    384*blockCount t ≤ (removed n t).card := by
  have separate : (↑(range (blockCount t)) : Set ℕ).PairwiseDisjoint (dropped n t) := by
    intro i _ j _ ne
    apply disjoint_left.mpr
    intro x hx hy
    have hi := mem_Icc.mp (mem_filter.mp (mem_sdiff.mp hx).1).1
    have hj := mem_Icc.mp (mem_filter.mp (mem_sdiff.mp hy).1).1
    unfold blockStart at hi hj
    omega
  rw [removed,card_biUnion separate]
  calc
    _ = ∑ _i ∈ range (blockCount t), (384:ℕ) := by simp [Nat.mul_comm]
    _ ≤ _ := by
      apply sum_le_sum
      intro i hi
      obtain ⟨pos,_,near⟩ := block_geometry large top (mem_range.mp hi)
      let a := blockStart t i
      have short := position_bound pos (by omega : a≤a+843) near (by omega)
      let kept := oddSites a (a+843) (lanes n (lower n (a+843)) (upper n a))
      change kept.card≤36 at short
      have allSites := card_le_card_sdiff_add_card (s:=ordinary a (a+843)) (t:=kept)
      rw [ordinary_full] at allSites
      change 384 ≤ (ordinary a (a+843) \ kept).card
      omega

/-- Strictly over six percent of the ordinary odd wheel positions in the
entire ratio-only band can be discarded. The discarded sets are disjoint. -/
theorem whole_band {n t l : ℤ} (large : 2^24≤t) (floor_low : t^2≤n)
    (floor_high : n<(t+1)^2) (positive : 0<l) (ceil_low : 2*(l-1)^2<n)
    (ceil_high : n≤2*l^2) (ordered : l≤t) :
    removed n t ⊆ ordinary l t ∧ 6*(ordinary l t).card < 100*(removed n t).card := by
  constructor
  · intro x hx
    obtain ⟨i,hi,inBlock⟩ := mem_biUnion.mp hx
    obtain ⟨pos,top,near⟩ := block_geometry large floor_high (mem_range.mp hi)
    obtain ⟨xb,odd,unit⟩ := (show x∈Icc (blockStart t i) (blockStart t i+843) ∧
        x%2=1 ∧ (x:ZMod 211)∈univ.erase 0 from mem_filter.mp (mem_sdiff.mp inBlock).1)
    obtain ⟨xl,xh⟩ := mem_Icc.mp xb
    have low : l≤blockStart t i := by
      by_contra! short
      have sq := pow_le_pow_left₀ pos.le (by omega : blockStart t i≤l-1) 2
      nlinarith only [sq,ceil_low,near,sq_nonneg (blockStart t i)]
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨low.trans xl,xh.trans top⟩,odd,unit⟩
  · have ratio : 7*t≤10*l := by
      by_contra! short
      have sq := (sq_lt_sq₀ (by omega : 0≤10*l) (by omega : 0≤7*t)).mpr short
      nlinarith only [sq,floor_low,ceil_high,sq_nonneg t]
    have baseline := odd_budget ordered
    have saving := removed_count large floor_high
    unfold blockCount at saving
    omega

/-- No discarded site can have an odd partner with the required integer product. -/
theorem safe {n t p q : ℤ} (large : 2^24≤t) (floor_low : t^2≤n) (floor_high : n<(t+1)^2)
    (prod : p*q=n) (oddp : Odd p) (oddq : Odd q) : p ∉ removed n t := by
  intro erased
  obtain ⟨i,hi,inBlock⟩ := mem_biUnion.mp erased
  obtain ⟨yes,no⟩ := mem_sdiff.mp inBlock
  obtain ⟨rangeP,parity,_⟩ := mem_filter.mp yes
  obtain ⟨xl,xh⟩ := mem_Icc.mp rangeP
  obtain ⟨pos,top,near⟩ := block_geometry large floor_high (mem_range.mp hi)
  have below := (pow_le_pow_left₀ (by omega : 0≤blockStart t i+843) top 2).trans floor_low
  exact no (mem_filter.mpr ⟨rangeP,parity,covers pos xl xh below near prod oddp oddq⟩)

/-- First smaller-factor candidate when the ratio is at most two. -/
def bandLow (n : ℕ) := ((n-1)/2).sqrt+1

set_option exponentiation.threshold 4096 in
/-- Unconditional count over the whole original balanced interval for every
2048-bit product, with no hypothesis about empirical location or wheel occupancy. -/
theorem target (n : ℕ) (large : 2^2047≤n) :
    removed n n.sqrt ⊆ ordinary (bandLow n) n.sqrt ∧
    6*(ordinary (bandLow n) n.sqrt).card < 100*(removed n n.sqrt).card := by
  let t := n.sqrt
  let v := ((n-1)/2).sqrt
  have big : 2^24≤t := Nat.le_sqrt'.mpr ((by decide +kernel : (2^24:ℕ)^2≤2^2047).trans large)
  have tlo : t^2≤n := Nat.le_sqrt'.mp le_rfl
  have thi : n<(t+1)^2 := Nat.lt_succ_sqrt' n
  have vlo : v^2≤(n-1)/2 := Nat.le_sqrt'.mp le_rfl
  have vhi : (n-1)/2<(v+1)^2 := Nat.lt_succ_sqrt' _
  have np : 0<n := (show (0:ℕ)<2^2047 by positivity).trans_le large
  have low : 2*v^2<n := by omega
  have high : n≤2*(v+1)^2 := by omega
  have lt : v<t := by
    by_contra! bad
    have sq := Nat.pow_le_pow_left bad 2
    have size := Nat.mul_le_mul_right t (by omega : 3≤t)
    nlinarith only [sq,low,thi,size,show 3≤t by omega]
  apply whole_band
  · exact_mod_cast big
  · exact_mod_cast tlo
  · exact_mod_cast thi
  · change (0:ℤ)<((v+1:ℕ):ℤ); positivity
  · change 2*(((v+1:ℕ):ℤ)-1)^2<(n:ℤ)
    simpa only [Nat.cast_add,Nat.cast_one,add_sub_cancel_right] using
      (show (2:ℤ)*(v:ℤ)^2<(n:ℤ) by exact_mod_cast low)
  · exact_mod_cast high
  · exact_mod_cast lt

end PrimeFactors.ReciprocalSumSlice
