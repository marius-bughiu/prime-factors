import PrimeFactors.BinomialDivisorWindow
import PrimeFactors.CenteredBinomialDivisorWindow

namespace PrimeFactors.BinomialDivisorCover

open Polynomial FeasibleDivisorCover

set_option exponentiation.threshold 4096
set_option maxRecDepth 8192

/-- Number of old intervals represented by one one-sided binomial window. -/
abbrev groupSize : ℕ := 2680

def locationsOf (g n : ℕ) (b : Bool) := (count n b+(g-1))/g

abbrev locations := locationsOf groupSize

def firstOf (g n : ℕ) (b : Bool) (i : ℕ) :=
  2*(start n b+i*g*(2*radius b))+1

abbrev first := firstOf groupSize

def span (b : Bool) := 5360*radius b

private lemma merge_address (l w i g : ℕ) (positive : 0<g) (x : ℤ) (near : |x|≤(w:ℤ)) :
    ∃ y : ℕ, ((2*(l+i*(2*w)+w)+1:ℕ):ℤ)+2*x =
      ((2*(l+(i/g)*g*(2*w))+1:ℕ):ℤ)+2*(y:ℤ) ∧ y≤g*(2*w) := by
  let z := (i%g:ℕ)*(2*w)
  have split : (i/g)*g + i%g = i := by simpa only [Nat.mul_comm (i/g) g] using Nat.div_add_mod i g
  have identity : (i/g)*g*(2*w) + z = i*(2*w) := by
    dsimp only [z]; rw [←Nat.add_mul,split]
  have chunk := Nat.mul_le_mul_right (2*w) (Nat.succ_le_of_lt (Nat.mod_lt i positive))
  have endpt : z+2*w≤g*(2*w) := by simpa only [z,Nat.succ_mul] using chunk
  have bounds := abs_le.mp near
  let y := (z:ℤ)+w+x
  have nn : 0≤y := by dsimp [y]; omega
  refine ⟨y.toNat,?_,?_⟩
  · rw [Int.toNat_of_nonneg nn]
    have eq := congrArg (fun a : ℕ => (a:ℤ)) identity
    push_cast at eq ⊢
    dsimp only [y]
    linarith only [eq]
  · omega

private theorem merged_budget (a b : ℕ) (h : 20*(a+b)<19*2^509) :
    (a+(groupSize-1))/groupSize+(b+(groupSize-1))/groupSize < 2^498 := by
  dsimp only [groupSize]
  omega

private theorem address_exists {n d q : ℕ} (g : ℕ) (positive : 0<g)
    (pair : n=d*q) (nd : Odd d) (ord : d≤q) (cap : q<Q) :
    ∃ b, ∃ i : Fin (locationsOf g n b), ∃ x : ℕ, divisorFloor n b≤d ∧
      (d:ℤ)=firstOf g n b i.val + 2*(x:ℤ) ∧ x≤g*(2*radius b) := by
  obtain ⟨b,i,x,floor,pos,near⟩ := address pair nd ord cap
  let j : Fin (locationsOf g n b) := ⟨i.val/g,by
    have hi := i.isLt
    have enough : i.val+g ≤ count n b+(g-1) := by omega
    have part : (i.val+g)/g ≤ (count n b+(g-1))/g := Nat.div_le_div_right enough
    rw [Nat.add_div_right _ positive] at part
    exact part⟩
  obtain ⟨y,eq,size⟩ := merge_address (start n b) (radius b) i.val g positive x near
  exact ⟨b,j,y,floor,pos.trans eq,size⟩

private lemma at_rank {r m n H D : ℕ} (hr : 0<r) (hn : 0<n) (kh : r-1≤H) (hd : 0<D)
    (room : n^(m+m.choose 2)*(r^r*BinomialDivisorScale.weights r H) < (D^m)^r) (t : ℤ) :
    ∃ F : ℤ[X], F≠0 ∧ F.roots.toFinset.card≤r-1 ∧ ∀ (x : ℕ) (d : ℤ), d∣(n:ℤ) →
      d∣(x:ℤ)-t → (D:ℤ)≤d → IsCoprime d ((r-1).factorial:ℤ) → x≤H → F.eval (x:ℤ)=0 := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr.ne'
  refine BinomialDivisorWindow.relation_exists (k:=k) (m:=m) (n:=n) (H:=H) (D:=D) hn kh hd ?_ t
  simpa only [Fin.prod_univ_eq_prod_range,BinomialDivisorScale.weights] using room

private theorem at_location {n : ℕ} (big : 2^2047≤n) (parity : Odd n) (b : Bool) (i : ℕ) :
    ∃ F : ℤ[X], F≠0 ∧ F.roots.toFinset.card≤dimension-1 ∧ ∀ x d : ℕ,
      d.Prime → dimension-1<d → d∣n → d=first n b i+2*x → divisorFloor n b≤d →
      x≤span b → F.eval (x:ℤ)=0 := by
  let c := first n b i
  let t := ((n:ℤ)-c)/2
  have anchor : (n:ℤ) ∣ (c:ℤ)+2*t := by
    obtain ⟨s,hs⟩ := parity
    refine ⟨1,?_⟩
    dsimp only [c,t,first,firstOf]
    push_cast
    omega
  have fd : 0 < lower n := Nat.succ_pos _
  have dp : 0<divisorFloor n b := by
    cases b
    · exact fd
    · exact fd.trans_le (le_max_left ..)
  have wide : dimension-1≤span b := by cases b <;> decide +kernel
  obtain ⟨F,nz,rank,hit⟩ := at_rank (r:=dimension) (m:=multiplicity)
    (D:=divisorFloor n b) (H:=span b) (by decide) (lt_of_lt_of_le (by positivity) big)
    wide dp (BinomialDivisorScale.rooms (H:=span b) big b le_rfl).1 t
  refine ⟨F,nz,rank,?_⟩
  intro x d prime larger hd pos floor near
  have unit : IsCoprime (2:ℤ) (n:ℤ) := by exact_mod_cast (Nat.coprime_two_left.mpr parity).isCoprime
  have factor : (d:ℤ)∣(n:ℤ) := by exact_mod_cast hd
  exact hit x d factor (QuarticDivisorWindow.progression_offset unit anchor factor (by exact_mod_cast pos))
    (by exact_mod_cast floor) (BinomialDivisorWindow.prime_denominator prime larger) near

/-- One-sided binomial polynomials cover every smaller 1,024-bit prime at fewer
than 2^498 locations, each with 24,576 rows. -/
theorem feasible_cover {n : ℕ} (big : 2^2047≤n) (parity : Odd n) :
    locations n false+locations n true < 2^498 ∧
    ∃ F : (b : Bool) → Fin (locations n b) → ℤ[X],
      (∀ b i, F b i ≠ 0 ∧ (F b i).roots.toFinset.card<dimension) ∧
      ∀ d q : ℕ, n=d*q → d.Prime → Odd d → 2^1023≤d → d≤q → q<Q →
        ∃ b, ∃ i : Fin (locations n b), ∃ x : ℕ, d=first n b i.val+2*x ∧
          x≤span b ∧ (x:ℤ)∈(F b i).roots.toFinset := by
  classical
  choose F nz rank roots using at_location big parity
  refine ⟨merged_budget _ _ (center_budget big),fun b i => F b i.val,
    fun b i => ⟨nz _ _,Nat.lt_of_le_of_lt (rank _ _) (by decide)⟩,?_⟩
  intro d q pair prime odd bits ord cap
  obtain ⟨b,i,x,floor,pos,near⟩ := address_exists groupSize (by decide) pair odd ord cap
  have pn : d=first n b i.val+2*x := by exact_mod_cast pos
  have larger : dimension-1<d := (show dimension-1<2^1023 by decide +kernel).trans_le bits
  exact ⟨b,i,x,pn,by simpa only [span,←Nat.mul_assoc] using near,Multiset.mem_toFinset.mpr ((mem_roots (nz b i.val)).mpr
    (roots b i.val x d prime larger ⟨q,pair⟩ pn floor (by simpa only [span,←Nat.mul_assoc] using near)))⟩

private theorem count_floor (n T : ℕ) (bound : groupSize*T < count n false+count n true) :
    T < locations n false + locations n true := by
  dsimp only [locations,locationsOf,groupSize] at *
  omega

theorem control_counts :
    2^495<locations ChebyshevQuarticScale.fresh false+locations ChebyshevQuarticScale.fresh true ∧
    2^496<locations ChebyshevQuarticScale.crossed false+locations ChebyshevQuarticScale.crossed true := by
  exact ⟨count_floor _ _ ((show groupSize*2^495≤2^507 by decide +kernel).trans_lt
    FeasibleDivisorCover.control_counts.1.1),
    count_floor _ _ ((show groupSize*2^496≤2^508 by decide +kernel).trans_lt
    FeasibleDivisorCover.control_counts.2.1)⟩

/-- The signed binomial basis admits 5,359 old addresses in one centered window. -/
abbrev signedGroup : ℕ := 5359

def signedCenter (n : ℕ) (b : Bool) (i : ℕ) :=
  firstOf signedGroup n b i + 2*(signedGroup*radius b)

theorem signed_cover {n : ℕ} (big : 2^2047≤n) (parity : Odd n) :
    locationsOf signedGroup n false+locationsOf signedGroup n true < 2^497 ∧
    ∃ F : (b : Bool) → Fin (locationsOf signedGroup n b) → ℤ[X],
      (∀ b i, F b i ≠ 0 ∧ (F b i).roots.toFinset.card<dimension) ∧
      ∀ d q : ℕ, n=d*q → d.Prime → Odd d → 2^1023≤d → d≤q → q<Q →
        ∃ b, ∃ i : Fin (locationsOf signedGroup n b), ∃ x : ℤ,
          (d:ℤ)=signedCenter n b i.val+2*x ∧ |x|≤((signedGroup*radius b:ℕ):ℤ) ∧
          x∈(F b i).roots.toFinset := by
  classical
  have oddCenter (b : Bool) (i : ℕ) : Odd (signedCenter n b i) := by
    refine ⟨start n b+i*signedGroup*(2*radius b)+signedGroup*radius b,?_⟩
    dsimp only [signedCenter, firstOf]
    omega
  choose F nz rank roots using fun b i => CenteredBinomialDivisorWindow.at_center big parity b
    (signedCenter n b i) (oddCenter b i)
  constructor
  · have budget := center_budget big
    dsimp only [locationsOf,signedGroup]
    omega
  · refine ⟨fun b i => F b i.val,fun b i => ⟨nz _ _,Nat.lt_of_le_of_lt (rank _ _) (by decide)⟩,?_⟩
    intro d q pair prime odd bits ord cap
    obtain ⟨b,i,y,floor,pos,near⟩ := address_exists signedGroup (by decide) pair odd ord cap
    let x : ℤ := (y:ℤ)-(signedGroup*radius b:ℕ)
    have wide : y≤2*(signedGroup*radius b) := by simpa [Nat.mul_left_comm] using near
    have size : |x|≤((signedGroup*radius b:ℕ):ℤ) := abs_le.mpr (by dsimp only [x]; omega)
    have mid : (d:ℤ)=signedCenter n b i.val+2*x := by
      dsimp only [signedCenter,x]
      push_cast at pos ⊢
      linarith only [pos]
    have larger : dimension-1<d := (show dimension-1<2^1023 by decide +kernel).trans_le bits
    exact ⟨b,i,x,mid,size,Multiset.mem_toFinset.mpr ((mem_roots (nz b i.val)).mpr
      (roots b i.val x d prime larger ⟨q,pair⟩ mid floor size))⟩

private theorem signed_floor (n T : ℕ) (bound : signedGroup*T < count n false+count n true) :
    T < locationsOf signedGroup n false + locationsOf signedGroup n true := by
  dsimp only [locationsOf,signedGroup] at *
  omega

theorem signed_control_counts :
    2^494<locationsOf signedGroup ChebyshevQuarticScale.fresh false+
      locationsOf signedGroup ChebyshevQuarticScale.fresh true ∧
    2^495<locationsOf signedGroup ChebyshevQuarticScale.crossed false+
      locationsOf signedGroup ChebyshevQuarticScale.crossed true := by
  exact ⟨signed_floor _ _ ((show signedGroup*2^494≤2^507 by decide +kernel).trans_lt
    FeasibleDivisorCover.control_counts.1.1),
    signed_floor _ _ ((show signedGroup*2^495≤2^508 by decide +kernel).trans_lt
    FeasibleDivisorCover.control_counts.2.1)⟩

end PrimeFactors.BinomialDivisorCover
