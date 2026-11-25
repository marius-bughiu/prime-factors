import PrimeFactors.RecursiveUnitWindows
import PrimeFactors.UnitWindowCover
import PrimeFactors.BinomialDivisorCover
import PrimeFactors.IntegerLaneWindowWork

/-! Full coverage for balanced semiprimes using the recursively rounded rows. -/

namespace PrimeFactors.RecursiveUnitCover

open Polynomial UnitWindowCover CoupledDivisorWindow
open ChebyshevQuarticScale (fresh crossed)

set_option exponentiation.threshold 8192
set_option maxRecDepth 16000

abbrev width : ℕ := 2^526

/-- The complete list depends only on the public number. Every possible smaller
factor lands in one of these windows and is a root of its corresponding equation. -/
theorem full {n : ℕ} (big : 2^2047≤n) (odd : Odd n)
    (cop : n.Coprime (ThreeUnitFactorialWindows.denominator 24575)) :
    locations n width<2^495 ∧ ∃ F : Fin (locations n width) → ℤ[X],
      (∀ i, F i≠0 ∧ (F i).roots.toFinset.card≤24575) ∧ ∀ d q : ℕ, n=d*q →
      Odd d → d≤q → q≤2^1024 → ∃ i x, d=first n width i.val+2*x ∧
      x≤width ∧ (F i).eval (x:ℤ)=0 := by
  refine ⟨count_lt big (by decide +kernel),cover ?_⟩
  intro c hc
  let t := ((n:ℤ)-c)/2
  have anc : (n:ℤ)∣(c:ℤ)+2*t := by
    obtain ⟨b,hb⟩ := odd
    obtain ⟨a,ha⟩ := hc
    exact ⟨1,by dsimp only [t];omega⟩
  obtain ⟨F,nz,card,hit⟩ := RecursiveUnitWindows.uniform_window big cop
    (Nat.coprime_two_left.mpr odd).isCoprime anc
  refine ⟨F,nz,card,?_⟩
  intro x d div pos floor near
  exact hit x d (by exact_mod_cast div) (by exact_mod_cast pos) (by exact_mod_cast floor) near

/-- The standard two-prime input supplies all parity and coprimality hypotheses. -/
theorem balanced {n p q : ℕ} (pair : n=p*q) (big : 2^2047≤n) (hp : p.Prime) (hq : q.Prime)
    (bits : 2^1023≤p) (ord : p≤q) (cap : q<2^1024) :
    locations n width<2^495 ∧ ∃ F : Fin (locations n width) → ℤ[X],
      (∀ i, F i≠0 ∧ (F i).roots.toFinset.card≤24575) ∧
      ∃ i x, p=first n width i.val+2*x ∧ x≤width ∧ (F i).eval (x:ℤ)=0 := by
  have above : 24575<p := (by decide +kernel : 24575<2^1023).trans_le bits
  have op := hp.odd_of_ne_two (by omega)
  have oq := hq.odd_of_ne_two (by omega)
  have cp := coprime_denominator hp above (by omega)
  have cq := coprime_denominator hq (above.trans_le ord) (by omega)
  obtain ⟨count,F,nz,hit⟩ := full big (pair ▸ Nat.odd_mul.mpr ⟨op,oq⟩) (pair ▸ Nat.coprime_mul_iff_left.mpr ⟨cp,cq⟩)
  exact ⟨count,F,nz,hit p q pair op ord cap.le⟩

def previousLocations (n : ℕ) := BinomialDivisorCover.locationsOf 5359 n false +
  BinomialDivisorCover.locationsOf 5359 n true

private def freshRoot : ℕ := 158327039176966334715448284019718823474497913662177975160442996009439310669941017429676080400185006424773254142252582891257193029659269227070095120289800339855421063931472090621260003180611046788905349147963313017385074143012442899089952314244753217806428276920663827209779196401916113023989449483782760844629
private def crossedRoot : ℕ := 135037911685235586269825030135549325391376915966798636179319977077209993450011760943044181307768476527897818717675959823440307553022185653953812606479930673789391793187765141283074720630433120513417190939648203494531748575804685158519937612233285802863014656458801051235008057526662884995918450838938076904614

private def countAt (n u : ℕ) := ((u+1)/2-start n+width)/(width+1)

private def oldRegionAt (n u : ℕ) (b : Bool) :=
  let cap := if b then u/2+1 else min (u/2+1) FeasibleDivisorCover.cut
  let stride := 2*FeasibleDivisorCover.radius b
  let blocks := (cap-FeasibleDivisorCover.start n b+(stride-1))/stride
  (blocks+5358)/5359

private theorem checked {n u e : ℕ} (root : u*u≤n ∧ n<(u+1)*(u+1))
    (arithmetic : let a := countAt n u
                  let b := oldRegionAt n u false + oldRegionAt n u true
                  2^e<a ∧ a<2^(e+1) ∧ 3*a<b ∧ b<4*a) :
    2^e<locations n width ∧ locations n width<2^(e+1) ∧
    3*locations n width<previousLocations n ∧ previousLocations n<4*locations n width := by
  have hr : n.sqrt=u := (Nat.eq_sqrt.mpr root).symm
  have ne : locations n width=countAt n u := by unfold locations positions stop countAt;rw [hr]
  have old (b : Bool) : BinomialDivisorCover.locationsOf 5359 n b=oldRegionAt n u b := by
    unfold BinomialDivisorCover.locationsOf FeasibleDivisorCover.count FeasibleDivisorCover.stop oldRegionAt
    rw [hr]
  simpa only [ne,previousLocations,old] using arithmetic

/-- Actual input-only window counts, including the short last block. -/
theorem control_counts :
    2^493<locations fresh width ∧ locations fresh width<2^494 ∧
    2^494<locations crossed width ∧ locations crossed width<2^495 ∧
    3*locations fresh width<previousLocations fresh ∧ previousLocations fresh<4*locations fresh width ∧
    3*locations crossed width<previousLocations crossed ∧ previousLocations crossed<4*locations crossed width := by
  have f := checked (n:=fresh) (e:=493) (u:=freshRoot)
    (by decide +kernel) (by decide +kernel)
  have c := checked (n:=crossed) (e:=494) (u:=crossedRoot)
    (by decide +kernel) (by decide +kernel)
  exact ⟨f.1,f.2.1,c.1,c.2.1,f.2.2.1,f.2.2.2,c.2.2.1,c.2.2.2⟩

private def laneSize (n u : ℕ) :=
  ((u-1)/6+1) - (((n+2^1024-2)/(2^1024-1)+4)/6)

private theorem domain_size (n u : ℕ) : (IntegerLaneWindowWork.domain n 3 u).card=laneSize n u := by
  simp only [IntegerLaneWindowWork.domain,Nat.card_Ico,laneSize]
  have ar (a : ℕ) : a+2*3-2=a+4 := by omega
  simp only [ar]

private theorem price {n u J ratio : ℕ} (root : u*u≤n ∧ n<(u+1)*(u+1))
    (receipt : (2*J)*(100*24576*countAt n u) < ratio*laneSize n u) :
    (2*J)*(100*24576*locations n width) < ratio*laneSize n n.sqrt := by
  have hr : n.sqrt=u := (Nat.eq_sqrt.mpr root).symm
  unfold locations positions stop
  rw [hr]
  exact receipt

/-- All degrees, window positions and bases can vary across the comparison
sweep. Every chosen column must be integer-valued and bounded along the tested lane. -/
def CostBound (n ratio : ℕ) (ι : Type*) [DecidableEq ι] : Prop :=
  ∀ (runs : Finset ι) (firstSlot len k m D : ι → ℕ) (w : ∀ i, IntegerLaneWindowWork.Lane (k i) (len i)),
    (IntegerLaneWindowWork.domain n 3 n.sqrt ⊆ runs.biUnion (fun i => Finset.Ico (firstSlot i) (firstSlot i+len i))) →
    (∀ i∈runs, D i^2≤n ∧ m i≤k i ∧ n^(m i+(m i).choose 2)*(∏ j,(w i).weight j)<D i^(m i*(k i+1))) →
    100*24576*locations n width < ratio*(∑ i∈runs,k i)

private theorem compare {n u J ratio : ℕ} (ι : Type*) [DecidableEq ι] (hn : 0<n) (hj : 0<J)
    (up : n≤J^4) (root : u*u≤n ∧ n<(u+1)*(u+1))
    (receipt : (2*J)*(100*24576*countAt n u) < ratio*laneSize n u) : CostBound n ratio ι := by
  intro runs firstSlot len k m D w covers passes
  have lower := IntegerLaneWindowWork.cover (n:=n) hj _ runs firstSlot len k m D w covers (by
    intro i hi
    obtain ⟨floor,depth,pass⟩ := passes i hi
    exact ⟨floor,depth,pass,IntegerLaneWindowWork.fourth_root hn up depth⟩)
  rw [domain_size] at lower
  have bound := (price root receipt).trans_le (Nat.mul_le_mul_left ratio lower)
  apply Nat.lt_of_mul_lt_mul_left (a:=2*J)
  exact bound.trans_eq (mul_left_comm ..)

/-- On the two controls, the new dense schedule is within factors of 8.45
and 7.81 of any full determinant-qualified cover on the mod-3 lane. -/
theorem compare_all_bases (ι : Type*) [DecidableEq ι] : CostBound fresh 845 ι ∧ CostBound crossed 781 ι := by
  constructor
  · exact compare (n:=fresh) (u:=freshRoot) (J:=3844*2^500) ι (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact compare (n:=crossed) (u:=crossedRoot) (J:=3551*2^500) ι (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

end PrimeFactors.RecursiveUnitCover
