import PrimeFactors.DyadicTotativeMasks
import PrimeFactors.GrowingFactorial

/-! Dyadic factorial-ratio readouts up to the first differing bit can be evaluated
by disjoint ordinary divisor intervals. Their endpoints use only the product. -/
namespace PrimeFactors.DyadicFactorBands
open Finset DyadicTotativeMasks

def lowerCut (n d : ℕ) : ℕ :=
  max (n.sqrt/d*d) (n/((n.sqrt/d+1)*d)+1)

def cut (n j : ℕ) : ℕ := lowerCut n (2^j)

private theorem root_bounds {p q : ℕ} (order : p<q) :
    p ≤ (p*q).sqrt ∧ (p*q).sqrt < q := by
  exact ⟨Nat.le_sqrt.mpr (Nat.mul_le_mul_left p order.le),
    Nat.sqrt_lt.mpr (Nat.mul_lt_mul_of_pos_right order (by omega))⟩

/-- For any positive cell width, both factors fall in the same cell exactly
when the smaller prime clears this public threshold. Primality is unnecessary. -/
theorem same_cell {p q d : ℕ} (pos : 0<p) (order : p<q) (hd : 0<d) :
    p/d=q/d ↔ lowerCut (p*q) d≤p := by
  let k := (p*q).sqrt/d
  have r := root_bounds order
  have left : p/d≤k := Nat.div_le_div_right r.1
  have right : k≤q/d := Nat.div_le_div_right r.2.le
  have dpos : 0<(k+1)*d := Nat.mul_pos (Nat.succ_pos k) hd
  change p/d=q/d ↔ max (k*d) (p*q/((k+1)*d)+1)≤p
  rw [max_le_iff]
  constructor
  · intro eq
    have pk : k≤p/d := by omega
    have qk : q/d<k+1 := by omega
    have below := (Nat.div_lt_iff_lt_mul hd).mp qk
    have product : p*q < p*((k+1)*d) := Nat.mul_lt_mul_of_pos_left below pos
    exact ⟨(Nat.le_div_iff_mul_le hd).mp pk, (Nat.div_lt_iff_lt_mul dpos).mpr product⟩
  · rintro ⟨pl,qh⟩
    have pk := (Nat.le_div_iff_mul_le hd).mpr pl
    have product := (Nat.div_lt_iff_lt_mul dpos).mp (show p*q/((k+1)*d)<p by omega)
    have qk := (Nat.div_lt_iff_lt_mul hd).mpr (Nat.lt_of_mul_lt_mul_left product)
    omega

theorem nested (n j : ℕ) : cut n (j+1) ≤ cut n j := by
  let d := 2^j
  let k := n.sqrt/d
  have coarse : n.sqrt/(2*d)=k/2 := by simp [k,Nat.div_div_eq_div_mul,mul_comm]
  have count : k/2*2≤k := by omega
  have count' : k+1≤(k/2+1)*2 := by omega
  have gap : 0<(k+1)*d := Nat.mul_pos (by omega) (pow_pos (by decide) _)
  unfold cut lowerCut
  rw [pow_succ, mul_comm (2^j) 2]
  change max (n.sqrt/(2*d)*(2*d)) (n/((n.sqrt/(2*d)+1)*(2*d))+1) ≤
    max (k*d) (n/((k+1)*d)+1)
  rw [coarse]
  apply max_le_max
  · rw [←mul_assoc]; exact Nat.mul_le_mul_right _ count
  · apply Nat.add_le_add_right
    apply Nat.div_le_div_left _ gap
    rw [←mul_assoc]; exact Nat.mul_le_mul_right _ count'

/-- The smaller factor lies in this band precisely when the current binary
digits differ and all higher digits agree. The smaller factor's digit is zero. -/
theorem band_criterion {p q j : ℕ} (pos : 0<p) (order : p<q) :
    (cut (p*q) (j+1)≤p ∧ p<cut (p*q) j) ↔
    (endpoint p (j+1)=endpoint q (j+1) ∧ digit p j=0 ∧ digit q j=1) := by
  have coarse := same_cell (d:=2^(j+1)) pos order (pow_pos (by decide) _)
  have fine := same_cell (d:=2^j) pos order (pow_pos (by decide) _)
  change (lowerCut (p*q) _≤p ∧ p<lowerCut (p*q) _) ↔ _
  have strict : p<lowerCut (p*q) (2^j) ↔ (p/2^j≠q/2^j) := (lt_iff_not_ge _ _).trans fine.not.symm
  rw [←coarse,strict]
  simp only [endpoint,digit,pow_succ,←Nat.div_div_eq_div_mul]
  have le : p/2^j≤q/2^j := Nat.div_le_div_right order.le
  omega

/-- Wheel candidates in the half-open band, clipped to the supplied
smaller-factor interval. -/
noncomputable def band (n lo wheel j : ℕ) : Finset ℕ :=
  (Ico (max lo (cut n (j+1))) (min (n.sqrt+1) (cut n j))).filter
    (fun x => x.Coprime wheel)

private theorem in_band {p q lo wheel j : ℕ} (order : p<q)
    (low : lo≤p) (cop : p.Coprime wheel) :
    p ∈ band (p*q) lo wheel j ↔ cut (p*q) (j+1)≤p ∧ p<cut (p*q) j := by
  have bound := (root_bounds order).1
  simp only [band,mem_filter,mem_Ico,max_le_iff,lt_min_iff]
  have upper : p<(p*q).sqrt+1 := by omega
  tauto

/-- The wheel product returns the smaller factor on its unique band and one
on other bands. The product can be computed modulo the input throughout. -/
theorem band_gcd {p q lo wheel j : ℕ} (pp : p.Prime) (qp : q.Prime) (order : p<q)
    (balanced : q≤2*p) (loPos : 0<lo) (low : lo≤p) (cop : (p*q).Coprime wheel) :
    (p*q).gcd (band (p*q) lo wheel j).toList.prod =
      if cut (p*q) (j+1)≤p ∧ p<cut (p*q) j then p else 1 := by
  let s := band (p*q) lo wheel j
  have valid (x : ℕ) (hx : x∈s.toList) : 0<x ∧ x≤(p*q).sqrt := by
    obtain ⟨xl,xh⟩ := mem_Ico.mp (mem_filter.mp (Finset.mem_toList.mp hx)).1
    exact ⟨loPos.trans_le (le_max_left .. |>.trans xl), by have := xh.trans_le (min_le_left ..); omega⟩
  rw [GrowingFactorial.membership pp qp order balanced _ valid]
  simp only [s,mem_toList,in_band order low (Nat.coprime_mul_iff_left.mp cop).1]

/-- All bands use distinct integer candidates, even before applying a gcd. -/
theorem disjoint_bands {n lo wheel i j : ℕ} (lt : i<j) :
    Disjoint (band n lo wheel i) (band n lo wheel j) := by
  have anti : Antitone (cut n) := antitone_nat_of_succ_le (nested n)
  apply disjoint_left.mpr
  intro x hx hy
  obtain ⟨left,_⟩ := mem_Ico.mp (mem_filter.mp hx).1
  obtain ⟨_,right⟩ := mem_Ico.mp (mem_filter.mp hy).1
  have a := (le_max_right ..).trans left
  have b := right.trans_le (min_le_right ..)
  have c := anti (show i+1≤j by omega)
  omega

/-- The total count of wheel candidates over any choice of bit positions
is at most the ordinary wheel count in the original smaller-factor box. -/
theorem total_candidates (n lo wheel : ℕ) (indices : Finset ℕ) :
    ∑ j ∈ indices, (band n lo wheel j).card ≤
      ((Icc lo n.sqrt).filter (fun x => x.Coprime wheel)).card := by
  have disjoint : indices.toSet.PairwiseDisjoint (band n lo wheel) := by
    intro i _ j _ ne
    rcases lt_or_gt_of_ne ne with h | h
    · exact disjoint_bands h
    · exact (disjoint_bands h).symm
  rw [←card_biUnion disjoint]
  apply card_le_card
  intro x hx
  obtain ⟨j,_,hx⟩ := mem_biUnion.mp hx
  obtain ⟨bounds,unit⟩ := mem_filter.mp hx
  obtain ⟨a,b⟩ := mem_Ico.mp bounds
  have low := (le_max_left ..).trans a
  have high := b.trans_le (min_le_left ..)
  exact mem_filter.mpr ⟨mem_Icc.mpr ⟨low,by omega⟩,unit⟩

/-- Before either factor departs from the square root's common prefix, the
next factorial-ratio gcd equals the current interval gcd, or the public value
one or N if that interval misses. -/
def read (n j g : ℕ) : ℕ := if g=1 then (if digit n.sqrt j=1 then n else 1) else g

theorem reproduces_ratio {p q lo wheel j : ℕ} (pp : p.Prime) (qp : q.Prime) (order : p<q)
    (balanced : q<2*p) (loPos : 0<lo) (low : lo≤p) (cop : (p*q).Coprime wheel)
    (hj : 1≤j) (common : cut (p*q) (j+1)≤p) :
    read (p*q) j ((p*q).gcd (band (p*q) lo wheel j).toList.prod) =
      (coefficient (endpoint (p*q) j)).gcd (p*q) := by
  rw [band_gcd pp qp order balanced.le loPos low cop,gcd_mask pp qp order balanced hj]
  by_cases miss : cut (p*q) j≤p
  · have eq := (same_cell pp.pos order (pow_pos (by decide : 0<2) j)).mpr miss
    have r := root_bounds order
    have a : p/2^j≤(p*q).sqrt/2^j := Nat.div_le_div_right r.1
    have b : (p*q).sqrt/2^j≤q/2^j := Nat.div_le_div_right r.2.le
    have e : p/2^j=(p*q).sqrt/2^j := by omega
    have f : q/2^j=(p*q).sqrt/2^j := by omega
    simp only [not_lt.mpr miss,and_false,if_false,read,if_pos rfl,digit,endpoint,e,f]
    split_ifs <;> simp
  · have inside : cut (p*q) (j+1)≤p ∧ p<cut (p*q) j := ⟨common,by omega⟩
    obtain ⟨_,a,b⟩ := (band_criterion pp.pos order).mp inside
    simp [inside,read,pp.ne_one,a,b]

private theorem threshold_crossing {f : ℕ → ℕ} {x : ℕ} (k : ℕ)
    (last : x<f 1) (first : f (k+1)≤x) :
    ∃ j, 1≤j ∧ j≤k ∧ f (j+1)≤x ∧ x<f j := by
  induction k with
  | zero => exact (not_lt_of_ge first last).elim
  | succ k ih =>
    by_cases coarse : f (k+1)≤x
    · obtain ⟨j,hj,hk,band⟩ := ih coarse
      exact ⟨j,hj,by omega,band⟩
    · exact ⟨k+1,by omega,le_rfl,first,by omega⟩

/-- Between the known equal leading bit and equal odd units bits, exactly
one band contains the smaller prime. -/
theorem exists_unique_band {p q k lo wheel : ℕ} (pp : p.Prime) (order : p<q)
    (oddP : p%2=1) (oddQ : q%2=1) (loP : 2^(k+1)≤p) (hiQ : q<2^(k+2))
    (low : lo≤p) (cop : (p*q).Coprime wheel) :
    ∃! j, (1≤j ∧ j≤k) ∧ p∈band (p*q) lo wheel j := by
  have sm := same_cell (d:=2) pp.pos order (by decide)
  have stop : p<cut (p*q) 1 := by
    change p<lowerCut (p*q) 2
    exact lt_of_not_ge (fun h => by have := sm.mpr h; omega)
  have eq : p/2^(k+1)=q/2^(k+1) := by
    rw [show k+2=(k+1)+1 by omega,pow_succ] at hiQ
    have ep : p/2^(k+1)=1 := Nat.div_eq_of_lt_le (by simpa using loP)
      (by simpa [mul_comm] using order.trans hiQ)
    have eq : q/2^(k+1)=1 := Nat.div_eq_of_lt_le (by simpa using loP.trans order.le)
      (by simpa [mul_comm] using hiQ)
    exact ep.trans eq.symm
  have start := (same_cell pp.pos order (pow_pos (by decide : 0<2) (k+1))).mp eq
  obtain ⟨j,hj,top,hit⟩ := threshold_crossing (f:=cut (p*q)) k stop start
  have member := (in_band (j:=j) order low (Nat.coprime_mul_iff_left.mp cop).1).mpr hit
  refine ⟨j,⟨⟨hj,top⟩,member⟩,?_⟩
  intro i hi
  rcases lt_trichotomy i j with h | h | h
  · exact ((disjoint_left.mp (disjoint_bands h)) hi.2 member).elim
  · exact h
  · exact ((disjoint_left.mp (disjoint_bands h)) member hi.2).elim

/-- If the product is at least three quarters of the square of the top
factor bound, both factors have their next binary digit set. The first
eligible ratio gcd is the whole input without any interval multiplication. -/
theorem upper_quarter_mask {p q j : ℕ} (pp : p.Prime) (qp : q.Prime) (order : p<q)
    (hj : 1≤j) (high : q<4*2^j) (large : 3*2^j*(4*2^j)≤p*q) :
    (coefficient (endpoint (p*q) j)).gcd (p*q)=p*q := by
  let d := 2^j
  have dp : 0<d := pow_pos (by decide) _
  have lo : 3*d≤p := by
    by_contra! small
    have a := Nat.mul_lt_mul_of_pos_right small qp.pos
    have b := Nat.mul_le_mul_left (3*d) (show q≤4*d from high.le)
    exact (not_lt_of_ge large) (a.trans_le b)
  have below : q<4*d := high
  have bal : q<2*p := by omega
  have p3 : p/d=3 := Nat.div_eq_of_lt_le lo (order.trans below)
  have q3 : q/d=3 := Nat.div_eq_of_lt_le (lo.trans order.le) below
  rw [gcd_mask pp qp order bal hj]
  change (if q/d%2=1 then p else 1)*(if p/d%2=1 then q else 1)=_
  simp [p3,q3]

end PrimeFactors.DyadicFactorBands
