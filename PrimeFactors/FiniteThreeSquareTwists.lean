import PrimeFactors.SplittingGuessPrimes
import PrimeFactors.ThreeSquareRadiusCounts

/-! Three-square representation counts at a fixed finite list of positive
twists. The classical input is the single-prime recurrence in equation (4)
of Hirschhorn and Sellers, *On representations of a number as a sum of three
squares* (1999). They also attribute this identity to G. Pall. -/

namespace PrimeFactors.FiniteThreeSquareTwists

open Finset
open private PrimeFactors.ThreeSquareRadiusCounts.signs
  PrimeFactors.ThreeSquareRadiusCounts.slice from PrimeFactors.ThreeSquareRadiusCounts

/-- Number of ordered, signed integral representations of an arbitrary target
as three squares, allowing zero coordinates. Once x and y are fixed in
magnitude, their nonnegative third coordinate is unique if it exists. -/
noncomputable def r₃ (n : ℕ) : ℕ :=
  ∑ x ∈ range (n.sqrt+1), ∑ y ∈ range (n.sqrt+1),
    let z := (n-x^2-y^2).sqrt
    if x^2+y^2+z^2=n then
      PrimeFactors.ThreeSquareRadiusCounts.signs x *
        PrimeFactors.ThreeSquareRadiusCounts.signs y *
        PrimeFactors.ThreeSquareRadiusCounts.signs z else 0

/-- At a perfect square this is the repository's unfiltered sphere count. -/
theorem radius (n : ℕ) : r₃ (n^2)=ThreeSquareRadiusCounts.count n false := by
  simp [r₃, ThreeSquareRadiusCounts.count, PrimeFactors.ThreeSquareRadiusCounts.slice,
    pow_two,Nat.sqrt_eq]

/-- Hirschhorn–Sellers equation (4). A nonintegral argument in the final
representation count contributes zero. For a prime denominator the Jacobi
symbol here agrees with the Legendre symbol in the paper. -/
def HirschhornSellers : Prop :=
  ∀ p n : ℕ, p.Prime → Odd p →
    (r₃ (p^2*n) : ℤ) = ((p:ℤ)+1-jacobiSym (-(n:ℤ)) p)*r₃ n -
      (if p^2∣n then (p:ℤ)*r₃ (n/p^2) else 0)

private theorem split_step (formula : HirschhornSellers) {p n : ℕ}
    (pp : p.Prime) (op : Odd p) (unit : ¬p∣n) (square : IsSquare (-(n:ZMod p))) :
    r₃ (p^2*n)=p*r₃ n := by
  letI : Fact p.Prime := ⟨pp⟩
  have nz : (n:ZMod p)≠0 := by simpa only [ne_eq,ZMod.natCast_zmod_eq_zero_iff_dvd] using unit
  have chi : jacobiSym (-(n:ℤ)) p=1 := by
    rw [←jacobiSym.legendreSym.to_jacobiSym]
    apply (legendreSym.eq_one_iff p (by simpa using nz : ((-(n:ℤ):ℤ):ZMod p)≠0)).2
    simpa using square
  have h := formula p n pp op
  have no : ¬p^2∣n := fun h => unit ((dvd_pow_self p (by decide : 2≠0)).trans h)
  rw [chi, if_neg no] at h
  exact_mod_cast (by simpa using h : (r₃ (p^2*n):ℤ)=(p:ℤ)*r₃ n)

/-- One common arithmetic progression splits every negative twist. -/
theorem negative_squares (S : Finset ℕ) (positive : ∀ d∈S, 0<d) {p : ℕ} (pp : p.Prime)
    (ap : p % (8*∏ d∈S,d) = 1) :
    Odd p ∧ ∀ d∈S, ¬p∣d ∧ IsSquare (-(d:ZMod p)) := by
  letI : Fact p.Prime := ⟨pp⟩
  have four : p%4=1 := by
    have dv : 4 ∣ 8*∏ d∈S,d := ⟨2*∏ d∈S,d,by ring⟩
    rw [←Nat.mod_mod_of_dvd p dv,ap]
  refine ⟨Nat.odd_iff.mpr (Nat.odd_of_mod_four_eq_one four), ?_⟩
  intro d hd
  have pos := positive d hd
  have div := Nat.mul_dvd_mul_left 8 (dvd_prod_of_mem (fun x : ℕ => x) hd)
  have rem : p%(8*d)=1 := by rw [←Nat.mod_mod_of_dvd p div,ap,Nat.mod_eq_of_lt (by omega : 1<8*d)]
  obtain ⟨unit,sq⟩ := SplittingGuessPrimes.square_of_one pos pp rem
  have minus : IsSquare (-1 : ZMod p) := ZMod.exists_sq_eq_neg_one_iff.mpr (by omega)
  exact ⟨unit,by simpa using minus.mul sq⟩

/-- For any two distinct primes in the displayed progression the entire
vector of counts is the known vector of base counts multiplied by pq. -/
theorem menu_at_primes (formula : HirschhornSellers) (S : Finset ℕ)
    (positive : ∀ d∈S, 0<d) {p q : ℕ} (pp : p.Prime) (qp : q.Prime) (ne : p≠q)
    (ap : p%(8*∏ d∈S,d)=1) (aq : q%(8*∏ d∈S,d)=1) :
    ∀ d∈S, r₃ (d*(p*q)^2)=(p*q)*r₃ d := by
  obtain ⟨op,hp⟩ := negative_squares S positive pp ap
  obtain ⟨oq,hq⟩ := negative_squares S positive qp aq
  intro d hd
  obtain ⟨pu,ps⟩ := hp d hd
  obtain ⟨qu,qs⟩ := hq d hd
  have qpunit : ¬q∣p := fun dv => ne ((pp.dvd_iff_eq qp.ne_one).mp dv)
  have funit : ¬q∣p^2*d := fun dv =>
    (qp.dvd_mul.mp dv).elim (fun h => qpunit (qp.dvd_of_dvd_pow h)) qu
  have fsquare : IsSquare (-((p^2*d:ℕ):ZMod q)) := by
    have square : IsSquare ((p:ZMod q)^2) := ⟨p,by ring⟩
    simpa only [Nat.cast_mul,Nat.cast_pow,mul_neg] using square.mul qs
  rw [show d*(p*q)^2=q^2*(p^2*d) by ring,split_step formula qp oq funit fsquare,
    split_step formula pp op pu ps]
  ring

/-- A finite set separated by a factor of two has a bounded reciprocal sum. -/
private theorem separated_sum (T : Finset ℕ) {c : ℕ} (pos : 0<c)
    (low : ∀ a∈T, c≤a) (sep : ∀ a∈T, ∀ b∈T, a<b → 2*a≤b) :
    (∑ a∈T, (1:ℝ)/a)≤2/c := by
  induction T using Finset.induction_on_min generalizing c with
  | h0 => simp; positivity
  | step a T smallest ih =>
    have amin : c≤a := low a (mem_insert_self ..)
    have apos : 0<a := pos.trans_le amin
    have tail := ih (c:=2*a) (by omega)
      (fun b hb => sep a (mem_insert_self ..) b (mem_insert_of_mem hb) (smallest b hb))
      (fun x hx y hy => sep x (mem_insert_of_mem hx) y (mem_insert_of_mem hy))
    have an : a∉T := fun h => (smallest a h).false
    rw [sum_insert an]
    calc
      _ ≤ 1/(a:ℝ)+2/(2*a:ℕ) := add_le_add_left tail _
      _ = 2/(a:ℝ) := by push_cast; ring
      _ ≤ 2/(c:ℝ) := div_le_div_of_nonneg_left (by norm_num)
        (by exact_mod_cast pos) (by exact_mod_cast amin)

/-- The divergence of reciprocal primes in the progression gives balanced
pairs beyond every bound. Otherwise the entire tail would be separated by
factors of at least two. -/
theorem balanced_primes {m : ℕ} (hm : 1<m) (cut : ℕ) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ cut<p ∧ p<q ∧ q<2*p ∧ p%m=1 ∧ q%m=1 := by
  classical
  letI : NeZero m := ⟨by omega⟩
  let f := SplittingGuessPrimes.reciprocal (1:ZMod m)
  by_contra none
  apply SplittingGuessPrimes.not_summable_progression (q:=m) (a:=1) isUnit_one
  apply summable_of_sum_range_le (c:=(∑ p∈range (cut+1),(1:ℝ)/p)+2)
  · intro p; dsimp [SplittingGuessPrimes.reciprocal]; split <;> positivity
  intro k
  let U := (range k).filter fun p : ℕ => p.Prime ∧ (p:ZMod m)=1
  let V := U ∩ range (cut+1)
  have count : (∑ p∈range k, f p) = ∑ p∈U,(1:ℝ)/p := by
    dsimp only [U]
    rw [sum_filter]
    rfl
  rw [show (∑ p∈range k, SplittingGuessPrimes.reciprocal (1:ZMod m) p)=_ from count]
  have small : (∑ p∈V,(1:ℝ)/p)≤∑ p∈range (cut+1),(1:ℝ)/p :=
    sum_le_sum_of_subset_of_nonneg (inter_subset_right : V ⊆ _) (fun _ _ _ => by positivity)
  have valid (p : ℕ) (h : p∈U\V) : p.Prime ∧ cut<p ∧ p%m=1 := by
    obtain ⟨u,v⟩ := mem_sdiff.mp h
    obtain ⟨pp, rem⟩ := (mem_filter.mp u).2
    have eq := (ZMod.natCast_eq_natCast_iff' p 1 m).mp (by simpa only [Nat.cast_one] using rem)
    rw [Nat.mod_eq_of_lt hm] at eq
    refine ⟨pp, ?_,eq⟩
    by_contra! le
    exact v (mem_inter.mpr ⟨u,mem_range.mpr (by omega)⟩)
  have bound := separated_sum (U\V) (c:=1) (by decide)
    (fun p hp => (valid p hp).1.pos) (by
      intro p hp q hq lt
      obtain ⟨pp,pc,pr⟩ := valid p hp
      obtain ⟨qp,_,qr⟩ := valid q hq
      exact le_of_not_gt (fun bal => none ⟨p,q,pp,qp,pc,lt,bal,pr,qr⟩))
  simp only [Nat.cast_one,div_one] at bound
  have combined := sum_sdiff (f:=fun p : ℕ => (1:ℝ)/p) (inter_subset_left : V⊆U)
  linarith only [small,bound,combined]

/-- No finite list of preselected positive twists distinguishes the two
prime factors throughout this infinite balanced family. Only the public
product times the twist's own base count appears in each entry. -/
theorem fixed_menu (formula : HirschhornSellers) (S : Finset ℕ)
    (positive : ∀ d∈S, 0<d) (cut : ℕ) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ cut<p ∧ p<q ∧ q<2*p ∧
      ∀ d∈S, r₃ (d*(p*q)^2)=(p*q)*r₃ d := by
  have pos : 0<∏ d∈S,d := prod_pos positive
  obtain ⟨p,q,pp,qp,lo,lt,bal,ap,aq⟩ := balanced_primes (by omega : 1<8*∏d∈S,d) cut
  exact ⟨p,q,pp,qp,lo,lt,bal,menu_at_primes formula S positive pp qp lt.ne ap aq⟩

/-- At the single prime 3, the positive twists 2 and 5 scale by 3, while
the untwisted count scales by 5. All six counts come directly from coordinates. -/
theorem small_counts : r₃ 2=12 ∧ r₃ 18=36 ∧ r₃ 5=24 ∧ r₃ 45=72 ∧
    r₃ 1=6 ∧ r₃ 9=30 := by decide +kernel

end PrimeFactors.FiniteThreeSquareTwists
