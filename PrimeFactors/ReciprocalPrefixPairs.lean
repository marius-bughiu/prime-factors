import Mathlib.Tactic
import Mathlib.Data.Nat.ModEq
import PrimeFactors.Certificate
import PrimeFactors.DisplacedTraceCoverage
import PrimeFactors.WeightedCrowdingEstimates

/-! Project paired rational intervals for the reciprocals M/p and M/q onto
the smaller coordinate. Ordered prefix partitions have only linearly many
compatible pairs. Separate coordinate residue checks have a matching limit. -/
namespace PrimeFactors.ReciprocalPrefixPairs
open Finset

/-- The rational interval [a/b,c/d). -/
structure Bracket where
  a : ℕ
  b : ℕ
  c : ℕ
  d : ℕ

def Bracket.Contains (h : Bracket) (v w : ℕ) :=
  h.a*w ≤ v*h.b ∧ v*h.d < h.c*w

def lower (n m : ℕ) (h j : Bracket) :=
  max (m*h.d/h.c+1) ((j.a*n-1)/(m*j.b)+1)

def upper (n m : ℕ) (h j : Bracket) :=
  min (m*h.b/h.a) ((j.c*n-1)/(m*j.d))

/-- The two bracket conditions on M/p and Mp/N give one exact integer interval.
All four endpoint computations use public integers. -/
theorem projection {n m : ℕ} {h j : Bracket}
    (hn : 0<n) (hm : 0<m) (ha : 0<h.a) (hc : 0<h.c)
    (ja : 0<j.a) (jb : 0<j.b) (jc : 0<j.c) (jd : 0<j.d) (p : ℕ) :
    h.Contains m p ∧ j.Contains (m*p) n ↔ p∈Icc (lower n m h j) (upper n m h j) := by
  simp only [Bracket.Contains,mem_Icc,lower,upper,max_le_iff,le_min_iff]
  have l₁ : m*h.d/h.c+1≤p ↔ m*h.d<h.c*p := by
    rw [Nat.succ_le_iff,Nat.div_lt_iff_lt_mul hc,mul_comm p h.c]
  have l₂ : (j.a*n-1)/(m*j.b)+1≤p ↔ j.a*n≤m*p*j.b := by
    rw [Nat.succ_le_iff,Nat.div_lt_iff_lt_mul (Nat.mul_pos hm jb)]
    have := Nat.mul_pos ja hn
    rw [show p*(m*j.b)=m*p*j.b by ring]
    omega
  have r₁ : p≤m*h.b/h.a ↔ h.a*p≤m*h.b := by
    rw [Nat.le_div_iff_mul_le ha,mul_comm p h.a]
  have r₂ : p≤(j.c*n-1)/(m*j.d) ↔ m*p*j.d<j.c*n := by
    rw [Nat.le_div_iff_mul_le (Nat.mul_pos hm jd),show p*(m*j.d)=m*p*j.d by ring]
    have := Nat.mul_pos jc hn
    omega
  rw [l₁,l₂,r₁,r₂]
  tauto

/-- At a true factor the reciprocal of its partner equals Mp/N. -/
theorem partner_bracket {n m p q : ℕ} (hp : 0<p) (prod : n=p*q) (h : Bracket) :
    h.Contains (m*p) n ↔ h.Contains m q := by
  rw [prod]
  unfold Bracket.Contains
  rw [show h.a*(p*q)=p*(h.a*q) by ring,show m*p*h.b=p*(m*h.b) by ring,
    show m*p*h.d=p*(m*h.d) by ring,show h.c*(p*q)=p*(h.c*q) by ring,
    Nat.mul_le_mul_left_iff hp,Nat.mul_lt_mul_left hp]

/-- On an ordered candidate list, the reversed rank of M/p and forward rank
of Mp/N are both monotone. Their sum distinguishes every occupied prefix pair. -/
theorem pair_count (s : Finset ℕ) (f g : ℕ→ℕ) {k l : ℕ}
    (mf : ∀ x∈s, ∀ y∈s, x≤y → f x≤f y) (mg : ∀ x∈s, ∀ y∈s, x≤y → g x≤g y)
    (size : ∀ x∈s, f x<k ∧ g x<l) :
    (s.image (fun x => (f x,g x))).card ≤ k+l-1 := by
  classical
  rw [←card_range (k+l-1)]
  apply card_le_card_of_injOn (fun z : ℕ×ℕ => z.1+z.2)
  · rintro z hz
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hz
    have := size x hx
    exact mem_range.mpr (by dsimp only; omega)
  · rintro z hz t ht same
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hz
    obtain ⟨y,hy,rfl⟩ := mem_image.mp ht
    change f x+g x=f y+g y at same
    rcases le_total x y with h|h
    · have := mf x hx y hy h
      have := mg x hx y hy h
      exact Prod.ext (by omega) (by omega)
    · have := mf y hy x hx h
      have := mg y hy x hx h
      exact Prod.ext (by omega) (by omega)

/-- If an interval covers two successive possible smaller coordinates a stride
apart below the square root, its reciprocal interval contains an integer
in any prescribed residue class modulo that stride. -/
theorem partner_between {n x stride : ℕ} (hs : 0<stride) (room : (x+stride)^2≤n) (r : ℕ) :
    ∃ y : ℕ, y%stride=r%stride ∧ x*y≤n ∧ n<(x+stride)*y := by
  let t := n/(x+stride)
  let w := t+stride-r%stride
  let y := stride*(w/stride)+r%stride
  have tx : x≤t := by
    apply (Nat.le_div_iff_mul_le (by omega : 0<x+stride)).mpr
    exact (Nat.mul_le_mul_right _ (Nat.le_add_right x stride)).trans (by simpa only [sq] using room)
  have lower := Nat.div_mul_le_self n (x+stride)
  have higher := Nat.lt_div_mul_add (by omega : 0<x+stride) (a:=n)
  have eq := Nat.mod_add_div w stride
  have sm := Nat.mod_lt w hs
  have rs := Nat.mod_lt r hs
  have interval : t<y ∧ y≤t+stride := by dsimp only [w,y] at *; omega
  have base : t*(x+stride)≤n := lower
  have up : n < (t+1)*(x+stride) := by dsimp only [t]; nlinarith only [higher]
  refine ⟨y,by simp [y],?_,?_⟩
  · calc x*y ≤ x*(t+stride) := Nat.mul_le_mul_left x interval.2
         _ ≤ t*(x+stride) := by nlinarith only [Nat.mul_le_mul_right stride tx]
         _ ≤ n := base
  · exact up.trans_le (by simpa only [mul_comm] using Nat.mul_le_mul_right (x+stride) interval.1)

noncomputable def lane (lo hi stride residue : ℕ) :=
  (Icc lo hi).filter (fun x => x%stride=residue%stride)

theorem singleton_iff {n x stride r : ℕ} (hx : 0<x) :
    (∃ y : ℕ, y%stride=r%stride ∧ x*y≤n ∧ n≤x*y) ↔
      x∣n ∧ (n/x)%stride=r%stride := by
  constructor
  · rintro ⟨y,yr,left,right⟩
    have h := le_antisymm right left
    exact ⟨⟨y,h⟩,by simpa only [h,Nat.mul_div_cancel_left _ hx] using yr⟩
  · rintro ⟨div,mod⟩
    have eq := Nat.mul_div_cancel' div
    exact ⟨_,mod,eq.le,eq.ge⟩

/-- Rejecting a whole cell for absence of a partner residue eliminates at most one
smaller location on the chosen lane. This includes product-dependent cells. -/
theorem rejected_cell {n lo hi stride residue r : ℕ} (hs : 0<stride) (room : hi^2≤n)
    (reject : ¬∃ y : ℕ, y%stride=r%stride ∧ lo*y≤n ∧ n≤hi*y) :
    (lane lo hi stride residue).card≤1 := by
  apply card_le_one.mpr
  have ordered {x z : ℕ} (hx : x∈lane lo hi stride residue) (hz : z∈lane lo hi stride residue)
      (xz : x<z) : False := by
    obtain ⟨bounds,mx⟩ := mem_filter.mp hx
    obtain ⟨bounds',mz⟩ := mem_filter.mp hz
    obtain ⟨left,_⟩ := mem_Icc.mp bounds
    obtain ⟨_,right⟩ := mem_Icc.mp bounds'
    have step := Nat.le_of_dvd (Nat.sub_pos_of_lt xz) ((Nat.modEq_iff_dvd' xz.le).mp (mx.trans mz.symm))
    have top : x+stride≤hi := by omega
    obtain ⟨y,yr,l,h⟩ := partner_between hs ((Nat.pow_le_pow_left top 2).trans room) r
    exact reject ⟨y,yr,(Nat.mul_le_mul_right y left).trans l,h.le.trans (Nat.mul_le_mul_right y top)⟩
  intro x hx z hz
  rcases lt_trichotomy x z with h|h|h
  · exact (ordered hx hz h).elim
  · exact h
  · exact (ordered hz hx h).elim

/-- Any finite collection of rejections, including adaptive or overlapping cells
and varying strides, removes no more distinct locations than its number of cells. -/
theorem rejected_total {ι : Type*} (cells : Finset ι) (n : ℕ)
    (lo hi stride residue partner : ι→ℕ)
    (reject : ∀ i∈cells, 0<stride i ∧ (hi i)^2≤n ∧
      ¬∃ y : ℕ, y%(stride i)=partner i%(stride i) ∧ lo i*y≤n ∧ n≤hi i*y) :
    (cells.biUnion (fun i => lane (lo i) (hi i) (stride i) (residue i))).card ≤ cells.card := by
  refine card_biUnion_le.trans ?_
  calc ∑ i∈cells, (lane (lo i) (hi i) (stride i) (residue i)).card ≤ ∑ _i∈cells, 1 :=
         sum_le_sum (fun i hi => rejected_cell (reject i hi).1 (reject i hi).2.1 (reject i hi).2.2)
       _ = _ := by simp

/-- In the central public product bin, even the prime candidates left by an
arbitrary preceding set of weighted trace checks lose at most one further
location per rejected reciprocal cell and residue lane. Dusart (6.6) is the
sole published distribution input. -/
theorem surviving_primes {ι κ : Type*} {n : ℕ} (dusart : WeightedCrowdingEstimates.Dusart)
    (low : 9*(2^1024)^2≤16*n) (high : 8*n≤5*(2^1024)^2)
    (rows : Finset κ) (k : κ→ℕ) (z : κ→ℤ) (weight : ∀ i∈rows, 0<k i ∧ k i≤n)
    (cells : Finset ι) (lo hi stride residue partner : ι→ℕ)
    (reject : ∀ i∈cells, 0<stride i ∧ (hi i)^2≤n ∧
      ¬∃ y : ℕ, y%(stride i)=partner i%(stride i) ∧ lo i*y≤n ∧ n≤hi i*y) :
    ∃ left : Finset ℕ, 2^1011+1-144*2^512*rows.card-cells.card≤left.card ∧
      ∀ x∈left, x.Prime ∧ DisplacedTraceCoverage.Feasible n x ∧
        (∀ i∈rows, ¬DisplacedTraceCoverage.Covered24 n (k i) (z i) x) ∧
        ∀ i∈cells, x∉lane (lo i) (hi i) (stride i) (residue i) := by
  classical
  have pi (m : ℕ) : (DisplacedTraceCoverage.primesTo m).card=m.primeCounting := by
    rw [DisplacedTraceCoverage.primesTo,←Nat.range_succ_eq_Icc_zero]
    exact (Nat.count_eq_card_filter_range Nat.Prime (m+1)).symm
  have ends := DisplacedTraceCoverage.dusart_endpoints
    (by dsimp only; rw [pi]; exact (dusart _ (by decide +kernel)).1)
    (by dsimp only; rw [pi]; exact (dusart _ (by decide +kernel)).2)
  obtain ⟨s,size,good⟩ := DisplacedTraceCoverage.prime_survivors low high ends.1 ends.2 rows k z weight
  let removed := cells.biUnion (fun i => lane (lo i) (hi i) (stride i) (residue i))
  have count : removed.card≤cells.card := rejected_total cells n lo hi stride residue partner reject
  have cover : s⊆(s \ removed) ∪ removed := by
    intro x hx
    by_cases h : x∈removed
    · exact mem_union_right _ h
    · exact mem_union_left _ (mem_sdiff.mpr ⟨hx,h⟩)
  have keep := (card_le_card cover).trans (card_union_le _ _)
  refine ⟨s \ removed,by omega,?_⟩
  intro x hx
  obtain ⟨sx,out⟩ := mem_sdiff.mp hx
  obtain ⟨p,fit,clear⟩ := good x sx
  exact ⟨p,fit,clear,fun i hi member => out (mem_biUnion.mpr ⟨i,hi,member⟩)⟩

/-- The depth-two example has one unit-lane candidate in its chosen residue.
Lean checks both prime factors and their product. -/
theorem example_split :
    lower 40913 256 ⟨3,2,5,3⟩ ⟨1,1,4,3⟩=160 ∧
    upper 40913 256 ⟨3,2,5,3⟩ ⟨1,1,4,3⟩=170 ∧
    lane 160 170 24 19={163} ∧ ExactFactorization 40913 [163,251] := by
  refine ⟨by decide,by decide,by decide,?_⟩
  exact ExactFactorization.cons (by decide +kernel : Nat.Prime 163)
    (.cons (by decide +kernel : Nat.Prime 251) exactFactorization_nil)

end PrimeFactors.ReciprocalPrefixPairs
