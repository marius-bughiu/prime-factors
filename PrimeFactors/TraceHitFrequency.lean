import PrimeFactors.TraceGapPopulation

/-! Bound the fraction of actual factor pairs whose true trace can occur anywhere in
the allowed initial blocks. Slopes and block budgets can depend on the whole product. -/

namespace PrimeFactors.TraceHitFrequency
open Finset TraceCoverCertificate

set_option exponentiation.threshold 8192

/-- A hit forces q into a short interval about floor(ap/b). The interval can be
used for counting even though the searched program has no access to p. -/
theorem partner_window {p q m g B U D : ℕ} {s : Slope}
    (pp : 0<p) (qp : 0<q) (ph : p≤U) (qh : q≤U) (bp : 0<s.b)
    (ba : s.b≤s.a) (ab : s.a≤2*s.b) (budget : 0<B) (mb : m≤B) (gb : g≤B)
    (radius : 288*U*B^2≤D^2)
    (start : validStart (p*q) s) (hit : s.a*p+s.b*q<cutoff m s g) :
    q∈Icc (s.a*p/s.b-D) (s.a*p/s.b+D) := by
  have bound := TraceGapPopulation.gap_bound (bp.trans_le ba) bp pp qp start hit
  have step : s.step≤24 := (of_decide_eq_true start).2.1 ▸ Nat.gcd_le_left _ (by decide)
  have prod := Nat.mul_le_mul mb gb
  have one : 1≤B^2 := Nat.one_le_pow _ _ budget
  have count : 1+m*g≤2*B^2 := by rw [pow_two] at one ⊢; omega
  have z : s.a*p+s.b*q≤3*(s.b*U) := by
    have f := Nat.mul_le_mul ab ph
    have h := Nat.mul_le_mul_left s.b qh
    nlinarith only [f,h]
  have top := Nat.mul_le_mul (Nat.mul_le_mul_left 2 z) (Nat.mul_le_mul step count)
  have rad : 2*(s.a*p+s.b*q)*(s.step*(1+m*g))≤(s.b*D)^2 := calc
    _ ≤ _ := top
    _ = s.b*(288*U*B^2) := by ring
    _ ≤ s.b*D^2 := Nat.mul_le_mul_left _ radius
    _ ≤ (s.b*D)^2 := by
      have k := Nat.mul_le_mul_right (s.b*D^2) (show 1≤s.b from bp)
      nlinarith only [k]
  have sq : |(s.a:ℤ)*p-s.b*q|^2 < ((s.b*D:ℕ):ℤ)^2 := by
    rw [sq_abs]
    exact bound.trans_le (by exact_mod_cast rad)
  have gap := abs_lt.mp (lt_of_pow_lt_pow_left₀ 2 (by positivity) sq)
  push_cast at gap
  let c := s.a*p/s.b
  have rem := Nat.div_add_mod (s.a*p) s.b
  have small := Nat.mod_lt (s.a*p) bp
  have left : s.b*c≤s.a*p := by dsimp [c]; omega
  have right : s.a*p<s.b*(c+1) := by rw [Nat.mul_add,Nat.mul_one]; dsimp [c]; omega
  have oneSide : s.b*c < s.b*(q+D) := by
    apply left.trans_lt
    exact_mod_cast (show (s.a:ℤ)*p<s.b*((q:ℤ)+D) by linarith only [gap.2])
  have otherSide : s.b*q < s.b*(c+1+D) := by
    have v : s.b*q<s.a*p+s.b*D := by exact_mod_cast (show (s.b:ℤ)*q<s.a*p+s.b*D by linarith only [gap.1])
    rw [Nat.mul_add]
    exact v.trans (Nat.add_lt_add_right right _)
  exact mem_Icc.mpr ⟨by have := Nat.lt_of_mul_lt_mul_left oneSide; omega,
    by have := Nat.lt_of_mul_lt_mul_left otherSide; omega⟩

/-- Count partners once, including all intersections between the available windows. -/
theorem window_count {pairs : Finset (ℕ×ℕ)} {first : Finset ℕ} {weights : Finset (ℕ×ℕ)}
    {D : ℕ} (hit : ∀ x∈pairs, x.1∈first ∧ ∃ w∈weights,
      x.2∈Icc (w.1*x.1/w.2-D) (w.1*x.1/w.2+D)) :
    pairs.card≤first.card*(weights.card*(2*D+1)) := by
  classical
  let row (p : ℕ) (w : ℕ×ℕ) := (Icc (w.1*p/w.2-D) (w.1*p/w.2+D)).image (fun q => (p,q))
  have sub : pairs ⊆ first.biUnion (fun p => weights.biUnion (row p)) := by
    intro x hx
    obtain ⟨hp,w,hw,hq⟩ := hit x hx
    exact mem_biUnion.mpr ⟨_,hp,mem_biUnion.mpr ⟨_,hw,mem_image.mpr ⟨x.2,hq,rfl⟩⟩⟩
  apply (card_le_card sub).trans (card_biUnion_le_card_mul _ _ _ ?_)
  intro p _
  apply card_biUnion_le_card_mul
  intro w _
  apply card_image_le.trans
  rw [Nat.card_Icc]
  omega

/-- Either assignment of weights to an ordered factor pair falls below the
first omitted label of some canonical row. -/
def Accessible (x : ℕ×ℕ) (weights : Finset (ℕ×ℕ)) (B : ℕ) : Prop :=
  0<x.1 ∧ x.1≤x.2 ∧ x.2≤2^1024 ∧
  ∃ (s : Slope) (m g : ℕ), (s.a,s.b)∈weights ∧ 0<s.b ∧ s.b≤s.a ∧ s.a≤2*s.b ∧
    m≤B ∧ g≤B ∧ validStart (x.1*x.2) s ∧
    (s.a*x.1+s.b*x.2<cutoff m s g ∨ s.a*x.2+s.b*x.1<cutoff m s g)

/-- The partner interval for two 1,024-bit factors and a common budget B. -/
theorem accessible_window {x : ℕ×ℕ} {weights : Finset (ℕ×ℕ)} {B : ℕ}
    (bp : 0<B) (accessible : Accessible x weights B) :
    ∃ w∈weights, x.2∈Icc (w.1*x.1/w.2-2^517*B) (w.1*x.1/w.2+2^517*B) := by
  obtain ⟨pp,order,qh,s,m,g,w,sb,ba,ab,mb,gb,start,hits⟩ := accessible
  have hit : s.a*x.1+s.b*x.2<cutoff m s g := by
    rcases hits with direct | swapped
    · exact direct
    · apply lt_of_le_of_lt _ swapped
      nlinarith only [mul_nonneg (show 0≤(s.a:ℤ)-s.b by omega) (show 0≤(x.2:ℤ)-x.1 by omega)]
  refine ⟨(s.a,s.b),w,partner_window pp (pp.trans_le order) (order.trans qh) qh sb ba ab bp mb gb ?_ start hit⟩
  rw [Nat.mul_pow]
  exact Nat.mul_le_mul_right _ (by decide +kernel)

/-- Allow arbitrary product-dependent windows in the fixed catalogue. Each may
use up to B blocks and B starting powers. Only the true weighted sum is counted. -/
theorem population {pairs : Finset (ℕ×ℕ)} {first : Finset ℕ} {weights : Finset (ℕ×ℕ)}
    {B : ℕ} (bp : 0<B) (support : ∀ x∈pairs, x.1∈first ∧ Accessible x weights B) :
    pairs.card ≤ first.card*(weights.card*(2*(2^517*B)+1)) :=
  window_count (fun x hx => ⟨(support x hx).1,accessible_window bp (support x hx).2⟩)

/-- Reduced catalogue at a public denominator cutoff. -/
noncomputable def directions (k : ℕ) : Finset (ℕ×ℕ) :=
  (Icc 1 (2*k) ×ˢ Icc 1 k).filter fun w => w.2≤w.1 ∧ w.1≤2*w.2 ∧ w.1.Coprime w.2

theorem directions_card (k : ℕ) : (directions k).card≤(2*k)*k := by
  apply (card_le_card (filter_subset ..)).trans
  simp [Nat.card_Icc]

/-- Convert the per-prime count to a fraction of all eligible unordered pairs,
using the published prime-population comparison as an explicit hypothesis. -/
theorem fraction {pairs : Finset (ℕ×ℕ)} {first : Finset ℕ} {weights : Finset (ℕ×ℕ)}
    {B W L pop : ℕ} (bp : 0<B) (wp : 0<W) (lp : 0<L) (card : weights.card≤W)
    (den : 2^1023*first.card < 44331*pop) (price : L*44331*(W*(2*2^517+1))≤2^1023)
    (support : ∀ x∈pairs, x.1∈first ∧ Accessible x weights B) :
    L*pairs.card < B*pop := by
  have width : 2*(2^517*B)+1≤(2*2^517+1)*B := by
    rw [Nat.add_mul,Nat.one_mul,Nat.mul_assoc]; omega
  have bound := (population bp support).trans (Nat.mul_le_mul_left first.card (Nat.mul_le_mul card width))
  have strict := Nat.mul_lt_mul_of_pos_right den (show 0<L*(W*((2*2^517+1)*B)) by positivity)
  apply Nat.lt_of_mul_lt_mul_left (a:=2^1023)
  calc
    _ ≤ 2^1023*(L*(first.card*(W*((2*2^517+1)*B)))) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left L bound)
    _ = (2^1023*first.card)*(L*(W*((2*2^517+1)*B))) := by ac_rfl
    _ < _ := strict
    _ = (L*44331*(W*(2*2^517+1)))*(B*pop) := by ac_rfl
    _ ≤ _ := Nat.mul_le_mul_right _ price

/-- With K=8 the reachable fraction is less than B/2^485, even allowing
B blocks at every slope after seeing the entire product. -/
theorem eight {pairs : Finset (ℕ×ℕ)} {first : Finset ℕ} {B pop : ℕ}
    (bp : 0<B) (den : 2^1023*first.card < 44331*pop)
    (support : ∀ x∈pairs, x.1∈first ∧ Accessible x (directions 8) B) :
    2^485*pairs.card < B*pop :=
  fraction (W:=23) bp (by decide) (by decide) (by decide +kernel) den (by decide +kernel) support

/-- The same count remains restrictive with as many as 2^32 possible
denominators, at most B blocks per slope, and up to B starting powers. -/
theorem many_directions {pairs : Finset (ℕ×ℕ)} {first : Finset ℕ} {B pop : ℕ}
    (bp : 0<B) (den : 2^1023*first.card < 44331*pop)
    (support : ∀ x∈pairs, x.1∈first ∧ Accessible x (directions (2^32)) B) :
    2^424*pairs.card < B*pop :=
  fraction bp (by decide) (by decide) (directions_card (2^32)) den (by decide +kernel) support

/-- A common concrete budget for the two catalogue sizes. -/
theorem at_two_pow_64 {pairs : Finset (ℕ×ℕ)} {first : Finset ℕ} {pop : ℕ}
    (den : 2^1023*first.card < 44331*pop) :
    ((∀ x∈pairs, x.1∈first ∧ Accessible x (directions 8) (2^64)) → 2^421*pairs.card<pop) ∧
    ((∀ x∈pairs, x.1∈first ∧ Accessible x (directions (2^32)) (2^64)) → 2^360*pairs.card<pop) := by
  constructor
  · intro H
    apply Nat.lt_of_mul_lt_mul_left (a:=2^64)
    simpa only [←Nat.mul_assoc,←pow_add] using eight (by decide) den H
  · intro H
    apply Nat.lt_of_mul_lt_mul_left (a:=2^64)
    simpa only [←Nat.mul_assoc,←pow_add] using many_directions (by decide) den H

end PrimeFactors.TraceHitFrequency
