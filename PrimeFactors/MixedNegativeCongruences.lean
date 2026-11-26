import PrimeFactors.QuantilePopulationBounds
import PrimeFactors.MixedNegativeTemplates
import Mathlib.Data.Nat.ModEq

/-! A product-only test for the 5,7 mixed-negative template. A square test
on an ordinary Fermat midpoint suffices to recognize each witness. The
population transfer takes a prime-count discrepancy as an explicit hypothesis. -/
namespace PrimeFactors.MixedNegativeCongruences

set_option maxRecDepth 8192

/-- All weighted equalities of this particular shape are ordinary differences of squares. -/
theorem match_iff (N t s : ℤ) :
    49*(N-t^2)=25*(2*N-s^2) ↔ (5*s-7*t)*(5*s+7*t)=N := by
  constructor <;> intro eq <;> linear_combination eq

/-- The actual positive gcd on this match is the smaller prime. The two
negative magnitudes are 25g and 49g, with g>0, hence they are unequal. -/
theorem witness {p q : ℕ} (pp : p.Prime) (qp : q.Prime) (large : 7<p)
    (order : p<q) (balance : q≤2*p) (same : p%7=q%7) (opposite : (p+q)%5=0) :
    ∃ t s g : ℕ, p+14*t=q ∧ 10*s=p+q ∧ 0<g ∧
      t^2+25*g=p*q ∧ s^2+49*g=2*(p*q) ∧ (t*s+35*g).gcd (p*q)=p := by
  have po := pp.odd_of_ne_two (by omega)
  have qo := qp.odd_of_ne_two (by omega)
  obtain ⟨i,hi⟩ := po
  obtain ⟨j,hj⟩ := qo
  let t := (q-p)/14
  let s := (p+q)/10
  have gap : p+14*t=q := by dsimp [t]; omega
  have total : 10*s=p+q := by dsimp [s]; omega
  have t0 : 0<t := by omega
  have gt : 7*t<q := by omega
  have tp : t<p := by omega
  have tlt : t^2<p*q := by simpa [pow_two] using Nat.mul_lt_mul_of_lt_of_lt tp (tp.trans order)
  let D := p*q-t^2
  have drow : t^2+D=p*q := by dsimp [D]; omega
  have mid : 5*s=p+7*t := by omega
  have squared : 25*s^2=p*q+49*t^2 := calc
    _ = (5*s)^2 := by ring
    _ = (p+7*t)^2 := by rw [mid]
    _ = _ := by rw [←gap]; ring
  have relation : 25*s^2+49*D=50*(p*q) := by omega
  have dv : 25 ∣ 49*D := by omega
  obtain ⟨g,eg⟩ := (show Nat.Coprime 25 49 by decide).dvd_of_dvd_mul_left dv
  have e1 : t^2+25*g=p*q := by omega
  have e2 : s^2+49*g=2*(p*q) := by omega
  have gpos : 0<g := by omega
  refine ⟨t,s,g,gap,total,gpos,e1,e2,?_⟩
  have scaled : 35*(t*s+35*g)=p*(7*t+49*q) := by
    zify at mid e1 ⊢
    linear_combination 49*e1 + 7*(t:ℤ)*mid
  have prime35 (r : ℕ) (pr : r.Prime) (big : 7<r) : Nat.Coprime 35 r := by
    have c5 : Nat.Coprime r 5 := (Nat.coprime_primes pr (by decide)).2 (by omega)
    have c7 : Nat.Coprime r 7 := (Nat.coprime_primes pr (by decide)).2 (by omega)
    exact (c5.mul_right c7).symm
  have cop := (prime35 p pp large).mul_right (prime35 q qp (large.trans order))
  rw [←Nat.Coprime.gcd_mul_left_cancel _ cop, scaled, Nat.gcd_mul_left]
  rw [Nat.gcd_comm, Nat.gcd_add_mul_right_right]
  have c : q.Coprime (7*t) := qp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by omega) gt)
  simp [c.gcd_eq_one]

/-- For an odd first factor, a single multiplier modulo 280 specifies
all three prime-pair conditions, including the public product residue 7 mod 8. -/
theorem residue_iff {p q : ℕ} (po : p%2=1) :
    q ≡ 239*p [MOD 280] ↔ (p*q)%8=7 ∧ p%7=q%7 ∧ (p+q)%5=0 := by
  have small : ∀ a b : Fin 8, a.val%2=1 →
      ((a.val*b.val)%8=7 ↔ b.val=(239*a.val)%8) := by decide
  have local8 := small ⟨p%8, Nat.mod_lt _ (by decide)⟩ ⟨q%8, Nat.mod_lt _ (by decide)⟩ (by simpa using po)
  change ((p%8)*(q%8))%8=7 ↔ q%8=(239*(p%8))%8 at local8
  rw [Nat.mul_mod p q 8]
  rw [show 280=8*(5*7) by decide, ←Nat.modEq_and_modEq_iff_modEq_mul (by decide),
    ←Nat.modEq_and_modEq_iff_modEq_mul (by decide : Nat.Coprime 5 7)]
  simp only [Nat.ModEq]
  omega

/-- For this public product class, the midpoint sieve imposes precisely the
divisibilities 5|x and 7|y whenever the usual difference really is a square. -/
theorem midpoint_sieve {N x y : ℕ} (seven : N%8=7) (sq : x^2=N+y^2) :
    (x%20=0 ∧ x^2%49=N%49) ↔ (5∣x ∧ 7∣y) := by
  have small : ∀ a b : Fin 8, a.val^2%8=(7+b.val^2%8)%8 → a.val%4=0 := by decide
  have reduction := congrArg (·%8) sq
  change x^2%8=(N+y^2)%8 at reduction
  rw [Nat.add_mod, seven, Nat.pow_mod x, Nat.pow_mod y] at reduction
  have four := small ⟨x%8, Nat.mod_lt _ (by decide)⟩ ⟨y%8, Nat.mod_lt _ (by decide)⟩ reduction
  change x%8%4=0 at four
  constructor
  · rintro ⟨m,h⟩
    have div : 49∣y^2 := by omega
    exact ⟨by omega, (show Nat.Prime 7 by decide).dvd_of_dvd_pow ((by decide : 7∣49).trans div)⟩
  · rintro ⟨m,⟨k,rfl⟩⟩
    have h : (7*k)^2=49*k^2 := by ring
    exact ⟨by omega, by omega⟩

/-- The coefficient of 20 within a complete period of 980 for the midpoint. -/
noncomputable def midpointClasses (N : ℕ) : Finset ℕ :=
  (Finset.range 49).filter fun u => (20*u)^2%49=N%49

set_option maxRecDepth 8192 in
theorem midpoint_classes_card (N : ℕ) (square : N%7∈([1,2,4] : List ℕ)) :
    (midpointClasses N).card=2 := by
  have cert : ∀ z : Fin 49, z.val%7∈([1,2,4] : List ℕ) → (midpointClasses z.val).card=2 := by decide
  simpa [midpointClasses] using cert ⟨N%49,Nat.mod_lt _ (by decide)⟩ (by
    simpa only [Nat.mod_mod_of_dvd N (by decide : 7∣49)] using square)

open Finset

noncomputable def units : Finset ℕ := (range 280).filter (Nat.Coprime 280)
noncomputable def allCells := units ×ˢ units
noncomputable def sevenGraph := units.image fun a => (a,239*a%280)

set_option maxRecDepth 8192 in
theorem graph_subset : sevenGraph⊆allCells := by
  intro v hv
  rw [sevenGraph] at hv
  obtain ⟨a,ha,rfl⟩ := mem_image.mp hv
  have hmem := ha
  rw [units] at hmem
  have u := (mem_filter.mp hmem).2
  apply mem_product.mpr
  refine ⟨ha,mem_filter.mpr ⟨mem_range.mpr (Nat.mod_lt _ (by decide)),?_⟩⟩
  change Nat.gcd 280 (239*a%280)=1
  rw [Nat.gcd_rec, Nat.mod_mod, ←Nat.gcd_rec]
  exact Nat.coprime_mul_iff_right.mpr ⟨by decide,u⟩

set_option maxRecDepth 8192 in
theorem cell_counts : sevenGraph.card=96 ∧ allCells.card=9216 := by
  have h : units.card=96 := by decide
  constructor
  · rw [sevenGraph,card_image_of_injective _ (fun _ _ eq => congrArg Prod.fst eq),h]
  · rw [allCells,card_product,h]

/-- The six product residues permitted by the three conditions have 16
possible first-factor residues each. The unit test is made on the factor
candidate and the product alone. -/
noncomputable def factorClasses (n : ℕ) : Finset ℕ :=
  units.filter fun a => 239*a^2%280=n%280

noncomputable def productClasses : Finset ℕ := {39,71,79,151,191,239}

set_option maxRecDepth 8192 in
theorem factor_classes_card (N : ℕ) :
    (factorClasses N).card=if N%280∈productClasses then 16 else 0 := by
  have inside : ∀ a : Fin 280, (280:ℕ).Coprime a.val → 239*a.val^2%280∈productClasses := by decide
  split_ifs with h
  · have concrete (r : ℕ) (hr : r∈productClasses) : (factorClasses r).card=16 := by
      simp only [productClasses,mem_insert,mem_singleton] at hr
      rcases hr with rfl|rfl|rfl|rfl|rfl|rfl <;> decide
    simpa only [factorClasses,Nat.mod_mod] using concrete (N%280) h
  · rw [card_eq_zero,eq_empty_iff_forall_not_mem]
    intro a ha
    obtain ⟨hu,eq⟩ := mem_filter.mp ha
    obtain ⟨hb,hcop⟩ := mem_filter.mp hu
    have hit := inside ⟨a,mem_range.mp hb⟩ hcop
    exact h (eq ▸ hit)

private theorem cell_sum {ι : Type*} (S : Finset ι) (w : ι → ℝ) (u E : ℝ)
    (error : ∀ i∈S, |w i-u|≤E) :
    |∑ i∈S, w i - S.card*u| ≤ S.card*E := by
  have hs := (Finset.abs_sum_le_sum_abs (fun i => w i-u) S).trans
    (Finset.sum_le_sum error)
  simpa only [sum_sub_distrib,sum_const,nsmul_eq_mul] using hs

set_option exponentiation.threshold 4096 in
/-- Uniform transfer for any two groups of residue cells. At the target
width the published progression estimate, applied in both coordinates,
supplies the per-cell error. It is not asserted here as an axiom. -/
theorem conditional_fraction {ι : Type*} (yes no : Finset ι) (w : ι → ℝ)
    {I : ℝ} (mass : 2^2024≤I) (budget : yes.card+no.card≤9216)
    (first : 0<yes.card) (second : 0<no.card)
    (pos : ∀ i, 0≤w i)
    (hy : ∀ i∈yes, |w i-I/9216|≤2^1546)
    (hn : ∀ i∈no, |w i-I/9216|≤2^1546) :
    |(∑ i∈yes,w i)/((∑ i∈yes,w i)+(∑ i∈no,w i)) -
      (yes.card:ℝ)/(yes.card+no.card)| < 1/2^464 := by
  let u := I/9216
  let E := ((yes.card:ℝ)+no.card)*2^1546
  have hu : (2:ℝ)^2010<u := by dsimp [u]; linarith only [mass]
  have up : 0<u := (by positivity : (0:ℝ)<2^2010).trans hu
  have ey := cell_sum yes w u (2^1546) hy
  have en := cell_sum no w u (2^1546) hn
  have y1 : (1:ℝ)≤yes.card := by exact_mod_cast first
  have n1 : (1:ℝ)≤no.card := by exact_mod_cast second
  have bd : (yes.card:ℝ)+no.card≤9216 := by exact_mod_cast budget
  have eur : E≤u := calc
    E ≤ 9216*(2:ℝ)^1546 := by dsimp [E]; gcongr
    _ ≤ (2:ℝ)^2010 := by norm_num
    _ ≤ u := hu.le
  have sy : |(∑ i∈yes,w i)-yes.card*u|≤E :=
    ey.trans (mul_le_mul_of_nonneg_right (by linarith only [n1]) (by positivity))
  have sn : |(∑ i∈no,w i)-no.card*u|≤E :=
    en.trans (mul_le_mul_of_nonneg_right (by linarith only [y1]) (by positivity))
  have fy := QuantilePopulationBounds.fraction_error (G:=(yes.card:ℝ)*u) (J:=(no.card:ℝ)*u)
    (by dsimp [E]; positivity) (eur.trans (le_mul_of_one_le_left up.le y1))
    (eur.trans (le_mul_of_one_le_left up.le n1)) (sum_nonneg fun i _ => pos i)
    (sum_nonneg fun i _ => pos i) sy sn
  rw [←add_mul, mul_div_mul_right _ _ up.ne'] at fy
  apply fy.trans_lt
  have both : (0:ℝ)<yes.card+no.card := by linarith only [y1,n1]
  change ((yes.card:ℝ)+no.card)*2^1546/(((yes.card:ℝ)+no.card)*u)<_
  rw [mul_div_mul_left _ _ both.ne']
  apply (div_lt_div_iff₀ up (by positivity : (0:ℝ)<2^464)).mpr
  calc (2:ℝ)^1546*2^464 = 2^2010 := by norm_num
    _ < 1*u := by simpa only [one_mul] using hu

/-- For an actual factor pair, membership of the residue pair in the graph
is exactly the three desired congruences. -/
theorem graph_iff {p q : ℕ} (hu : Nat.Coprime 280 p) :
    (p%280,q%280)∈sevenGraph ↔ (p*q)%8=7 ∧ p%7=q%7 ∧ (p+q)%5=0 := by
  have u : p%280∈units := by
    refine mem_filter.mpr ⟨mem_range.mpr (Nat.mod_lt _ (by decide)),?_⟩
    change Nat.gcd 280 (p%280)=1
    rw [Nat.gcd_rec, Nat.mod_mod, ←Nat.gcd_rec]
    exact hu
  have two : 2∣280 := by decide
  have po : p%2=1 := by
    by_contra bad
    have even : 2∣p := by omega
    have div := Nat.dvd_gcd two even
    rw [hu.gcd_eq_one] at div
    omega
  rw [←residue_iff po,sevenGraph,mem_image]
  have cross : 239*(p%280)%280=239*p%280 := by simp only [Nat.mul_mod, Nat.mod_mod]
  constructor
  · rintro ⟨a,_,eq⟩
    obtain ⟨rfl,e⟩ := Prod.mk.inj eq
    exact e.symm.trans cross
  · intro e
    exact ⟨p%280,u,Prod.ext rfl (cross.trans e.symm)⟩

set_option exponentiation.threshold 4096 in
/-- Specialization to the 96 cells in the template, out of 9,216. -/
theorem target_fraction (w : ℕ × ℕ → ℝ) {I : ℝ} (mass : 2^2024≤I)
    (pos : ∀ i, 0≤w i) (err : ∀ i∈allCells, |w i-I/9216|≤2^1546) :
    |(∑ i∈sevenGraph,w i)/(∑ i∈allCells,w i)-1/96|<1/2^464 := by
  obtain ⟨g,a⟩ := cell_counts
  have rest : (allCells \ sevenGraph).card=9120 := by rw [card_sdiff graph_subset,a,g]
  have f := conditional_fraction sevenGraph (allCells \ sevenGraph) w mass
    (by rw [g,rest]) (by rw [g]; decide) (by rw [rest]; decide) pos
    (fun i hi => err i (graph_subset hi)) (fun i hi => err i (mem_sdiff.mp hi).1)
  rw [add_comm (∑ i∈sevenGraph, w i) _,sum_sdiff graph_subset] at f
  rw [g,rest] at f
  norm_num at f ⊢
  exact f

set_option exponentiation.threshold 4096 in
/-- Bennett–Martin–O'Bryant–Rechnitzer Theorem 1.3 gives an endpoint
error at most 2X/(840·700²). Sum the two interval-coordinate errors and
remove at most X equal-prime pairs to obtain the hypothesis below. -/
theorem unconditional_cell {X u e : ℝ} (size : 2^1023≤X)
    (mass : X^2/(4*710^2*96^2)≤u)
    (err : e≤(4*X/(840*700^2))*(2*X/(96*700)+4*X/(840*700^2))+X) :
    e<u/180 := by
  have xp : 0<X := (by positivity : (0:ℝ)<2^1023).trans_le size
  have big : 10^15≤X := le_trans (by norm_num) size
  have room := mul_le_mul_of_nonneg_right big xp.le
  nlinarith only [err,mass,room,xp]

/-- No zero-location hypothesis is required for the wider interval once
the unconditional per-cell estimate is supplied. -/
theorem unconditional_fraction (w : ℕ × ℕ → ℝ) {u : ℝ} (up : 0<u)
    (err : ∀ i∈allCells, |w i-u|≤u/180) :
    179/(181*96)≤(∑ i∈sevenGraph,w i)/(∑ i∈allCells,w i) ∧
    (∑ i∈sevenGraph,w i)/(∑ i∈allCells,w i)≤181/(179*96) := by
  obtain ⟨g,a⟩ := cell_counts
  have e1 := abs_le.mp (cell_sum sevenGraph w u (u/180) (fun i hi => err i (graph_subset hi)))
  have e2 := abs_le.mp (cell_sum allCells w u (u/180) err)
  rw [g] at e1
  rw [a] at e2
  norm_num only [Nat.cast_ofNat] at e1 e2
  have den : 0<∑ i∈allCells,w i := by linarith only [e2.1,up]
  constructor
  · apply (le_div_iff₀ den).mpr
    linarith only [e1.1,e2.2]
  · apply (div_le_iff₀ den).mpr
    linarith only [e1.2,e2.1]

/-- First such pair in increasing smaller prime above seven, with q≤2p. -/
theorem example_3551 :
    53*67=(3551:ℕ) ∧ 1^2+25*142=(3551:ℕ) ∧ 12^2+49*142=2*(3551:ℕ) ∧
    (1*12+35*142).gcd 3551=53 := by decide

/-- Both families, with unrestricted product residue for the 5,7 family. -/
def accepts (p q : ℕ) : Prop := (p*q)%12=5 ∨ (p%7=q%7 ∧ (p+q)%5=0)

/-- Every member of the union has unequal positive remainders whose product
is a square and whose actual plus-sign gcd recovers the smaller prime. -/
theorem union_witness {p q : ℕ} (pp : p.Prime) (qp : q.Prime) (large : 7<p)
    (order : p<q) (balance : q≤2*p) (ok : accepts p q) :
    ∃ t s D E r : ℕ, 0<t ∧ 0<s ∧ 0<D ∧ D<E ∧ t^2+D=p*q ∧
      s^2+E=2*(p*q) ∧ D*E=r^2 ∧ (t*s+r).gcd (p*q)=p := by
  rcases ok with h|h
  · obtain ⟨g,ht,hs,hg,_,_,e1,e2,_,_,_,sq,_,hit⟩ :=
      MixedNegativeTemplates.five_mod_twelve pp qp order balance h
    exact ⟨_,_,4*g,9*g,6*g,ht,hs,by omega,by omega,e1,e2,sq,hit⟩
  · obtain ⟨t,s,g,gt,st,gp,e1,e2,hit⟩ := witness pp qp large order balance h.1 h.2
    exact ⟨t,s,25*g,49*g,35*g,by omega,by omega,by omega,by omega,e1,e2,by ring,hit⟩

/-- The second coordinate is q/p in the unit group, giving just 420 possible
integer representatives to inspect instead of a table of prime pairs. -/
noncomputable def unionUnits := (range 420).filter (Nat.Coprime 420)
noncomputable def unionCodes := unionUnits.filter fun v => v%12=5 ∨ v%35=29
noncomputable def allRatioCells := unionUnits ×ˢ unionUnits
noncomputable def goodRatioCells := unionUnits ×ˢ unionCodes

theorem ratio_criterion {p q v : ℕ} (pu : Nat.Coprime 420 p) (h : q ≡ v*p [MOD 420]) :
    accepts p q ↔ v%12=5 ∨ v%35=29 := by
  have u12 := pu.of_dvd_left (by decide : 12∣420)
  have u35 := pu.of_dvd_left (by decide : 35∣420)
  have small : ∀ a : Fin 12, Nat.Coprime 12 a.val → a.val^2%12=1 := by decide
  have u12' : Nat.Coprime 12 (p%12) := by
    change Nat.gcd 12 (p%12)=1
    rw [Nat.gcd_rec,Nat.mod_mod,←Nat.gcd_rec]
    exact u12
  have sq : p^2 ≡ 1 [MOD 12] := by
    change p^2%12=1
    rw [Nat.pow_mod]
    exact small ⟨p%12,Nat.mod_lt _ (by decide)⟩ u12'
  have prod : p*q ≡ v [MOD 12] := calc
    _ ≡ p*(v*p) [MOD 12] := (h.of_dvd (by decide : 12∣420)).mul_left _
    _ = p^2*v := by ring
    _ ≡ 1*v [MOD 12] := sq.mul_right _
    _ = _ := one_mul _
  have rel : (p%7=q%7 ∧ (p+q)%5=0) ↔ q ≡ 29*p [MOD 35] := by
    rw [show 35=5*7 by decide, ←Nat.modEq_and_modEq_iff_modEq_mul (by decide)]
    simp only [Nat.ModEq]
    omega
  have reduced := h.of_dvd (by decide : 35∣420)
  have second : q ≡ 29*p [MOD 35] ↔ v ≡ 29 [MOD 35] := by
    constructor
    · intro right
      have cancel := Nat.ModEq.cancel_right_div_gcd (by decide : 0<35) (reduced.symm.trans right)
      simpa only [u35.gcd_eq_one,Nat.div_one] using cancel
    · intro right
      exact reduced.trans (right.mul_right _)
  change p*q%12=5 ∨ _ ↔ _
  rw [show p*q%12=v%12 from prod, rel, second]
  rfl

/-- Multiplying the unit ratio by the first residue permutes every second
unit class. This justifies applying ordinary per-residue-pair count errors
to the ratio coordinates. -/
def pairOfRatio (z : ℕ × ℕ) := (z.1,z.2*z.1%420)

theorem pairOfRatio_image : allRatioCells.image pairOfRatio=allRatioCells := by
  apply eq_of_subset_of_card_le
  · intro z hz
    obtain ⟨⟨a,v⟩,hp,rfl⟩ := mem_image.mp hz
    obtain ⟨au,vu⟩ := mem_product.mp hp
    have ca := (mem_filter.mp au).2
    have cv := (mem_filter.mp vu).2
    refine mem_product.mpr ⟨au,mem_filter.mpr ⟨mem_range.mpr (Nat.mod_lt _ (by decide)),?_⟩⟩
    change Nat.gcd 420 (v*a%420)=1
    rw [Nat.gcd_rec,Nat.mod_mod,←Nat.gcd_rec]
    exact cv.mul_right ca
  · apply le_of_eq
    symm
    apply card_image_of_injOn
    rintro ⟨a,v⟩ hv ⟨b,w⟩ hw eq
    obtain ⟨e1,e2⟩ := Prod.mk.inj eq
    dsimp [pairOfRatio] at e1 e2
    subst b
    have au := (mem_filter.mp (mem_product.mp hv).1).2
    have vl := mem_range.mp (mem_filter.mp (mem_product.mp hv).2).1
    have wl := mem_range.mp (mem_filter.mp (mem_product.mp hw).2).1
    have red := Nat.ModEq.cancel_right_div_gcd (by decide : 0<420)
      (show v*a ≡ w*a [MOD 420] from e2)
    rw [au.gcd_eq_one,Nat.div_one] at red
    exact Prod.ext rfl (red.eq_of_lt_of_lt vl wl)

theorem ratio_subset : goodRatioCells⊆allRatioCells := by
  intro z hz
  obtain ⟨a,b⟩ := mem_product.mp hz
  exact mem_product.mpr ⟨a,(mem_filter.mp b).1⟩

theorem union_counts : unionUnits.card=96 ∧ unionCodes.card=27 ∧
    goodRatioCells.card=2592 ∧ allRatioCells.card=9216 := by
  have u : unionUnits.card=96 := by decide
  have r : unionCodes.card=27 := by decide
  exact ⟨u,r,by rw [goodRatioCells,card_product,u,r],by rw [allRatioCells,card_product,u]⟩

set_option exponentiation.threshold 4096 in
theorem union_grh_fraction (w : ℕ × ℕ → ℝ) {I : ℝ} (mass : 2^2024≤I)
    (pos : ∀ i, 0≤w i) (err : ∀ i∈allRatioCells, |w i-I/9216|≤2^1546) :
    |(∑ i∈goodRatioCells,w i)/(∑ i∈allRatioCells,w i)-9/32|<1/2^464 := by
  obtain ⟨_,_,g,a⟩ := union_counts
  have rest : (allRatioCells \ goodRatioCells).card=6624 := by rw [card_sdiff ratio_subset,a,g]
  have f := conditional_fraction goodRatioCells (allRatioCells \ goodRatioCells) w mass
    (by rw [g,rest]) (by rw [g]; decide) (by rw [rest]; decide) pos
    (fun i hi => err i (ratio_subset hi)) (fun i hi => err i (mem_sdiff.mp hi).1)
  rw [add_comm (∑ i∈goodRatioCells, w i) _,sum_sdiff ratio_subset] at f
  rw [g,rest] at f
  norm_num at f ⊢
  exact f

/-- The triangle above x+y=3X in [X,2X]² consists entirely of full-width
products. Its area is X²/2. -/
theorem triangle_eligible {X x y : ℝ} (xp : 0≤X) (lo : X≤x) (hi : x≤2*X)
    (triangle : 3*X≤x+y) : 2*X^2≤x*y := by
  nlinarith only [mul_nonneg (sub_nonneg.mpr lo) (sub_nonneg.mpr hi),
    mul_nonneg (xp.trans lo) (sub_nonneg.mpr triangle)]

set_option exponentiation.threshold 4096 in
/-- The triangle doubles the elementary lower bound on each cell's mass. -/
theorem triangle_cell {X u e : ℝ} (size : 2^1023≤X)
    (mass : X^2/(2*710^2*96^2)≤u)
    (err : e≤(4*X/(840*700^2))*(2*X/(96*700)+4*X/(840*700^2))+X) :
    e<u/370 := by
  have xp : 0<X := (by positivity : (0:ℝ)<2^1023).trans_le size
  have big : 10^18≤X := le_trans (by norm_num) size
  have room := mul_le_mul_of_nonneg_right big xp.le
  nlinarith only [err,mass,room,xp]

/-- Using the q≤10,000 estimate at modulus 420, the fraction of prime
pairs in this specified union exceeds 28%. Other matches may also exist. -/
theorem union_unconditional_fraction (w : ℕ × ℕ → ℝ) {u : ℝ} (up : 0<u)
    (err : ∀ i∈allRatioCells, |w i-u|≤u/370) :
    (9*369)/(9*369+23*371)≤(∑ i∈goodRatioCells,w i)/(∑ i∈allRatioCells,w i) ∧
    (∑ i∈goodRatioCells,w i)/(∑ i∈allRatioCells,w i)≤(9*371)/(9*371+23*369) := by
  obtain ⟨_,_,g,a⟩ := union_counts
  have rest : (allRatioCells \ goodRatioCells).card=6624 := by rw [card_sdiff ratio_subset,a,g]
  have e1 := abs_le.mp (cell_sum goodRatioCells w u (u/370) (fun i hi => err i (ratio_subset hi)))
  have e2 := abs_le.mp (cell_sum (allRatioCells \ goodRatioCells) w u (u/370)
      (fun i hi => err i (mem_sdiff.mp hi).1))
  rw [g] at e1
  rw [rest] at e2
  norm_num only [Nat.cast_ofNat] at e1 e2
  have part := sum_sdiff (f:=w) ratio_subset
  have den : 0<∑ i∈allRatioCells,w i := by linarith only [e2.1,e1.1,up,part]
  constructor
  · apply (le_div_iff₀ den).mpr
    linarith only [e1.1,e2.2,part]
  · apply (div_le_iff₀ den).mpr
    linarith only [e1.2,e2.1,part]

theorem ratio_event_counts :
    (unionUnits.filter (fun v => v%12=5)).card=24 ∧
    (unionUnits.filter (fun v => v%35=29)).card=4 ∧
    (unionUnits.filter (fun v => v%12=5 ∧ v%35=29)).card=1 := by decide

end PrimeFactors.MixedNegativeCongruences
