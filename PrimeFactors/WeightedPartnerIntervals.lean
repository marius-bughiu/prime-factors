import PrimeFactors.MarginalTraceCoverage
import PrimeFactors.SwitchedBatchComparison

/-! For distribution analysis, hold the smaller prime and partner residue
fixed. The phase of the true weighted trace determines an exact integer
interval for the partners reached in a bounded mod-24 search. -/
namespace PrimeFactors.WeightedPartnerIntervals
open Finset MarginalTraceWidth

private def test (r a b s : ℕ) := s.gcd 24 = (a+b*r).gcd 24

private instance (r a b s : ℕ) : Decidable (test r a b s) := inferInstanceAs (Decidable (_ = _))

private theorem lane_nonempty {f s r a b : ℕ} (lo : f≤s) (pass : test r a b s) :
    0<(offsets r (f%24) a b).length := by
  let d := s-f
  have eq : f+d=s := by dsimp [d]; omega
  have mem : d%24 ∈ offsets r (f%24) a b := by
    apply List.mem_filter.mpr
    refine ⟨List.mem_range.mpr (Nat.mod_lt _ (by decide)),beq_iff_eq.mpr ?_⟩
    rw [((Nat.mod_modEq f 24).add (Nat.mod_modEq d 24)).gcd_eq,eq]
    exact pass
  have := List.idxOf_lt_length_iff.mpr mem
  omega

private theorem at_index {f r a b : ℕ} (pos : 0<(offsets r (f%24) a b).length) (i : ℕ) :
    test r a b (f+offset r (f%24) a b i) := by
  let xs := offsets r (f%24) a b
  have index : i%xs.length<xs.length := Nat.mod_lt _ pos
  let u := xs[i%xs.length]'index
  have mem : u∈xs := List.getElem_mem index
  have pass := beq_iff_eq.mp (List.mem_filter.mp mem).2
  have eq : offset r (f%24) a b i=24*(i/xs.length)+u := by
    change 24*(i/xs.length)+(xs[i%xs.length]?).getD 0=_
    rw [List.getElem?_eq_getElem index]; rfl
  have m : f+offset r (f%24) a b i ≡ f%24+u [MOD 24] := by
    rw [eq]; change _%24=_%24
    omega
  exact m.gcd_eq.trans pass

private theorem count_before {f r a b : ℕ} (pos : 0<(offsets r (f%24) a b).length) (H : ℕ) :
    ((Ico f (f+offset r (f%24) a b H)).filter (test r a b)).card=H := by
  let label i := f+offset r (f%24) a b i
  have sorted : StrictMono label := fun _ _ h => Nat.add_lt_add_left (ordered_offsets _ _ _ _ pos h) _
  have cover : (range H).image label = (Ico f (label H)).filter (test r a b) := by
    ext s
    constructor
    · intro h
      obtain ⟨i,hi,rfl⟩ := mem_image.mp h
      exact mem_filter.mpr ⟨mem_Ico.mpr ⟨Nat.le_add_right _ _,sorted (mem_range.mp hi)⟩,at_index pos _⟩
    · intro h
      obtain ⟨int,ok⟩ := mem_filter.mp h
      obtain ⟨lo,lt⟩ := mem_Ico.mp int
      obtain ⟨i,hi,eq⟩ := (admitted_iff (H:=H) lo ok).mp lt
      exact mem_image.mpr ⟨i,mem_range.mpr hi,eq.symm⟩
  rw [←cover,card_image_of_injective _ sorted.injective,card_range]

private theorem rank_iff {f r a b s H : ℕ} (lo : f≤s) (pass : test r a b s) :
    (∃ i<H, s=f+offset r (f%24) a b i) ↔
      ((Ico f s).filter (test r a b)).card < H := by
  have count := count_before (lane_nonempty lo pass) H
  let omitted := f+offset r (f%24) a b H
  rw [←admitted_iff lo pass]
  constructor
  · intro lt
    have sub : (Ico f s).filter (test r a b) ⊆ (Ico f omitted).filter (test r a b) :=
      filter_subset_filter _ (Ico_subset_Ico_right lt.le)
    have strict := (ssubset_iff_of_subset sub).mpr ⟨s,mem_filter.mpr ⟨mem_Ico.mpr ⟨lo,lt⟩,pass⟩,
      fun h => (Nat.lt_irrefl s) (mem_Ico.mp (mem_filter.mp h).1).2⟩
    exact (card_lt_card strict).trans_eq count
  · intro small
    by_contra! le
    have sub := filter_subset_filter (test r a b) (Ico_subset_Ico_right (a:=f) le)
    exact (not_le_of_gt small) (count ▸ card_le_card sub)

/-- Distance to the H-th preceding allowed label on the doubly infinite
wheel. The zeroth preceding label is the trace itself. This uses a single
period of at most 24 residues for arbitrary H. -/
noncomputable def gap (phase H : ℕ) :=
  let reflected := (24-phase%24)%24
  offset 0 reflected (phase%24) 0 H

private theorem neg_gcd : ∀ j : Fin 24, (24-(j:ℕ)).gcd 24=(j:ℕ).gcd 24 := by decide +kernel

/-- The exact backward cutoff depends only on the phase of the target
trace, including for budgets that extend over many periods. -/
theorem reverse_iff {r a b s f H : ℕ} (lo : f≤s) (pass : s.gcd 24=(a+b*r).gcd 24) :
    (∃ i<H, s=f+offset r (f%24) a b i) ↔ s-f < gap s H := by
  let v := 24-s%24
  let rev (t : ℕ) := v+s-t
  let okay := test r a b
  let back := test 0 (s%24) 0
  have flip (t : ℕ) (ht : t≤s) : (rev t).gcd 24=t.gcd 24 := by
    have mo : rev t ≡ 24-t%24 [MOD 24] := by
      change (24-s%24+s-t)%24=(24-t%24)%24
      omega
    exact mo.gcd_eq.trans ((neg_gcd ⟨_,Nat.mod_lt t (by decide)⟩).trans (Nat.mod_modEq t 24).gcd_eq)
  have compatible (t : ℕ) (ht : t≤s) : back (rev t) ↔ okay t := by
    change (rev t).gcd 24=(s%24+0*0).gcd 24 ↔ t.gcd 24=(a+b*r).gcd 24
    rw [flip t ht, Nat.zero_mul, Nat.add_zero, (Nat.mod_modEq s 24).gcd_eq,pass]
  have base : back v := by
    have eq : rev s = v := by dsimp [rev]; omega
    rw [←eq]; exact (compatible s (le_refl _)).mpr pass
  have pos := lane_nonempty (f:=v) (le_refl _) base
  let omitted := v+offset 0 (v%24) (s%24) 0 H
  have omitted_eq : omitted = v+gap s H := rfl
  have accepted : back omitted := at_index pos H
  have count : ((Ico v omitted).filter back).card=H := count_before pos H
  have reflected : ((Icc f s).filter okay).card = ((Icc v (rev f)).filter back).card := by
    apply card_bij (fun t _ => rev t)
    · intro t ht
      obtain ⟨int,ok⟩ := mem_filter.mp ht
      obtain ⟨ft,ts⟩ := mem_Icc.mp int
      exact mem_filter.mpr ⟨mem_Icc.mpr (by dsimp [rev]; omega),(compatible _ ts).mpr ok⟩
    · intro t ht z hz eq
      have l := (mem_Icc.mp (mem_filter.mp ht).1).2
      have u := (mem_Icc.mp (mem_filter.mp hz).1).2
      dsimp [rev] at eq
      omega
    · intro y hy
      obtain ⟨int,ok⟩ := mem_filter.mp hy
      obtain ⟨bot,top⟩ := mem_Icc.mp int
      have bounds : f≤rev y ∧ rev y≤s := by dsimp [rev] at top ⊢; omega
      have inverse : rev (rev y)=y := by dsimp [rev] at top ⊢; omega
      exact ⟨rev y,mem_filter.mpr ⟨mem_Icc.mpr bounds,
        (compatible (rev y) bounds.2).mp (by simpa only [inverse] using ok)⟩,inverse⟩
  have add_last : (Icc f s).filter okay = insert s ((Ico f s).filter okay) := by
    ext t
    simp only [mem_filter,mem_insert,mem_Icc,mem_Ico]
    dsimp only [okay]
    constructor
    · rintro ⟨⟨fl,sl⟩,ok⟩
      rcases sl.lt_or_eq with h|h
      · exact Or.inr ⟨⟨fl,h⟩,ok⟩
      · exact Or.inl h
    · rintro (rfl|⟨⟨fl,sl⟩,ok⟩)
      · exact ⟨⟨lo,le_refl _⟩,pass⟩
      · exact ⟨⟨fl,sl.le⟩,ok⟩
  have not_last : s∉(Ico f s).filter okay := fun h => (Nat.lt_irrefl s) (mem_Ico.mp (mem_filter.mp h).1).2
  rw [add_last,card_insert_of_not_mem not_last] at reflected
  rw [rank_iff lo pass]
  change ((Ico f s).filter okay).card<H ↔ _
  constructor
  · intro fewer
    by_contra! short
    have le : omitted≤rev f := by rw [omitted_eq]; dsimp [rev]; omega
    have sub : (Ico v omitted).filter back ⊆ (Icc v (rev f)).filter back := by
      apply filter_subset_filter
      intro t ht
      exact mem_Icc.mpr ⟨(mem_Ico.mp ht).1,(mem_Ico.mp ht).2.le.trans le⟩
    have strict := (ssubset_iff_of_subset sub).mpr ⟨omitted,
      mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.le_add_right _ _,le⟩,accepted⟩,
      fun h => (Nat.lt_irrefl omitted) (mem_Ico.mp (mem_filter.mp h).1).2⟩
    have h := card_lt_card strict
    omega
  · intro long
    have lt : rev f<omitted := by rw [omitted_eq]; dsimp [rev]; omega
    have sub : (Icc v (rev f)).filter back ⊆ (Ico v omitted).filter back := by
      apply filter_subset_filter
      intro t ht
      exact mem_Ico.mpr ⟨(mem_Icc.mp ht).1,(mem_Icc.mp ht).2.trans_lt lt⟩
    have h := card_le_card sub
    omega

/-- Compute one table entry per residue class of the unknown partner. -/
noncomputable def partnerGap (p a b phase H : ℕ) := gap (a*p+b*phase) H

private theorem gap_congr {s t H : ℕ} (eq : s≡t [MOD 24]) : gap s H=gap t H := by
  change s%24=t%24 at eq
  simp only [gap,eq]

/-- The coefficients A,B of a true split may differ from the public wheel
weights a,b. Only their product and the admissibility of the trace matter.
Natural subtraction handles a negative theoretical predecessor. -/
theorem allocation_square {p q A B a b phase H : ℕ} (pp : 0<p) (qp : 0<q)
    (ap : 0<A) (bp : 0<B) (weights : A*B=a*b) (res : q≡phase [MOD 24])
    (pass : (A*p+B*q).gcd 24=(a+b*((p*q)%24)).gcd 24) :
    let s := A*p+B*q
    let f := ceilSqrt (4*a*b*(p*q))
    let r := (p*q)%24
    (∃ i<H, s=f+offset r (f%24) a b i) ↔ (s-partnerGap p A B phase H)^2 < 4*A*B*(p*q) := by
  let s := A*p+B*q
  let n := 4*A*B*(p*q)
  let f := ceilSqrt n
  have sameWeight : 4*a*b*(p*q)=n := by dsimp [n]; rw [mul_assoc 4 a b,←weights,mul_assoc 4 A B]
  have lo : f≤s := by
    apply ceilSqrt_le_iff.mpr
    rw [multiplier_sum_square p q A B]
    exact Nat.le_add_right _ _
  have np : 0<n := by dsimp [n]; positivity
  have fp : 0<f := by
    by_contra! z
    have := ceilSqrt_le_iff.mp z
    norm_num at this
    omega
  have same : gap s H=partnerGap p A B phase H := gap_congr ((res.mul_left B).add_left (A*p))
  dsimp only
  rw [sameWeight,reverse_iff lo pass,←same]
  change s-f<gap s H ↔ (s-gap s H)^2<n
  have comp : f≤s-gap s H ↔ n≤(s-gap s H)^2 := ceilSqrt_le_iff
  omega

theorem square_criterion {p q a b phase H : ℕ} (pp : 0<p) (qp : 0<q)
    (ap : 0<a) (bp : 0<b) (pu : p.Coprime 6) (res : q≡phase [MOD 24]) :
    let s := a*p+b*q
    let f := ceilSqrt (4*a*b*(p*q))
    let r := (p*q)%24
    (∃ i<H, s=f+offset r (f%24) a b i) ↔ (s-partnerGap p a b phase H)^2 < 4*a*b*(p*q) :=
  allocation_square pp qp ap bp rfl res (sum_allowed a b pu)

/-- Integer endpoints for b*q when A=a*p and the backward gap is D. -/
def radius (A D : ℕ) : ℤ := ((4*(A:ℤ)*D-1).toNat.sqrt : ℕ)

def lower (A b D : ℕ) : ℤ := -((radius A D-((A:ℤ)+D))/b)
def upper (A b D : ℕ) : ℤ := (((A:ℤ)+D)+radius A D)/b

private theorem solve_quadratic {A q b D : ℕ} (ap : 0<A) (bp : 0<b) (cap : D≤A) :
    (A+b*q-D)^2<4*A*(b*q) ↔ 0<D ∧ lower A b D≤q ∧ (q:ℤ)≤upper A b D := by
  have cast : D≤A+b*q := cap.trans (Nat.le_add_right _ _)
  have moved : (A+b*q-D)^2<4*A*(b*q) ↔ ((b:ℤ)*q-((A:ℤ)+D))^2<4*(A:ℤ)*D := by
    have identity : ((A:ℤ)+b*q-D)^2-4*A*(b*q) = ((b:ℤ)*q-(A+D))^2-4*A*D := by ring
    have square : (A+b*q-D)^2<4*A*(b*q) ↔ ((A:ℤ)+b*q-D)^2<4*A*(b*q) := by
      have hcast : ((A+b*q-D:ℕ):ℤ)=(A:ℤ)+b*q-D := by
        simp only [Nat.cast_sub cast,Nat.cast_add,Nat.cast_mul]
      rw [←hcast]
      norm_cast
    rw [square]
    constructor <;> intro h <;> linarith only [identity,h]
  rw [moved]
  by_cases d : 0<D
  · have pos : (0:ℤ)<4*(A:ℤ)*D := by positivity
    rw [WeightedTracePrefix.square_strip pos, and_iff_right d]
    change -radius A D≤(b:ℤ)*q-((A:ℤ)+D) ∧ (b:ℤ)*q-((A:ℤ)+D)≤radius A D ↔ _
    have bz : (0:ℤ)<b := by exact_mod_cast bp
    have low : -((radius A D-((A:ℤ)+D))/b) ≤ (q:ℤ) ↔
        -(q:ℤ)≤(radius A D-((A:ℤ)+D))/b := by omega
    rw [lower,upper,low,Int.le_ediv_iff_mul_le bz,Int.le_ediv_iff_mul_le bz]
    constructor <;> rintro ⟨x,y⟩ <;> constructor <;> nlinarith only [x,y]
  · have zero : D=0 := by omega
    subst D
    simp [sq_nonneg]

private theorem all_lanes (r a b f : ℕ) : 0<(offsets r (f%24) a b).length := by
  let t := 24*f+(a+b*r)
  have lo : f≤t := by dsimp [t]; omega
  have same : t ≡ a+b*r [MOD 24] := by change (24*f+(a+b*r))%24=(a+b*r)%24; omega
  exact lane_nonempty lo same.gcd_eq

/-- Exact criterion for every orientation, including those whose true
trace fails the original search's wheel. -/
theorem allocation_interval {p q A B a b phase H : ℕ} (pp : 0<p) (qp : 0<q)
    (ap : 0<A) (bp : 0<B) (weights : A*B=a*b) (res : q≡phase [MOD 24])
    (cap : partnerGap p A B phase H ≤ A*p) :
    let s := A*p+B*q
    let f := ceilSqrt (4*a*b*(p*q))
    let r := (p*q)%24
    let D := partnerGap p A B phase H
    (∃ i<H, s=f+offset r (f%24) a b i) ↔
      s.gcd 24=(a+b*r).gcd 24 ∧ 0<D ∧ lower (A*p) B D≤q ∧ (q:ℤ)≤upper (A*p) B D := by
  dsimp only
  let f := ceilSqrt (4*a*b*(p*q))
  let r := (p*q)%24
  by_cases pass : (A*p+B*q).gcd 24=(a+b*r).gcd 24
  · have hit := allocation_square (H:=H) pp qp ap bp weights res pass
    dsimp only at hit
    rw [hit,and_iff_right pass]
    have order : 4*A*B*(p*q)=4*(A*p)*(B*q) := by ring
    rw [order]
    exact solve_quadratic (Nat.mul_pos ap pp) bp cap
  · constructor
    · rintro ⟨i,_,eq⟩
      exact (pass (eq ▸ at_index (all_lanes r a b f) i)).elim
    · exact fun h => (pass h.1).elim

/-- For fixed p, weights, budget and residue class of q, a trace is reached
exactly on one closed interval of integer partner values. One integer
square root computes both endpoints for the whole class. -/
theorem interval_criterion {p q a b phase H : ℕ} (pp : 0<p) (qp : 0<q)
    (ap : 0<a) (bp : 0<b) (pu : p.Coprime 6) (res : q≡phase [MOD 24])
    (cap : partnerGap p a b phase H ≤ a*p) :
    let s := a*p+b*q
    let f := ceilSqrt (4*a*b*(p*q))
    let r := (p*q)%24
    let D := partnerGap p a b phase H
    (∃ i<H, s=f+offset r (f%24) a b i) ↔
      0<D ∧ lower (a*p) b D≤q ∧ (q:ℤ)≤upper (a*p) b D := by
  dsimp only
  have hit := square_criterion (H:=H) pp qp ap bp pu res
  dsimp only at hit
  rw [hit]
  have order : 4*a*b*(p*q)=4*(a*p)*(b*q) := by ring
  rw [order]
  exact solve_quadratic (Nat.mul_pos ap pp) bp cap

/-- For any phase, the true backward gap is at most 24H: the original
label's residue repeats every 24. This bound suffices for the interval
criterion whenever 24H≤Ap. -/
theorem gap_le (s H : ℕ) : gap s H≤24*H := by
  let v := 24-s%24
  have base : test 0 (s%24) 0 v := by
    change (24-s%24).gcd 24=(s%24+0*0).gcd 24
    simp only [zero_mul,add_zero]
    exact neg_gcd ⟨_,Nat.mod_lt s (by decide)⟩
  have pos := lane_nonempty (f:=v) (le_refl _) base
  let omitted := v+gap s H
  have count : ((Ico v omitted).filter (test 0 (s%24) 0)).card=H := count_before pos H
  by_contra! far
  have into (i : ℕ) (hi : i∈range (H+1)) : v+24*i∈(Ico v omitted).filter (test 0 (s%24) 0) := by
    have small := mem_range.mp hi
    have phase : v+24*i ≡ v [MOD 24] := by change (v+24*i)%24=v%24; omega
    exact mem_filter.mpr ⟨mem_Ico.mpr ⟨Nat.le_add_right _ _,by dsimp [omitted]; omega⟩,
      phase.gcd_eq.trans base⟩
  have bad := card_le_card_of_injOn (fun i => v+24*i) into (by
    intro i _ j _ h; change v+24*i=v+24*j at h; omega)
  rw [count,card_range] at bad
  omega

/-- An exact public square/gcd split at any tested label comes from one of
the allocations AB=ab when the input is a product of distinct primes.
Conversely every such admitted allocation gives a proper divisor if ab is
coprime to the input. -/
theorem split_iff_allocations {p q a b H : ℕ} (pp : p.Prime) (qp : q.Prime)
    (ne : p≠q) (unit : (a*b).Coprime (p*q)) :
    let f := ceilSqrt (4*a*b*(p*q))
    let r := (p*q)%24
    let label i := f+offset r (f%24) a b i
    (∃ i<H, InteriorBatchPopulation.properSquare (p*q) (a*b) (label i)) ↔
      ∃ A B, A*B=a*b ∧ ∃ i<H, A*p+B*q=label i := by
  intro f r label
  constructor
  · rintro ⟨i,hi,hit⟩
    let s := label i
    let d := (s^2-4*(a*b)*(p*q)).sqrt
    obtain ⟨sq,lo,proper⟩ := hit
    have roots := OffsetSquareSplit.root_identities (k:=1) (N:=a*b*(p*q)) (d:=d) (S:=s)
      (by simpa only [d,s,one_pow,mul_one,mul_assoc] using sq)
    dsimp only at roots
    obtain ⟨x,y,mul,sum⟩ := ShiftedEndpointPopulation.allocation pp qp ne
      (by simpa using roots.2 : (s+d)/2*((s-d)/2)=(a*b)*(p*q)) lo proper
    refine ⟨y,x,by simpa only [Nat.mul_comm x y] using mul.symm,i,hi,?_⟩
    exact sum.symm.trans roots.1
  · rintro ⟨A,B,weights,i,hi,trace⟩
    refine ⟨i,hi,?_⟩
    rw [←trace]
    let s := A*p+B*q
    have id := multiplier_sum_square p q A B
    rw [mul_assoc 4 A B,weights] at id
    change s^2=4*(a*b)*(p*q)+(A*p).dist (B*q)^2 at id
    change s^2=4*(a*b)*(p*q)+(s^2-4*(a*b)*(p*q)).sqrt^2 ∧ _
    constructor
    · rw [id,Nat.add_sub_cancel_left,Nat.sqrt_eq']
    · have g := WeightedTracePrefix.shared_gcd (p:=p) (q:=q) rfl weights unit rfl
      rcases g with hp|hq
      · rw [hp]
        exact ⟨pp.one_lt,by nlinarith only [Nat.mul_le_mul_left p qp.two_le,pp.pos]⟩
      · rw [hq]
        exact ⟨qp.one_lt,by nlinarith only [Nat.mul_le_mul_right q pp.two_le,qp.pos]⟩

/-- Compatibility depends only on the partner residue even when the
allocation differs from the wheel used for enumeration. -/
theorem phase_pass {p q A B a b phase : ℕ} (res : q≡phase [MOD 24]) :
    ((A*p+B*q).gcd 24=(a+b*((p*q)%24)).gcd 24) ↔
    ((A*p+B*phase).gcd 24=(a+b*(p*phase)).gcd 24) := by
  have lhs := ((res.mul_left B).add_left (A*p)).gcd_eq
  have rhs := ((((Nat.mod_modEq (p*q) 24).trans (res.mul_left p)).mul_left b).add_left a).gcd_eq
  rw [lhs,rhs]

/-- A complete split criterion for one public residue lane. For short
budgets one can evaluate these intervals just once per candidate smaller
prime and partner residue, then count primes in the resulting union. -/
theorem split_iff_intervals {p q a b phase H : ℕ} (pp : p.Prime) (qp : q.Prime)
    (ne : p≠q) (ap : 0<a) (bp : 0<b) (unit : (a*b).Coprime (p*q))
    (res : q≡phase [MOD 24]) (short : 24*H≤p) :
    let f := ceilSqrt (4*a*b*(p*q))
    let r := (p*q)%24
    (∃ i<H, InteriorBatchPopulation.properSquare (p*q) (a*b) (f+offset r (f%24) a b i)) ↔
      ∃ A B, A*B=a*b ∧ (A*p+B*phase).gcd 24=(a+b*(p*phase)).gcd 24 ∧
        let D := partnerGap p A B phase H
        0<D ∧ lower (A*p) B D≤q ∧ (q:ℤ)≤upper (A*p) B D := by
  dsimp only
  have first := split_iff_allocations (H:=H) pp qp ne unit
  dsimp only at first
  rw [first]
  apply exists_congr; intro A
  apply exists_congr; intro B
  apply and_congr_right; intro weights
  have pos : 0<A*B := weights ▸ Nat.mul_pos ap bp
  have aa := Nat.pos_of_mul_pos_right pos
  have bb := Nat.pos_of_mul_pos_left pos
  have minp : p≤A*p := by simpa only [one_mul] using Nat.mul_le_mul_right p (show 1≤A from aa)
  have cap : partnerGap p A B phase H≤A*p := (gap_le _ _).trans (short.trans minp)
  have h := allocation_interval pp.pos qp.pos aa bb weights res cap
  dsimp only at h
  rwa [phase_pass res] at h

/-- Number of primes in the specified residue class strictly below x. -/
noncomputable def primePrefix (phase x : ℕ) := ((range x).filter (fun q => q.Prime ∧ q%24=phase%24)).card

/-- Two cumulative counts give the exact prime count on any inclusive
integer interval. Natural subtraction handles an empty reversed interval. -/
theorem count_interval (phase lo hi : ℕ) :
    ((Icc lo hi).filter (fun q => q.Prime ∧ q%24=phase%24)).card =
      primePrefix phase (hi+1)-primePrefix phase lo := by
  let P (q : ℕ) := q.Prime ∧ q%24=phase%24
  change ((Icc lo hi).filter P).card =
    ((range (hi+1)).filter P).card - ((range lo).filter P).card
  by_cases order : lo≤hi+1
  · have cover : (range (hi+1)).filter P = (range lo).filter P ∪ (Icc lo hi).filter P := by
      ext x
      simp only [mem_filter,mem_range,mem_union,mem_Icc]
      constructor
      · rintro ⟨lt,pr⟩
        by_cases before : x<lo
        · exact Or.inl ⟨before,pr⟩
        · exact Or.inr ⟨⟨by omega,by omega⟩,pr⟩
      · rintro (⟨lt,pr⟩|⟨⟨_,lt⟩,pr⟩) <;> exact ⟨by omega,pr⟩
    have dis : Disjoint ((range lo).filter P) ((Icc lo hi).filter P) := by
      rw [Finset.disjoint_left]
      intro q h k
      exact (not_lt_of_ge (mem_Icc.mp (mem_filter.mp k).1).1) (mem_range.mp (mem_filter.mp h).1)
    rw [cover,card_union_of_disjoint dis]
    omega
  · have cover := card_le_card (filter_subset_filter P (range_mono (by omega : hi+1≤lo)))
    rw [Nat.sub_eq_zero_of_le cover,Finset.Icc_eq_empty_of_lt (by omega : hi<lo)]
    simp

/-- Prime partners under a single orientation at a fixed smaller factor.
The outer bounds can include bit-width and public-product restrictions. -/
noncomputable def primePartners (p A B a b phase H lo hi : ℕ) : Finset ℕ := by
  classical
  exact (Icc lo hi).filter fun q => q.Prime ∧ q%24=phase%24 ∧
    let s := A*p+B*q
    let f := ceilSqrt (4*a*b*(p*q))
    ∃ i<H, s=f+offset ((p*q)%24) (f%24) a b i

/-- One orientation in one phase class is counted exactly by two prime
prefixes after clipping the algebraic endpoints to the requested interval. -/
theorem primePartners_card {p A B a b phase H lo hi : ℕ} (pp : 0<p) (ap : 0<A)
    (bp : 0<B) (weights : A*B=a*b) (cap : partnerGap p A B phase H≤A*p) :
    let D := partnerGap p A B phase H
    let l := max lo (lower (A*p) B D).toNat
    let u := min hi (upper (A*p) B D).toNat
    (primePartners p A B a b phase H lo hi).card =
      if (A*p+B*phase).gcd 24=(a+b*(p*phase)).gcd 24 ∧ 0<D
      then primePrefix phase (u+1)-primePrefix phase l else 0 := by
  classical
  let D := partnerGap p A B phase H
  let l := lower (A*p) B D
  let u := upper (A*p) B D
  have upos : 0≤u := by
    dsimp [u,upper,radius]
    positivity
  dsimp only
  by_cases eligible : (A*p+B*phase).gcd 24=(a+b*(p*phase)).gcd 24 ∧ 0<D
  · rw [if_pos eligible,←count_interval]
    have sets : primePartners p A B a b phase H lo hi =
        (Icc (max lo l.toNat) (min hi u.toNat)).filter (fun q => q.Prime ∧ q%24=phase%24) := by
      ext q
      simp only [primePartners,mem_filter,mem_Icc,max_le_iff,le_min_iff]
      constructor
      · rintro ⟨⟨ql,qh⟩,qp,res,hit⟩
        have cmp := allocation_interval (H:=H) pp qp.pos ap bp weights (show q≡phase [MOD 24] from res) cap
        obtain ⟨_,_,left,right⟩ := cmp.mp hit
        change l≤(q:ℤ) at left
        change (q:ℤ)≤u at right
        exact ⟨⟨⟨ql,by omega⟩,⟨qh,by omega⟩⟩,qp,res⟩
      · rintro ⟨⟨⟨ql,left⟩,qh,right⟩,qp,res⟩
        have mod : q≡phase [MOD 24] := res
        apply And.intro ⟨ql,qh⟩
        refine ⟨qp,res,(allocation_interval (H:=H) pp qp.pos ap bp weights mod cap).mpr ?_⟩
        exact ⟨(phase_pass mod).mpr eligible.1,eligible.2,
          show l≤(q:ℤ) by omega,show (q:ℤ)≤u by omega⟩
    exact congrArg Finset.card sets
  · rw [if_neg eligible,card_eq_zero]
    apply eq_empty_iff_forall_not_mem.mpr
    intro q mem
    obtain ⟨_,qp,res,hit⟩ := mem_filter.mp (by simpa only [primePartners] using mem)
    have mod : q≡phase [MOD 24] := res
    obtain ⟨check,dpos,_,_⟩ := (allocation_interval pp qp.pos ap bp weights mod cap).mp hit
    exact eligible ⟨(phase_pass mod).mp check,dpos⟩

end PrimeFactors.WeightedPartnerIntervals
