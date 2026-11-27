import PrimeFactors.IntermediateTotientRows
import PrimeFactors.IntermediateTotientObstruction

/-! A dyadic deficit band meets at most one upper block of the Euclidean walk.
The selected block is read via its two coefficient endpoints. -/
namespace PrimeFactors.IntermediateBlockCutoff

open UpperConvergentDeficit (Row step next_upper next_lower)
open IntermediateTotientRows
open IntermediateTotientObstruction (rowAt)

structure Window where
  index : ℕ
  lo : ℕ
  hi : ℕ
deriving DecidableEq, Repr

/-- An empty endpoint interval selects no coefficients. -/
def contains (w : Option Window) (i t : ℕ) : Prop :=
  ∃ b, w=some b ∧ b.index=i ∧ b.lo≤t ∧ t≤b.hi

/-- The inspected row has a positive numerator and its exact rational deficit lies in [L,H). -/
def InBand (N E L H : ℕ) (z : Row) : Prop :=
  0<z.a ∧ E*z.b+L*z.a≤N*z.a ∧ N*z.a<E*z.b+H*z.a

def Eligible (N E L H i t u v : ℕ) (x y : Row) : Prop :=
  ∃ z, rowAt i t u v x y=some z ∧ InBand N E L H z

/-- The strict upper endpoint H determines the initial coefficient independently of L. -/
def firstAt (u v H a₀ a₁ : ℕ) := 1+(u-H*a₀)/(v+H*a₁)

theorem range_iff {u v L H a₀ a₁ t : ℕ} (vp : 0<v) :
    firstAt u v H a₀ a₁ ≤ t ∧ t ≤ last u v L a₀ a₁ ↔
      1≤t ∧ t≤u/v ∧ L*(a₀+t*a₁)+t*v≤u ∧ u<H*(a₀+t*a₁)+t*v := by
  have p₁ : 0<v+L*a₁ := by omega
  have p₂ : 0<v+H*a₁ := by omega
  rw [firstAt,last,le_min_iff]
  have lower {t : ℕ} (tp : 0<t) :
      (u-H*a₀)/(v+H*a₁)<t ↔ u<H*a₀+t*(v+H*a₁) := by
    rw [Nat.div_lt_iff_lt_mul p₂]
    have := Nat.mul_pos tp p₂
    omega
  have upper {t : ℕ} (tp : 0<t) :
      t≤(u-L*a₀)/(v+L*a₁) ↔ L*a₀+t*(v+L*a₁)≤u := by
    rw [Nat.le_div_iff_mul_le p₁]
    have := Nat.mul_pos tp p₁
    omega
  constructor
  · rintro ⟨lo,q,hi⟩
    have tp : 0<t := (by positivity : 0<1+(u-H*a₀)/(v+H*a₁)).trans_le lo
    have a := (lower tp).mp (by omega)
    have b := (upper tp).mp hi
    exact ⟨tp,q,by nlinarith only [b],by nlinarith only [a]⟩
  · rintro ⟨tp,q,lo,hi⟩
    exact ⟨by have := (lower tp).mpr (by nlinarith only [hi]); omega,q,
      (upper tp).mpr (by nlinarith only [lo])⟩

theorem width_range {N E u v L H t : ℕ} {x y : Row} (vp : 0<v)
    (high : N*x.a=E*x.b+u) (low : E*y.b=N*y.a+v) :
    firstAt u v H x.a y.a ≤ t ∧ t ≤ last u v L x.a y.a ↔
      1≤t ∧ t≤u/v ∧ E*(step x y t).b+L*(step x y t).a≤N*(step x y t).a ∧
        N*(step x y t).a < E*(step x y t).b+H*(step x y t).a := by
  rw [range_iff vp]
  simp only [step]
  have eq : N*(x.a+t*y.a)+t*v=E*(x.b+t*y.b)+u := by
    nlinarith only [high,congrArg (fun z => t*z) low]
  omega

/-- Skipping uses ordinary Euclidean quotient and remainder updates and one comparison.
Only the return branch needs the two extra divisions for the coefficient endpoints. -/
def seek : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Row → Row → Option Window
  | 0, _, _, _, _, _, _, _ => none
  | fuel+1, index, L, H, u, v, x, y =>
    if v=0 then none else
      let z := step x y (u/v)
      let r := u%v
      if r<H*z.a then some ⟨index,firstAt u v H x.a y.a,last u v L x.a y.a⟩
      else if r=0 then none
      else seek fuel (index+2) L H r (v%r) z (step y z (v/r))

/-- The initial block from (0,1),(1,0) is lower, even when E≥N.
The first upper block has index one, with high parent (1,0). -/
def locateInterval (N E L H : ℕ) : Option Window :=
  if N=0 then none else
    seek (E%N) 1 L H N (E%N) ⟨1,0⟩ (step ⟨0,1⟩ ⟨1,0⟩ (E/N))

private theorem no_selection (i t : ℕ) : ¬contains none i t := by simp [contains]

private theorem ended (N E L H i t u : ℕ) (x y : Row) : ¬ Eligible N E L H i t u 0 x y := by
  rintro ⟨z,h,_⟩
  cases i <;> simp [rowAt] at h

private theorem shift {v : ℕ} (vp : 0<v) (N E L H i t u : ℕ) (x y : Row) :
    Eligible N E L H (i+1) t u v x y ↔
      Eligible N E L H i t v (u%v) y (step x y (u/v)) := by
  cases v with
  | zero => omega
  | succ v => rfl

private theorem here {v : ℕ} (vp : 0<v) (N E L H t u : ℕ) (x y : Row) :
    Eligible N E L H 0 t u v x y ↔ 0<t ∧ t≤u/v ∧ InBand N E L H (step x y t) := by
  cases v with
  | zero => omega
  | succ v =>
    simp only [Eligible,rowAt]
    split_ifs with ht <;> simp <;> tauto

private theorem upper {N E L H t u v : ℕ} {x y : Row} (vp : 0<v) (xp : 0<x.a)
    (high : N*x.a=E*x.b+u) (low : E*y.b=N*y.a+v) :
    Eligible N E L H 0 t u v x y ↔
      firstAt u v H x.a y.a≤t ∧ t≤last u v L x.a y.a := by
  rw [here vp,width_range vp high low]
  have pos : 0<(step x y t).a := by dsimp [step]; omega
  simp [InBand,pos,Nat.succ_le_iff]

private theorem lower {N E L H t u v : ℕ} {x y : Row} (vp : 0<v) (lp : 0<L)
    (low : E*x.b=N*x.a+u) (high : N*y.a=E*y.b+v) :
    ¬ Eligible N E L H 0 t u v x y := by
  rw [here vp]
  rintro ⟨_,fits,ap,bound,_⟩
  exact (not_lt_of_ge bound) (lower_skips vp lp fits ap low high)

private theorem mono (x y : Row) {s t : ℕ} (h : s≤t) : (step x y s).a≤(step x y t).a :=
  Nat.add_le_add_left (Nat.mul_le_mul_right _ h) _

private theorem initial_le (x y : Row) {t : ℕ} (h : 0<t) : x.a+y.a≤(step x y t).a := by
  simpa [step] using mono x y h

/-- If the ordinary upper endpoint is still at least H, every preceding coefficient
in that same block misses the strict upper edge of the band. Equality is included. -/
theorem skip {u v L H t : ℕ} {x y : Row} (vp : 0<v)
    (above : H*(step x y (u/v)).a≤u%v) :
    ¬ (firstAt u v H x.a y.a≤t ∧ t≤last u v L x.a y.a) := by
  rw [range_iff vp]
  rintro ⟨_,fits,_,strict⟩
  have num := Nat.mul_le_mul_left H (mono x y fits)
  have err := Nat.mul_le_mul_right v fits
  have mass : u%v+u/v*v=u := by simpa [Nat.mul_comm] using Nat.mod_add_div u v
  change H*(x.a+t*y.a)≤_ at num
  omega

/-- A hit anywhere at or after this upper block must be at least as accessible
as its first coefficient. This applies to every later block in the terminated walk. -/
private theorem threshold {N E L H : ℕ} (lp : 0<L) (i t u v : ℕ) (x y : Row)
    (vu : v≤u) (xp : 0<x.a) (high : N*x.a=E*x.b+u) (low : E*y.b=N*y.a+v)
    (hit : Eligible N E L H i t u v x y) : L*(x.a+y.a)≤u := by
  induction i using Nat.strong_induction_on generalizing t u v x y with
  | h i ih =>
    by_cases vz : v=0
    · subst v; exact False.elim (ended _ _ _ _ _ _ _ _ _ hit)
    have vp := Nat.pos_of_ne_zero vz
    let z := step x y (u/v)
    let r := u%v
    have num : x.a+y.a≤z.a := initial_le _ _ (Nat.div_pos vu vp)
    have zp : 0<z.a := by omega
    have high' : N*z.a=E*z.b+r := next_upper high low
    cases i with
    | zero =>
      obtain ⟨tp,_,bot,_⟩ := (range_iff vp).1 ((upper vp xp high low).1 hit)
      have line := Nat.mul_le_mul_left L (initial_le x y tp)
      change L*(x.a+y.a)≤L*(x.a+t*y.a) at line
      omega
    | succ i =>
      have later := (shift vp _ _ _ _ i _ _ _ _).1 hit
      by_cases rz : r=0
      · change Eligible N E L H i t v r y z at later
        rw [rz] at later
        exact False.elim (ended _ _ _ _ _ _ _ _ _ later)
      have rp := Nat.pos_of_ne_zero rz
      cases i with
      | zero => exact False.elim (lower rp lp low high' later)
      | succ j =>
        let w := step y z (v/r)
        have next := (shift rp _ _ _ _ j _ _ _ _).1 later
        have need := ih j (by omega) t r (v%r) z w (Nat.mod_lt _ rp).le zp
          high' (next_lower low high') next
        exact ((Nat.mul_le_mul_left L (num.trans (Nat.le_add_right ..))).trans need).trans
          (Nat.mod_le _ _)

/-- At a qualifying endpoint, even the first upper of the next upper block is already
below L. The intervening ordinary lower step has numerator at least the upper endpoint's. -/
theorem drop {u v L : ℕ} {x y : Row} (vp : 0<v) (rp : 0<u%v)
    (cut : u%v<2*L*(step x y (u/v)).a) :
    u%v<L*((step x y (u/v)).a+(step y (step x y (u/v)) (v/(u%v))).a) := by
  let z := step x y (u/v)
  have big := initial_le y z (Nat.div_pos (Nat.mod_lt u vp).le rp)
  have num : 2*z.a≤z.a+(step y z (v/(u%v))).a := by omega
  have bound := Nat.mul_le_mul_left L num
  exact cut.trans_le (by simpa only [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm,z] using bound)

/-- The first allowable coefficient in the next upper block has strictly less than half the
deficit of the present upper endpoint. A zero next lower remainder ends the Euclidean walk. -/
theorem first_drop {u v : ℕ} {x y : Row} (vp : 0<v) (rp : 0<u%v) (sp : 0<v%(u%v))
    (zp : 0<(step x y (u/v)).a) :
    let z := step x y (u/v)
    let w := step y z (v/(u%v))
    2*(u%v-v%(u%v))*z.a < (u%v)*(step z w 1).a := by
  let z := step x y (u/v)
  let w := step y z (v/(u%v))
  have big := initial_le y z (Nat.div_pos (Nat.mod_lt u vp).le rp)
  have doubled : 2*z.a≤(step z w 1).a := by
    change y.a+z.a≤w.a at big
    simp only [step,Nat.one_mul]
    omega
  exact UpperConvergentDeficit.strict_drop zp doubled (Nat.sub_lt rp sp)

/-- The index of a selected window can never precede the current block. -/
private theorem index_le (fuel index L H u v : ℕ) (x y : Row) {b : Window}
    (selected : seek fuel index L H u v x y=some b) : index≤b.index := by
  induction fuel generalizing index u v x y with
  | zero => simp [seek] at selected
  | succ k ih =>
    simp only [seek] at selected
    split at selected
    · contradiction
    split at selected
    · injection selected with eq
      rw [←eq]
    split at selected
    · contradiction
    exact (by omega : index ≤ index+2).trans (ih _ _ _ _ _ selected)

private theorem early {k index L H u v i t : ℕ} {x y : Row} (lt : i < index) :
    ¬contains (seek k index L H u v x y) i t := by
  rintro ⟨b,sel,now,_,_⟩
  have := index_le _ _ _ _ _ _ _ _ sel
  omega

private theorem seek_correct {N E L H : ℕ} (lp : 0<L) (hp : 0<H) (capH : H≤2*L) (fuel index i t u v : ℕ) (x y : Row)
    (cap : v≤fuel) (vu : v≤u) (xp : 0<x.a) (high : N*x.a=E*x.b+u) (low : E*y.b=N*y.a+v) :
    contains (seek fuel index L H u v x y) (index+i) t ↔ Eligible N E L H i t u v x y := by
  induction fuel generalizing index i t u v x y with
  | zero =>
    have : v=0 := by omega
    subst v
    exact iff_of_false (no_selection _ _) (ended _ _ _ _ _ _ _ _ _)
  | succ k ih =>
    by_cases vz : v=0
    · subst v
      simpa only [seek,if_pos rfl] using iff_of_false (no_selection (index+i) t)
        (ended N E L H i t u x y)
    have vp := Nat.pos_of_ne_zero vz
    let z := step x y (u/v)
    let r := u%v
    let w := step y z (v/r)
    have num : x.a+y.a≤z.a := initial_le _ _ (Nat.div_pos vu vp)
    have zp : 0<z.a := by omega
    have high' : N*z.a=E*z.b+r := next_upper high low
    have rv : r<v := Nat.mod_lt _ vp
    rw [seek,if_neg vz]
    change contains (if r<H*z.a then some _ else if r=0 then none else _) (index+i) t ↔ _
    by_cases cut : r<H*z.a
    · rw [if_pos cut]
      cases i with
      | zero =>
        simpa [contains] using (upper (t:=t) (L:=L) vp xp high low).symm
      | succ j =>
        have pre : ¬contains (some ⟨index,firstAt u v H x.a y.a,last u v L x.a y.a⟩)
            (index+(j+1)) t := by simp [contains]
        apply iff_of_false pre
        rw [shift vp]
        change ¬ Eligible N E L H j t v r y z
        by_cases rz : r=0
        · rw [rz]; exact ended _ _ _ _ _ _ _ _ _
        have rp := Nat.pos_of_ne_zero rz
        cases j with
        | zero => exact lower rp lp low high'
        | succ j =>
          rw [shift rp]
          intro hit
          have needed := threshold (H:=H) lp j t r (v%r) z w (Nat.mod_lt _ rp).le zp high'
            (next_lower low high') hit
          exact (not_lt_of_ge needed) (drop vp rp (cut.trans_le (Nat.mul_le_mul_right z.a capH)))
    · rw [if_neg cut]
      have pos := Nat.mul_pos hp zp
      have rp : 0<r := by omega
      rw [if_neg rp.ne']
      cases i with
      | zero =>
        apply iff_of_false (early (by omega))
        rw [upper vp xp high low]
        exact skip vp (Nat.le_of_not_gt cut)
      | succ j =>
        rw [shift vp]
        change _ ↔ Eligible N E L H j t v r y z
        cases j with
        | zero => exact iff_of_false (early (by omega)) (lower rp lp low high')
        | succ j =>
          rw [shift rp]
          have sr := Nat.mod_lt v rp
          have rec := ih (index+2) j t r (v%r) z w (by omega) sr.le zp high'
            (next_lower low high')
          simpa only [show index+(j+1+1)=index+2+j by omega] using rec

/-- Exact agreement with the positive intermediate rows of the full native walk.
It covers every index, including invalid coefficients and indices past termination. -/
theorem correct_interval (N E : ℕ) {L H : ℕ} (lp : 0<L) (hp : 0<H) (capH : H≤2*L) (i t : ℕ) :
    contains (locateInterval N E L H) i t ↔ Eligible N E L H i t E N ⟨0,1⟩ ⟨1,0⟩ := by
  by_cases nz : N=0
  · subst N
    exact iff_of_false (no_selection _ _) (ended _ _ _ _ _ _ _ _ _)
  have np := Nat.pos_of_ne_zero nz
  rw [locateInterval,if_neg nz]
  have lo : E*(Row.mk 0 1).b=N*(Row.mk 0 1).a+E := by simp
  have hi : N*(Row.mk 1 0).a=E*(Row.mk 1 0).b+N := by simp
  cases i with
  | zero => exact iff_of_false (early (by decide)) (lower np lp lo hi)
  | succ j =>
    rw [shift np]
    simpa only [Nat.add_comm 1 j] using
      seek_correct lp hp capH (E%N) 1 j t N (E%N) ⟨1,0⟩ _ le_rfl (Nat.mod_lt E np).le (by decide)
        hi (next_lower lo hi)

/-- The original dyadic cutoff is the interval specialization H=2L. -/
def locate (N E L : ℕ) : Option Window := locateInterval N E L (2*L)

theorem correct (N E : ℕ) {L : ℕ} (lp : 0<L) (i t : ℕ) :
    contains (locate N E L) i t ↔ Eligible N E L (2*L) i t E N ⟨0,1⟩ ⟨1,0⟩ :=
  correct_interval N E lp (by omega) le_rfl i t

/-- Clipping [B,2B) to any contained interval [L,H) can only discard coefficients.
Each surviving row has the same index and coefficient in the original dyadic window. -/
theorem subwindow {N E B L H i t : ℕ} (bp : 0<B) (bot : B≤L) (capH : H≤2*B)
    (narrow : Eligible N E L H i t E N ⟨0,1⟩ ⟨1,0⟩) :
    contains (locate N E B) i t := by
  obtain ⟨z,found,ap,lo,hi⟩ := narrow
  apply (correct _ _ bp _ _).2
  exact ⟨z,found,ap,(Nat.add_le_add_left (Nat.mul_le_mul_right z.a bot) _).trans lo,
    hi.trans_le (Nat.add_le_add_left (Nat.mul_le_mul_right z.a capH) _)⟩

/-- The dyadic locator followed by clipping both edges returns exactly the same coefficients
as locating the narrower window directly. The original locator already certifies positivity. -/
theorem clip_iff {N E B L H i t : ℕ} (bp : 0<B) (hp : 0<H) (bot : B≤L) (capH : H≤2*B) :
    contains (locateInterval N E L H) i t ↔ contains (locate N E B) i t ∧
      ∃ z, rowAt i t E N ⟨0,1⟩ ⟨1,0⟩=some z ∧
        E*z.b+L*z.a≤N*z.a ∧ N*z.a<E*z.b+H*z.a := by
  rw [correct_interval N E (bp.trans_le bot) hp (by omega)]
  constructor
  · intro h
    have mem := subwindow bp bot capH h
    obtain ⟨z,found,_,lo,hi⟩ := h
    exact ⟨mem,z,found,lo,hi⟩
  · rintro ⟨dyadic,z,found,lo,hi⟩
    obtain ⟨w,broad,ap,_,_⟩ := (correct _ _ bp _ _).1 dyadic
    obtain rfl := Option.some.inj (broad.symm.trans found)
    exact ⟨w,broad,ap,lo,hi⟩

/-- The first coefficient has the largest deficit. A strict miss below the inclusive
lower edge excludes the entire block, before computing either coefficient endpoint. -/
theorem below_first {u v L H t : ℕ} {x y : Row} (vp : 0<v)
    (below : u-v<L*(x.a+y.a)) :
    ¬ (firstAt u v H x.a y.a≤t ∧ t≤last u v L x.a y.a) := by
  rw [range_iff vp]
  rintro ⟨tp,_,bound,_⟩
  have num := Nat.mul_le_mul_left L (initial_le x y tp)
  change L*(x.a+y.a)≤L*(x.a+t*y.a) at num
  have tv := Nat.le_mul_of_pos_left v tp
  omega

/-- Either empty-edge test skips both endpoint divisions, including on the dyadic
locator's selected block. Equality at H is excluded; equality at L can survive. -/
theorem empty_edges {N E L H t u v : ℕ} {x y : Row} (vp : 0<v) (xp : 0<x.a)
    (high : N*x.a=E*x.b+u) (low : E*y.b=N*y.a+v)
    (empty : H*(step x y (u/v)).a≤u%v ∨ u-v<L*(x.a+y.a)) :
    ¬ Eligible N E L H 0 t u v x y := by
  rw [upper vp xp high low]
  exact empty.elim (skip vp) (below_first vp)

/-- Any number of surviving coefficients must lie in a single quotient block. -/
theorem one_block {N E L H i j t s : ℕ} (lp : 0<L) (hp : 0<H) (capH : H≤2*L)
    (left : Eligible N E L H i t E N ⟨0,1⟩ ⟨1,0⟩)
    (right : Eligible N E L H j s E N ⟨0,1⟩ ⟨1,0⟩) : i=j := by
  obtain ⟨a,h,ai,_,_⟩ := (correct_interval _ _ lp hp capH _ _).2 left
  obtain ⟨b,k,bj,_,_⟩ := (correct_interval _ _ lp hp capH _ _).2 right
  obtain rfl := Option.some.inj (h.symm.trans k)
  exact ai.symm.trans bj

/-- Retain every row representing the true ratio E/F whenever the actual deficit lies
in the stated public interval. A positive numerator is needed to preserve its strict edge. -/
theorem retain {N E F L H i t : ℕ} {z : Row} (lp : 0<L) (hp : 0<H) (capH : H≤2*L)
    (fn : F≤N) (lo : L≤N-F) (hi : N-F<H) (ap : 0<z.a)
    (found : rowAt i t E N ⟨0,1⟩ ⟨1,0⟩ = some z) (eq : E*z.b=z.a*F) :
    contains (locateInterval N E L H) i t := by
  apply (correct_interval _ _ lp hp capH _ _).2
  refine ⟨z,found,ap,?_,?_⟩
  · rw [eq,Nat.mul_comm z.a,←Nat.add_mul]
    exact Nat.mul_le_mul_right _ (by omega)
  · rw [eq,Nat.mul_comm z.a,←Nat.add_mul]
    exact Nat.mul_lt_mul_of_pos_right (by omega) ap

/-- Without the interval-ratio assumption two blocks can contain eligible rows. For
391=17·23 and E=137, the deficits at 6/17 and 13/37 are 17/6 and 14/13. Both lie
in [1,3). This example concerns a general interval and makes no claim about the totient. -/
theorem wider_example :
    Eligible 391 137 1 3 3 5 137 391 ⟨0,1⟩ ⟨1,0⟩ ∧
    Eligible 391 137 1 3 5 1 137 391 ⟨0,1⟩ ⟨1,0⟩ := by
  exact ⟨⟨⟨6,17⟩,by decide,by unfold InBand; decide⟩,
    ⟨⟨13,37⟩,by decide,by unfold InBand; decide⟩⟩

/-- At 437, narrowing the public deficit interval shortens the third-indexed block.
The second input has a large first quotient and needs only the two range divisions. -/
theorem examples :
    locate 437 224 32=some ⟨3,2,4⟩ ∧
    locateInterval 437 224 33 62=some ⟨3,3,4⟩ ∧
    locateInterval 1000003 2 123 130=some ⟨1,499937,499940⟩ ∧
    locate 123 123 8=none := by decide +kernel

end PrimeFactors.IntermediateBlockCutoff
