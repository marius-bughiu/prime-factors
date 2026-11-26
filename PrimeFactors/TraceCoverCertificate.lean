import Mathlib.Tactic

/-! Independent verification for upper and lower certificates of a rational
weighted-sum cover. The lower certificate prices coverage of the specified
probe ratios. Such probes need not correspond to actual divisors. -/

namespace PrimeFactors.TraceCoverCertificate

structure Point where
  num : ℕ
  den : ℕ
  deriving DecidableEq, Repr

structure Slope where
  a : ℕ
  b : ℕ
  start : ℕ
  step : ℕ
  deriving DecidableEq, Repr

def cutoff (m : ℕ) (s : Slope) (g : ℕ) := s.start+s.step*m*g

/-- Strict upper test on the first omitted label; includes zero-block schedules. -/
def covers (n m : ℕ) (s : Slope) (g : ℕ) (r : Point) : Bool :=
  decide (n*(s.a*r.den+s.b*r.num)^2 < r.num*r.den*(cutoff m s g)^2)

def positive (r : Point) : Bool := decide (0<r.num ∧ 0<r.den)

def before (l r : Point) : Bool := decide (l.num*r.den≤r.num*l.den)

noncomputable def Point.value (r : Point) : ℚ := (r.num:ℚ)/r.den

private theorem before_iff {l r : Point} (ld : 0<l.den) (rd : 0<r.den) :
    before l r ↔ l.value≤r.value := by
  simp only [before,decide_eq_true_eq,Point.value,div_le_div_iff₀
    (show (0:ℚ)<l.den by exact_mod_cast ld) (show (0:ℚ)<r.den by exact_mod_cast rd)]
  exact_mod_cast Iff.rfl

private theorem cover_iff {n m g : ℕ} {s : Slope} {r : Point} (rd : 0<r.den) :
    covers n m s g r ↔
      (n:ℚ)*((s.a:ℚ)+s.b*r.value)^2 < (cutoff m s g:ℚ)^2*r.value := by
  simp only [covers,decide_eq_true_eq,Point.value]
  have den : (0:ℚ)<r.den := by exact_mod_cast rd
  have cancel : ((n:ℚ)*((s.a:ℚ)+s.b*((r.num:ℚ)/r.den))^2)*(r.den:ℚ)^2 =
      (n:ℚ)*(s.a*r.den+s.b*r.num)^2 := by field_simp
  have cancel' : (((cutoff m s g:ℚ)^2)*((r.num:ℚ)/r.den))*(r.den:ℚ)^2 =
      (r.num:ℚ)*r.den*(cutoff m s g:ℚ)^2 := by field_simp; ring
  rw [←mul_lt_mul_iff_of_pos_right (sq_pos_of_pos den),cancel,cancel']
  exact_mod_cast Iff.rfl

/-- A quadratic with nonnegative leading coefficient stays negative between
any two points where it is negative. Its minimum may be outside the interval. -/
theorem whole_segment {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    {n a b T l x r : F} (hn : 0≤n) (lo : l≤x) (hi : x≤r)
    (left : n*(a+b*l)^2<T^2*l) (right : n*(a+b*r)^2<T^2*r) :
    n*(a+b*x)^2<T^2*x := by
  rcases eq_or_lt_of_le hi with eq | strict
  · simpa only [eq] using right
  have dl := sub_nonneg.mpr lo; have dr := sub_pos.mpr strict
  have span := sub_pos.mpr (lo.trans_lt strict)
  have sum := add_lt_add_of_lt_of_le
    (mul_lt_mul_of_pos_left left dr) (mul_le_mul_of_nonneg_left right.le dl)
  have defect := mul_nonneg (mul_nonneg hn (sq_nonneg b))
    (mul_nonneg span.le (mul_nonneg dr.le dl))
  apply lt_of_mul_lt_mul_left (a:=r-l) _ span.le
  nlinarith only [sum,defect]

/-- No relation between the tested slope and the segment endpoints is required. -/
theorem segment {n m g : ℕ} {s : Slope} {l x r : Point}
    (ld : 0<l.den) (xd : 0<x.den) (rd : 0<r.den) (lo : before l x) (hi : before x r)
    (left : covers n m s g l) (right : covers n m s g r) : covers n m s g x :=
  (cover_iff xd).mpr (whole_segment (by positivity) ((before_iff ld xd).mp lo)
    ((before_iff xd rd).mp hi) ((cover_iff ld).mp left) ((cover_iff rd).mp right))

/-- For an actual factor ratio the rational test bounds the ordinary integer trace. -/
theorem at_product {n m g p q : ℕ} {s : Slope} (prod : p*q=n)
    (h : covers n m s g ⟨q,p⟩) : s.a*p+s.b*q < cutoff m s g := by
  subst n
  change decide (_ < _) = true at h
  have hh := of_decide_eq_true h
  change p*q*(s.a*p+s.b*q)^2<q*p*(cutoff m s g)^2 at hh
  rw [mul_comm q p] at hh
  exact lt_of_not_ge (fun h => (Nat.not_lt_of_ge (Nat.pow_le_pow_left h 2))
    (Nat.lt_of_mul_lt_mul_left hh))

/-- Each successive right endpoint is paired with its zero-based schedule index.
The final endpoint agrees literally with `right`; different presentations of
neighboring rational endpoints are accepted by `before`. -/
def upperCheck (n m : ℕ) (schedule : List (Slope × ℕ)) (left right : Point) :
    List (Point × ℕ) → Bool
  | [] => false
  | (r,i)::more => match schedule[i]? with
    | none => false
    | some (s,g) => positive left && positive r && before left r &&
        covers n m s g left && covers n m s g r &&
        (if more.isEmpty then decide (r=right) else upperCheck n m schedule r right more)

private theorem real_test {n m g : ℕ} {s : Slope} {r : Point} (rd : 0<r.den) :
    covers n m s g r ↔ (n:ℝ)*((s.a:ℝ)+s.b*(r.value:ℝ))^2 < (cutoff m s g:ℝ)^2*(r.value:ℝ) := by
  rw [cover_iff rd]; constructor <;> intro h <;> exact_mod_cast h

/-- The finite integer checks certify strict coverage even at irrational ratios. -/
theorem upper_real {n m : ℕ} {schedule : List (Slope × ℕ)} {left right : Point} {x : ℝ}
    {cuts : List (Point × ℕ)} (proof : upperCheck n m schedule left right cuts)
    (lo : (left.value:ℝ)≤x) (hi : x≤(right.value:ℝ)) :
    ∃ e∈schedule, (n:ℝ)*((e.1.a:ℝ)+e.1.b*x)^2 < (cutoff m e.1 e.2:ℝ)^2*x := by
  induction cuts generalizing left with
  | nil => simp [upperCheck] at proof
  | cons v more ih =>
    obtain ⟨r,i⟩:=v
    unfold upperCheck at proof
    split at proof
    · contradiction
    next s g lookup =>
      simp only [Bool.and_eq_true,positive,decide_eq_true_eq] at proof
      obtain ⟨⟨⟨⟨⟨lp,rp⟩,_⟩,lh⟩,rh⟩,tail⟩:=proof
      by_cases within : x≤(r.value:ℝ)
      · exact ⟨(s,g),List.mem_of_getElem? lookup,whole_segment (by positivity) lo within
          ((real_test lp.2).mp lh) ((real_test rp.2).mp rh)⟩
      · split at tail
        · have eq := of_decide_eq_true tail
          subst r; exact (within hi).elim
        · exact ih tail (le_of_not_ge within)

private theorem endpoints_positive {n m : ℕ} {schedule : List (Slope × ℕ)} {l r : Point}
    {cuts : List (Point × ℕ)} (checked : upperCheck n m schedule l r cuts) : 0<l.den ∧ 0<r.den := by
  induction cuts generalizing l with
  | nil => simp [upperCheck] at checked
  | cons v tail ih =>
    obtain ⟨u,i⟩:=v; unfold upperCheck at checked; split at checked
    · contradiction
    next =>
      simp only [Bool.and_eq_true,positive,decide_eq_true_eq] at checked
      rcases checked with ⟨⟨⟨⟨⟨lp,up⟩,_⟩,_⟩,_⟩,more⟩
      refine ⟨lp.2,?_⟩; split at more
      · have eq := of_decide_eq_true more; exact eq ▸ up.2
      · exact (ih more).2

/-- Accepted pieces tile the entire closed rational interval. -/
theorem upper_sound {n m : ℕ} {schedule : List (Slope × ℕ)} {left right x : Point}
    {cuts : List (Point × ℕ)} (hx : 0<x.den) (proof : upperCheck n m schedule left right cuts)
    (lo : before left x) (hi : before x right) :
    ∃ e∈schedule, covers n m e.1 e.2 x := by
  obtain ⟨ld,rd⟩ := endpoints_positive proof
  have l := (before_iff ld hx).mp lo; have r := (before_iff hx rd).mp hi
  obtain ⟨e,mem,h⟩ := upper_real (x:=(x.value:ℝ)) proof (by exact_mod_cast l) (by exact_mod_cast r)
  exact ⟨e,mem,(real_test hx).mpr h⟩

private def sumBy {α : Type} (f : α → ℕ) : List α → ℕ
  | [] => 0
  | x::xs => f x + sumBy f xs

private theorem sumBy_eq {α : Type} (f : α → ℕ) (l : List α) : sumBy f l = (l.map f).sum := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp only [sumBy,List.map_cons,List.sum_cons,ih]

/-- Total probe weight, counting repeated probes at their full weight. -/
def mass (probes : List (Point × ℕ)) := sumBy Prod.snd probes

def credit (n m : ℕ) (s : Slope) (g : ℕ) (p : Point × ℕ) :=
  if covers n m s g p.1 then p.2 else 0

def observed (n m : ℕ) (s : Slope) (g : ℕ) (probes : List (Point × ℕ)) :=
  sumBy (credit n m s g) probes

/-- Check every block count cheaper than the asserted lower bound. Larger
counts already pay the entire probe weight. -/
def lowerCheck (n m : ℕ) (catalogue : List Slope) (probes : List (Point × ℕ)) : Bool :=
  catalogue.all fun s => (List.range (mass probes)).all fun g =>
    decide (observed n m s g probes ≤ g)

/-- Independent test that the lower witness uses positive probes inside the domain. -/
def probesIn (left right : Point) (probes : List (Point × ℕ)) : Bool :=
  positive left && positive right && probes.all fun p =>
    positive p.1 && before left p.1 && before p.1 right

private theorem sum_mono {α : Type} {f g : α → ℕ} {l : List α}
    (h : ∀ x∈l, f x≤g x) : (l.map f).sum≤(l.map g).sum := by
  induction l with
  | nil => rfl
  | cons x xs ih => exact Nat.add_le_add (h x (by simp)) (ih (fun t ht => h t (by simp [ht])))

private theorem mem_sum {w : ℕ} {l : List ℕ} (h : w∈l) : w≤l.sum := by
  induction l with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with rfl|rest
    · simp
    · simpa only [List.sum_cons] using (ih rest).trans (Nat.le_add_left xs.sum x)

private theorem union_bound {n m : ℕ} {schedule : List (Slope × ℕ)} {ps : List (Point × ℕ)}
    (cover : ∀ p∈ps, ∃ e∈schedule, covers n m e.1 e.2 p.1) :
    mass ps ≤ (schedule.map (fun e => observed n m e.1 e.2 ps)).sum := by
  induction ps with
  | nil => simp [mass,observed,sumBy]
  | cons p ps ih =>
    obtain ⟨e,he,hit⟩ := cover p (by simp)
    have mem : p.2 ∈ schedule.map (fun z => credit n m z.1 z.2 p) := by
      exact List.mem_map.mpr ⟨e,he,by simp [credit,hit]⟩
    have tail := ih (fun t ht => cover t (by simp [ht]))
    have total := Nat.add_le_add (mem_sum mem) tail
    simpa only [mass,observed,sumBy_eq,List.map_cons,List.sum_cons,List.sum_map_add] using total

/-- Every schedule made from the catalogue that covers all probes costs at
least their total weight. Repeating a slope in the schedule is allowed. -/
theorem lower_sound {n m : ℕ} {catalogue : List Slope} {probes : List (Point × ℕ)}
    (checked : lowerCheck n m catalogue probes) (schedule : List (Slope × ℕ))
    (inside : ∀ e∈schedule, e.1∈catalogue)
    (cover : ∀ p∈probes, ∃ e∈schedule, covers n m e.1 e.2 p.1) :
    mass probes ≤ (schedule.map Prod.snd).sum := by
  apply (union_bound cover).trans
  apply sum_mono; rintro ⟨s,g⟩ hs
  by_cases hg : g<mass probes
  · apply of_decide_eq_true
    exact List.all_eq_true.mp (List.all_eq_true.mp checked s (inside _ hs)) g (List.mem_range.mpr hg)
  · apply le_trans _ (Nat.le_of_not_gt hg)
    simp only [observed,mass,sumBy_eq]; apply sum_mono; intro x _; unfold credit; split <;> simp


/-- Coverage is a geometric property of every rational ratio in the interval. -/
def CoversRange (n m : ℕ) (schedule : List (Slope × ℕ)) (left right : Point) : Prop :=
  ∀ x : Point, 0<x.den → before left x → before x right → ∃ e∈schedule, covers n m e.1 e.2 x

def cost (schedule : List (Slope × ℕ)) := sumBy Prod.snd schedule

def admissible (catalogue : List Slope) (schedule : List (Slope × ℕ)) : Bool :=
  schedule.all fun e => catalogue.any fun s =>
    s.a==e.1.a && s.b==e.1.b && s.start==e.1.start && s.step==e.1.step

theorem catalogue_member {catalogue : List Slope} {schedule : List (Slope × ℕ)}
    (allowed : admissible catalogue schedule) {e : Slope × ℕ} (he : e∈schedule) : e.1∈catalogue := by
  obtain ⟨s,hs,eq⟩ := List.any_eq_true.mp (List.all_eq_true.mp allowed e he)
  simp only [Bool.and_eq_true,beq_iff_eq] at eq
  have same : s=e.1 := by cases s; rcases e with ⟨⟨_,_,_,_⟩,_⟩; simp_all
  exact same ▸ hs

/-- The upper and lower certificates together establish global optimality for
this catalogue, labelled window rule, and rational ratio interval. -/
theorem certified_minimum {n m : ℕ} {catalogue : List Slope} {schedule : List (Slope × ℕ)}
    {left right : Point} {cuts probes : List (Point × ℕ)}
    (upper : upperCheck n m schedule left right cuts) (allowed : admissible catalogue schedule)
    (lower : lowerCheck n m catalogue probes) (inside : probesIn left right probes)
    (price : cost schedule = mass probes) :
    admissible catalogue schedule ∧ CoversRange n m schedule left right ∧
    ∀ alternative, admissible catalogue alternative → CoversRange n m alternative left right →
      cost schedule ≤ cost alternative := by
  refine ⟨allowed,fun _ hx lo hi => upper_sound hx upper lo hi,?_⟩
  intro alternative permitted cover
  rw [price,cost,sumBy_eq]
  apply lower_sound lower alternative (fun _ he => catalogue_member permitted he)
  intro p hp
  simp only [probesIn,Bool.and_eq_true] at inside
  obtain ⟨_,probed⟩ := inside
  have conditions := List.all_eq_true.mp probed p hp
  simp only [Bool.and_eq_true,positive,decide_eq_true_eq] at conditions
  exact cover p.1 conditions.1.1.2 conditions.1.2 conditions.2

/-- The segment lies strictly to the right of the unique catalogue slope.
At zero blocks its rightmost probe fails the test, and one block suffices. -/
theorem example_optimum :
    let s : Slope := ⟨1,1,8,2⟩
    let left : Point := ⟨3,2⟩
    let right : Point := ⟨2,1⟩
    CoversRange 15 1 [(s,1)] left right ∧
    ∀ alt, admissible [s] alt → CoversRange 15 1 alt left right → 1≤cost alt := by
  dsimp only
  exact (certified_minimum (cuts:=[(⟨2,1⟩,0)]) (probes:=[(⟨2,1⟩,1)])
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)).2

end PrimeFactors.TraceCoverCertificate
