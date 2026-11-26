import PrimeFactors.TraceProgression
import PrimeFactors.Fermat
import Mathlib.Algebra.Order.Floor.Div

/-! Porting a weighted-trace cover to a different product. The template
need only cover the geometric ratios. Its own factors are never used. -/

namespace PrimeFactors.TraceCoverTransfer

open TraceCoverCertificate

/-- All rows have the same strides for products in the same class modulo 12. -/
theorem stride_congr {n old : ℕ} (same : n ≡ old [MOD 12]) (a b : ℕ) :
    weightedStride n a b=weightedStride old a b := by
  have congr : a+b*n ≡ a+b*old [MOD 12] := (same.mul_left b).add_left a
  unfold weightedStride
  rw [show 24=2*12 by decide,Nat.gcd_mul_left,Nat.gcd_mul_left]
  rw [Nat.gcd_rec 12 (a+b*n),Nat.gcd_rec 12 (a+b*old)]
  rw [show (a+b*n)%12=(a+b*old)%12 from congr]

private theorem scaled_add {n old a b c d : ℕ} (first : n*a^2<old*b^2)
    (second : n*c^2≤old*d^2) : n*(a+c)^2<old*(b+d)^2 := by
  have cross : n*a*c≤old*b*d := by
    apply (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp
    calc
      _ = n*a^2*(n*c^2) := by ring
      _ ≤ old*b^2*(old*d^2) := Nat.mul_le_mul first.le second
      _ = _ := by ring
  nlinarith only [first,second,cross]

/-- The exact squared cutoff grows strictly after accounting for the two
strides and the scaling of the input. The inputs need not be ordered if the
new label budget satisfies the stated public comparison. -/
theorem scaled_cutoffs {n old a b z z₀ d d₀ u t : ℕ} (pos : 0<n)
    (newStart : validStart n ⟨a,b,z,d⟩) (oldStart : validStart old ⟨a,b,z₀,d₀⟩)
    (budget : n*(d₀*(t+1))^2≤old*(d*u)^2) :
    n*(z₀+d₀*t)^2<old*(z+d*u)^2 := by
  obtain ⟨_,_,_,base,_⟩ := of_decide_eq_true newStart
  obtain ⟨_,_,_,_,predecessor⟩ := of_decide_eq_true oldStart
  change 4*a*b*n≤z^2 at base
  change z₀<d₀ ∨ (z₀-d₀)^2<4*a*b*old at predecessor
  rcases predecessor with small|prev
  · have ordered : z₀+d₀*t<d₀*(t+1) := by rw [Nat.mul_add,Nat.mul_one]; omega
    have sq := Nat.pow_lt_pow_left ordered (by decide : 2≠0)
    exact (Nat.mul_lt_mul_of_pos_left sq pos).trans_le (budget.trans
      (Nat.mul_le_mul_left old (Nat.pow_le_pow_left (Nat.le_add_left _ _) 2)))
  · have side : n*(z₀-d₀)^2 < old*z^2 := calc
      _ < n*(4*a*b*old) := Nat.mul_lt_mul_of_pos_left prev pos
      _ = old*(4*a*b*n) := by ring
      _ ≤ _ := Nat.mul_le_mul_left old base
    have ceil := scaled_add side budget
    have le : z₀+d₀*t ≤ z₀-d₀ + d₀*(t+1) := by rw [Nat.mul_add,Nat.mul_one]; omega
    exact (Nat.mul_le_mul_left n (Nat.pow_le_pow_left le 2)).trans_lt ceil

/-- Transfer even a non-strict template bound for every positive real
factor ratio. The output comparison to the next omitted label is strict. -/
theorem real_transfer {n old a b z z₀ d d₀ u t : ℕ} {x : ℝ} (pos : 0<n) (op : 0<old)
    (newStart : validStart n ⟨a,b,z,d⟩) (oldStart : validStart old ⟨a,b,z₀,d₀⟩)
    (budget : n*(d₀*(t+1))^2≤old*(d*u)^2) (xp : 0<x)
    (oldCover : (old:ℝ)*(a+b*x)^2 ≤ ((z₀+d₀*t : ℕ):ℝ)^2*x) :
    (n:ℝ)*(a+b*x)^2 < ((z+d*u : ℕ):ℝ)^2*x := by
  have comp : (n:ℝ)*((z₀+d₀*t:ℕ):ℝ)^2 < (old:ℝ)*((z+d*u:ℕ):ℝ)^2 := by
    exact_mod_cast scaled_cutoffs pos newStart oldStart budget
  apply lt_of_mul_lt_mul_left (a:=(old:ℝ)) _ (by positivity)
  calc
    _ = (n:ℝ)*(old*(a+b*x)^2) := by ring
    _ ≤ n*(((z₀+d₀*t:ℕ):ℝ)^2*x) := mul_le_mul_of_nonneg_left oldCover (by positivity)
    _ = (n*((z₀+d₀*t:ℕ):ℝ)^2)*x := by ring
    _ < (old*((z+d*u:ℕ):ℝ)^2)*x := mul_lt_mul_of_pos_right comp xp
    _ = _ := by ring

/-- Transfer the Boolean cover test used by the catalogue certificates. -/
theorem transfer {n old a b z z₀ d d₀ m m₀ g g₀ : ℕ} {r : Point} (pos : 0<n)
    (newStart : validStart n ⟨a,b,z,d⟩) (oldStart : validStart old ⟨a,b,z₀,d₀⟩)
    (budget : n*(d₀*(m₀*g₀+1))^2≤old*(d*(m*g))^2)
    (prior : covers old m₀ ⟨a,b,z₀,d₀⟩ g₀ r) : covers n m ⟨a,b,z,d⟩ g r := by
  have comp := scaled_cutoffs pos newStart oldStart budget
  simp only [covers,decide_eq_true_eq,cutoff] at prior ⊢
  rw [Nat.mul_assoc d₀ m₀ g₀] at prior
  rw [Nat.mul_assoc d m g]
  let v := (a*r.den+b*r.num)^2
  let k := r.num*r.den
  change old*v < k*(z₀+d₀*(m₀*g₀))^2 at prior
  change n*v < k*(z+d*(m*g))^2
  apply Nat.lt_of_mul_lt_mul_left (a:=old)
  calc
    _ = n*(old*v) := by ring
    _ < n*(k*(z₀+d₀*(m₀*g₀))^2) := Nat.mul_lt_mul_of_pos_left prior pos
    _ = k*(n*(z₀+d₀*(m₀*g₀))^2) := by ring
    _ ≤ k*(old*(z+d*(m*g))^2) := Nat.mul_le_mul_left _ comp.le
    _ = _ := by ring

/-- The smallest integer label count satisfying the public scaling
comparison. One integer ceiling division and one integer square root suffice. -/
def labelBudget (n old d₀ d t : ℕ) : ℕ :=
  ceilSqrt ((n*(d₀*(t+1))^2) ⌈/⌉ (old*d^2))

theorem labelBudget_le {n old d₀ d t u : ℕ} (op : 0<old) (dp : 0<d) :
    labelBudget n old d₀ d t ≤ u ↔ n*(d₀*(t+1))^2 ≤ old*(d*u)^2 := by
  rw [labelBudget,ceilSqrt_le_iff,ceilDiv_le_iff_le_mul (Nat.mul_pos op (Nat.pow_pos dp))]
  simp only [Nat.mul_pow,Nat.mul_assoc]

/-- A target progression computed directly from the product and the old
weights. The phase is the first admissible residue at or above ceil√(4abN). -/
def rebase (n : ℕ) (s : Slope) : Slope :=
  let d := weightedStride n s.a s.b
  let L := ceilSqrt (4*s.a*s.b*n)
  let r := (s.a+s.b*n)%d
  let z := d*(L/d)+r+(if r<L%d then d else 0)
  ⟨s.a,s.b,z,d⟩

theorem rebase_valid (n : ℕ) (s : Slope) : validStart n (rebase n s) := by
  let d := weightedStride n s.a s.b
  let L := ceilSqrt (4*s.a*s.b*n)
  let r := (s.a+s.b*n)%d
  let z := d*(L/d)+r+(if r<L%d then d else 0)
  have dp : 0<d := Nat.gcd_pos_of_pos_left _ (by decide : 0<24)
  have hr : r<d := Nat.mod_lt _ dp
  have rem := Nat.mod_lt L dp
  have euclid := Nat.div_add_mod L d
  have first : L≤z ∧ z<L+d := by dsimp only [z]; split <;> omega
  have phase : z ≡ s.a+s.b*n [MOD d] := by
    change _%d=r
    dsimp only [z]
    split <;> simp [Nat.add_mod,Nat.mod_eq_of_lt hr]
  apply decide_eq_true
  change 0<d ∧ d=d ∧ z ≡ s.a+s.b*n [MOD d] ∧ 4*s.a*s.b*n≤z^2 ∧
    (z<d ∨ (z-d)^2<4*s.a*s.b*n)
  refine ⟨dp,rfl,phase,ceilSqrt_le_iff.mp first.1,?_⟩
  by_cases small : z<d
  · exact Or.inl small
  · right; by_contra! le
    have under : L≤z-d := ceilSqrt_le_iff.mpr le
    omega

/-- Rebase a row under a common stride. Any additional labels may be
packaged into new blocks independently of the old block size. -/
theorem rebase_transfer {n old m g m' g' : ℕ} {s : Slope} {r : Point}
    (pos : 0<n) (smaller : n≤old) (common : weightedStride n s.a s.b=weightedStride old s.a s.b)
    (priorStart : validStart old s) (size : m*g+1≤m'*g') (prior : covers old m s g r) :
    covers n m' (rebase n s) g' r := by
  obtain ⟨a,b,z,d⟩ := s
  let s : Slope := ⟨a,b,z,d⟩
  have step : (rebase n s).step=d := common.trans (of_decide_eq_true priorStart).2.1.symm
  have compare : n*(d*(m*g+1))^2≤old*((rebase n s).step*(m'*g'))^2 := by
    rw [step]
    exact Nat.mul_le_mul smaller (Nat.pow_le_pow_left (Nat.mul_le_mul_left d size) 2)
  exact transfer pos (newStart:=rebase_valid n s) priorStart compare prior

/-- A product-only price also ports a row across different stride classes,
or from a smaller template to a larger target. -/
theorem priced_transfer {n old m g : ℕ} {s : Slope} {r : Point}
    (pos : 0<n) (op : 0<old) (priorStart : validStart old s) (prior : covers old m s g r) :
    covers n 1 (rebase n s) (labelBudget n old s.step (rebase n s).step (m*g)) r := by
  obtain ⟨a,b,z,d⟩ := s
  let s : Slope := ⟨a,b,z,d⟩
  have fresh := rebase_valid n s
  have dp : 0<(rebase n s).step := (of_decide_eq_true fresh).1
  apply transfer pos fresh priorStart _ prior
  simp only [one_mul]
  exact (labelBudget_le op dp).mp le_rfl

/-- Reindex just the template entries used in the cover. Every such entry
gets one extra label. An entry originally using zero blocks receives one label. -/
theorem schedule_transfer {n old m m' : ℕ} {schedule : List (Slope×ℕ)} {left right : Point}
    (pos : 0<n) (smaller : n≤old) (same : n ≡ old [MOD 12])
    (starts : ∀ e∈schedule, validStart old e.1) (choice : Slope×ℕ → ℕ)
    (room : ∀ e∈schedule, m*e.2+1≤m'*choice e)
    (prior : CoversRange old m schedule left right) :
    CoversRange n m' (schedule.map fun e => (rebase n e.1,choice e)) left right := by
  intro r rd lo hi
  obtain ⟨e,mem,hit⟩ := prior r rd lo hi
  exact ⟨_,List.mem_map_of_mem mem,rebase_transfer pos smaller (stride_congr same _ _)
    (starts e mem) (room e mem) hit⟩

/-- One label for a zero-block window; g blocks of m+1 labels suffice for
every positive g. Both forms cover every rational ratio the template covered. -/
theorem port {n old m : ℕ} {schedule : List (Slope×ℕ)} {L R : Point}
    (pos : 0<n) (smaller : n≤old) (same : n ≡ old [MOD 12])
    (starts : ∀ e∈schedule, validStart old e.1) (prior : CoversRange old m schedule L R) :
    CoversRange n 1 (schedule.map fun e => (rebase n e.1,m*e.2+1)) L R ∧
    CoversRange n (m+1) (schedule.map fun e => (rebase n e.1,max 1 e.2)) L R := by
  constructor
  · exact schedule_transfer pos smaller same starts _ (by simp) prior
  · apply schedule_transfer pos smaller same starts _ _ prior
    intro e _
    change m*e.2+1≤(m+1)*max 1 e.2
    rw [Nat.add_mul,Nat.one_mul]
    have := Nat.mul_le_mul_left m (le_max_right 1 e.2)
    omega

/-- The product-only recentering contains a genuine searched label for each
eligible factor pair, using only one direct label on an active zero-block row. -/
theorem actual_label {n old m p q : ℕ} {schedule : List (Slope×ℕ)} {L R : Point}
    (pos : 0<n) (smaller : n≤old) (same : n ≡ old [MOD 12])
    (starts : ∀ e∈schedule, validStart old e.1) (prior : CoversRange old m schedule L R)
    (product : p*q=n) (cop : p.Coprime 6) (lo : before L ⟨q,p⟩) (hi : before ⟨q,p⟩ R) :
    ∃ e∈schedule, ∃ j<m*e.2+1,
      (rebase n e.1).start+(rebase n e.1).step*j=e.1.a*p+e.1.b*q := by
  have pp : 0<p := Nat.pos_of_mul_pos_right (product ▸ pos : 0<p*q)
  obtain ⟨e,mem,hit⟩ := prior ⟨q,p⟩ pp lo hi
  have ok := rebase_transfer pos smaller (stride_congr same _ _) (starts e mem)
    (m':=1) (g':=m*e.2+1) (by simp) hit
  obtain ⟨j,bound,found⟩ := actual_index product cop (rebase_valid n e.1) ok
  exact ⟨e,mem,j,by simpa only [one_mul] using bound,found⟩

/-- The extra label can be necessary at an actual prime pair. The two
products are coprime and have the same residue modulo 12. -/
theorem extra_label_needed :
    Nat.Prime 29 ∧ Nat.Prime 31 ∧ 29*31=899 ∧ Nat.Prime 41 ∧ Nat.Prime 43 ∧ 41*43=1763 ∧
    Nat.Coprime 899 1763 ∧ 899 ≡ 1763 [MOD 12] ∧
    validStart 1763 ⟨3,2,207,2⟩ ∧ validStart 899 ⟨3,2,147,2⟩ ∧
    covers 1763 1 ⟨3,2,207,2⟩ 1 ⟨31,29⟩ ∧
    covers 899 1 ⟨3,2,147,2⟩ 1 ⟨31,29⟩=false ∧
    covers 899 1 ⟨3,2,147,2⟩ 2 ⟨31,29⟩ ∧ 147+2=3*29+2*31 := by decide +kernel

end PrimeFactors.TraceCoverTransfer
