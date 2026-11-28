import PrimeFactors.HighLowSumPopulation

/-! Sharp sum precision for recognizing the two low factor remainders
of an individual pair. Congruent product and sum reduce the question
to the divisibility of (x-p)(x-q). -/
namespace PrimeFactors.FactorPairSeparationDepth

/-- Required low sum bits at factor width k when the gap has exact
two-adic order t. The middle branch saves two bits because the two
lifts of the common factor ending are already occupied. -/
def depth (k t : ℕ) : ℕ :=
  if t+1<k then k+t else if t+1=k then 2*k-3 else 2*k-1

/-- Every candidate for a root of the reduced quadratic has a true ending. -/
def Determines (p q : ℤ) (k e : ℕ) : Prop :=
  ∀ x : ℤ, (2:ℤ)^e ∣ (x-p)*(x-q) → (2:ℤ)^k ∣ x-p ∨ (2:ℤ)^k ∣ x-q

/-- Evaluating the quadratic at one candidate is equivalent to trying
all partners with the specified sum and product. -/
theorem candidate_iff (p q x : ℤ) (e : ℕ) :
    (∃ y : ℤ, x+y ≡ p+q [ZMOD (2:ℤ)^e] ∧ x*y ≡ p*q [ZMOD (2:ℤ)^e]) ↔
    (2:ℤ)^e ∣ (x-p)*(x-q) := by
  constructor
  · rintro ⟨y,s,prod⟩
    have ds := Int.modEq_iff_dvd.mp s
    have dp := Int.modEq_iff_dvd.mp prod
    convert dvd_sub dp (dvd_mul_of_dvd_right ds x) using 1
    ring
  · intro h
    refine ⟨p+q-x,by rw [show x+(p+q-x)=p+q by ring],Int.modEq_iff_dvd.mpr ?_⟩
    convert h using 1
    ring

private theorem one_high {x y : ℤ} {v : ℕ} (h : (2:ℤ)^(2*v+1) ∣ x*y) :
    (2:ℤ)^(v+1) ∣ x ∨ (2:ℤ)^(v+1) ∣ y := by
  by_cases hx : x=0
  · simp [hx]
  by_cases hy : y=0
  · simp [hy]
  change ((2:ℕ):ℤ)^(2*v+1) ∣ x*y at h
  change ((2:ℕ):ℤ)^(v+1) ∣ x ∨ ((2:ℕ):ℤ)^(v+1) ∣ y
  simp only [padicValInt_dvd_iff, mul_ne_zero hx hy,hx,hy,false_or,or_false,padicValInt.mul hx hy] at h ⊢
  omega

private theorem nondiv {g : ℤ} (odd : Odd g) {i k : ℕ} (lt : i<k) :
    ¬(2:ℤ)^k ∣ 2^i*g := by
  intro h
  obtain ⟨c,hc⟩ := (pow_dvd_pow (2:ℤ) (show i+1≤k by omega)).trans h
  rw [pow_succ,mul_assoc] at hc
  have eq := mul_left_cancel₀ (by positivity : (2:ℤ)^i ≠ 0) hc
  obtain ⟨u,hu⟩ := odd
  omega

private theorem lift_pair {x p q g : ℤ} {t : ℕ} (gap : q-p=2^t*g) (o : Odd g)
    (h : (2:ℤ)^t ∣ x-p) :
    (2:ℤ)^(t+1) ∣ x-p ∨ (2:ℤ)^(t+1) ∣ x-q := by
  obtain ⟨z,hz⟩ := h
  obtain ⟨u,hu⟩ := o
  rcases Int.even_or_odd z with ⟨v,hv⟩|⟨v,hv⟩
  · exact Or.inl ⟨v,by rw [hz,hv,pow_succ]; ring⟩
  · refine Or.inr ⟨v-u,?_⟩
    have eq : x-q=(x-p)-(q-p) := by ring
    rw [eq,hz,hv,gap,hu,pow_succ]
    ring

/-- Pointwise upper bound, including the boundary where either lift of a
common (k-1)-bit ending already names one of the two true factor endings. -/
theorem at_depth {p q g : ℤ} {k t : ℕ} (hk : 3≤k)
    (gap : q-p=(2:ℤ)^t*g) (o : Odd g) : Determines p q k (depth k t) := by
  unfold depth
  split_ifs with small edge
  · intro x h
    have prod : p*q ≡ x*(p+q-x) [ZMOD (2:ℤ)^(k+t)] := by
      apply Int.modEq_iff_dvd.mpr
      convert dvd_neg.mpr h using 1
      ring
    have eq : p+q=x+(p+q-x) := by ring
    have near := HighLowSumPopulation.two_roots gap o eq prod
    rw [Nat.add_sub_cancel] at near
    exact near.imp (fun l => Int.modEq_iff_dvd.mp l.symm) (fun r => Int.modEq_iff_dvd.mp r.symm)
  · intro x h
    have e : 2*k-3=2*(t-1)+1 := by omega
    rw [e] at h
    have high := one_high h
    rw [show t-1+1=t by omega] at high
    have either : (2:ℤ)^t ∣ x-p := by
      rcases high with l|r
      · exact l
      · convert dvd_add r (show (2:ℤ)^t ∣ q-p from ⟨g,gap⟩) using 1
        ring
    simpa only [edge] using lift_pair gap o either
  · intro x h
    rw [show 2*k-1=2*(k-1)+1 by omega] at h
    simpa only [show k-1+1=k by omega] using one_high h

private theorem shift_order {t j : ℕ} {g : ℤ} (o : Odd g) (ne : j≠t) :
    ∃ w : ℤ, Odd w ∧ (2:ℤ)^j-2^t*g=2^(min j t)*w := by
  rcases lt_or_gt_of_ne ne with small|large
  · have split : t=j+((t-j-1)+1) := by omega
    have eq : (2:ℤ)^t=2^j*(2^(t-j-1)*2) := by
      conv_lhs => rw [split,pow_add,pow_succ]
    rw [min_eq_left small.le,eq]
    refine ⟨1-(2^(t-j-1)*2)*g,⟨-(2^(t-j-1)*g),by ring⟩,by ring⟩
  · have split : j=t+((j-t-1)+1) := by omega
    have eq : (2:ℤ)^j=2^t*(2^(j-t-1)*2) := by
      conv_lhs => rw [split,pow_add,pow_succ]
    obtain ⟨u,hu⟩ := o
    rw [min_eq_right large.le,eq,hu]
    refine ⟨2^(j-t-1)*2-(2*u+1),⟨2^(j-t-1)-u-1,by ring⟩,by ring⟩

/-- A concrete offset gives a false root one bit before the threshold
for every pair, with a partner that even realizes the exact original sum. -/
theorem earlier_collision {p q g : ℤ} {k t : ℕ} (hk : 3≤k)
    (gap : q-p=(2:ℤ)^t*g) (o : Odd g) :
    ∃ x : ℤ, (2:ℤ)^(depth k t-1) ∣ (x-p)*(x-q) ∧
      ¬(2:ℤ)^k ∣ x-p ∧ ¬(2:ℤ)^k ∣ x-q := by
  let j := if t+1=k then k-2 else k-1
  have jt : j≠t := by dsimp [j]; split_ifs <;> omega
  have jk : j<k := by dsimp [j]; split_ifs <;> omega
  have de : depth k t-1=j+min j t := by
    unfold depth j
    split_ifs <;> omega
  obtain ⟨w,wo,hw⟩ := shift_order o jt
  let x := p+2^j
  have xp : x-p=(2:ℤ)^j := by dsimp [x]; ring
  have xq : x-q=2^(min j t)*w := by
    have move : x-q=(x-p)-(q-p) := by ring
    rw [move,xp,gap,hw]
  refine ⟨x,?_,?_,?_⟩
  · rw [de,pow_add,xp,xq]
    exact ⟨w,by ring⟩
  · rw [xp]
    simpa only [mul_one] using nondiv (by decide : Odd (1:ℤ)) jk
  · rw [xq]
    exact nondiv wo (lt_of_le_of_lt (min_le_left ..) jk)

/-- Least sufficient input precision for the particular factor pair. -/
theorem determines_iff {p q g : ℤ} {k t e : ℕ} (hk : 3≤k)
    (gap : q-p=(2:ℤ)^t*g) (o : Odd g) : Determines p q k e ↔ depth k t≤e := by
  constructor
  · intro det
    by_contra! fewer
    obtain ⟨x,prod,np,nq⟩ := earlier_collision hk gap o
    exact (det x ((pow_dvd_pow (2:ℤ) (by omega : e≤depth k t-1)).trans prod)).elim np nq
  · intro enough x h
    exact at_depth hk gap o x ((pow_dvd_pow (2:ℤ) enough).trans h)

end PrimeFactors.FactorPairSeparationDepth
