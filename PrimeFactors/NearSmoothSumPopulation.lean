import PrimeFactors.SmoothSumSelector

/-! Population counts for a list of approximate prime sums. The first count
covers every actual sum near a center. The second bounds a publicly detectable
loss of precision in passing from the sum to a larger-factor interval. -/

namespace PrimeFactors.NearSmoothSumPopulation

open Finset SmoothSumSelector

set_option exponentiation.threshold 4096

/-- Half the public even sum at exponent b. -/
def midpoint (b : ℕ) : ℕ := candidate b / 2

/-- A possible even sum lies within distance 2t of a public candidate. -/
def Near (s t : ℕ) : Prop :=
  ∃ b<647, s ≤ candidate b+2*t ∧ candidate b ≤ s+2*t

/-- The upper midpoint of the band reaches the product's square root, and its
lower midpoint fails the public squared-gap test g² ≤ (c−t)²−n.
The strict inequality avoids any rounding at the boundary. -/
def IllConditioned (n b t g : ℕ) : Prop :=
  n ≤ (midpoint b+t)^2 ∧ (midpoint b-t)^2 < n+g^2

private theorem label_count {pairs : Finset (ℕ × ℕ)} {first : Finset ℕ} {K M : ℕ}
    (decode : ℕ → ℕ → ℕ → ℕ)
    (valid : ∀ x ∈ pairs, x.1 ∈ first ∧ ∃ b<M, ∃ i<K, x.2=decode x.1 b i) :
    pairs.card ≤ first.card*(M*K) := by
  classical
  let domain := first ×ˢ (range M ×ˢ range K)
  let read (z : ℕ × (ℕ × ℕ)) := (z.1,decode z.1 z.2.1 z.2.2)
  have subset : pairs ⊆ domain.image read := by
    intro x hx
    obtain ⟨mem,b,hb,i,hi,eq⟩ := valid x hx
    apply mem_image.mpr
    refine ⟨(x.1,b,i),?_,?_⟩
    · simp only [domain,mem_product,mem_range]
      exact ⟨mem,hb,hi⟩
    · exact Prod.ext rfl eq.symm
  calc
    _ ≤ _ := card_le_card subset
    _ ≤ _ := card_image_le
    _ = _ := by simp only [domain,card_product,card_range]

/-- At fixed first prime and even center, parity gives at most 2t+1
possible even sums in a band of absolute radius 2t. -/
theorem menu_count {pairs : Finset (ℕ × ℕ)} {first : Finset ℕ} {M t : ℕ}
    (center : ℕ → ℕ) (even : ∀ b<M, 2∣center b)
    (valid : ∀ x∈pairs, x.1∈first ∧ Even (x.1+x.2) ∧
      ∃ b<M, x.1+x.2≤center b+2*t ∧ center b≤x.1+x.2+2*t) :
    pairs.card ≤ first.card*(M*(2*t+1)) := by
  apply label_count (fun p b i => 2*(center b/2+i-t)-p)
  intro x h
  obtain ⟨mem,⟨k,hk⟩,b,hb,lo,hi⟩ := valid x h
  obtain ⟨c,hc⟩ := even b hb
  exact ⟨mem,b,hb,k+t-center b/2,by omega,by omega⟩

private theorem midpoint_range {b : ℕ} (hb : b<647) :
    2^1023 ≤ midpoint b ∧ midpoint b < 2^1024 := by
  obtain ⟨lo,hi,_⟩ := candidate_bounds hb
  dsimp only [midpoint]
  omega

/-- At fixed first prime p, changing its partner by one changes the product by
p. This bounds the number of partners which could make a public band unstable. -/
theorem exception_count {pairs : Finset (ℕ × ℕ)} {first : Finset ℕ} {t g : ℕ}
    (tcap : t ≤ 2^1023)
    (valid : ∀ x∈pairs, x.1∈first ∧ 2^1023≤x.1 ∧ ∃ b<647, IllConditioned (x.1*x.2) b t g) :
    pairs.card ≤ first.card*(647*((4*2^1024*t+g^2)/2^1023+1)) := by
  let U (p b : ℕ) := (midpoint b+t)^2/p
  apply label_count (fun p b i => U p b-i)
  intro x hx
  obtain ⟨mem,hp,b,hb,upper,lower⟩ := valid x hx
  have pr : 0<x.1 := by omega
  let c := midpoint b
  have cm := midpoint_range hb
  have ct : t≤c := tcap.trans cm.1
  have top : x.2 ≤ U x.1 b := (Nat.le_div_iff_mul_le pr).mpr (by simpa [Nat.mul_comm] using upper)
  let i := U x.1 b-x.2
  have ui : i+x.2=U x.1 b := Nat.sub_add_cancel top
  have cap := Nat.div_mul_le_self ((c+t)^2) x.1
  change U x.1 b*x.1 ≤ (c+t)^2 at cap
  have expand : (c-t)^2+4*c*t=(c+t)^2 := by
    obtain ⟨d,hd⟩ := Nat.exists_eq_add_of_le ct
    rw [hd,Nat.add_sub_cancel_left]
    ring
  have span : i*x.1 ≤ 4*c*t+g^2 := by
    change (c-t)^2 < x.1*x.2+g^2 at lower
    rw [←ui,Nat.add_mul,←expand] at cap
    nlinarith only [lower,cap]
  have radius : i*2^1023 ≤ 4*2^1024*t+g^2 := calc
    _ ≤ i*x.1 := Nat.mul_le_mul_left i hp
    _ ≤ _ := span
    _ ≤ _ := Nat.add_le_add_right (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ cm.2.le)) _
  exact ⟨mem,b,hb,i,by exact Nat.lt_succ_of_le ((Nat.le_div_iff_mul_le (show 0<(2:ℕ)^1023 by positivity)).mpr radius),by omega⟩

/-- The prime-count input is the project's published comparison of the first
prime population with the population of unordered target products. -/
private theorem fraction {pairs : Finset (ℕ × ℕ)} {first : Finset ℕ} {pop k bits : ℕ}
    (den : 2^1023*first.card < 44331*pop) (num : pairs.card ≤ first.card*k)
    (pos : 0<k) (scale : 44331*(2^bits*k) ≤ 2^1023) : 2^bits*pairs.card<pop := by
  apply Nat.lt_of_mul_lt_mul_left (a:=2^1023)
  calc
    _ ≤ 2^1023*(2^bits*(first.card*k)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ num)
    _ = (2^1023*first.card)*(2^bits*k) := by ac_rfl
    _ < (44331*pop)*(2^bits*k) := Nat.mul_lt_mul_of_pos_right den (by positivity)
    _ = 44331*(2^bits*k)*pop := by ac_rfl
    _ ≤ _ := Nat.mul_le_mul_right pop scale

/-- For any fixed catalog of 648 even centers and absolute error 2^k, the
covered fraction is below 2^(k−998) for 3 ≤ k ≤ 998. The choice within the
catalog may depend on the product. This includes the 647 octave centers and
the extra upper endpoint 2^1025. -/
theorem menu_fraction_pow {pairs : Finset (ℕ × ℕ)} {first : Finset ℕ} {pop k t : ℕ}
    (center : ℕ → ℕ) (even : ∀ b<648, 2∣center b)
    (den : 2^1023*first.card < 44331*pop) (minK : 3≤k) (maxK : k≤998)
    (size : 2*t=2^k)
    (valid : ∀ x∈pairs, x.1∈first ∧ Even (x.1+x.2) ∧
      ∃ b<648, x.1+x.2≤center b+2*t ∧ center b≤x.1+x.2+2*t) :
    2^(998-k)*pairs.card < pop := by
  apply fraction den (menu_count center even valid) (by positivity)
  rw [size]
  have eight : 8≤(2:ℕ)^k := (Nat.pow_le_pow_right (by decide : 0<2) minK)
  have budget : 8*(2^k+1)≤9*(2^k) := by omega
  have combine : (2:ℕ)^(998-k)*2^k=2^998 := by rw [←pow_add,Nat.sub_add_cancel maxK]
  apply (Nat.mul_le_mul_left_iff (by decide : 0<8)).mp
  calc
    _ = (44331*648*2^(998-k))*(8*(2^k+1)) := by ac_rfl
    _ ≤ (44331*648*2^(998-k))*(9*(2^k)) := Nat.mul_le_mul_left _ budget
    _ = (44331*648*9)*(2^(998-k)*2^k) := by ac_rfl
    _ ≤ 8*2^1023 := by rw [combine]; decide +kernel

/-- In-range centers together with the upper endpoint have the same
power-of-two population bound at every stated tolerance. -/
theorem including_upper_fraction {pairs : Finset (ℕ × ℕ)} {first : Finset ℕ} {pop k t : ℕ}
    (den : 2^1023*first.card < 44331*pop) (minK : 3≤k) (maxK : k≤998) (size : 2*t=2^k)
    (valid : ∀ x∈pairs, x.1∈first ∧ Even (x.1+x.2) ∧
      (Near (x.1+x.2) t ∨ (x.1+x.2≤2^1025+2*t ∧ 2^1025≤x.1+x.2+2*t))) :
    2^(998-k)*pairs.card < pop := by
  let c (b : ℕ) := if b=647 then 2^1025 else candidate b
  apply menu_fraction_pow c _ den minK maxK size
  · intro x h
    obtain ⟨mem,ev,alt⟩ := valid x h
    refine ⟨mem,ev,?_⟩
    rcases alt with ⟨b,hb,lo,hi⟩|endpoint
    · exact ⟨b,by omega,by simpa [c,show b≠647 by omega] using And.intro lo hi⟩
    · exact ⟨647,by decide,by simpa [c] using endpoint⟩
  · intro b hb
    by_cases e : b=647
    · simp [c,e]
    · simpa [c,e] using (candidate_bounds (b:=b) (by omega)).2.2

/-- Allowing absolute sum error 2^400 still covers fewer than one in 2^598
uniform target pairs under the explicit prime-count estimate. -/
theorem near_fraction {pairs : Finset (ℕ × ℕ)} {first : Finset ℕ} {pop : ℕ}
    (den : 2^1023*first.card < 44331*pop)
    (valid : ∀ x∈pairs, x.1∈first ∧ Even (x.1+x.2) ∧ Near (x.1+x.2) (2^399)) :
    2^598*pairs.card < pop :=
  including_upper_fraction (k:=400) den (by decide) (by decide) (by decide +kernel)
    (fun x h => ⟨(valid x h).1,(valid x h).2.1,Or.inl (valid x h).2.2⟩)

/-- For the same error allowance, fewer than one pair in 2^55 can have even
one geometrically feasible center failing the squared-gap screen at 2^983.
This count is over all target pairs, independently of their sum. -/
theorem exception_fraction {pairs : Finset (ℕ × ℕ)} {first : Finset ℕ} {pop : ℕ}
    (den : 2^1023*first.card < 44331*pop)
    (valid : ∀ x∈pairs, x.1∈first ∧ 2^1023≤x.1 ∧
      ∃ b<647, IllConditioned (x.1*x.2) b (2^399) (2^983)) :
    2^55*pairs.card < pop :=
  fraction den (exception_count (by decide +kernel) valid) (by decide +kernel) (by decide +kernel)

end PrimeFactors.NearSmoothSumPopulation
