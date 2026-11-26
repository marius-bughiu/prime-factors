import PrimeFactors.CRTResidueAdvice

/-! Approximate factor sums selected by the remainders of the product.
For odd inputs use the public word N / 2. Disjoint terminal congruence
classes may use different moduli and return unrelated lists of guesses. -/

namespace PrimeFactors.AdaptiveSumBands

open Finset

set_option exponentiation.threshold 4096

/-- Multiplication by an odd partner induces an affine map on half-words. -/
theorem half_product {p q : ℕ} (odd : Odd q) : p*q/2 = p*(q/2)+p/2 := by
  obtain ⟨v,hv⟩ := odd
  have eq : p*q = p + 2*(p*v) := by rw [hv]; ring
  rw [eq, Nat.add_mul_div_left _ _ (by decide : 0<2)]
  have hvq : q/2=v := by omega
  rw [hvq, Nat.add_comm]

/-- One sum guess within E places the odd partner's half-word in an
interval of diameter E, including guesses below the feasible range. -/
theorem half_interval {p q c E : ℕ} (odd : Odd q)
    (below : c≤p+q+E) (above : p+q≤c+E) :
    (c-E-p)/2 ≤ q/2 ∧ q/2 ≤ (c-E-p)/2+E := by
  obtain ⟨_,_⟩ := odd
  omega

private theorem cell {m r E K : ℕ} (pairs : Finset (ℕ × ℕ))
    (first : Finset ℕ) (center : ℕ → ℕ)
    (valid : ∀ z∈pairs, z.1∈first ∧ Odd z.2 ∧ m.Coprime z.1 ∧
      z.1*z.2/2 ≡ r [MOD m] ∧ ∃ j<K, center j≤z.1+z.2+E ∧ z.1+z.2≤center j+E) :
    pairs.card ≤ first.card*K*(E/m+1) := by
  classical
  let slot (z : ℕ × ℕ) := if h : z∈pairs then ((valid z h).2.2.2.2).choose else 0
  let base (p j : ℕ) := (center j-E-p)/2
  have hslot (z : ℕ × ℕ) (hz : z∈pairs) : slot z<K ∧
      base z.1 (slot z)≤z.2/2 ∧ z.2/2≤base z.1 (slot z)+E := by
    obtain ⟨_,odd,_,_,hs⟩ := valid z hz
    have spec := hs.choose_spec
    simpa only [slot,dif_pos hz] using
      And.intro spec.1 (half_interval odd spec.2.1 spec.2.2)
  let code (z : ℕ × ℕ) := ((z.1,slot z),(z.2/2-base z.1 (slot z))/m)
  rw [←card_range K,←card_product,←card_range (E/m+1),←card_product]
  apply card_le_card_of_injOn code
  · intro z hz
    obtain ⟨hj,_,upper⟩ := hslot z hz
    exact mem_product.mpr ⟨mem_product.mpr ⟨(valid z hz).1,mem_range.mpr hj⟩,
      mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right (by omega)))⟩
  · rintro ⟨p,q⟩ hq ⟨p',s⟩ hs equal
    have sameP : p=p' := congrArg (fun x : (ℕ×ℕ)×ℕ => x.1.1) equal
    subst p'
    have sameJ : slot (p,q)=slot (p,s) := congrArg (fun x : (ℕ×ℕ)×ℕ => x.1.2) equal
    have sameD : (q/2-base p (slot (p,q)))/m=(s/2-base p (slot (p,s)))/m :=
      congrArg Prod.snd equal
    rw [←sameJ] at sameD
    obtain ⟨_,oq,cop,cq,_⟩ := valid (p,q) hq
    obtain ⟨_,os,_,cs,_⟩ := valid (p,s) hs
    change p*q/2 ≡ r [MOD m] at cq
    change p*s/2 ≡ r [MOD m] at cs
    rw [half_product oq] at cq
    rw [half_product os] at cs
    have sameR := (Nat.ModEq.add_right_cancel' (p/2) (cq.trans cs.symm)).cancel_left_of_coprime cop
    let b := base p (slot (p,q))
    have lq : b≤q/2 := (hslot _ hq).2.1
    have ls : b≤s/2 := by simpa only [b,sameJ] using (hslot _ hs).2.1
    have shifted : (q/2-b)+b ≡ (s/2-b)+b [MOD m] := by
      simpa only [Nat.sub_add_cancel lq,Nat.sub_add_cancel ls] using sameR
    have rem := Nat.ModEq.add_right_cancel' b shifted
    change (q/2-b)%m = (s/2-b)%m at rem
    change (q/2-b)/m=(s/2-b)/m at sameD
    have join : q/2-b=s/2-b := by
      rw [←Nat.mod_add_div (q/2-b) m,rem,sameD,Nat.mod_add_div]
    obtain ⟨_,_⟩ := oq
    obtain ⟨_,_⟩ := os
    exact Prod.ext rfl (by omega)

/-- Each terminal congruence owns at least floor(E/m) integers in [0,E). -/
private theorem prefix_slots {m r E : ℕ} (pos : 0<m) (small : r<m) :
    E/m ≤ ((range E).filter fun t => t ≡ r [MOD m]).card := by
  rw [←card_range (E/m)]
  apply card_le_card_of_injOn (fun j : ℕ => r+m*j)
  · intro j hj
    have bound := Nat.div_mul_le_self E m
    have hj' : j+1≤E/m := mem_range.mp hj
    have mul := Nat.mul_le_mul_left m hj'
    rw [mul_add,Nat.mul_one,Nat.mul_comm m (E/m)] at mul
    exact mem_filter.mpr ⟨mem_range.mpr (by omega), by simp [Nat.ModEq]⟩
  · intro i _ j _ eq
    exact Nat.eq_of_mul_eq_mul_left pos (Nat.add_left_cancel eq)

/-- A remainder protocol with L reachable leaves and K guesses per leaf
can cover at most K(E+L) partners per first prime on average over that set.
There is no cap on the moduli when they are coprime to the first primes. -/
theorem count {ι : Type*} (leaves : Finset ι) (m r : ι → ℕ) (center : ι → ℕ → ℕ)
    (hits : ι → Finset (ℕ×ℕ)) (first : Finset ℕ) (E K : ℕ)
    (params : ∀ i∈leaves, 0<m i ∧ r i<m i)
    (disjoint : (leaves : Set ι).PairwiseDisjoint
      (fun i => (range E).filter fun t => t ≡ r i [MOD m i]))
    (valid : ∀ i∈leaves, ∀ z∈hits i, z.1∈first ∧ Odd z.2 ∧ (m i).Coprime z.1 ∧
      z.1*z.2/2 ≡ r i [MOD m i] ∧ ∃ j<K, center i j≤z.1+z.2+E ∧ z.1+z.2≤center i j+E) :
    (leaves.biUnion hits).card ≤ first.card*K*(E+leaves.card) := by
  classical
  let bucket i := (range E).filter fun t => t ≡ r i [MOD m i]
  have sub : leaves.biUnion bucket ⊆ range E := by
    intro x hx
    obtain ⟨_,_,mem⟩ := mem_biUnion.mp hx
    exact (mem_filter.mp mem).1
  have total := card_le_card sub
  rw [card_biUnion disjoint,card_range] at total
  have density : ∑ i ∈ leaves, E/m i ≤ E := by
    exact (sum_le_sum fun i hi => prefix_slots (params i hi).1 (params i hi).2).trans total
  calc
    _ ≤ ∑ i ∈ leaves, (hits i).card := card_biUnion_le
    _ ≤ ∑ i ∈ leaves, first.card*K*(E/m i+1) := by
      exact sum_le_sum fun i hi => cell _ _ _ (valid i hi)
    _ = first.card*K*((∑ i ∈ leaves, E/m i)+leaves.card) := by
      rw [←mul_sum,sum_add_distrib]; simp
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.add_le_add_right density _)

/-- The explicit prime-population comparison is the independent denominator
estimate used in the project. A thousand-bit modulus built from small primes
is allowed when the number of reachable residue classes meets the bound. -/
theorem frequency {first : Finset ℕ} {pop hits E K L extra bits : ℕ}
    (den : 2^1023*first.card < 44331*pop)
    (cap : hits ≤ 2^extra*(first.card*K*(E+L)))
    (nonzero : 0<K*(E+L))
    (numeric : 2^bits*2^extra*K*(E+L)*44331≤2^1023) : 2^bits*hits<pop := by
  let scale := 2^bits*2^extra*K*(E+L)
  have pos : 0<scale := by
    dsimp [scale]; rw [mul_assoc]; exact Nat.mul_pos (by positivity) nonzero
  apply Nat.lt_of_mul_lt_mul_left (a:=2^1023)
  calc
    _ ≤ 2^1023*(2^bits*(2^extra*(first.card*K*(E+L)))) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ cap)
    _ = (2^1023*first.card)*scale := by dsimp [scale]; ring
    _ < (44331*pop)*scale := Nat.mul_lt_mul_of_pos_right den pos
    _ = (scale*44331)*pop := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ numeric

/-- All possible processing of 512 low product bits (one forced bit) with
648 guesses at tolerance 2^400. Another 100 arbitrary binary answers are
also priced. The lower exponents measure the fraction of successful pairs. -/
theorem budgets :
    2^487 * 2^0 * 648 * (2^400+2^511)*44331 ≤ (2:ℕ)^1023 ∧
    2^387 * 2^100 * 648 * (2^400+2^511)*44331 ≤ (2:ℕ)^1023 ∧
    2^597 * 2^0 * 648 * (2^400+2^399)*44331 ≤ (2:ℕ)^1023 := by decide +kernel

end PrimeFactors.AdaptiveSumBands
