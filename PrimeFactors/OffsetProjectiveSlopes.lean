import PrimeFactors.CompleteOffsetWork
import PrimeFactors.ResidueCount

namespace PrimeFactors.OffsetProjectiveSlopes
open CompleteOffsetWork

/-- A finite slope is j/k. The single extra value represents k=0 modulo p. -/
noncomputable def localSlopes (p : ℕ) [Fact p.Prime] (N T : ZMod p) :
    Finset (Option (ZMod p)) :=
  insert none ((factorSumResidues p N).image fun a => some (a-2*T))

theorem infinity_mem (p : ℕ) [Fact p.Prime] (N T : ZMod p) : none ∈ localSlopes p N T :=
  Finset.mem_insert_self ..

theorem finite_mem_iff {p : ℕ} [Fact p.Prime] (odd : p≠2) {N T r : ZMod p} (unit : N≠0) :
    some r ∈ localSlopes p N T ↔ IsSquare ((r+2*T)^2-4*N) := by
  rw [←admissibleSum_iff_isSquare odd, ←mem_factorSumResidues_iff p unit]
  simp only [localSlopes,Finset.mem_insert,Option.some_ne_none,false_or,Finset.mem_image,
    Option.some.injEq,sub_eq_iff_eq_add]
  simp

/-- A true weighted square selects a permitted projective slope at each prime.
If k vanishes, the primitive-slot hypothesis separately ensures j is nonzero. -/
theorem mem_of_square {p : ℕ} [Fact p.Prime] (odd : p≠2) {N T j k d : ZMod p} (unit : N≠0)
    (square : (j+2*T*k)^2=4*k^2*N+d^2) :
    (if k=0 then none else some (j/k)) ∈ localSlopes p N T := by
  split
  · exact infinity_mem ..
  next nz =>
    apply (finite_mem_iff odd unit).mpr
    refine ⟨d/k,?_⟩
    field_simp
    linear_combination k^2*square

theorem card_localSlopes {p : ℕ} [Fact p.Prime] (N T : ZMod p) :
    (localSlopes p N T).card=(factorSumResidues p N).card+1 := by
  classical
  rw [localSlopes,Finset.card_insert_of_not_mem (by simp)]
  congr 1
  apply Finset.card_image_of_injective
  intro a b same
  exact sub_left_inj.mp (Option.some.inj same)

theorem card_localSlopes_of_square {p : ℕ} [Fact p.Prime] (odd : p≠2) (N T : ZMod p)
    (unit : N≠0) (square : IsSquare N) : (localSlopes p N T).card=(p+3)/2 := by
  rw [card_localSlopes,card_factorSumResidues_of_square p odd N unit square]
  omega

theorem card_localSlopes_of_nonsquare {p : ℕ} [Fact p.Prime] (N T : ZMod p) (unit : N≠0)
    (non : ¬IsSquare N) : (localSlopes p N T).card=(p+1)/2 := by
  rw [card_localSlopes,card_factorSumResidues_of_nonsquare p N unit non]
  have := (Fact.out : p.Prime).two_le
  omega

theorem card_localSlopes_le {p : ℕ} [Fact p.Prime] (odd : p≠2) (N T : ZMod p)
    (unit : N≠0) : (localSlopes p N T).card≤(p+3)/2 := by
  by_cases sq : IsSquare N
  · exact (card_localSlopes_of_square odd N T unit sq).le
  · rw [card_localSlopes_of_nonsquare N T unit sq]
    omega

/-- All odd primes from 5 through 743. Leaving out 3 divides the worst-case branch count by three
while retaining enough modulus for every 2048-bit product. -/
def primes130 : List ℕ := [
  5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,
  101,103,107,109,113,127,131,137,139,149,151,157,163,167,173,179,181,191,
  193,197,199,211,223,227,229,233,239,241,251,257,263,269,271,277,281,283,
  293,307,311,313,317,331,337,347,349,353,359,367,373,379,383,389,397,
  401,409,419,421,431,433,439,443,449,457,461,463,467,479,487,491,499,
  503,509,521,523,541,547,557,563,569,571,577,587,593,599,601,607,613,
  617,619,631,641,643,647,653,659,661,673,677,683,691,701,709,719,727,
  733,739,743]

def primes131 : List ℕ := 3::primes130

set_option maxRecDepth 4000 in
theorem primes131_checked : primes131.length=131 ∧ primes131.Nodup ∧
    ∀ p∈primes131, p.Prime ∧ p≠2 ∧ p≤743 := by decide +kernel

noncomputable def branchBound (ps : List ℕ) : ℕ := (ps.map fun p => (p+3)/2).prod

set_option maxRecDepth 4000 in
theorem fixed_bounds : branchBound primes130<2^901 ∧ branchBound primes131<2^903 ∧
    8*2^1024+6*2^514 < 3*primes130.prod := by decide +kernel

/-- Product of the numbers of local labels, evaluated with the input-specific masks. -/
noncomputable def localCount (N T p : ℕ) : ℕ :=
  if prime : p.Prime then
    letI : Fact p.Prime := ⟨prime⟩
    (localSlopes p N T).card
  else 0

theorem localCount_eq (N T p : ℕ) [prime : Fact p.Prime] :
    localCount N T p=(localSlopes p N T).card := by simp [localCount, prime.out]

/-- Both outcomes of the local count occur modulo 5, including infinity. -/
theorem local_examples : localCount 11 3 5=4 ∧ localCount 143 11 5=3 := by
  letI : Fact (Nat.Prime 5) := ⟨by decide⟩
  constructor
  · rw [localCount_eq,card_localSlopes_of_square (by decide) _ _ (by decide) ⟨1,by decide⟩]
  · rw [localCount_eq,card_localSlopes_of_nonsquare _ _ (by decide) (by
      rintro ⟨x,hx⟩
      exact (by decide : ∀ z : ZMod 5, ((143:ℕ):ZMod 5)≠z*z) x hx)]

private theorem product_bound (N T : ℕ) (ps : List ℕ)
    (ok : ∀ p∈ps, p.Prime ∧ p≠2 ∧ ¬p∣N) :
    (ps.map (localCount N T)).prod≤branchBound ps := by
  induction ps with
  | nil => simp [branchBound]
  | cons p ps ih =>
    obtain ⟨prime,odd,unit⟩ := ok p (by simp)
    letI : Fact p.Prime := ⟨prime⟩
    have nz := mt (ZMod.natCast_zmod_eq_zero_iff_dvd N p).mp unit
    have localBound := card_localSlopes_le odd (N:ZMod p) (T:ZMod p) nz
    simp only [List.map_cons,List.prod_cons,branchBound,localCount_eq] at *
    exact Nat.mul_le_mul localBound (ih (fun l hl => ok l (List.mem_cons_of_mem p hl)))

theorem target_counts {N T : ℕ} (unit : ∀ p∈primes131, ¬p∣N) :
    (primes130.map (localCount N T)).prod<2^901 ∧
    (primes131.map (localCount N T)).prod<2^903 := by
  have ok (p : ℕ) (mem : p∈primes131) : p.Prime ∧ p≠2 ∧ ¬p∣N :=
    ⟨(primes131_checked.2.2 p mem).1,(primes131_checked.2.2 p mem).2.1,unit p mem⟩
  exact ⟨(product_bound N T primes130 (fun p mem => ok p (List.mem_cons_of_mem 3 mem))).trans_lt
            fixed_bounds.1,
         (product_bound N T primes131 ok).trans_lt fixed_bounds.2.1⟩

/-- For large prime factors, the unit hypotheses for the local counts follow
directly from the public lower bound on their width. -/
theorem target_semiprime_counts {P Q T : ℕ} (pp : P.Prime) (qp : Q.Prime)
    (largeP : 743<P) (largeQ : 743<Q) :
    (primes130.map (localCount (P*Q) T)).prod<2^901 ∧
    (primes131.map (localCount (P*Q) T)).prod<2^903 := by
  apply target_counts
  intro p mem div
  obtain ⟨prime,_,cap⟩ := primes131_checked.2.2 p mem
  rcases prime.dvd_mul.mp div with left|right
  · exact ((Nat.prime_dvd_prime_iff_eq prime pp).mp left).not_lt (cap.trans_lt largeP)
  · exact ((Nat.prime_dvd_prime_iff_eq prime qp).mp right).not_lt (cap.trans_lt largeQ)

/-- Let J be the maximum offset and K the maximum multiplier. The natural
division in K costs at most one extra multiplier. -/
theorem box_product {T h : ℕ} (hp : 0<h) :
    let J := height h
    let K := T*J/h+1
    3*(J*K) ≤ 4*T+3*J := by
  intro J K
  have jsq : J^2*3≤4*h := (Nat.le_div_iff_mul_le (by decide : 0<3)).mp (Nat.sqrt_le' _)
  have div := Nat.div_mul_le_self (T*J) h
  have scaled := Nat.mul_le_mul_left (3*J) div
  have weight := Nat.mul_le_mul_left T jsq
  apply Nat.le_of_mul_le_mul_left (c:=h) _ hp
  dsimp only [K]
  nlinarith only [scaled,weight]

/-- A single fixed modulus works for every nonsquare positive input below
2^2048, including the full 2048-bit range. -/
theorem target_modulus130 {N : ℕ} (upper : N<2^2048) (nonsquare : N.sqrt^2<N) :
    let T := N.sqrt
    let h := N-T^2
    let J := height h
    let K := T*J/h+1
    2*J*K < primes130.prod := by
  intro T h J K
  have tcap : T<2^1024 := by
    apply Nat.sqrt_lt'.mpr
    exact upper.trans_eq (by ring)
  have hp : 0<h := Nat.sub_pos_of_lt nonsquare
  have hcap : h≤2*T := by
    have sum : h+T^2=N := Nat.sub_add_cancel nonsquare.le
    have next : N<(T+1)^2 := Nat.lt_succ_sqrt' _
    nlinarith only [sum,next]
  have jcap : J≤2^514 := by
    have jsq : J^2*3≤4*h := (Nat.le_div_iff_mul_le (by decide : 0<3)).mp (Nat.sqrt_le' _)
    by_contra! big
    have over := Nat.pow_le_pow_left big.le 2
    have size : 8*2^1024<3*((2:ℕ)^514)^2 := by decide +kernel
    omega
  have box := box_product (T:=T) hp
  change 3*(J*K)≤4*T+3*J at box
  have num := fixed_bounds.2.2
  rw [Nat.mul_assoc]
  omega

theorem target_modulus131 {N : ℕ} (upper : N<2^2048) (nonsquare : N.sqrt^2<N) :
    let T := N.sqrt
    let h := N-T^2
    let J := height h
    let K := T*J/h+1
    2*J*K < primes131.prod := by
  have h := target_modulus130 upper nonsquare
  dsimp only at h ⊢
  simp only [primes131,List.prod_cons]
  omega

/-- The lower endpoint of the exact local label count at an eligible odd prime. -/
theorem localCount_floor {N T p : ℕ} (prime : p.Prime) (odd : p≠2) (unit : ¬p∣N) :
    (p+1)/2 ≤ localCount N T p := by
  letI : Fact p.Prime := ⟨prime⟩
  have nz := mt (ZMod.natCast_zmod_eq_zero_iff_dvd N p).mp unit
  rw [localCount_eq]
  by_cases square : IsSquare (N:ZMod p)
  · rw [card_localSlopes_of_square odd _ _ nz square]
    omega
  · rw [card_localSlopes_of_nonsquare _ _ nz square]

/-- Actual counts are nondecreasing along eligible odd primes, even when the
quadratic character switches from +1 to −1. -/
theorem localCount_mono {N T p q : ℕ} (pp : p.Prime) (qp : q.Prime)
    (po : p≠2) (qo : q≠2) (pu : ¬p∣N) (qu : ¬q∣N) (lt : p<q) :
    localCount N T p≤localCount N T q := by
  letI : Fact p.Prime := ⟨pp⟩
  have top := card_localSlopes_le po (N:ZMod p) (T:ZMod p)
    (mt (ZMod.natCast_zmod_eq_zero_iff_dvd N p).mp pu)
  have bot := localCount_floor (T:=T) qp qo qu
  rw [←localCount_eq] at top
  obtain ⟨a,ha⟩ := pp.odd_of_ne_two po
  obtain ⟨b,hb⟩ := qp.odd_of_ne_two qo
  omega

/-- Replacing a prefix by any set of at least as many prices increases the
product when the removed prices are at most v and the added ones at least v.
Extra entries each cost at least v. This covers both a cheapest actual prefix
and repetition of its last price beyond a finite price table. -/
theorem cheapest_prefix {α : Type*} [DecidableEq α] (P S : Finset α) (c : α → ℕ) (v : ℕ)
    (size : P.card≤S.card) (missing : ∀ x∈P \ S, c x≤v)
    (added : ∀ x∈S \ P, v≤c x) :
    v^(S.card-P.card)*(∏ x∈P, c x) ≤ ∏ x∈S, c x := by
  have split (a b : Finset α) : (∏ x∈a \ b, c x)*(∏ x∈a ∩ b, c x) = ∏ x∈a, c x := by
    simpa only [Finset.sdiff_inter_self_left] using
      (Finset.prod_sdiff (f:=c) (Finset.inter_subset_left (s₁:=a) (s₂:=b)))
  have count : S.card-P.card+(P \ S).card=(S \ P).card := by
    have a := Finset.card_sdiff_add_card_inter P S
    have b := Finset.card_sdiff_add_card_inter S P
    rw [Finset.inter_comm S P] at b
    omega
  have diffs : v^(S.card-P.card)*(∏ x∈P \ S,c x)≤∏ x∈S \ P,c x := calc
    _ ≤ v^(S.card-P.card)*v^(P \ S).card := Nat.mul_le_mul_left _ (by
      simpa using Finset.prod_le_prod' missing)
    _ = v^(S \ P).card := by rw [←pow_add,count]
    _ ≤ _ := by simpa using Finset.prod_le_prod' added
  rw [←split P S,←split S P,Finset.inter_comm S P,←mul_assoc]
  exact Nat.mul_le_mul_right _ diffs

/-- Modulus versus product of prices for any tail of qualifying primes. -/
theorem modulus_le_cost {N T : ℕ} (S : Finset ℕ)
    (ok : ∀ p∈S, p.Prime ∧ p≠2 ∧ ¬p∣N) :
    (∏ p∈S, p) ≤ 2^S.card*(∏ p∈S, localCount N T p) := by
  calc
    _ ≤ ∏ p∈S, 2*localCount N T p := by
      apply Finset.prod_le_prod'
      intro p mem
      obtain ⟨prime,odd,unit⟩ := ok p mem
      obtain ⟨a,ha⟩ := prime.odd_of_ne_two odd
      have := localCount_floor (T:=T) prime odd unit
      omega
    _ = _ := by rw [Finset.prod_mul_distrib,Finset.prod_const]

/-- After fixing the small-prime subset with modulus m and cost c, both its
residual modulus target and a certified cheapest-tail price constrain the full
cost. The statement includes the empty tail. -/
theorem conditioned_lower {N T m c H P : ℕ} (S : Finset ℕ)
    (ok : ∀ p∈S, p.Prime ∧ p≠2 ∧ ¬p∣N) (mp : 0<m)
    (room : H<m*(∏ p∈S,p)) (cheapest : P≤∏ p∈S,localCount N T p) :
    c*max P (H/m/2^S.card+1) ≤ c*(∏ p∈S,localCount N T p) := by
  have h := (Nat.div_lt_iff_lt_mul mp).mpr (by simpa [mul_comm] using room)
  have cap := h.trans_le (modulus_le_cost (T:=T) S ok)
  have div : H/m/2^S.card<∏ p∈S,localCount N T p :=
    (Nat.div_lt_iff_lt_mul (show 0<2^S.card by positivity)).mpr (by rwa [mul_comm])
  exact Nat.mul_le_mul_left _ (max_le cheapest div)

private abbrev oddThrough743 : Finset ℕ := primes131.toFinset

set_option maxRecDepth 4000 in
private theorem prefix_floor_cost : 2^898 < (primes131.map fun p => (p+1)/2).prod :=
  by decide +kernel

set_option maxRecDepth 4000 in
private theorem prefix_complete : ∀ p∈List.range 744, p∈primes131 ∨ p=2 ∨ ¬p.Prime :=
  by decide +kernel

private theorem first131_floor : oddThrough743.card=131 ∧
    2^898 < ∏ p∈oddThrough743, (p+1)/2 := by
  constructor
  · exact (List.toFinset_card_of_nodup primes131_checked.2.1).trans primes131_checked.1
  · change 2^898 < primes131.toFinset.prod (fun p => (p+1)/2)
    rw [List.prod_toFinset _ primes131_checked.2.1]
    exact prefix_floor_cost


/-- An arbitrary set of 131 or more eligible odd primes already has more than
2^898 possible tuples, even with the cheaper square class at each prime. -/
theorem many_primes_floor {N T : ℕ} (S : Finset ℕ) (ok : ∀ p∈S, p.Prime ∧ p≠2 ∧ ¬p∣N)
    (many : 131≤S.card) : 2^898 < ∏ p∈S, localCount N T p := by
  let f := fun p:ℕ => (p+1)/2
  have cheap := cheapest_prefix oddThrough743 S f 372 (by simpa only [first131_floor.1] using many)
    (fun x hx => by
      have := (primes131_checked.2.2 x (List.mem_toFinset.mp (Finset.mem_sdiff.mp hx).1)).2.2
      dsimp [f]; omega)
    (fun x hx => by
      obtain ⟨xs,xout⟩ := Finset.mem_sdiff.mp hx
      obtain ⟨prime,odd,_⟩ := ok x xs
      have lower := prime.two_le
      have cap : 743<x := by
        by_contra! no
        rcases prefix_complete x (List.mem_range.mpr (by omega)) with inside|two|non
        · exact xout (List.mem_toFinset.mpr inside)
        · exact odd two
        · exact non prime
      dsimp [f]; omega)
  have price := Nat.le_mul_of_pos_left (∏ p∈oddThrough743,f p)
    (show 0<372^(S.card-oddThrough743.card) by positivity)
  exact first131_floor.2.trans_le ((price.trans cheap).trans (Finset.prod_le_prod' (fun p hp =>
    localCount_floor (T:=T) (ok p hp).1 (ok p hp).2.1 (ok p hp).2.2)))

/-- Every distinct odd-prime wheel meeting the rational reconstruction
threshold on a nonsquare input with at least 2048 bits needs over 2^893
tuples. A prime dividing N yields a divisor separately. -/
theorem target_wheel_lower {N : ℕ} (width : 2^2047≤N) (nonsquare : N.sqrt^2<N)
    (S : Finset ℕ) (ok : ∀ p∈S, p.Prime ∧ p≠2 ∧ ¬p∣N)
    (room : let T := N.sqrt; let h := N-T^2; let J := height h;
      2*J*(T*J/h+1)<∏ p∈S,p) : 2^893<∏ p∈S,localCount N N.sqrt p := by
  by_cases many : 131≤S.card
  · exact (show (2:ℕ)^893≤2^898 by decide +kernel).trans_lt (many_primes_floor S ok many)
  · have floor : 2^1023≤N.sqrt := Nat.le_sqrt'.mpr
      ((show ((2:ℕ)^1023)^2≤2^2047 by decide +kernel).trans width)
    have threshold := rectangle_threshold (T:=N.sqrt) (Nat.sub_pos_of_lt nonsquare)
    have pm := floor.trans_lt (threshold.trans room)
    have bound := modulus_le_cost (T:=N.sqrt) S ok
    have pow := Nat.pow_le_pow_right (by decide : 0<2) (show S.card≤130 by omega)
    have high := pm.trans_le (bound.trans (Nat.mul_le_mul_right _ pow))
    have scale : (2:ℕ)^1023=2^130*2^893 := by decide +kernel
    rw [scale] at high
    exact (Nat.mul_lt_mul_left (by positivity)).mp high

end PrimeFactors.OffsetProjectiveSlopes
