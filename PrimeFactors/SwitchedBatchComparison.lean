import PrimeFactors.OrdinaryBatchRanks

/-! Count the products at which each of two explicit trace schedules finds
a proper divisor after the shared prefix has failed. -/
namespace PrimeFactors.InteriorBatchPopulation
open Real Finset MarginalTraceWidth

set_option exponentiation.threshold 8192
set_option maxRecDepth 4096
set_option maxHeartbeats 1500000

/-- Both tests use the same square and upper-root gcd. -/
def properSquare (n k S : ℕ) : Prop :=
  let d := (S^2-4*k*n).sqrt
  S^2=4*k*n+d^2 ∧ 1<n.gcd ((S+d)/2) ∧ n.gcd ((S+d)/2)<n

private theorem ordinary_sum {p q S : ℕ} (pp : p.Prime) (qp : q.Prime) (pq : p<q)
    (hit : properSquare (p*q) 1 S) : S=p+q := by
  obtain ⟨sq,lo,hi⟩ := hit
  let d := (S^2-4*1*(p*q)).sqrt
  have h := OffsetSquareSplit.root_identities (k:=1) (N:=p*q) (d:=d) (S:=S) (by simpa using sq)
  dsimp only at h
  obtain ⟨a,b,ab,tr⟩ := ShiftedEndpointPopulation.allocation pp qp pq.ne
    (by simpa using h.2 : (S+d)/2*((S-d)/2)=1*(p*q)) lo hi
  have ha : a=1 := Nat.eq_one_of_mul_eq_one_right ab.symm
  have hb : b=1 := Nat.eq_one_of_mul_eq_one_left ab.symm
  simpa only [ha,hb,one_mul,h.1] using tr

private theorem ordinary_units {p q : ℕ} (pp : p.Prime) (qp : q.Prime)
    (pl : 6<p) (pq : p≤q) : (p*q).Coprime 6 := by
  have u (l : ℕ) (pr : l.Prime) (large : 6<l) : l.Coprime 6 :=
    pr.coprime_iff_not_dvd.mpr (fun h => (not_le_of_gt large) (Nat.le_of_dvd (by decide) h))
  exact Nat.coprime_mul_iff_left.mpr ⟨u p pp pl,u q qp (pl.trans_le pq)⟩

private theorem cycle_spec : ∀ r o : Fin 24, (r:ℕ).Coprime 6 → 0 < (offsets r o 1 1).length := by
  decide +kernel

private theorem residue_unit' {n : ℕ} (hn : n.Coprime 6) : (n%24).Coprime 6 := by
  change (n%24).gcd 6=1
  rw [Nat.gcd_comm,Nat.gcd_rec,Nat.mod_mod_of_dvd _ (by decide : 6∣24),←Nat.gcd_rec,Nat.gcd_comm]
  exact hn

private theorem ordinary_offsets {r o : Fin 24} (hu : (r:ℕ).Coprime 6) :
    Monotone (offset r o 1 1) ∧ ∀ i, offset r o 1 1 i ≤ 24*i+23 := by
  let xs := offsets r o 1 1
  have pos : 0<xs.length := cycle_spec r o hu
  have idx (i : ℕ) : i%xs.length<xs.length := Nat.mod_lt _ pos
  have eq (i : ℕ) : offset r o 1 1 i = 24*(i/xs.length) + xs[i%xs.length]'(idx i) := by
    unfold offset
    change 24*(i/xs.length) + xs[i%xs.length]?.getD 0 = _
    rw [List.getElem?_eq_getElem (idx i)]; rfl
  have small (i : ℕ) : xs[i%xs.length]'(idx i) < 24 := by
    apply List.mem_range.mp
    exact (List.mem_filter.mp (List.getElem_mem (idx i) : xs[i%xs.length]'(idx i)∈xs)).1
  have sorted : xs.Pairwise (· < ·) := List.pairwise_lt_range.filter _
  constructor
  · intro i j order
    rw [eq i,eq j]
    have divle : i/xs.length ≤ j/xs.length := Nat.div_le_div_right order
    rcases divle.lt_or_eq with lower|same
    · have := small i
      omega
    · rw [same]
      apply Nat.add_le_add_left
      have di := Nat.div_add_mod i xs.length
      rw [same] at di
      have rem : i%xs.length ≤ j%xs.length := by
        have dj := Nat.div_add_mod j xs.length
        omega
      rcases rem.lt_or_eq with lt|eq'
      · exact ((List.pairwise_iff_getElem.mp sorted) _ _ (idx i) (idx j) lt).le
      · simp [eq']
  · intro i
    rw [eq i]
    have divle := Nat.div_le_self i xs.length
    have lt := small i
    omega

theorem ordinaryLabel_mono {n : ℕ} (unit : n.Coprime 6) : Monotone (ordinaryLabel n) := by
  let f := ⌈2*sqrt (n:ℝ)⌉₊
  let r : Fin 24 := ⟨n%24,Nat.mod_lt _ (by decide)⟩
  let o : Fin 24 := ⟨f%24,Nat.mod_lt _ (by decide)⟩
  intro i j h
  exact Nat.add_le_add_left ((ordinary_offsets (r:=r) (o:=o) (residue_unit' unit)).1 h) f

/-- Stage two is counted only after every stage-one test has missed. -/
def commonMiss (n : ℕ) : Prop := ∀ i<m*B, ¬properSquare n 1 (ordinaryLabel n i)

def ordinaryExtra (n : ℕ) : Prop :=
  commonMiss n ∧ ∃ i∈Icc (m*B) ((m+1)*B), properSquare n 1 (ordinaryLabel n i)

def switchedExtra (n : ℕ) : Prop :=
  commonMiss n ∧ ∃ S∈Ico ⌈2*sqrt (6*(n:ℝ))⌉₊ (⌈2*sqrt (6*(n:ℝ))⌉₊+B), properSquare n 6 S

private theorem interior_new {p q : ℕ} (hp : p∈interior) (hq : q∈neighbors p) :
    switchedExtra (p*q) := by
  have pp : p.Prime := (mem_filter.mp (by simpa only [interior,firstPrimes] using hp)).2
  have qp : q.Prime := (mem_filter.mp (by simpa only [neighbors] using hq)).2
  obtain ⟨_,pl,pq,_,_,far⟩ := interior_split hp hq
  have unit := ordinary_units pp qp (by omega) pq.le
  constructor
  · intro i hi hit
    let n := p*q
    let x : ℝ := 2*sqrt (n:ℝ)
    let f := ⌈x⌉₊
    let r : Fin 24 := ⟨n%24,Nat.mod_lt _ (by decide)⟩
    let o : Fin 24 := ⟨f%24,Nat.mod_lt _ (by decide)⟩
    have id : (sqrt q-sqrt p)^2=(p:ℝ)+q-x := by
      dsimp [x,n]
      rw [Nat.cast_mul,Real.sqrt_mul (Nat.cast_nonneg p)]
      nlinarith only [sq_sqrt (Nat.cast_nonneg q),sq_sqrt (Nat.cast_nonneg p)]
    have sum := ordinary_sum pp qp pq hit
    change f+offset r o 1 1 i=p+q at sum
    have off := (ordinary_offsets (r:=r) (o:=o) (residue_unit' unit)).2 i
    have blocks : m*B ≤ (m+1)*B := by decide +kernel
    have cap : p+q≤f+24*((m+1)*B)+23 := by omega
    have cap' : (p:ℝ)+q ≤ f+(24*((m+1)*B):ℕ)+23 := by exact_mod_cast cap
    have fle : (f:ℝ)<x+1 := Nat.ceil_lt_add_one (by dsimp [x]; positivity)
    rw [id] at far
    simp only [Nat.cast_add,Nat.cast_ofNat] at far
    linarith only [far,cap',fle]
  · obtain ⟨S,hS,hs,g⟩ := interior_witness hp hq
    refine ⟨S,hS,hs,?_⟩
    rcases g with h|h
    · rw [h]
      exact ⟨pp.one_lt, by nlinarith only [Nat.mul_le_mul_left p qp.two_le,pp.pos]⟩
    · rw [h]
      exact ⟨qp.one_lt, by nlinarith only [Nat.mul_le_mul_right q pp.two_le,qp.pos]⟩

/-- Ordered distinct full-width prime pairs in the public bin that this stage splits. -/
noncomputable def stagePairs (stage : ℕ → Prop) : Finset (ℕ×ℕ) := by
  classical
  exact ((Ico (U/2) U) ×ˢ (Ico (U/2) U)).filter fun z =>
    z.1<z.2 ∧ z.1.Prime ∧ z.2.Prime ∧ bin z.1 z.2 ∧ stage (z.1*z.2)

private theorem mem_stagePairs {stage : ℕ → Prop} {p q : ℕ} :
    (p,q) ∈ stagePairs stage ↔
      U/2≤p ∧ p<q ∧ q<U ∧ p.Prime ∧ q.Prime ∧ bin p q ∧ stage (p*q) := by
  classical
  simp only [stagePairs,mem_filter,mem_product,mem_Ico]
  constructor
  · rintro ⟨⟨hp,hq⟩,pq,pp,qp,b,h⟩
    exact ⟨hp.1,pq,hq.2,pp,qp,b,h⟩
  · rintro ⟨pl,pq,qu,pp,qp,b,h⟩
    exact ⟨⟨⟨pl,pq.trans qu⟩,⟨pl.trans pq.le,qu⟩⟩,pq,pp,qp,b,h⟩

attribute [local irreducible] stagePairs interior neighbors firstPrimes

/-- The two square/gcd schedules compare actual additional splits in the
specified bin. Their sole external premise is the pair of prime counts. -/
theorem scheduled_gain (C : Counts) :
    9*(stagePairs ordinaryExtra).card < 5*(stagePairs switchedExtra).card := by
  have upper := gain C (stagePairs ordinaryExtra) (by
    rintro ⟨p,q⟩ h
    obtain ⟨pl,pq,qu,pp,qp,hb,_,i,hi,split⟩ := mem_stagePairs.mp h
    have unit := ordinary_units pp qp (lt_of_lt_of_le (by decide +kernel : 6<U/2) pl) pq.le
    obtain ⟨lo,hi⟩ := mem_Icc.mp hi
    have eq := ordinary_sum pp qp pq split
    exact ⟨pl,pq.le,qu.le,pp,qp,hb,tail_of_labels unit ((ordinaryLabel_mono unit lo).trans_eq eq)
      (eq.symm.trans_le (ordinaryLabel_mono unit hi))⟩)
  have lower : (interior.sigma neighbors).card ≤ (stagePairs switchedExtra).card := by
    apply card_le_card_of_injOn (fun z => (z.1,z.2))
    · rintro ⟨p,q⟩ h
      obtain ⟨hp,hq⟩ := mem_sigma.mp h
      obtain ⟨b,pl,pq,qu,_,_⟩ := interior_split hp hq
      have pp : p.Prime := (mem_filter.mp (by simpa only [interior,firstPrimes] using hp)).2
      have qp : q.Prime := (mem_filter.mp (by simpa only [neighbors] using hq)).2
      exact mem_stagePairs.mpr ⟨pl,pq,qu,pp,qp,b,interior_new hp hq⟩
    · rintro ⟨p,q⟩ _ ⟨u,v⟩ _ e
      simpa using e
  exact upper.trans_le (Nat.mul_le_mul_left 5 lower)

/-- Count input integers once, even though their search certificates exhibit both primes. -/
noncomputable def successfulProducts (stage : ℕ → Prop) :=
  (stagePairs stage).image (fun z => z.1*z.2)

private theorem prime_products_card (F : Finset (ℕ×ℕ))
    (ordered : ∀ z∈F, z.1<z.2 ∧ z.1.Prime ∧ z.2.Prime) :
    (F.image (fun z => z.1*z.2)).card = F.card := by
  apply card_image_iff.mpr
  rintro ⟨p,q⟩ h ⟨u,v⟩ k product
  obtain ⟨pq,pp,_⟩ := ordered _ h
  obtain ⟨uv,up,vp⟩ := ordered _ k
  change p*q=u*v at product
  have d : p∣u*v := product ▸ dvd_mul_right p q
  rcases pp.dvd_mul.mp d with du|dv
  · obtain rfl := (Nat.prime_dvd_prime_iff_eq pp up).mp du
    obtain rfl := Nat.eq_of_mul_eq_mul_left pp.pos product
    rfl
  · obtain rfl := (Nat.prime_dvd_prime_iff_eq pp vp).mp dv
    have qu := Nat.eq_of_mul_eq_mul_left pp.pos (product.trans (Nat.mul_comm u p))
    omega

theorem successfulProducts_card (stage : ℕ → Prop) :
    (successfulProducts stage).card = (stagePairs stage).card := by
  unfold successfulProducts
  apply prime_products_card
  rintro ⟨p,q⟩ h
  obtain ⟨_,pq,_,pp,qp,_,_⟩ := mem_stagePairs.mp h
  exact ⟨pq,pp,qp⟩

theorem scheduled_product_gain (C : Counts) :
    9*(successfulProducts ordinaryExtra).card < 5*(successfulProducts switchedExtra).card := by
  simpa only [successfulProducts_card] using scheduled_gain C

end PrimeFactors.InteriorBatchPopulation
