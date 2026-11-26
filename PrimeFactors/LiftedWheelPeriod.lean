import PrimeFactors.TraceFoldedRight

/-! Lift a right CRT residue modulo m through h periods. The sum interval can
be wider than the resulting table period. -/
namespace PrimeFactors.LiftedWheelPeriod
open Finset TraceFoldedRight

/-- The original right residue is taken modulo m even after extending the table. -/
noncomputable def lifted (m h : ℤ) (right : Finset ℤ) : Finset ℤ :=
  (Ico 0 (m*h)).filter (fun r => r%m∈right)

/-- The product of a raw right menu with h high digits has no CRT duplications. -/
theorem card_lifted {m h : ℤ} (mp : 0<m) (right : Finset ℤ)
    (inside : ∀ r∈right, 0≤r ∧ r<m) :
    (lifted m h right).card = right.card*h.toNat := by
  have split : (lifted m h right).card = (right ×ˢ Ico 0 h).card := by
    apply card_nbij' (fun z => (z%m,z/m)) (fun t => t.1+m*t.2)
    · intro z hz
      obtain ⟨zr,zm⟩ := mem_filter.mp hz
      obtain ⟨lo,hi⟩ := mem_Ico.mp zr
      exact mem_product.mpr ⟨zm,mem_Ico.mpr ⟨Int.ediv_nonneg lo mp.le,
        (Int.ediv_lt_iff_lt_mul mp).mpr (mul_comm m h ▸ hi)⟩⟩
    · rintro ⟨r,i⟩ hp
      obtain ⟨hr,hi⟩ := mem_product.mp hp
      obtain ⟨i0,ih⟩ := mem_Ico.mp hi
      obtain ⟨r0,rm⟩ := inside r hr
      have last : i+1≤h := by omega
      have bound := mul_le_mul_of_nonneg_left last mp.le
      exact mem_filter.mpr ⟨mem_Ico.mpr ⟨add_nonneg r0 (mul_nonneg mp.le i0),by linarith⟩,
        by simpa only [Int.add_mul_emod_self_left,Int.emod_eq_of_lt r0 rm] using hr⟩
    · intro z _
      exact Int.emod_add_ediv z m
    · rintro ⟨r,i⟩ hri
      obtain ⟨r0,rm⟩ := inside r (mem_product.mp hri).1
      simp [Int.add_mul_emod_self_left,Int.emod_eq_of_lt r0 rm,
        Int.add_mul_ediv_left _ _ mp.ne',Int.ediv_eq_zero_of_lt r0 rm]
  simpa [Int.card_Ico] using split

/-- The loop visits at most floor(w/Q)+2 targets on one left row. -/
theorem query_count {Q a c w : ℤ} (qp : 0<Q) (wp : 0≤w) :
    (Icc (-((w+Q/2-a-c)/Q)) ((a+c+Q/2)/Q)).card ≤ (w/Q).toNat+2 := by
  let u := w+Q/2-a-c
  let v := a+c+Q/2
  have le (x : ℤ) : (x/Q)*Q ≤ x := (Int.le_ediv_iff_mul_le qp).mp le_rfl
  have add : u/Q+v/Q≤(u+v)/Q := (Int.le_ediv_iff_mul_le qp).mpr
    (by rw [add_mul]; exact add_le_add (le u) (le v))
  have bound : (u+v)/Q≤(w+Q)/Q := Int.ediv_le_ediv qp (by dsimp [u,v]; omega)
  rw [Int.add_ediv_of_dvd_right (dvd_refl Q),Int.ediv_self qp.ne'] at bound
  have w0 : 0≤w/Q := Int.ediv_nonneg wp qp.le
  rw [Int.card_Icc,sub_neg_eq_add]
  change (v/Q+1+u/Q).toNat≤(w/Q).toNat+2
  omega

private theorem wrap_of_window {Q a c w k t : ℤ} {plus : Bool} (qp : 0<Q)
    (ok : rankWindow Q (a+c-k*Q) w plus t) : wrapWindow Q a c w k := by
  have h : (-k)*Q≤w+Q/2-a-c ∧ k*Q≤a+c+Q/2 := by
    cases plus <;> simp only [rankWindow,Bool.false_eq_true,↓reduceIte,max_le_iff,
      le_min_iff,neg_mul] at * <;> omega
  have lo := (Int.le_ediv_iff_mul_le qp).mpr h.1
  exact ⟨by omega,(Int.le_ediv_iff_mul_le qp).mpr h.2⟩

private theorem mod_center {m h r : ℤ} : (centered (m*h) r)%m=r%m := by
  unfold centered
  split
  · rfl
  · rw [show r-m*h=r+m*(-h) by ring,Int.add_mul_emod_self_left]

private def reflect (Q r : ℤ) : ℤ := if r=0 then 0 else Q-r

private theorem card_stored {Q : ℤ} (qp : 0<Q) (S : Finset ℤ)
    (inside : ∀ r∈S, 0≤r ∧ r<Q) (closed : ∀ r∈S, reflect Q r∈S) :
    2*(stored Q S).card=S.card+(S.filter fun r => r=0 ∨ 2*r=Q).card := by
  have invol : ∀ r∈S, reflect Q (reflect Q r)=r := by
    intro r hr
    obtain ⟨r0,rq⟩ := inside r hr
    unfold reflect
    split_ifs <;> omega
  have eq := orbit_count S (reflect Q) closed invol
  have fixed : (S.filter fun r => r=reflect Q r) = S.filter fun r => r=0 ∨ 2*r=Q := by
    ext r
    simp only [mem_filter,reflect]
    apply and_congr_right
    intro _
    split_ifs <;> omega
  have raw : stored Q S=representatives S (reflect Q) := by
    ext t
    constructor
    · intro z
      obtain ⟨r,hr,rfl⟩ := mem_image.mp z
      obtain ⟨r0,rq⟩ := inside r hr
      by_cases low : 2*r≤Q
      · have mag : |centered Q r|=r := by simp [centered,low,abs_of_nonneg r0]
        rw [mag]
        apply mem_filter.mpr ⟨hr,?_⟩
        unfold reflect
        split_ifs <;> omega
      · have mag : |centered Q r|=Q-r := by
          rw [centered,if_neg low,abs_of_neg (sub_neg.mpr rq)]; omega
        rw [mag]
        have cl := closed r hr
        rw [reflect,if_neg (show r≠0 by omega)] at cl
        apply mem_filter.mpr ⟨cl,?_⟩
        unfold reflect
        split_ifs <;> omega
    · intro z
      obtain ⟨ht,tr⟩ := mem_filter.mp z
      obtain ⟨t0,tq⟩ := inside t ht
      have low : 2*t≤Q := by unfold reflect at tr; split_ifs at tr <;> omega
      exact mem_image.mpr ⟨t,ht,by simp [centered,low,abs_of_nonneg t0]⟩
  rwa [raw,←fixed]

/-- Exact storage including both possible singleton ranks. Membership of the
even midpoint is determined by its residue in the original wheel. -/
theorem storage {m h : ℤ} (mp : 0<m) (hp : 0<h) (right : Finset ℤ)
    (inside : ∀ r∈right, 0≤r ∧ r<m)
    (stable : ∀ r : ℤ, r%m∈right → (-r)%m∈right) :
    2*(stored (m*h) (lifted m h right)).card =
      right.card*h.toNat+(if 0∈right then 1 else 0)+
      (if (m*h)%2=0 ∧ ((m*h)/2)%m∈right then 1 else 0) := by
  let Q := m*h
  let S := lifted m h right
  have qp : 0<Q := mul_pos mp hp
  have bounded : ∀ r∈S, 0≤r ∧ r<Q := fun _ hr => mem_Ico.mp (mem_filter.mp hr).1
  have symmetrical : ∀ r∈S, reflect Q r∈S := by
    intro r hr
    obtain ⟨r0,rq⟩ := bounded r hr
    by_cases zero : r=0
    · simpa [reflect,zero] using hr
    · rw [reflect,if_neg zero]
      refine mem_filter.mpr ⟨mem_Ico.mpr ⟨by omega,by omega⟩,?_⟩
      rw [show Q-r=(-r)+m*h by dsimp [Q]; ring,Int.add_mul_emod_self_left]
      exact stable r (mem_filter.mp hr).2
  have fixed : (S.filter fun r => r=0 ∨ 2*r=Q)=
      (if 0∈right then {0} else ∅)∪
      (if Q%2=0 ∧ (Q/2)%m∈right then {Q/2} else ∅) := by
    ext r
    have zero : (0:ℤ)∈S ↔ (0:ℤ)∈right := by simp [S,lifted,show 0<m*h from qp]
    have mid : Q/2∈S ↔ (Q/2)%m∈right :=
      ⟨fun z => (mem_filter.mp z).2,fun z => mem_filter.mpr ⟨mem_Ico.mpr ⟨by omega,by omega⟩,z⟩⟩
    have single (H : Prop) [Decidable H] (b : ℤ) :
        r∈(if H then {b} else ∅ : Finset ℤ) ↔ r=b ∧ H := by
      by_cases yes : H <;> simp [yes]
    rw [mem_filter,mem_union,single,single]
    constructor
    · rintro ⟨hr,rz|rh⟩
      · exact Or.inl ⟨rz,zero.mp (rz ▸ hr)⟩
      · have eq : r=Q/2 := by omega
        exact Or.inr ⟨eq,by omega,mid.mp (eq ▸ hr)⟩
    · rintro (⟨rfl,hr⟩|⟨rfl,evenQ,hr⟩)
      · exact ⟨zero.mpr hr,Or.inl rfl⟩
      · exact ⟨mid.mpr hr,Or.inr (by omega)⟩
  have eq := card_stored qp S bounded symmetrical
  rw [fixed] at eq
  have rcard : S.card=right.card*h.toNat := card_lifted mp right inside
  rw [rcard] at eq
  change 2*(stored Q S).card = right.card*h.toNat+(if 0∈right then 1 else 0)+
    (if Q%2=0 ∧ (Q/2)%m∈right then 1 else 0)
  by_cases z : (0:ℤ)∈right <;> by_cases mid : Q%2=0 ∧ (Q/2)%m∈right
  · have nz : (0:ℤ)≠Q/2 := by omega
    have dis : Disjoint ({0}:Finset ℤ) {Q/2} := by simpa using Ne.symm nz
    simp only [if_pos z,if_pos mid,card_union_of_disjoint dis,card_singleton] at eq ⊢
    omega
  · simp only [if_pos z,if_neg mid,union_empty,card_singleton,add_zero] at eq ⊢
    exact eq
  · simp only [if_neg z,if_pos mid,empty_union,card_singleton,add_zero] at eq ⊢
    exact eq
  · simp only [if_neg z,if_neg mid,empty_union,card_empty,add_zero] at eq ⊢
    exact eq

/-- A candidate hits the original CRT menu precisely when an admitted
table rank with one of the two signs recovers it at a visited period shift.
The statement allows arbitrary nonnegative widths, including many periods. -/
theorem coverage {m h a c w x : ℤ} (mp : 0<m) (hp : 0<h)
    (right : Finset ℤ) (stable : ∀ r : ℤ, r%m∈right → (-r)%m∈right) :
    (0≤x ∧ x≤w ∧ (x-a-c)%m∈right) ↔
      ∃ t∈stored (m*h) (lifted m h right), ∃ (k : ℤ) (plus : Bool),
        wrapWindow (m*h) a c w k ∧ rankWindow (m*h) (a+c-k*(m*h)) w plus t ∧
        x=a+c-k*(m*h)+signedRank plus t := by
  let Q := m*h
  have qp : 0<Q := mul_pos mp hp
  constructor
  · rintro ⟨x0,xw,localHit⟩
    let v := x-a-c
    let r := v%Q
    let j := v/Q
    have r0 : 0≤r := Int.emod_nonneg v qp.ne'
    have rQ : r<Q := Int.emod_lt_of_pos v qp
    have localR : r%m∈right := by
      dsimp [r,v,Q]
      rwa [Int.emod_emod_of_dvd _ (dvd_mul_right ..)]
    have kept : r∈lifted m h right := mem_filter.mpr ⟨mem_Ico.mpr ⟨r0,rQ⟩,localR⟩
    have seen : |centered Q r|∈stored Q (lifted m h right) := mem_image.mpr ⟨r,kept,rfl⟩
    have dec : r+Q*j=x-a-c := Int.emod_add_ediv v Q
    by_cases low : 2*r≤Q
    · have mag : |centered Q r|=r := by simp [centered,low,abs_of_nonneg r0]
      rw [mag] at seen
      have exactX : x=a+c-(-j)*Q+r := by linarith only [dec]
      have ok : rankWindow Q (a+c-(-j)*Q) w true r := by
        simp only [rankWindow,↓reduceIte,max_le_iff,le_min_iff]; omega
      exact ⟨r,seen,-j,true,wrap_of_window qp ok,ok,exactX⟩
    · have mag : |centered Q r|=Q-r := by
        rw [centered,if_neg low,abs_of_neg (sub_neg.mpr rQ)]; omega
      rw [mag] at seen
      have exactX : x=a+c-(-j-1)*Q+(-(Q-r)) := by nlinarith only [dec]
      have ok : rankWindow Q (a+c-(-j-1)*Q) w false (Q-r) := by
        simp only [rankWindow,Bool.false_eq_true,↓reduceIte,max_le_iff,le_min_iff]; omega
      exact ⟨Q-r,seen,-j-1,false,wrap_of_window qp ok,ok,exactX⟩
  · rintro ⟨t,ht,k,plus,_,hk,rfl⟩
    obtain ⟨r,hr,rfl⟩ := mem_image.mp ht
    have localR := (mem_filter.mp hr).2
    have pos : (centered Q r)%m∈right := by rwa [mod_center]
    have neg := stable _ pos
    have sign : (signedRank plus |centered Q r|)%m∈right := by
      by_cases z0 : 0≤centered Q r
      · cases plus <;> simp only [signedRank,Bool.false_eq_true,↓reduceIte,abs_of_nonneg z0] <;> assumption
      · cases plus <;> simp only [signedRank,Bool.false_eq_true,↓reduceIte,
          abs_of_neg (lt_of_not_ge z0),neg_neg] <;> assumption
    constructor
    · cases plus <;> simp only [signedRank,rankWindow,Bool.false_eq_true,↓reduceIte,max_le_iff,
        le_min_iff] at hk ⊢ <;> omega
    constructor
    · cases plus <;> simp only [signedRank,rankWindow,Bool.false_eq_true,↓reduceIte,max_le_iff,
        le_min_iff] at hk ⊢ <;> omega
    · change (a+c-k*(m*h)+signedRank plus |centered Q r|-a-c)%m∈right
      rw [show a+c-k*(m*h)+signedRank plus |centered Q r|-a-c=
        signedRank plus |centered Q r|+m*(-k*h) by ring,Int.add_mul_emod_self_left]
      exact sign

end PrimeFactors.LiftedWheelPeriod
