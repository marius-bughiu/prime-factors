import PrimeFactors.TracePrimePartners
import PrimeFactors.TraceCollisionWidth
import PrimeFactors.TraceCollisionOrder

/-! A finite upper bound for matches of modular trace rows. The period may
vary with the anchor and the coefficients. Both anchors and both assignments
of coefficients are included. -/

namespace PrimeFactors.TraceCollisionPopulation

open Finset TraceHitFrequency TraceCollisionWidth TraceCollisionOrder

set_option exponentiation.threshold 8192

/-- The excess over the exact real weighted geometric mean belongs to the
band beginning at a multiple of the period. -/
def InBand (a b p q t period L : ℕ) : Prop :=
  (↑(t*period) : ℝ) ≤ excess a b p q ∧ excess a b p q ≤ ↑(t*period)+(L:ℝ)

/-- Per-slope bound, with a near interval about `a*p/b` and two monotone
far branches per band. All branches refer to the same fixed anchor and period. -/
theorem one_direction {pool : Finset ℕ} {a b p U R L M period : ℕ}
    (bp : 0<b) (ab : a≤2*b) (pu : p≤U) (rp : 0<R) (qu : ∀ q∈pool, q≤U)
    (eligible : ∀ q∈pool, ∃ t<M, InBand a b p q t period L) :
    pool.card ≤ 2*R+1+M*(2*(3*U*L/R+1)) := by
  classical
  let near := pool.filter fun q => a*p≤b*q+R ∧ b*q≤a*p+R
  let left (t : ℕ) := pool.filter fun q => b*q+R≤a*p ∧ InBand a b p q t period L
  let right (t : ℕ) := pool.filter fun q => a*p+R≤b*q ∧ InBand a b p q t period L
  have nc : near.card ≤ 2*R+1 := calc
    _ ≤ (Icc (a*p-R) (a*p+R)).card := by
      apply card_le_card_of_injOn (fun q => b*q)
      · intro q hq
        obtain ⟨_,h,hh⟩ := mem_filter.mp hq
        exact mem_Icc.mpr ⟨by omega,hh⟩
      · intro x _ y _ eq; exact Nat.mul_left_cancel bp eq
    _ ≤ _ := by rw [Nat.card_Icc]; omega
  have cost {s : Finset ℕ} (t : ℕ) (sub : s ⊆ pool)
      (side : (∀ q∈s, a*p+R≤b*q) ∨ (∀ q∈s, b*q+R≤a*p))
      (hit : ∀ q∈s, InBand a b p q t period L) : s.card≤3*U*L/R+1 := by
    have sides : (∀ q∈s, (R:ℝ) ≤ (b:ℝ)*q-(a:ℝ)*p) ∨
        (∀ q∈s, (R:ℝ) ≤ (a:ℝ)*p-(b:ℝ)*q) := by
      rcases side with h|h
      · left; intro q hq; apply le_sub_iff_add_le.mpr; rw [add_comm]; exact_mod_cast h q hq
      · right; intro q hq; apply le_sub_iff_add_le.mpr; rw [add_comm]; exact_mod_cast h q hq
    have length := band_card (s:=s) (a:=(a:ℝ)) (b:=(b:ℝ)) (p:=(p:ℝ)) (U:=(U:ℝ))
      (R:=(R:ℝ)) (L:=(L:ℝ)) (C:=(↑(t*period):ℝ)) (by exact_mod_cast bp)
      (by positivity) (by exact_mod_cast ab) (by positivity) (by exact_mod_cast pu)
      (by exact_mod_cast rp) (fun q hq => by exact_mod_cast qu q (sub hq)) sides hit
    simpa only [←Nat.cast_ofNat (R:=ℝ) (n:=3),←Nat.cast_mul,Nat.floor_div_eq_div] using length
  have lc (t : ℕ) : (left t).card ≤ 3*U*L/R+1 :=
    cost t (filter_subset ..) (Or.inr fun _ h => (mem_filter.mp h).2.1) (fun _ h => (mem_filter.mp h).2.2)
  have rc (t : ℕ) : (right t).card ≤ 3*U*L/R+1 :=
    cost t (filter_subset ..) (Or.inl fun _ h => (mem_filter.mp h).2.1) (fun _ h => (mem_filter.mp h).2.2)
  have sub : pool ⊆ near ∪ (range M).biUnion (fun t => left t ∪ right t) := by
    intro q hq
    by_cases n : a*p≤b*q+R ∧ b*q≤a*p+R
    · exact mem_union_left _ (mem_filter.mpr ⟨hq,n⟩)
    obtain ⟨t,ht,h⟩ := eligible q hq
    apply mem_union_right; apply mem_biUnion.mpr; refine ⟨t,mem_range.mpr ht,?_⟩
    have side : b*q+R≤a*p ∨ a*p+R≤b*q := by omega
    cases side with
    | inl h' => exact mem_union_left _ (mem_filter.mpr ⟨hq,h',h⟩)
    | inr h' => exact mem_union_right _ (mem_filter.mpr ⟨hq,h',h⟩)
  apply (card_le_card sub).trans ((card_union_le ..).trans (Nat.add_le_add nc ?_))
  have rows := card_biUnion_le_card_mul (range M) (fun t => left t ∪ right t)
    (2*(3*U*L/R+1)) (fun t _ => (card_union_le (left t) (right t)).trans
      (by simpa only [two_mul] using Nat.add_le_add (lc t) (rc t)))
  simpa only [card_range] using rows

/-- A partner reaches one of finitely many bands for some ordered coefficient pair. -/
def Reached (ticks : ℕ → ℕ×ℕ → ℕ) (ws : Finset (ℕ×ℕ)) (M L p q : ℕ) : Prop :=
  ∃ w∈ws, ∃ t<M, InBand w.1 w.2 p q t (ticks p w) L

/-- Finite union over near and far partners, exceptional anchors, and both
orientations of the factor pair. The count permits overlap. -/
theorem population {pairs : Finset (ℕ×ℕ)} {pool bad : Finset ℕ} {ws : Finset (ℕ×ℕ)}
    {ticks : ℕ → ℕ×ℕ → ℕ} {U R L M : ℕ} (rp : 0<R) (qu : ∀ q∈pool, q≤U)
    (valid : ∀ w∈ws, 0<w.2 ∧ w.1≤2*w.2)
    (support : ∀ x∈pairs, x.1∈pool ∧ x.2∈pool ∧
      (x.1∈bad ∨ Reached ticks ws M L x.1 x.2 ∨ x.2∈bad ∨ Reached ticks ws M L x.2 x.1)) :
    pairs.card ≤ 2*pool.card*(bad.card+ws.card*(2*R+1+M*(2*(3*U*L/R+1)))) := by
  classical
  let qs (p : ℕ) (w : ℕ×ℕ) := pool.filter (fun q => ∃ t<M, InBand w.1 w.2 p q t (ticks p w) L)
  let partners p := ws.biUnion (qs p)
  let direct := (bad ×ˢ pool) ∪ pool.biUnion (fun p => (partners p).image (fun q => (p,q)))
  have mem {p q : ℕ} (hp : p∈pool) (hq : q∈pool) (hit : p∈bad ∨ Reached ticks ws M L p q) :
      (p,q) ∈ direct := by
    rcases hit with low|⟨w,hw,t,ht,win⟩
    · exact mem_union_left _ (mem_product.mpr ⟨low,hq⟩)
    apply mem_union_right; apply mem_biUnion.mpr
    exact ⟨p,hp,mem_image.mpr ⟨q,mem_biUnion.mpr ⟨w,hw,mem_filter.mpr ⟨hq,t,ht,win⟩⟩,rfl⟩⟩
  have sub : pairs ⊆ direct ∪ direct.image Prod.swap := by
    intro x hx; obtain ⟨hp,hq,h⟩ := support x hx
    rcases h with lo|hi|lo|hi
    · exact mem_union_left _ (mem hp hq (Or.inl lo))
    · exact mem_union_left _ (mem hp hq (Or.inr hi))
    · exact mem_union_right _ (mem_image.mpr ⟨x.swap,mem hq hp (Or.inl lo),rfl⟩)
    · exact mem_union_right _ (mem_image.mpr ⟨x.swap,mem hq hp (Or.inr hi),rfl⟩)
  have cap (p : ℕ) (hp : p∈pool) : (partners p).card ≤ ws.card*(2*R+1+M*(2*(3*U*L/R+1))) := by
    apply card_biUnion_le_card_mul; intro w hw
    obtain ⟨b,ab⟩ := valid w hw
    exact one_direction b ab (qu p hp) rp (fun _ h => qu _ (mem_filter.mp h).1)
      (fun _ h => (mem_filter.mp h).2)
  have dc : direct.card ≤ pool.card*(bad.card+ws.card*(2*R+1+M*(2*(3*U*L/R+1)))) := by
    apply (card_union_le ..).trans
    rw [card_product,Nat.mul_add,mul_comm bad.card]
    apply Nat.add_le_add_left; apply card_biUnion_le_card_mul; intro p hp
    exact card_image_le.trans (cap p hp)
  apply (card_le_card sub).trans ((card_union_le ..).trans ?_)
  have image : (direct.image Prod.swap).card≤direct.card := card_image_le
  rw [Nat.mul_assoc, two_mul]
  exact Nat.add_le_add dc (image.trans dc)

/-- Catalogue with both coefficient assignments. -/
noncomputable def oriented (k : ℕ) := directions k ∪ (directions k).image Prod.swap

private theorem direct_mem (k : ℕ) {w : ℕ×ℕ} (hw : w∈directions k) : w∈oriented k :=
  mem_union_left _ hw

private theorem swapped_mem (k : ℕ) {w : ℕ×ℕ} (hw : w∈directions k) : w.swap∈oriented k :=
  mem_union_right _ (mem_image.mpr ⟨w,hw,rfl⟩)

private theorem oriented_valid (k : ℕ) (w : ℕ×ℕ) (hw : w∈oriented k) : 0<w.2 ∧ w.1≤2*w.2 := by
  have valid {v : ℕ×ℕ} (h : v∈directions k) : 0<v.2 ∧ v.2≤v.1 ∧ v.1≤2*v.2 := by
    obtain ⟨⟨_,den⟩,lo,hi,_⟩ := mem_filter.mp h |>.imp_left mem_product.mp
    exact ⟨(mem_Icc.mp den).1,lo,hi⟩
  rcases mem_union.mp hw with h|h
  · exact ⟨(valid h).1,(valid h).2.2⟩
  obtain ⟨v,hv,rfl⟩ := mem_image.mp h
  obtain ⟨pos,lo,_⟩ := valid hv
  exact ⟨pos.trans_le lo,by change v.2≤2*v.1; omega⟩

private theorem oriented_card (k : ℕ) : (oriented k).card ≤ 2*(k*(k+3)/2) := by
  apply (card_union_le ..).trans
  rw [two_mul]; exact Nat.add_le_add (TracePrimePartners.triangular _) (card_image_le.trans (TracePrimePartners.triangular _))

noncomputable def weights : Finset (ℕ×ℕ) := oriented (2^32)

attribute [local irreducible] directions oriented

theorem mem_weights {w : ℕ×ℕ} (hw : w∈directions (2^32)) : w∈weights := @direct_mem (2^32) w hw

theorem swap_mem_weights {w : ℕ×ℕ} (hw : w∈directions (2^32)) : w.swap∈weights := @swapped_mem (2^32) w hw

def tickCount : ℕ := 3*(2*(2^32))*2^1024/2^470+1

def HighHit (ticks : ℕ → ℕ×ℕ → ℕ) (p q : ℕ) : Prop := Reached ticks weights tickCount (2^133) p q

/-- A modular match may use either anchor; the period within each oriented
row is fixed once that anchor and the coefficients have been specified. -/
def Event (bad : Finset ℕ) (ticks : ℕ → ℕ×ℕ → ℕ) (p q : ℕ) : Prop :=
  p∈bad ∨ HighHit ticks p q ∨ q∈bad ∨ HighHit ticks q p

/-- Per eligible prime, both anchors and all oriented rows together cost at
most this many partners when the exceptional set has size at most `E`. -/
def partnerBudget (E : ℕ) : ℕ :=
  2*(E+(2*((2^32)*(2^32+3)/2))*(2*2^874+1+tickCount*(2*(3*2^1024*2^133/2^874+1))))

theorem base_count {pairs : Finset (ℕ×ℕ)} {pool bad : Finset ℕ} {E : ℕ}
    (ticks : ℕ → ℕ×ℕ → ℕ) (qu : ∀ q∈pool, q≤2^1024) (exc : bad.card≤E)
    (support : ∀ x∈pairs, x.1∈pool ∧ x.2∈pool ∧ Event bad ticks x.1 x.2) :
    pairs.card ≤ pool.card*partnerBudget E := by
  let C : ℕ := 2*2^874+1+tickCount*(2*(3*2^1024*2^133/2^874+1))
  have hc := population (ticks:=ticks) (R:=2^874) (by decide +kernel) qu (oriented_valid (2^32)) support
  have hcost : bad.card+weights.card*C ≤ E+(2*((2^32)*(2^32+3)/2))*C :=
    Nat.add_le_add exc (Nat.mul_le_mul_right _ (oriented_card (2^32)))
  calc
    _ ≤ _ := hc
    _ ≤ _ := Nat.mul_le_mul_left (2*pool.card) hcost
    _ = _ := by dsimp only [partnerBudget,C]; ac_rfl

private theorem price_bound {A P E factor pop : ℕ} (count : A≤P*E)
    (den : 2^1023*P<44331*pop) (pos : 0<factor*E) (rate : factor*44331*E≤2^1023) :
    factor*A<pop := by
  apply Nat.lt_of_mul_lt_mul_left (a:=2^1023)
  calc
    _ ≤ 2^1023*(factor*(P*E)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ count)
    _ = (2^1023*P)*(factor*E) := by ac_rfl
    _ < (44331*pop)*(factor*E) := Nat.mul_lt_mul_of_pos_right den pos
    _ = (factor*44331*E)*pop := by ac_rfl
    _ ≤ _ := Nat.mul_le_mul_right _ rate

/-- The power-of-two exception bound gives 57 bits for any one fixed base. -/
theorem fixed_fraction {pairs : Finset (ℕ×ℕ)} {pool bad : Finset ℕ} {pop : ℕ}
    (ticks : ℕ → ℕ×ℕ → ℕ) (qu : ∀ q∈pool, q≤2^1024) (exc : bad.card≤2^949)
    (den : 2^1023*pool.card<44331*pop)
    (support : ∀ x∈pairs, x.1∈pool ∧ x.2∈pool ∧ Event bad ticks x.1 x.2) :
    2^57*pairs.card<pop :=
  price_bound (base_count ticks qu exc support) den (by decide +kernel) (by decide +kernel)

/-- Each pair may use any member of the menu. No probability-independence
assumption is needed, including when the base is selected from the product. -/
theorem menu_count {pairs : Finset (ℕ×ℕ)} {pool menu : Finset ℕ} {E F : ℕ}
    (bad : ℕ → Finset ℕ) (ticks : ℕ → ℕ → ℕ×ℕ → ℕ) (qu : ∀ q∈pool, q≤2^1024)
    (exc : ∀ base∈menu, (bad base).card≤E) (size : menu.card≤F)
    (support : ∀ x∈pairs, x.1∈pool ∧ x.2∈pool ∧ ∃ base∈menu, Event (bad base) (ticks base) x.1 x.2) :
    pairs.card ≤ pool.card*(F*partnerBudget E) := by
  classical
  let row (b : ℕ) := pairs.filter (fun x => Event (bad b) (ticks b) x.1 x.2)
  have sub : pairs ⊆ menu.biUnion row := by
    intro x hx; obtain ⟨b,hb,h⟩ := (support x hx).2.2
    exact mem_biUnion.mpr ⟨b,hb,mem_filter.mpr ⟨hx,h⟩⟩
  have localCount (b : ℕ) (hb : b∈menu) : (row b).card≤pool.card*partnerBudget E := by
    apply base_count (ticks b) qu (exc b hb)
    intro x hx; obtain ⟨hp,hh⟩ := mem_filter.mp hx
    exact ⟨(support x hp).1,(support x hp).2.1,hh⟩
  calc
    _ ≤ _ := card_le_card sub
    _ ≤ _ := card_biUnion_le_card_mul menu row _ localCount
    _ ≤ _ := Nat.mul_le_mul_right _ size
    _ = _ := by ac_rfl

private def menuExceptions : ℕ := (22*(12*2^470*(2^470+1)))/1023

private theorem low_card {base : ℕ} (lo : 2≤base) (hi : base≤2^22) :
    (lowFor base (2^470)).card≤menuExceptions := by
  apply (Nat.le_div_iff_mul_le (by decide : 0<1023)).mpr
  rw [mul_comm _ 1023]
  exact lowFor_bits lo hi

/-- Retaining the exact integer exception-size estimate gives 66 bits for
one of the allowed fixed bases. -/
theorem fixed_small_base {pairs : Finset (ℕ×ℕ)} {pool : Finset ℕ} {base pop : ℕ}
    (lo : 2≤base) (hi : base≤2^22) (ticks : ℕ → ℕ×ℕ → ℕ)
    (qu : ∀ q∈pool, q≤2^1024) (den : 2^1023*pool.card<44331*pop)
    (support : ∀ x∈pairs, x.1∈pool ∧ x.2∈pool ∧ Event (lowFor base (2^470)) ticks x.1 x.2) :
    2^66*pairs.card<pop :=
  price_bound (base_count ticks qu (low_card lo hi) support) den (by decide +kernel) (by decide +kernel)

/-- The elementary order and interval counts jointly yield less than one
pair in 2^66 under the explicit population normalization. -/
theorem fraction {pairs : Finset (ℕ×ℕ)} {pool : Finset ℕ} {pop : ℕ}
    (ticks : ℕ → ℕ×ℕ → ℕ) (qu : ∀ q∈pool, q≤2^1024)
    (den : 2^1023*pool.card<44331*pop)
    (support : ∀ x∈pairs, x.1∈pool ∧ x.2∈pool ∧ (x.1∈lowOrderPrimes (2^470) ∨
      HighHit ticks x.1 x.2 ∨ x.2∈lowOrderPrimes (2^470) ∨ HighHit ticks x.2 x.1)) :
    2^66*pairs.card<pop :=
  fixed_small_base (base:=2) (by decide) (by decide +kernel) ticks qu den support

/-- The union over every integer base in [2,2^22] accounts for a base
chosen separately for each product, including retrospectively. -/
theorem adaptive_fraction {pairs : Finset (ℕ×ℕ)} {pool : Finset ℕ} {pop : ℕ}
    (ticks : ℕ → ℕ → ℕ×ℕ → ℕ) (qu : ∀ q∈pool, q≤2^1024)
    (den : 2^1023*pool.card<44331*pop)
    (support : ∀ x∈pairs, x.1∈pool ∧ x.2∈pool ∧ ∃ base, 2≤base ∧ base≤2^22 ∧
      Event (lowFor base (2^470)) (ticks base) x.1 x.2) : 2^44*pairs.card<pop := by
  let menu := Icc 2 (2^22)
  have size : menu.card≤2^22 := by rw [Nat.card_Icc]; decide +kernel
  have support' : ∀ x∈pairs, x.1∈pool ∧ x.2∈pool ∧ ∃ base∈menu,
      Event (lowFor base (2^470)) (ticks base) x.1 x.2 := by
    intro x hx; obtain ⟨p,q,b,lo,hi,h⟩ := support x hx
    exact ⟨p,q,b,mem_Icc.mpr ⟨lo,hi⟩,h⟩
  have count := menu_count (fun b => lowFor b (2^470)) ticks qu
    (fun _ h => low_card (mem_Icc.mp h).1 (mem_Icc.mp h).2) size support'
  exact price_bound count den (by decide +kernel) (by decide +kernel)

end PrimeFactors.TraceCollisionPopulation
