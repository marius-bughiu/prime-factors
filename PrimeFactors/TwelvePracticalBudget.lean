import PrimeFactors.TwelveResidueCollision
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

/-! Union bounds for unrestricted, independent public draws with replacement.
Exceptional samples, repeated global keys and one-coordinate hits all count
toward the upper envelope. No regular-seed conditioning is used. -/

namespace PrimeFactors.TwelvePracticalBudget
open Finset TwelveResidueCollision

set_option exponentiation.threshold 2050
set_option maxRecDepth 4096

section Words
variable {A : Type*} [Fintype A] [DecidableEq A]

private noncomputable def dangers (exceptional : Finset A) (partners : A → Finset A)
    {m : ℕ} (w : Fin m → A) : Finset A :=
  exceptional ∪ univ.biUnion (fun i => partners (w i))

/-- A word has a suspect position, or a suspect pair of positions. -/
def Opportunity (exceptional : Finset A) (partners : A → Finset A)
    {m : ℕ} (w : Fin m → A) : Prop :=
  (∃ i, w i ∈ exceptional) ∨ ∃ i j, i<j ∧ w i ∈ partners (w j)

/-- All words containing an exceptional seed or an eligible pair, before normalization. -/
noncomputable def opportunityWords (exceptional : Finset A) (partners : A → Finset A)
    (m : ℕ) : Finset (Fin m → A) := by
  classical exact univ.filter (Opportunity exceptional partners)

omit [Fintype A] in
private theorem extension {m : ℕ} (exceptional : Finset A) (partners : A → Finset A)
    (w : Fin (m+1) → A) (h : Opportunity exceptional partners w) :
    Opportunity exceptional partners (Fin.tail w) ∨ w 0 ∈ dangers exceptional partners (Fin.tail w) := by
  rcases h with ⟨i,h⟩ | ⟨i,j,lt,hit⟩
  · refine Fin.cases ?_ (fun i hi => Or.inl (Or.inl ⟨i,hi⟩)) i h
    intro zero
    exact .inr (mem_union_left _ zero)
  · revert lt hit
    refine Fin.cases ?_ (fun i => ?_) i
    · refine Fin.cases (by simp) (fun j _ hj => ?_) j
      exact .inr (mem_union_right _ (mem_biUnion.mpr ⟨j,mem_univ _,hj⟩))
    · refine Fin.cases (by simp) (fun j lt hj => ?_) j
      exact .inl (.inr ⟨i,j,Fin.succ_lt_succ_iff.mp lt,hj⟩)

private theorem step {m E L : ℕ} (exceptional : Finset A) (partners : A → Finset A)
    (ex : exceptional.card≤E) (fiber : ∀ x, (partners x).card≤L) :
    (opportunityWords exceptional partners (m+1)).card ≤
      Fintype.card A * (opportunityWords exceptional partners m).card + (Fintype.card A)^m*(E+m*L) := by
  classical
  let e := Fin.consEquiv (fun _ : Fin (m+1) => A)
  let previous : Finset (A × (Fin m → A)) := univ ×ˢ opportunityWords exceptional partners m
  let fresh := univ.biUnion (fun w : Fin m → A => dangers exceptional partners w ×ˢ {w})
  have cover : opportunityWords exceptional partners (m+1) ⊆ (previous ∪ fresh).map e.toEmbedding := by
    intro w hw
    obtain old | new := extension exceptional partners w (mem_filter.mp hw).2
    · exact mem_map.mpr ⟨e.symm w, mem_union_left _ (mem_product.mpr
        ⟨mem_univ _,mem_filter.mpr ⟨mem_univ _,old⟩⟩), e.apply_symm_apply _⟩
    · refine mem_map.mpr ⟨e.symm w,mem_union_right _ (mem_biUnion.mpr ?_),e.apply_symm_apply _⟩
      exact ⟨Fin.tail w,mem_univ _,mem_product.mpr ⟨new,mem_singleton_self _⟩⟩
  have hd (w : Fin m → A) : (dangers exceptional partners w).card ≤ E+m*L := by
    apply (card_union_le _ _).trans (Nat.add_le_add ex ?_)
    simpa using card_biUnion_le_card_mul (univ : Finset (Fin m)) _ L (fun i _ => fiber (w i))
  have hf : fresh.card ≤ (Fintype.card A)^m*(E+m*L) := by
    simpa [fresh] using card_biUnion_le_card_mul (univ : Finset (Fin m → A))
      (fun w => dangers exceptional partners w ×ˢ {w}) (E+m*L) (fun w _ => by simpa using hd w)
  have hp : previous.card = Fintype.card A * (opportunityWords exceptional partners m).card := by
    simp [previous]
  exact (card_le_card cover).trans (by rw [card_map]; exact (card_union_le _ _).trans (Nat.add_le_add hp.le hf))

/-- Clearing denominators in the finite union bound allows any population
size, and counts every pair once. -/
theorem word_bound {E L : ℕ} (exceptional : Finset A) (partners : A → Finset A)
    (ex : exceptional.card≤E) (fiber : ∀ x, (partners x).card≤L) (m : ℕ) :
    (opportunityWords exceptional partners m).card * Fintype.card A ≤
      (m*E + m.choose 2*L)*(Fintype.card A)^m := by
  classical
  induction m with
  | zero =>
    have h : opportunityWords exceptional partners 0=∅ := by
      ext w
      simp [opportunityWords,Opportunity]
    simp [h]
  | succ m ih =>
    have h := Nat.mul_le_mul_right (Fintype.card A) (step (m:=m) exceptional partners ex fiber)
    have old := Nat.mul_le_mul_left (Fintype.card A) ih
    rw [Nat.choose_succ_succ m 1,Nat.choose_one_right,pow_succ]
    nlinarith only [h,old]

end Words

private noncomputable def exceptional (p : ℕ) [Fact p.Prime] : Finset (ZMod p) :=
  univ.filter (fun x => mask x=0)

private noncomputable def partners {p : ℕ} [Fact p.Prime] (x : ZMod p) : Finset (ZMod p) :=
  if mask x=0 then ∅ else univ.filter (fun y => num x*den y=num y*den x)

private theorem partner_card {p : ℕ} [Fact p.Prime] (big : 108<p) (x : ZMod p) :
    (partners x).card≤12 := by
  unfold partners
  split_ifs with h
  · simp
  · exact (fiber_card big h).le

private noncomputable def exceptionalPair (p q : ℕ) [Fact p.Prime] [Fact q.Prime] :
    Finset (ZMod p × ZMod q) :=
  (exceptional p ×ˢ univ) ∪ (univ ×ˢ exceptional q)

private noncomputable def partnersPair {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (x : ZMod p × ZMod q) : Finset (ZMod p × ZMod q) :=
  (partners x.1 ×ˢ univ) ∪ (univ ×ˢ partners x.2)

private theorem exceptionalPair_bound (p q : ℕ) [Fact p.Prime] [Fact q.Prime] :
    (exceptionalPair p q).card≤13*(p+q) := by
  have hp := exceptions (p:=p)
  have hq := exceptions (p:=q)
  apply (card_union_le _ _).trans
  simp only [card_product,card_univ,ZMod.card,exceptional]
  nlinarith only [Nat.mul_le_mul_right q hp,Nat.mul_le_mul_left p hq]

private theorem partnersPair_bound {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hp : 108<p) (hq : 108<q) (x : ZMod p × ZMod q) :
    (partnersPair x).card≤12*(p+q) := by
  apply (card_union_le _ _).trans
  simp only [card_product,card_univ,ZMod.card]
  nlinarith only [Nat.mul_le_mul_right q (partner_card hp x.1),Nat.mul_le_mul_left p (partner_card hq x.2)]

/-- At least one exceptional seed, or any regular local match, including
two equal public keys. The word coordinates are unrestricted residues mod N. -/
def PublicOpportunity {p q m : ℕ} [Fact p.Prime] [Fact q.Prime] (cop : p.Coprime q)
    (w : Fin m → ZMod (p*q)) : Prop :=
  Opportunity (exceptionalPair p q) partnersPair (fun i => ZMod.chineseRemainder cop (w i))

private theorem zero_coordinate {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (cop : p.Coprime q) {z : ZMod (p*q)} (h : ¬IsUnit z) :
    (ZMod.chineseRemainder cop z).1=0 ∨ (ZMod.chineseRemainder cop z).2=0 := by
  by_contra! good
  let e := ZMod.chineseRemainder cop
  have hu : IsUnit (e z) := Prod.isUnit_iff.mpr
    ⟨isUnit_iff_ne_zero.mpr good.1,isUnit_iff_ne_zero.mpr good.2⟩
  exact h (by simpa [e] using hu.map e.symm.toRingHom)

private theorem local_equal {R K : Type*} [CommRing R] [Field K] (f : R →+* K)
    {x y a b : R} (ha : a*den x=num x) (hb : b*den y=num y) (same : f a=f b) :
    num (f y)*den (f x)=num (f x)*den (f y) := by
  have a : f a*den (f x)=num (f x) := by simpa [num,den,sextic,map_ofNat] using congrArg f ha
  have b : f b*den (f y)=num (f y) := by simpa [num,den,sextic,map_ofNat] using congrArg f hb
  rw [←a,←b,same]
  ring

private theorem match_or_exception {p : ℕ} [Fact p.Prime] {x y : ZMod p}
    (eq : num x*den y=num y*den x) : x∈exceptional p ∨ y∈partners x := by
  by_cases reg : mask x=0
  · exact .inl (mem_filter.mpr ⟨mem_univ _,reg⟩)
  · right
    simp [partners,reg,eq]

/-- All public setup exceptions and all nonunit differences between normalized
keys. This includes duplicate inputs and global key ties, even if neither splits. -/
def SearchEvent {n m : ℕ} (w : Fin m → ZMod n) : Prop :=
  (∃ i, ¬IsUnit (mask (w i))) ∨ ∃ i j, i<j ∧ ∃ a b : ZMod n,
    a*den (w i)=num (w i) ∧ b*den (w j)=num (w j) ∧ ¬IsUnit (a-b)

/-- Every setup nonunit, and every nonunit difference between two normalized
public keys, lies in the counted event. Equal public keys give difference zero
and are included even if orientation testing goes on to reveal a divisor. -/
theorem covers_search {p q m : ℕ} [Fact p.Prime] [Fact q.Prime] (cop : p.Coprime q)
    (w : Fin m → ZMod (p*q)) (h : SearchEvent w) : PublicOpportunity cop w := by
  let e := ZMod.chineseRemainder cop
  let f := (RingHom.fst (ZMod p) (ZMod q)).comp e.toRingHom
  let g := (RingHom.snd (ZMod p) (ZMod q)).comp e.toRingHom
  have left (i : Fin m) (bad : f (w i)∈exceptional p) : PublicOpportunity cop w :=
    .inl ⟨i, mem_union_left _ (mem_product.mpr ⟨bad,mem_univ _⟩)⟩
  have right (i : Fin m) (bad : g (w i)∈exceptional q) : PublicOpportunity cop w :=
    .inl ⟨i, mem_union_right _ (mem_product.mpr ⟨mem_univ _,bad⟩)⟩
  rcases h with ⟨i,bad⟩ | ⟨i,j,lt,a,b,ha,hb,bad⟩
  · rcases zero_coordinate cop bad with hp | hq
    · apply left i (mem_filter.mpr ⟨mem_univ _,?_⟩)
      change f (mask (w i))=0 at hp
      simpa [mask,map_ofNat] using hp
    · apply right i (mem_filter.mpr ⟨mem_univ _,?_⟩)
      change g (mask (w i))=0 at hq
      simpa [mask,map_ofNat] using hq
  · rcases zero_coordinate cop bad with hp | hq
    · change f (a-b)=0 at hp
      rw [map_sub,sub_eq_zero] at hp
      rcases match_or_exception (local_equal f ha hb hp) with ex | hit
      · exact left j ex
      · exact .inr ⟨i,j,lt,mem_union_left _ (mem_product.mpr ⟨hit,mem_univ _⟩)⟩
    · change g (a-b)=0 at hq
      rw [map_sub,sub_eq_zero] at hq
      rcases match_or_exception (local_equal g ha hb hq) with ex | hit
      · exact right j ex
      · exact .inr ⟨i,j,lt,mem_union_right _ (mem_product.mpr ⟨mem_univ _,hit⟩)⟩

noncomputable def publicWords (n m : ℕ) [NeZero n] : Finset (Fin m → ZMod n) := by
  classical exact univ.filter SearchEvent

/-- Finite proportion, i.e. iid uniform sampling from the entire public ring
with replacement, before applying the regularity check. -/
noncomputable def chance (n m : ℕ) [NeZero n] : ℝ := ((publicWords n m).card : ℝ) / (n:ℝ)^m

theorem public_bound {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (cop : p.Coprime q)
    (hp : 108<p) (hq : 108<q) (m : ℕ) :
    (publicWords (p*q) m).card * (p*q) ≤ (13*m+12*m.choose 2)*(p+q)*(p*q)^m := by
  classical
  let e := Equiv.arrowCongr (Equiv.refl (Fin m)) (ZMod.chineseRemainder cop).toEquiv
  let cover : Finset (Fin m → ZMod (p*q)) := univ.filter (PublicOpportunity cop)
  have admits : publicWords (p*q) m ⊆ cover := by
    intro w hw
    exact mem_filter.mpr ⟨mem_univ _,covers_search cop w (mem_filter.mp hw).2⟩
  have card : cover.card = (opportunityWords (exceptionalPair p q) partnersPair m).card := by
    apply card_bijective e e.bijective
    intro w
    simp [cover,opportunityWords,PublicOpportunity,e,Equiv.arrowCongr,Function.comp_def]
  apply (Nat.mul_le_mul_right _ (card_le_card admits)).trans
  rw [card]
  have h := word_bound (exceptionalPair p q) partnersPair (exceptionalPair_bound p q)
    (partnersPair_bound hp hq) m
  simp only [Fintype.card_prod,ZMod.card] at h
  convert h using 1
  ring

/-- Each draw contributes at most thirteen exceptional residues per prime.
Each unordered pair contributes at most twelve partners per prime. -/
theorem chance_bound {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (cop : p.Coprime q)
    (hp : 108<p) (hq : 108<q) (m : ℕ) :
    chance (p*q) m ≤ ((13*m+12*m.choose 2:ℕ):ℝ) * (1/(p:ℝ)+1/(q:ℝ)) := by
  have h := public_bound cop hp hq m
  have cast : ((publicWords (p*q) m).card:ℝ) * ((p:ℝ)*q) ≤
      ((13*m+12*m.choose 2:ℕ):ℝ)*((p:ℝ)+q)*((p:ℝ)*q)^m := by exact_mod_cast h
  have ppos : 0<(p:ℝ) := by exact_mod_cast (show 0<p by omega)
  have qpos : 0<(q:ℝ) := by exact_mod_cast (show 0<q by omega)
  unfold chance
  rw [Nat.cast_mul,div_le_iff₀ (pow_pos (mul_pos ppos qpos) m)]
  apply (le_div_iff₀ (mul_pos ppos qpos)).mpr cast |>.trans_eq
  field_simp [ppos.ne',qpos.ne']
  ring_nf
  simp

/-- At most a trillion independent, unrestricted draws have a probability
below 2^-939 of even seeing an opportunity at 1024-bit factor sizes. -/
theorem trillion {p q m : ℕ} [Fact p.Prime] [Fact q.Prime] (cop : p.Coprime q)
    (pl : 2^1023≤p) (ql : 2^1023≤q) (budget : m≤10^12) :
    chance (p*q) m < 1/(2:ℝ)^939 := by
  have hp : 108<p := (by norm_num : 108<2^1023).trans_le pl
  have hq : 108<q := (by norm_num : 108<2^1023).trans_le ql
  have pbound : (2:ℝ)^1023≤p := by exact_mod_cast pl
  have qbound : (2:ℝ)^1023≤q := by exact_mod_cast ql
  have ip := one_div_le_one_div_of_le (by positivity : 0<(2:ℝ)^1023) pbound
  have iq := one_div_le_one_div_of_le (by positivity : 0<(2:ℝ)^1023) qbound
  have count : 13*m+12*m.choose 2 ≤ 13*10^12+12*(10^12).choose 2 := by
    exact Nat.add_le_add (Nat.mul_le_mul_left _ budget)
      (Nat.mul_le_mul_left _ (Nat.choose_le_choose _ budget))
  apply (chance_bound cop hp hq m).trans_lt
  have cast : ((13*m+12*m.choose 2:ℕ):ℝ) ≤ ((13*10^12+12*(10^12).choose 2:ℕ):ℝ) :=
    Nat.cast_le.mpr count
  apply (mul_le_mul cast (add_le_add ip iq) (by positivity) (Nat.cast_nonneg _)).trans_lt
  rw [Nat.choose_two_right]
  norm_num

end PrimeFactors.TwelvePracticalBudget
