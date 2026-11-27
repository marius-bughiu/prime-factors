import PrimeFactors.ComplementaryBirthday
import PrimeFactors.NearEndpointPrimes
import Mathlib.Data.Complex.ExponentialBounds

namespace PrimeFactors.ComplementarySameBudget
open UniformFiberBirthday ComplementaryBirthday TwelveResidueCollision TwelveImageSize
open Finset

set_option exponentiation.threshold 2050
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192

private theorem exp_step {x d s : ℝ} (hx : 0≤x) (hs : 0<s) (gap : s≤d-x) :
    Real.exp (-(x/s)) ≤ 1-x/d := by
  have pos : 0<d-x := hs.trans_le gap
  have dp : 0<d := by linarith
  have h : d/(d-x) ≤ Real.exp (x/s) := by
    calc d/(d-x) = x/(d-x)+1 := by field_simp
         _ ≤ x/s+1 := add_le_add_right (div_le_div_of_nonneg_left hx hs gap) _
         _ ≤ _ := Real.add_one_le_exp _
  rw [Real.exp_neg,inv_eq_one_div]
  have inv := one_div_le_one_div_of_le (div_pos dp pos) h
  apply inv.trans_eq
  field_simp

private theorem lower_fixed {D M n : ℕ} (bound : n≤M) (cap : M<D) :
    Real.exp (-(n:ℝ)*(n-1)/(2*((D:ℝ)-M))) ≤ distinctProbability D n := by
  have gap : 0<(D:ℝ)-M := sub_pos.mpr (by exact_mod_cast cap)
  have dp : 0<(D:ℝ) := by exact_mod_cast (show 0<D by omega)
  induction n with
  | zero => simp [distinctProbability]
  | succ n ih =>
    have hm : n≤M := by omega
    have hn : (n:ℝ)≤M := by exact_mod_cast hm
    have step := exp_step (show (0:ℝ)≤n by positivity) gap (show (D:ℝ)-M≤D-n by linarith)
    have mul := mul_le_mul (ih hm) step (Real.exp_pos _).le (by unfold distinctProbability; positivity)
    have tick : distinctProbability D (n+1)=distinctProbability D n*(1-(n:ℝ)/D) := by
      unfold distinctProbability
      rw [Nat.descFactorial_succ,Nat.cast_mul,Nat.cast_sub (show n≤D by omega),pow_succ]
      field_simp
      ring
    rw [←Real.exp_add] at mul
    rw [tick,Nat.cast_succ]
    convert mul using 1
    congr 1
    field_simp
    ring

/-- A sustained lower birthday bound, valid through the entire draw budget. -/
theorem distinct_probability_exp_lower {d m : ℕ} (hm : m<d) :
    Real.exp (-(m:ℝ)*(m-1)/(2*((d:ℝ)-m))) ≤ distinctProbability d m :=
  lower_fixed (le_refl m) hm

noncomputable def oldLabels (p : ℕ) [Fact p.Prime] := (cleaned p).image value

noncomputable def oldKey {p : ℕ} [Fact p.Prime] (x : ↥(cleaned p)) : ↥(oldLabels p) :=
  ⟨value x.val,mem_image_of_mem _ x.property⟩

private theorem old_fiber {p : ℕ} [Fact p.Prime] (big : 864<p) (z : ↥(oldLabels p)) :
    Nat.card {x : ↥(cleaned p) // oldKey x=z} = 12 := by
  obtain ⟨a,ha,eq⟩ := mem_image.mp z.property
  obtain ⟨ra,nonmiddle⟩ := mem_filter.mp ha
  let target := TwelveSeedBirthday.label big ⟨a,ra⟩
  let e : {x : ↥(cleaned p) // oldKey x=z} ≃
      {x : TwelveSeedBirthday.Seed p // TwelveSeedBirthday.label big x=target} :=
    { toFun := fun x => ⟨⟨x.1.val,(mem_filter.mp x.1.property).1⟩,
        Subtype.ext ((congrArg Subtype.val x.2).trans eq.symm)⟩
      invFun := fun y => by
        have h : value y.1.val=value a := congrArg Subtype.val y.2
        exact ⟨⟨y.1.val,mem_filter.mpr ⟨y.1.property,by simpa [h] using nonmiddle⟩⟩,
          Subtype.ext (h.trans eq)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact (Nat.card_congr e).trans (TwelveSeedBirthday.label_fiber big target)

private theorem old_size {p : ℕ} [Fact p.Prime] (big : 864<p) :
    p≤12*(oldLabels p).card+25 := by
  have h := seed_card (oldKey (p:=p)) (old_fiber big)
  simp only [Fintype.card_coe] at h
  have a := filter_card_add_filter_neg_card_eq_card (s:=regulars p) (fun x => value x=1-value x)
  change _ + (cleaned p).card = (regulars p).card at a
  have b := ComplementaryKeys.middle_bound big
  have c := regular_count p
  omega

/-- Any repeat in either old coordinate counts, including a shared key
whose separate orientation tests might still split the product. -/
def DistinctBoth {B C : Type*} {m : ℕ} (w : Fin m → B × C) : Prop :=
  Function.Injective (Prod.fst ∘ w) ∧ Function.Injective (Prod.snd ∘ w)

private theorem repeat_fraction {B C : Type*} [Fintype B] [Fintype C]
    (m : ℕ) (bp : 0<Fintype.card B) (cp : 0<Fintype.card C) :
    (Nat.card {w : Fin m → B × C // ¬DistinctBoth w}:ℝ) /
        ((Fintype.card B*Fintype.card C:ℕ):ℝ)^m =
      1-distinctProbability (Fintype.card B) m*distinctProbability (Fintype.card C) m := by
  classical
  let e : {w : Fin m → B × C // DistinctBoth w} ≃ (Fin m ↪ B) × (Fin m ↪ C) :=
    { toFun := fun w => (⟨Prod.fst ∘ w.1,w.2.1⟩,⟨Prod.snd ∘ w.1,w.2.2⟩)
      invFun := fun v => ⟨fun i => (v.1 i,v.2 i),v.1.injective,v.2.injective⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have count := Fintype.card_congr e
  simp only [Fintype.card_prod,Fintype.card_embedding_eq,Fintype.card_fin] at count
  have le := Fintype.card_subtype_le (p:=DistinctBoth (m:=m) (B:=B) (C:=C))
  rw [Nat.card_eq_fintype_card,Fintype.card_subtype_compl]
  unfold distinctProbability
  rw [Nat.cast_sub le,count,Fintype.card_fun,Fintype.card_prod,Fintype.card_fin]
  push_cast
  have bpos : 0<(Fintype.card B:ℝ) := by exact_mod_cast bp
  have cpos : 0<(Fintype.card C:ℝ) := by exact_mod_cast cp
  rw [mul_pow]
  field_simp

noncomputable def oldChance (p q : ℕ) [Fact p.Prime] [Fact q.Prime] : ℝ :=
  let f := Prod.map (oldKey (p:=p)) (oldKey (p:=q))
  (Nat.card {w : Fin budget → ↥(cleaned p) × ↥(cleaned q) // ¬DistinctBoth (f ∘ w)}:ℝ) /
    ((Fintype.card ↥(cleaned p)*Fintype.card ↥(cleaned q):ℕ):ℝ)^budget

private theorem no_repeat {p : ℕ} [Fact p.Prime] (high : 99*2^1024≤100*p) :
    Real.exp (-(51/50:ℝ)) ≤ distinctProbability (oldLabels p).card budget := by
  have big : 864<p := by norm_num at high; omega
  have h := old_size big
  have size : budget<(oldLabels p).card := by norm_num [budget] at high ⊢; omega
  have pos : 0<((oldLabels p).card:ℝ)-budget := sub_pos.mpr (by exact_mod_cast size)
  have density : 99*(2:ℝ)^1024≤100*(12*((oldLabels p).card:ℝ)+25) := by
    exact_mod_cast high.trans (Nat.mul_le_mul_left 100 h)
  apply (Real.exp_le_exp.mpr _).trans (distinct_probability_exp_lower size)
  apply (le_div_iff₀ (mul_pos (by norm_num : (0:ℝ)<2) pos)).mpr
  norm_num [budget] at density ⊢
  linarith only [density]

private theorem exp_constant : (1:ℝ)/8 < Real.exp (-(51/50:ℝ))*Real.exp (-(51/50:ℝ)) := by
  have exp1 : Real.exp 1 < (11:ℝ)/4 := Real.exp_one_lt_d9.trans (by norm_num)
  have rest : Real.exp ((1:ℝ)/25) ≤ 25/24 := by
    have h := Real.add_one_le_exp (-(1/25:ℝ))
    rw [Real.exp_neg,inv_eq_one_div] at h
    have b := (le_div_iff₀ (Real.exp_pos _)).mp h
    linarith
  have h : Real.exp (51/50+51/50) < 8 := by
    rw [show (51/50:ℝ)+51/50=1+1+1/25 by norm_num,Real.exp_add,Real.exp_add]
    have sq := mul_self_lt_mul_self (Real.exp_pos 1).le exp1
    exact (mul_le_mul sq.le rest (Real.exp_pos _).le (by norm_num)).trans_lt (by norm_num)
  rw [←Real.exp_add,←neg_add,Real.exp_neg,inv_eq_one_div]
  exact one_div_lt_one_div_of_lt (Real.exp_pos _) h

private theorem high_factor {p q : ℕ} (qh : q<2^1024) (n : 99*2^2048≤100*(p*q)) :
    99*2^1024≤100*p := by
  have hp := Nat.mul_le_mul_left (100*p) qh.le
  have h : (99*2^1024)*(2^1024) ≤ (100*p)*(2^1024) := by
    calc _ = 99*2^2048 := by norm_num
         _ ≤ _ := n
         _ ≤ _ := by simpa [Nat.mul_assoc] using hp
  exact Nat.le_of_mul_le_mul_right h (by positivity)

/-- The public high-product condition alone bounds the old chance, regardless
of which prime supports complementary labels. -/
theorem old_upper {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (ph : p<2^1024) (qh : q<2^1024)
    (n : 99*2^2048≤100*(p*q)) : oldChance p q < 7/8 := by
  have hp := high_factor qh n
  have hq := high_factor ph (p:=q) (by rwa [Nat.mul_comm q p])
  have lp := no_repeat hp
  have lq := no_repeat hq
  have pp : 864<p := by norm_num at hp; omega
  have qq : 864<q := by norm_num at hq; omega
  have pos {r : ℕ} [Fact r.Prime] (hh : 99*2^1024≤100*r) (big : 864<r) :
      0<Fintype.card ↥(oldLabels r) := by
    rw [Fintype.card_coe]
    have h:=old_size big
    norm_num at hh
    omega
  let f := Prod.map (oldKey (p:=p)) (oldKey (p:=q))
  have eq := event_probability f (product_fibers _ _ (old_fiber pp) (old_fiber qq))
    (by decide : 0<12*12) (m:=budget) (fun w => ¬DistinctBoth w)
  rw [Fintype.card_prod,Fintype.card_prod] at eq
  unfold oldChance
  rw [eq,repeat_fraction budget (pos hp pp) (pos hq qq),Fintype.card_coe,Fintype.card_coe]
  have gt := exp_constant.trans_le (mul_le_mul lp lq (Real.exp_pos _).le
    ((Real.exp_pos _).le.trans lp))
  linarith

private theorem swap_odds {A B C D : Type*} [Fintype A] [Fintype B]
    (f : A → C) (g : B → D) (m : ℕ) :
    TwelveSeedBirthday.odds (Prod.map f g) m = TwelveSeedBirthday.odds (Prod.map g f) m := by
  let e := Equiv.arrowCongr (Equiv.refl (Fin m)) (Equiv.prodComm A B)
  have event (w : Fin m → A×B) :
      ProperPair ((Prod.map f g) ∘ w) ↔ ProperPair ((Prod.map g f) ∘ (e w)) := by
    simp [ProperPair,e,Equiv.arrowCongr,Function.comp_def,or_comm]
  have count := Nat.card_congr (e.subtypeEquiv
    (p:=fun w => ProperPair ((Prod.map f g) ∘ w))
    (q:=fun w => ProperPair ((Prod.map g f) ∘ w)) event)
  unfold TwelveSeedBirthday.odds
  rw [count,Fintype.card_prod,Fintype.card_prod,Nat.mul_comm (Fintype.card A)]

/-- The same raw word of regular, nonmiddle CRT seeds is used for both
methods. New counts only pairs that give a proper gcd. Old counts every
word repeating in at least one local coordinate, including all global ties. -/
def Comparison (p q : ℕ) [Fact p.Prime] [Fact q.Prime] : Prop :=
  oldChance p q < 7/8 ∧
  (95:ℝ)/100 < TwelveSeedBirthday.odds (Prod.map (project (p:=p)) (project (p:=q))) budget

theorem same_budget {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (ph : p<2^1024) (qh : q<2^1024)
    (top : 99*2^2048≤100*(p*q)) (mixed : (p*q)%12=5 ∨ (p*q)%12=7) : Comparison p q := by
  have ha := high_factor qh top
  have hb := high_factor ph (p:=q) (by rwa [Nat.mul_comm q p])
  have pl : 2^1023≤p := by norm_num at ha ⊢; omega
  have ql : 2^1023≤q := by norm_num at hb ⊢; omega
  refine ⟨old_upper ph qh top,?_⟩
  rcases ComplementaryKeys.mixed ((by norm_num : 864<2^1023).trans_le pl)
    ((by norm_num : 864<2^1023).trans_le ql) mixed with ⟨yes,no⟩|⟨yes,no⟩
  · exact mixed_odds pl ph ql qh yes no
  · rw [swap_odds]
    exact mixed_odds ql qh pl ph yes no

abbrev Samples (p q : ℕ) [Fact p.Prime] [Fact q.Prime] := ↥(cleaned p) × ↥(cleaned q)

private theorem count_new {S : Type*} [Fintype S] (new safe : S → Prop) :
    Nat.card {s : S // new s} ≤ Nat.card {s : S // ¬safe s} + Nat.card {s : S // new s ∧ safe s} := by
  classical
  have incl : univ.filter new ⊆ (univ.filter fun w => ¬safe w) ∪ (univ.filter fun w => new w ∧ safe w) := by
    intro w hw
    by_cases h : safe w
    · exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hw).2,h⟩)
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _,h⟩)
  simpa only [Nat.card_eq_fintype_card,Fintype.card_subtype] using
    (card_le_card incl).trans (card_union_le _ _)

/-- A positive fraction of the very same words give a new proper gcd
while neither of their two original local label sequences has any repeat. -/
theorem newly_split {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (ph : p<2^1024) (qh : q<2^1024)
    (top : 99*2^2048≤100*(p*q)) (mixed : (p*q)%12=5 ∨ (p*q)%12=7) :
    let f := Prod.map (oldKey (p:=p)) (oldKey (p:=q))
    let g := Prod.map (project (p:=p)) (project (p:=q))
    (3:ℝ)/40 < (Nat.card {w : Fin budget → Samples p q // ProperPair (g ∘ w) ∧ DistinctBoth (f ∘ w)}:ℝ) /
      (Fintype.card (Samples p q):ℝ)^budget := by
  intro f g
  obtain ⟨old,new⟩ := same_budget ph qh top mixed
  let N := fun w : Fin budget → Samples p q => ProperPair (g ∘ w)
  let S := fun w : Fin budget → Samples p q => DistinctBoth (f ∘ w)
  let D := (Fintype.card (Samples p q):ℝ)^budget
  have count := count_new N S
  have bound : (Nat.card {w // N w}:ℝ)/D ≤
      (Nat.card {w // ¬S w}:ℝ)/D + (Nat.card {w // N w ∧ S w}:ℝ)/D := by
    rw [←add_div]
    exact div_le_div_of_nonneg_right (by exact_mod_cast count) (by dsimp [D]; positivity)
  change (95:ℝ)/100 < (Nat.card {w // N w}:ℝ)/D at new
  have upper : (Nat.card {w // ¬S w}:ℝ)/D < 7/8 := by
    simpa only [D,S,Samples,Fintype.card_prod] using old
  change (3:ℝ)/40 < (Nat.card {w // N w ∧ S w}:ℝ)/D
  linarith

/-- Lift the same two accepted prime coordinates to one public input. -/
noncomputable def input {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (cop : p.Coprime q) (s : Samples p q) :
    TwelveSeedBirthday.Input (p*q) := (TwelveSeedBirthday.seedEquiv cop).symm
  (⟨s.1.val,(mem_filter.mp s.1.property).1⟩,⟨s.2.val,(mem_filter.mp s.2.property).1⟩)

private theorem coords {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (pp : 864<p) (qq : 864<q)
    (cop : p.Coprime q) (s : Samples p q) :
    ZMod.chineseRemainder cop (TwelveSeedBirthday.publicKey (input cop s)) =
      ((oldKey s.1).val,(oldKey s.2).val) := by
  simpa only [input,Equiv.apply_symm_apply] using
    TwelveSeedBirthday.coordinates pp qq cop (input cop s)

/-- The old event really covers nonunits of actual key differences over the
public product. This includes zero differences, before trying any tie breaker. -/
theorem covers_old {p q m : ℕ} [Fact p.Prime] [Fact q.Prime] (pp : 864<p) (qq : 864<q)
    (cop : p.Coprime q) (w : Fin m → Samples p q) {i j : Fin m} (ne : i≠j)
    (hit : ¬IsUnit (TwelveSeedBirthday.publicKey (input cop (w i))-
        TwelveSeedBirthday.publicKey (input cop (w j)))) :
    ¬DistinctBoth (Prod.map (oldKey (p:=p)) (oldKey (p:=q)) ∘ w) := by
  intro both
  let e := ZMod.chineseRemainder cop
  have u : IsUnit (e (TwelveSeedBirthday.publicKey (input cop (w i))-
        TwelveSeedBirthday.publicKey (input cop (w j)))) := by
    rw [map_sub,coords pp qq cop,coords pp qq cop]
    exact Prod.isUnit_iff.mpr
      ⟨isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr (fun eq => ne (both.1 (Subtype.ext eq)))),
       isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr (fun eq => ne (both.2 (Subtype.ext eq))))⟩
  exact hit (by simpa [e] using u.map e.symm.toRingHom)

/-- A new proper-pair word has an actual public folded difference whose
gcd with the input is strictly between one and the product. -/
theorem new_gcd_iff {p q m : ℕ} [Fact p.Prime] [Fact q.Prime] (pp : 864<p) (qq : 864<q)
    (cop : p.Coprime q) (w : Fin m → Samples p q) :
    ProperPair ((Prod.map (project (p:=p)) (project (p:=q))) ∘ w) ↔
    ∃ i j, i≠j ∧ TwelveSeedBirthday.ProperGcd
      (ComplementaryKeys.fold (TwelveSeedBirthday.publicKey (input cop (w i))))
      (ComplementaryKeys.fold (TwelveSeedBirthday.publicKey (input cop (w j)))) := by
  have red (s : Samples p q) : ZMod.chineseRemainder cop
      (ComplementaryKeys.fold (TwelveSeedBirthday.publicKey (input cop s))) =
      ((project s.1).val,(project s.2).val) := by
    simp only [ComplementaryKeys.fold,map_mul,map_sub,map_one,coords pp qq cop]
    rfl
  simp only [TwelveSeedBirthday.proper_gcd_iff cop,red,ProperPair,Function.comp_apply,ne_eq,Subtype.ext_iff]
  rfl

/-- Two independently kernel-certified endpoint primes instantiate the
comparison inside the main project's pinned toolchain. -/
theorem certified_pair :
    @Comparison (2^1024-NearEndpointPrimes.smallerOffset) (2^1024-NearEndpointPrimes.largerOffset)
      ⟨NearEndpointPrimes.smallerOffset_prime⟩ ⟨NearEndpointPrimes.largerOffset_prime⟩ := by
  letI : Fact (Nat.Prime (2^1024-NearEndpointPrimes.smallerOffset)) :=
    ⟨NearEndpointPrimes.smallerOffset_prime⟩
  letI : Fact (Nat.Prime (2^1024-NearEndpointPrimes.largerOffset)) :=
    ⟨NearEndpointPrimes.largerOffset_prime⟩
  exact same_budget (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end PrimeFactors.ComplementarySameBudget
