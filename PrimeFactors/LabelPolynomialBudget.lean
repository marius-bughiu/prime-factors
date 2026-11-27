import PrimeFactors.TwelveSeedBirthday
import PrimeFactors.TwelvePracticalBudget
import Mathlib.Algebra.MvPolynomial.SchwartzZippel

/-! Bounds for specified nonzero polynomial tests on the public centered labels.
The polynomial and its nonvanishing after reduction are hypotheses at each prime. -/
namespace PrimeFactors.LabelPolynomialBudget
open Finset TwelveResidueCollision TwelveImageSize TwelveSeedBirthday MvPolynomial
open scoped NNReal
set_option exponentiation.threshold 2050

abbrev Poly (p m : ℕ) := MvPolynomial (Fin m) (ZMod p)

def center {R : Type*} [Ring R] (u : R) : R := 2*u-1

private theorem center_injective {p : ℕ} [Fact p.Prime] (big : 864<p) :
    Function.Injective (center (R := ZMod p)) := by
  have nz : (2:ZMod p) ≠ 0 := by
    exact_mod_cast (show ((2:ℕ):ZMod p) ≠ 0 by
      rw [Ne,ZMod.natCast_zmod_eq_zero_iff_dvd]; exact Nat.not_dvd_of_pos_of_lt (by decide) (by omega))
  intro x y eq
  exact mul_left_cancel₀ nz (sub_left_inj.mp eq)

noncomputable def centered (p : ℕ) [Fact p.Prime] : Finset (ZMod p) := (keys (ZMod p)).image center

theorem alphabet {p : ℕ} [Fact p.Prime] (big : 864<p) : (centered p).card=(p-5)/12 := by
  rw [centered,card_image_of_injective _ (center_injective big),prime_image_size big]

noncomputable def zeros {p m : ℕ} [Fact p.Prime] (F : Poly p m) :=
  (Fintype.piFinset (fun _ : Fin m => centered p)).filter (fun w => eval w F=0)

/-- Each coordinate is uniform in the centered regular-label alphabet, with replacement. -/
theorem label_bound {p m : ℕ} [Fact p.Prime] {F : Poly p m} (nonzero : F≠0) :
    ((zeros F).card : ℚ≥0) / ((centered p).card : ℚ≥0)^m ≤ (F.totalDegree : ℚ≥0)/(centered p).card :=
  schwartz_zippel_totalDegree nonzero _

/-- A finite family is covered by its product and pays at most the sum of the degrees. -/
theorem product_tests {p m : ℕ} [Fact p.Prime] {ι : Type*} (I : Finset ι)
    (F : ι → Poly p m) (nz : ∀ i ∈ I, F i ≠ 0) :
    (∏ i ∈ I, F i) ≠ 0 ∧ (∏ i ∈ I, F i).totalDegree ≤ ∑ i ∈ I, (F i).totalDegree ∧
    ∀ w, eval w (∏ i ∈ I, F i) = 0 ↔ ∃ i ∈ I, eval w (F i)=0 := by
  classical
  exact ⟨Finset.prod_ne_zero_iff.mpr nz,totalDegree_finset_prod _ _,fun w => by simp only [map_prod,Finset.prod_eq_zero_iff]⟩

/-- A setup exception or a zero of the polynomial in the centered rational labels. -/
def LocalEvent {p m : ℕ} [Fact p.Prime] (F : Poly p m) (w : Fin m → ZMod p) : Prop :=
  (∃ i, mask (w i)=0) ∨ eval (fun i => center (value (w i))) F=0

noncomputable def localWords {p m : ℕ} [Fact p.Prime] (F : Poly p m) : Finset (Fin m → ZMod p) := by
  classical exact univ.filter (LocalEvent F)

private theorem grid_card {R : Type*} [DecidableEq R] {m : ℕ} (s : Finset R)
    (P : (Fin m → R) → Prop) [DecidablePred P] :
    ((Fintype.piFinset (fun _ : Fin m => s)).filter P).card =
      Nat.card {w : Fin m → ↥s // P (fun i => (w i).val)} := by
  let e : {w : Fin m → ↥s // P (fun i => (w i).val)} ≃ ↥((Fintype.piFinset (fun _ : Fin m => s)).filter P) := {
    toFun := fun w => ⟨_,mem_filter.mpr ⟨Fintype.mem_piFinset.mpr (fun i => (w.val i).property),w.property⟩⟩
    invFun := fun w => ⟨fun i => ⟨_,Fintype.mem_piFinset.mp (mem_filter.mp w.property).1 i⟩,(mem_filter.mp w.property).2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  simpa only [Nat.card_eq_fintype_card,Fintype.card_coe] using (Nat.card_congr e).symm

private theorem regular_grid {p m : ℕ} [Fact p.Prime] (big : 864<p) (F : Poly p m) :
    ((Fintype.piFinset (fun _ : Fin m => regulars p)).filter
      (fun w => eval (fun i => center (value (w i))) F=0)).card ≤ (zeros F).card*12^m := by
  classical
  let E (w : Fin m → Label p) := eval (fun i => center (w i).val) F=0
  rw [grid_card]
  change Nat.card {w : Fin m → Seed p // E (label big ∘ w)} ≤ _
  rw [UniformFiberBirthday.event_card _ (label_fiber big) E]
  apply Nat.mul_le_mul_right
  let lift (w : {w : Fin m → Label p // E w}) : ↥(zeros F) :=
    ⟨_,mem_filter.mpr ⟨Fintype.mem_piFinset.mpr (fun i => mem_image_of_mem center (w.val i).property),w.property⟩⟩
  have one : Function.Injective lift := by
    intro x y eq
    apply Subtype.ext; funext i; apply Subtype.ext; apply center_injective big
    exact congrFun (congrArg Subtype.val eq) i
  simpa only [Nat.card_eq_fintype_card,Fintype.card_coe] using Nat.card_le_card_of_injective lift one

/-- The local probability includes all discarded raw seeds. Equal label fibers have size 12. -/
theorem local_bound {p m : ℕ} [Fact p.Prime] (big : 864<p) {F : Poly p m} (nz : F≠0) :
    ((localWords F).card : ℚ≥0)/(p:ℚ≥0)^m ≤ 13*m/(p:ℚ≥0) + (F.totalDegree:ℚ≥0)/(centered p).card := by
  classical
  let ex := univ.filter (fun x : ZMod p => mask x=0)
  let exc := TwelvePracticalBudget.opportunityWords ex (fun _ => ∅) m
  let reg := (Fintype.piFinset (fun _ : Fin m => regulars p)).filter (fun w => eval (fun i => center (value (w i))) F=0)
  have sub : localWords F ⊆ exc ∪ reg := by
    intro w h
    have cond : LocalEvent F w := (mem_filter.mp h).2
    by_cases e : ∃ i, mask (w i)=0
    · apply mem_union_left; apply mem_filter.mpr; refine ⟨mem_univ _,Or.inl ?_⟩
      obtain ⟨i,hi⟩ := e; exact ⟨i,mem_filter.mpr ⟨mem_univ _,hi⟩⟩
    · apply mem_union_right; apply mem_filter.mpr
      exact ⟨Fintype.mem_piFinset.mpr (fun i => mem_filter.mpr ⟨mem_univ _,fun z => e ⟨i,z⟩⟩),
        cond.resolve_left e⟩
  have count := (card_le_card sub).trans (card_union_le exc reg)
  have bad := TwelvePracticalBudget.word_bound ex (fun _ => ∅) (exceptions (p:=p))
    (fun _ => (by simp : (∅ : Finset (ZMod p)).card ≤ 0)) m
  change exc.card * _ ≤ _ at bad
  simp only [ZMod.card,mul_zero,add_zero] at bad
  have pos : 0<(p:ℚ≥0) := by exact_mod_cast (Fact.out : p.Prime).pos
  have cap : 0 < (centered p).card := by rw [alphabet big]; omega
  have capQ : 0 < ((centered p).card:ℚ≥0) := by exact_mod_cast cap
  have excB : (exc.card:ℚ≥0)/(p:ℚ≥0)^m ≤ 13*m/p := by
    rw [div_le_div_iff₀ (by positivity) pos]
    exact_mod_cast (by simpa [Nat.mul_comm m 13] using bad : exc.card*p ≤ 13*m*p^m)
  have sizes : (centered p).card*12 ≤ p := by rw [alphabet big]; omega
  have sizesQ : ((centered p).card:ℚ≥0)^m * 12^m ≤ (p:ℚ≥0)^m := by
    rw [← mul_pow]; exact_mod_cast (Nat.pow_le_pow_left sizes m)
  have regB : (reg.card:ℚ≥0)/(p:ℚ≥0)^m ≤ (F.totalDegree:ℚ≥0)/(centered p).card := by
    apply le_trans _ (label_bound nz)
    calc
      _ ≤ ((zeros F).card * 12^m : ℚ≥0) / (((centered p).card:ℚ≥0)^m * 12^m) :=
        div_le_div₀ (by positivity) (by exact_mod_cast regular_grid big F) (by positivity) sizesQ
      _ = _ := by rw [mul_div_mul_right _ _ (by positivity)]
  apply le_trans (div_le_div_of_nonneg_right (Nat.cast_le.mpr count) (by positivity))
  simpa only [Nat.cast_add,add_div] using add_le_add excB regB

/-- Ordered raw draws are uniform residues of N. The two coordinate polynomials may differ. -/
noncomputable def rawWords {p q m : ℕ} [Fact p.Prime] [Fact q.Prime] (cop : p.Coprime q)
    (F : Poly p m) (H : Poly q m) : Finset (Fin m → ZMod (p*q)) := by
  classical exact univ.filter fun w => LocalEvent F (fun i => (ZMod.chineseRemainder cop (w i)).1) ∨
    LocalEvent H (fun i => (ZMod.chineseRemainder cop (w i)).2)

/-- A nonunit polynomial value computed from the public product-ring labels on a regular word
places that same raw word in the event counted below. Both reductions come from one polynomial. -/
theorem public_nonunit {p q m : ℕ} [Fact p.Prime] [Fact q.Prime] (cop : p.Coprime q)
    (hp : 864<p) (hq : 864<q) (F : Poly (p*q) m) (w : Fin m → Input (p*q))
    (hit : ¬IsUnit (eval (fun i => center (publicKey (w i))) F)) :
    (fun i => (w i).val) ∈ rawWords cop
      (map ((RingHom.fst _ _).comp (ZMod.chineseRemainder cop).toRingHom) F)
      (map ((RingHom.snd _ _).comp (ZMod.chineseRemainder cop).toRingHom) F) := by
  classical
  let z := eval (fun i => center (publicKey (w i))) F
  let e := ZMod.chineseRemainder cop
  have split : (e z).1=0 ∨ (e z).2=0 := by
    by_contra! both
    have unit := Prod.isUnit_iff.mpr ⟨isUnit_iff_ne_zero.mpr both.1,isUnit_iff_ne_zero.mpr both.2⟩
    exact hit (by simpa [z] using unit.map e.symm.toRingHom)
  have reduce {r : ℕ} [Fact r.Prime] (f : ZMod (p*q) →+* ZMod r)
      (readAt : ∀ i, f (publicKey (w i))=value (f (w i).val)) :
      f z = eval (fun i => center (value (f (w i).val))) (map f F) := by
    dsimp only [z]
    rw [eval₂_comp,eval_map]
    congr 1
    funext i
    simp [Function.comp_def,center,readAt,map_ofNat]
  apply mem_filter.mpr
  refine ⟨mem_univ _,?_⟩
  rcases split with h|h
  · left; right
    exact (reduce ((RingHom.fst _ _).comp e.toRingHom)
      (fun i => congrArg Prod.fst (coordinates hp hq cop (w i)))).symm.trans h
  · right; right
    exact (reduce ((RingHom.snd _ _).comp e.toRingHom)
      (fun i => congrArg Prod.snd (coordinates hp hq cop (w i)))).symm.trans h

noncomputable def chance {p q m : ℕ} [Fact p.Prime] [Fact q.Prime] (cop : p.Coprime q)
    (F : Poly p m) (H : Poly q m) : ℚ≥0 := ((rawWords cop F H).card:ℚ≥0)/((p*q:ℕ):ℚ≥0)^m

/-- The local bounds lift to the product. Setup exceptions at either prime are included. -/
theorem crt_bound {p q m : ℕ} [Fact p.Prime] [Fact q.Prime] (cop : p.Coprime q)
    (hp : 864<p) (hq : 864<q) {F : Poly p m} {H : Poly q m} (fp : F≠0) (fq : H≠0) :
    chance cop F H ≤ (13*m/(p:ℚ≥0) + (F.totalDegree:ℚ≥0)/(centered p).card) +
      (13*m/(q:ℚ≥0) + (H.totalDegree:ℚ≥0)/(centered q).card) := by
  classical
  let e := (Equiv.arrowCongr (Equiv.refl (Fin m)) (ZMod.chineseRemainder cop).toEquiv).trans
    (Equiv.arrowProdEquivProdArrow (Fin m) (fun _ => ZMod p) (fun _ => ZMod q))
  let s := localWords F ×ˢ (univ : Finset (Fin m → ZMod q))
  let t := (univ : Finset (Fin m → ZMod p)) ×ˢ localWords H
  have sub : (rawWords cop F H).card ≤ (s ∪ t).card := by
    apply card_le_card_of_injOn e _ e.injective.injOn
    intro w hw
    rcases (mem_filter.mp hw).2 with he|he
    · exact mem_union_left _ (mem_product.mpr ⟨mem_filter.mpr ⟨mem_univ _,he⟩,mem_univ _⟩)
    · exact mem_union_right _ (mem_product.mpr ⟨mem_univ _,mem_filter.mpr ⟨mem_univ _,he⟩⟩)
  have count := sub.trans (card_union_le s t)
  simp only [s,t,card_product,card_univ,Fintype.card_fun,Fintype.card_fin,ZMod.card] at count
  have posP : 0<(p:ℚ≥0) := by exact_mod_cast (Fact.out : p.Prime).pos
  have posQ : 0<(q:ℚ≥0) := by exact_mod_cast (Fact.out : q.Prime).pos
  apply le_trans _ (add_le_add (local_bound hp fp) (local_bound hq fq))
  unfold chance
  apply le_trans (div_le_div_of_nonneg_right (Nat.cast_le.mpr count) (by positivity))
  push_cast
  rw [mul_pow,add_div]
  field_simp
  rw [mul_comm ((p:ℚ≥0)^m) ((localWords H).card:ℚ≥0)]

/-- Keep the integer alphabet floor when a concrete polynomial degree is available. -/
theorem full_size {p q m M D : ℕ} [Fact p.Prime] [Fact q.Prime] (cop : p.Coprime q)
    (pl : 2^1023≤p) (ql : 2^1023≤q) (budget : m≤M)
    {F : Poly p m} {H : Poly q m} (fp : F≠0) (fq : H≠0)
    (dp : F.totalDegree≤D) (dq : H.totalDegree≤D) :
    chance cop F H ≤ 2*(13*M/(2:ℚ≥0)^1023 + (D:ℚ≥0)/(((2^1023-5)/12 : ℕ):ℚ≥0)) := by
  have big : 864<2^1023 := by norm_num
  have capP := big.trans_le pl
  have capQ := big.trans_le ql
  have coord {r d : ℕ} [Fact r.Prime] (full : 2^1023≤r) (deg : d≤D) :
      13*m/(r:ℚ≥0) + (d:ℚ≥0)/(centered r).card ≤
        13*M/(2:ℚ≥0)^1023 + (D:ℚ≥0)/(((2^1023-5)/12 : ℕ):ℚ≥0) := by
    rw [alphabet (big.trans_le full)]
    apply add_le_add
    · apply div_le_div₀ (by positivity) _ (by positivity) (by exact_mod_cast full)
      exact_mod_cast Nat.mul_le_mul_left 13 budget
    · apply div_le_div₀ (by positivity) (by exact_mod_cast deg) (by norm_num) _
      exact_mod_cast Nat.div_le_div_right (Nat.sub_le_sub_right full 5)
  rw [two_mul]
  exact (crt_bound cop capP capQ fp fq).trans (add_le_add (coord pl dp) (coord ql dq))

private theorem bounded_trillion {p q m C : ℕ} [Fact p.Prime] [Fact q.Prime] (cop : p.Coprime q)
    (pl : 2^1023≤p) (ql : 2^1023≤q) (budget : m≤10^12)
    {F : Poly p m} {H : Poly q m} (fp : F≠0) (fq : H≠0)
    (dp : F.totalDegree≤C*m^3) (dq : H.totalDegree≤C*m^3) :
    chance cop F H ≤ 2*(13*(10^12)/(2:ℚ≥0)^1023 + (C*(10^12)^3)/(((2^1023-5)/12 : ℕ):ℚ≥0)) := by
  have deg := Nat.mul_le_mul_left C (Nat.pow_le_pow_left budget 3)
  simpa only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] using
    full_size cop pl ql budget fp fq (dp.trans deg) (dq.trans deg)

/-- For arbitrary 1024-bit primes this class of polynomial tests, including mask exceptions,
has probability below 2^-897 at one trillion raw draws. Both nonzero hypotheses matter. -/
theorem trillion {p q m : ℕ} [Fact p.Prime] [Fact q.Prime] (cop : p.Coprime q)
    (pl : 2^1023≤p) (ql : 2^1023≤q) (budget : m≤10^12)
    {F : Poly p m} {H : Poly q m} (fp : F≠0) (fq : H≠0)
    (dp : F.totalDegree≤2*m^3) (dq : H.totalDegree≤2*m^3) :
    chance cop F H < 1/(2:ℚ≥0)^897 := by
  apply (bounded_trillion cop pl ql budget fp fq dp dq).trans_lt
  rw [←NNRat.coe_lt_coe]; norm_num

/-- A degree bound of m³ sharpens the same raw-word probability by one further bit. -/
theorem trillion_cubic {p q m : ℕ} [Fact p.Prime] [Fact q.Prime] (cop : p.Coprime q)
    (pl : 2^1023≤p) (ql : 2^1023≤q) (budget : m≤10^12)
    {F : Poly p m} {H : Poly q m} (fp : F≠0) (fq : H≠0)
    (dp : F.totalDegree≤m^3) (dq : H.totalDegree≤m^3) :
    chance cop F H < 1/(2:ℚ≥0)^898 := by
  apply (bounded_trillion (C:=1) cop pl ql budget fp fq (by simpa using dp) (by simpa using dq)).trans_lt
  rw [←NNRat.coe_lt_coe]; norm_num

/-- Retaining the exact image size gives a sharper budget for degree at most m³/12. -/
theorem trillion_twelfth {p q m : ℕ} [Fact p.Prime] [Fact q.Prime] (cop : p.Coprime q)
    (pl : 2^1023≤p) (ql : 2^1023≤q) (budget : m≤10^12)
    {F : Poly p m} {H : Poly q m} (fp : F≠0) (fq : H≠0)
    (dp : 12*F.totalDegree≤m^3) (dq : 12*H.totalDegree≤m^3) :
    chance cop F H < 1/(2:ℚ≥0)^902 := by
  have deg {d : ℕ} (h : 12*d≤m^3) : d≤(10^12)^3/12 := by
    apply (Nat.le_div_iff_mul_le (by decide)).mpr
    rw [Nat.mul_comm]; exact h.trans (Nat.pow_le_pow_left budget 3)
  apply (full_size cop pl ql budget fp fq (deg dp) (deg dq)).trans_lt
  rw [←NNRat.coe_lt_coe]; norm_num

end PrimeFactors.LabelPolynomialBudget
