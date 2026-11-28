import PrimeFactors.PrimePowerWeightMonotone
import PrimeFactors.PrimePowerWheelDensity
import PrimeFactors.BudgetedSumGuesses

/-! A uniform component in every complete sum table at distinct odd
prime-power moduli with at least two digits per prime. -/
namespace PrimeFactors.PrimePowerUniformShare

open Finset CoprimeGuessTables PrimeSquareExpectedRank PrimeSquareSumWeights PrimeSquareUniformFloor
open scoped Classical

open private PrimeFactors.PrimeSquareExpectedRank.class_count from PrimeFactors.PrimeSquareExpectedRank

/-- Every attained sum over an odd prime power with at least two digits
has at least two ordered representations. -/
theorem two_le_weight {p e n : ℕ} [Fact p.Prime] (odd : p≠2) (depth : 2≤e)
    (s : Labels (p^e) n) : 2≤weight n s.val := by
  apply le_trans _ (PrimePowerWeightMonotone.weight_lift odd depth s)
  rw [weight_formula odd,if_pos (PrimePowerWeightMonotone.reduce_label depth s)]
  split_ifs
  · exact (Fact.out : p.Prime).two_le
  · exact le_rfl

/-- At three, a square unit product gives at least three ordered
representations of every attained sum at these depths. -/
theorem three_le_weight {e n : ℕ} (unit : ¬3∣n) (sq : IsSquare (n:ZMod 3)) (depth : 2≤e)
    (s : Labels (3^e) n) : 3≤weight n s.val := by
  let t : Allowed 3 n := ⟨PrimePowerWeightMonotone.reduce depth s.val,
    PrimePowerWeightMonotone.reduce_label depth s⟩
  have low := local_bound (p:=3) (by decide) unit t
  rw [PrimeFactors.PrimeSquareExpectedRank.class_count (p:=3) (by decide) unit sq] at low
  norm_num [numerator,classes,pairs] at low
  have lower : 3≤weight n t.val := by omega
  exact lower.trans (PrimePowerWeightMonotone.weight_lift (by decide) depth s)

noncomputable def period (S : Finset ℕ) (E : ℕ→ℕ) := ∏ i : S, i.val^(E i.val)

variable (S : Finset ℕ) [∀ i:S,Fact i.val.Prime] (E : ℕ→ℕ)

instance : NeZero (period S E) :=
  ⟨prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (Fact.out : i.val.Prime).ne_zero)⟩

private noncomputable def extra := ∏ i:S,i.val^(E i.val-2)

omit [∀ i:S,Fact i.val.Prime] in
private theorem period_scale (deep : ∀ i:S,2≤E i.val) :
    period S E=modulus (fun i:S => i.val)*extra S E := by
  rw [modulus,extra,←prod_mul_distrib]
  apply prod_congr rfl
  intro i _
  rw [←pow_add,show 2+(E i.val-2)=E i.val by have := deep i; omega]

private theorem totient_product (T : Finset ℕ) (d : ℕ→ℕ)
    (prime : ∀ p∈T,p.Prime) (pos : ∀ p∈T,0<d p) :
    (∏ p∈T,p^(d p)).totient=∏ p∈T,p^(d p-1)*(p-1) := by
  induction T using Finset.induction_on with
  | empty => simp
  | @insert p T miss ih =>
    have P := prime p (mem_insert_self ..)
    have cop : (p^(d p)).Coprime (∏ q∈T,q^(d q)) :=
      Nat.Coprime.prod_right (fun q hq => (((Nat.coprime_primes P (prime q (mem_insert_of_mem hq))).mpr
        (fun eq => miss (eq ▸ hq))).pow_left _).pow_right _)
    rw [prod_insert miss,prod_insert miss,Nat.totient_mul cop,Nat.totient_prime_pow P (pos _ (mem_insert_self ..)),
      ih (fun q hq => prime q (mem_insert_of_mem hq)) (fun q hq => pos q (mem_insert_of_mem hq))]

private theorem total_scale (n : ℕ) (unit : ∀ i:S,¬i.val∣n) (deep : ∀ i:S,2≤E i.val) :
    Nat.card (Pairs n (period S E))=(∏ i:S, pairs i.val)*extra S E := by
  have cop : n.Coprime (period S E) := Nat.Coprime.prod_right (fun i _ =>
    ((Fact.out : i.val.Prime).coprime_iff_not_dvd.mpr (unit i)).symm.pow_right _)
  have phi := totient_product S E (fun p hp => (Fact.out : (⟨p,hp⟩:S).val.Prime))
    (fun p hp => (by decide : 0<2).trans_le (deep ⟨p,hp⟩))
  rw [total ((ZMod.isUnit_iff_coprime ..).mpr cop),period,prod_coe_sort S (fun p => p ^ E p),phi,
    ←prod_coe_sort S (fun p => p^(E p-1)*(p-1)),extra,←prod_mul_distrib]
  apply prod_congr rfl
  intro i _
  have pow : i.val^(E i.val-1)=i.val*i.val^(E i.val-2) := by
    rw [←pow_succ']; congr 1; have := deep i; omega
  rw [pow,pairs]
  ring

/-- Every attained high-precision label has a two-digit CRT label whose
multiplicity is no larger. -/
theorem square_witness (n : ℕ) (odd : ∀ i:S,i.val≠2) (deep : ∀ i:S,2≤E i.val)
    (s : Labels (period S E) n) :
    ∃ t : Labels (modulus (fun i:S => i.val)) n, weight n t.val≤weight n s.val := by
  let m (i:S) := i.val^(E i.val)
  have cop : Pairwise (fun i j : S => (m i).Coprime (m j)) :=
    fun i j ne => (((Nat.coprime_primes (Fact.out : i.val.Prime) (Fact.out : j.val.Prime)).mpr
      (fun eq => ne (Subtype.ext eq))).pow_left _).pow_right _
  let e := ZMod.prodEquivPi m cop
  have w := weight_pi m cop n s.val
  have wh := (positive_iff s.val).mpr s.property
  rw [w,Nat.pos_iff_ne_zero,prod_ne_zero_iff] at wh
  let hi (i:S) : Labels (m i) n :=
    ⟨e s.val i,(positive_iff _).mp (Nat.pos_of_ne_zero (wh i (mem_univ _)))⟩
  let low (i:S) : Allowed i.val n :=
    ⟨PrimePowerWeightMonotone.reduce (deep i) (hi i).val,PrimePowerWeightMonotone.reduce_label (deep i) (hi i)⟩
  let a := allowedEquiv (fun i:S => i.val) Subtype.val_injective n
  refine ⟨a.symm low,?_⟩
  rw [w,weight_equiv (fun i:S => i.val) Subtype.val_injective n]
  change (∏ i,weight n ((a (a.symm low)) i).val)≤_
  rw [a.apply_symm_apply]
  exact prod_le_prod' (fun i _ => PrimePowerWeightMonotone.weight_lift (odd i) (deep i) (hi i))

private theorem scale_density {a q h k : ℕ} (pq : 0<q) (pk : 0<k)
    (bound : (a:ℚ)/q<4*((h:ℚ)/((q:ℚ)*k))) : a*k<4*h := by
  have step := (div_lt_div_iff₀ (by positivity : (0:ℚ)<q) (by positivity : (0:ℚ)<(q:ℚ)*k)).mp
    (show (a:ℚ)/q < (4*h)/((q:ℚ)*k) by simpa only [mul_div_assoc] using bound)
  have cast : a*(q*k)<(4*h)*q := by exact_mod_cast step
  apply Nat.lt_of_mul_lt_mul_left (a:=q)
  nlinarith only [cast]

private theorem label_scale (n : ℕ) (odd : ∀ i:S,i.val≠2) (unit : ∀ i:S,¬i.val∣n)
    (deep : ∀ i:S,2≤E i.val) :
    Fintype.card (Labels (modulus (fun i:S => i.val)) n)*extra S E <
      4*Fintype.card (Labels (period S E) n) := by
  have density := PrimePowerWheelDensity.less_than_four n S E (fun p hp =>
    ⟨(Fact.out : (⟨p,hp⟩:S).val.Prime),odd ⟨p,hp⟩,unit ⟨p,hp⟩,deep ⟨p,hp⟩⟩)
  have raw : PrimePowerDensityRatio.density n (modulus (fun i:S => i.val)) <
      4*PrimePowerDensityRatio.density n (period S E) := by
    simpa only [modulus,period,prod_coe_sort S (fun p => p^2),prod_coe_sort S (fun p => p^(E p))] using density
  have qpos : 0<modulus (fun i:S => i.val) := Nat.pos_of_ne_zero (NeZero.ne _)
  have kpos : 0<extra S E := prod_pos (fun i _ => pow_pos (Fact.out : i.val.Prime).pos _)
  unfold PrimePowerDensityRatio.density LocalSumMenu.count at raw
  rw [Nat.card_eq_fintype_card,Nat.card_eq_fintype_card] at raw
  have scale : (period S E:ℚ)=(modulus (fun i:S => i.val):ℚ)*(extra S E:ℚ) := by
    exact_mod_cast period_scale S E deep
  rw [scale] at raw
  exact scale_density qpos kpos raw

/-- At any prime-power depths ≥2, every attained label retains at least one
quarter of the product of the square-digit uniform components. No modulus
budget is required. -/
theorem label_bound (n : ℕ) (odd : ∀ i:S,i.val≠2) (unit : ∀ i:S,¬i.val∣n)
    (deep : ∀ i:S,2≤E i.val) (s : Labels (period S E) n) :
    (∏ i:S,(numerator i.val:ℝ)/pairs i.val)/4*Nat.card (Pairs n (period S E)) ≤
      (Fintype.card (Labels (period S E) n):ℝ)*weight n s.val := by
  obtain ⟨t,weights⟩ := square_witness S E n odd deep s
  have sizes := label_scale S E n odd unit deep
  have low := PrimeSquareUniformFloor.label_bound (fun i:S => i.val) Subtype.val_injective n odd unit t
  have both := (Nat.mul_le_mul_right (extra S E) low).trans (by
    simpa only [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using Nat.mul_le_mul sizes.le weights)
  have positive : (0:ℝ)<(∏ i:S,pairs i.val:ℕ) := by
    exact_mod_cast (prod_pos (fun i (_ : i∈(univ:Finset S)) => Nat.mul_pos (Fact.out : i.val.Prime).pos
      (Nat.sub_pos_of_lt (Fact.out : i.val.Prime).one_lt)) : 0<∏ i:S,pairs i.val)
  have numerical : ((∏ i:S,numerator i.val:ℕ):ℝ)*extra S E ≤
      4*((Fintype.card (Labels (period S E) n):ℝ)*weight n s.val) := by exact_mod_cast both
  rw [total_scale S E n unit deep,prod_div_distrib,←Nat.cast_prod,←Nat.cast_prod,Nat.cast_mul]
  have cancel {u t k : ℝ} (tp : 0<t) : u/t/4*(t*k)=u*k/4 := by field_simp; ring
  rw [cancel positive]
  linarith only [numerical]

end PrimeFactors.PrimePowerUniformShare
