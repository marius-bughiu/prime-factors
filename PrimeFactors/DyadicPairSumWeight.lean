import PrimeFactors.DyadicSumPeak

/-! Multiplicity of the sum of one modular factor pair, in terms of the
number of low binary digits shared by its coordinates. -/
namespace PrimeFactors.DyadicPairSumWeight

open PrimeSquareSumWeights DyadicSumPeak
open private PrimeFactors.DyadicSumPeak.odd_square_roots from PrimeFactors.DyadicSumPeak

private theorem tiny : (∀ x : ZMod (2^1), x.val%2=1 → roots 1 (x^2)=1) ∧
    (∀ x : ZMod (2^2), x.val%2=1 → roots 2 (x^2)=2) := by
  simp only [roots,Nat.card_eq_fintype_card,Fintype.card_subtype]
  decide +kernel

/-- The squared half-gap loses two powers of two per removed digit.
There are one, two or four odd roots at the remaining depth. -/
private theorem gap_roots (e i u : ℕ) (odd : Odd u) :
    roots e (((2^i*u:ℕ):ZMod (2^e))^2)=
      if e≤2*(i+1) then 2^(e/2) else 2^(i+2) := by
  by_cases zero : e≤2*i
  · have vanish : (((2^i*u:ℕ):ZMod (2^e))^2)=0 := by
      rw [←Nat.cast_pow,ZMod.natCast_zmod_eq_zero_iff_dvd,mul_pow,←pow_mul]
      exact dvd_mul_of_dvd_left (pow_dvd_pow 2 (by omega : e ≤ i*2)) _
    rw [if_pos (by omega),vanish,roots,PrimePowerPairWeight.roots_zero]
  · let j := e-2*i
    have size : e=2*i+j := by dsimp [j]; omega
    have positive : 0<j := by omega
    have parity : (u:ZMod (2^j)).val%2=1 := by
      rw [ZMod.val_natCast,Nat.mod_mod_of_dvd _ (dvd_pow_self 2 positive.ne')]
      exact Nat.odd_iff.mp odd
    have pull := PrimePowerPairWeight.roots_scaled (p:=2) e i j (u^2) size
    rw [Nat.cast_mul,mul_pow]
    change roots e (((↑((2:ℕ)^i):ZMod _)^2)*(u:ZMod _)^2)=_
    have reduced : roots e ((↑((2:ℕ)^i):ZMod _)^2*(u:ZMod _)^2) =
        roots j ((u:ZMod (2^j))^2)*2^i := by simpa only [roots,Nat.cast_pow] using pull
    rw [reduced]
    rcases (show j=1 ∨ j=2 ∨ 3≤j by omega) with one|two|high
    · rw [one] at parity ⊢
      rw [if_pos (by omega)]
      rw [tiny.1 _ parity,one_mul,show e/2=i by omega]
    · rw [two] at parity ⊢
      rw [if_pos (by omega)]
      rw [tiny.2 _ parity,show e/2=i+1 by omega,pow_succ,mul_comm]
    · rw [if_neg (by omega),PrimeFactors.DyadicSumPeak.odd_square_roots high (Nat.odd_iff.mpr parity),
        pow_add,mul_comm]
      rfl

/-- Exact ordered-pair multiplicity at every depth. Here a-b is given
modulo 2^e as 2^t times an odd residue, with t positive. -/
theorem pair_weight {e N t u : ℕ} (pos : 0<t) (odd : Odd u) {a b : ZMod (2^e)}
    (product : a*b=N) (gap : a-b=((2^t*u:ℕ):ZMod (2^e))) :
    weight N (a+b)=if e≤2*t then 2^(e/2) else 2^(t+1) := by
  obtain ⟨i,rfl⟩ := Nat.exists_eq_add_of_le' pos
  let d : ZMod (2^e) := (2^i*u:ℕ)
  have diff : a=b+2*d := by
    dsimp [d]; push_cast
    push_cast at gap
    rw [pow_succ] at gap
    linear_combination gap
  have hsum : a+b=2*(b+d) := by rw [diff]; ring
  have discr : (b+d)^2-N=d^2 := by rw [←product,diff]; ring
  rw [hsum,DyadicSumPeak.midpoint,discr]
  exact gap_roots e i u odd

/-- Equal coordinates modulo the full modulus have no finite first
differing bit. Their half-gap is zero. -/
theorem diagonal {e N : ℕ} {a : ZMod (2^e)} (product : a*a=N) :
    weight N (a+a)=2^(e/2) := by
  rw [←two_mul,DyadicSumPeak.midpoint,←product,sq,sub_self,roots,PrimePowerPairWeight.roots_zero]

/-- For (9,1), the shared three low bits give weights 4, 8, 16, 16
at depths five through eight. -/
theorem control : ([5,6,7,8].map fun e : ℕ => weight (m:=2^e) 9 10)=[4,8,16,16] := by
  have row (e : ℕ) : weight (m:=2^e) 9 10=if e≤6 then 2^(e/2) else 16 := by
    have h := pair_weight (e:=e) (N:=9) (t:=3) (u:=1) (by decide) (by decide)
      (a:=9) (b:=1) (by simp) (by norm_num)
    simpa only [show (9:ZMod (2^e))+1=10 by norm_num, Nat.reduceMul,Nat.reduceAdd,Nat.reducePow] using h
  simp only [List.map_cons,List.map_nil,row]
  decide +kernel

private theorem gap_even {e N : ℕ} (ep : 0<e) (odd : Odd N) {a b : ZMod (2^e)}
    (product : a*b=N) : 2∣(a-b).val := by
  let f := ZMod.castHom (dvd_pow_self 2 ep.ne') (ZMod 2)
  have nlow : (N:ZMod 2)=1 := by
    simpa only [Nat.cast_one] using (ZMod.natCast_eq_natCast_iff N 1 2).mpr
      (show N ≡ 1 [MOD 2] from Nat.odd_iff.mp odd)
  have plow := congrArg f product
  rw [map_mul,map_natCast,nlow] at plow
  have table : ∀ x y : ZMod 2,x*y=1 → x-y=0 := by decide +kernel
  have zero : f (a-b)=0 := by rw [map_sub]; exact table _ _ plow
  apply (ZMod.natCast_zmod_eq_zero_iff_dvd ..).mp
  rwa [←map_natCast f,ZMod.natCast_zmod_val]

/-- A single witness with a factor gap outside the multiples of 2^T
already bounds the entire sum class, including all its other witnesses. -/
theorem weight_le_of_gap {e N T : ℕ} (enough : T≤e) (odd : Odd N) {a b : ZMod (2^e)}
    (product : a*b=(N:ZMod _)) (miss : ¬2^T∣(a-b).val) : weight N (a+b)≤2^T := by
  have tp : 0<T := by
    apply Nat.pos_of_ne_zero
    rintro rfl
    exact miss (one_dvd _)
  have nz : (a-b).val≠0 := fun eq => miss (eq ▸ dvd_zero _)
  obtain ⟨t,u,uo,gap⟩ := Nat.exists_eq_two_pow_mul_odd nz
  have lt : t<T := lt_of_not_ge (fun le => miss (gap ▸
    (pow_dvd_pow 2 le).trans (dvd_mul_right _ _)))
  have even := gap_even (tp.trans_le enough) odd product
  have pos : 0<t := by
    apply Nat.pos_of_ne_zero
    rintro rfl
    simp only [pow_zero,one_mul] at gap
    exact (Nat.not_even_iff_odd.mpr uo) (even_iff_two_dvd.mpr (gap ▸ even))
  have actual : a-b=((2^t*u:ℕ):ZMod _) := by rw [←gap,ZMod.natCast_zmod_val]
  rw [pair_weight pos uo product actual]
  split <;> apply Nat.pow_le_pow_right (by decide) <;> omega

end PrimeFactors.DyadicPairSumWeight
