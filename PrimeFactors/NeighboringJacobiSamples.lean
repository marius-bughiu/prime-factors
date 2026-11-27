import PrimeFactors.NeighboringJacobiMoments
import PrimeFactors.JacobiHistogramSamples

/-! # The joint distribution of three related Jacobi signs

We keep only the three signs at 2s−2, 2s+2 and s, with s uniform modulo pq.
Counts below use integer-scaled overlaps to avoid irrational or rounded probabilities.
-/

namespace PrimeFactors.NeighboringJacobiSamples
open Finset

theorem triangle (n : ℕ) (s : ℤ) :
    J n (2*s-2) * J n (2*s+2) = jacobiSym (4*s) n ^ 2 * J n s := by
  unfold J
  rw [←jacobiSym.mul_left, ←jacobiSym.pow_left, ←jacobiSym.mul_left]
  congr 1
  ring

theorem triangle_unit {n : ℕ} {s : ℤ} (unit : (4*s).gcd n=1) :
    J n (2*s-2) * J n (2*s+2)=J n s := by rw [triangle,jacobiSym.sq_one unit,one_mul]

theorem triangle_nonnegative (n : ℕ) (s : ℤ) :
    0 ≤ J n (2*s-2) * J n (2*s+2) * J n s := by
  rw [triangle, mul_assoc, ←sq]
  positivity

def coin (b : Bool) : ℤ := if b then 1 else -1

/-- This single event witnesses distance at least 1/2 from three independent fair signs. -/
theorem half_event (n : ℕ) [NeZero n] :
    (univ.filter (fun t : ZMod n => J n (2*(t.val:ℤ)-2)*J n (2*(t.val:ℤ)+2)*J n t.val < 0)).card = 0 ∧
    2*(univ.filter (fun s : Bool × Bool × Bool => coin s.1 * coin s.2.1 * coin s.2.2 < 0)).card =
      Fintype.card (Bool × Bool × Bool) := by
  constructor
  · simp [not_lt_of_ge (triangle_nonnegative ..)]
  · decide +kernel



private theorem bias_bounds (z : ℤ) (p q : ℕ) [Fact p.Prime] [Fact q.Prime] :
    0 ≤ bias z p q ∧ bias z p q ≤ 4 := by
  have value (l : ℕ) [Fact l.Prime] : 0 ≤ 1+quadraticChar (ZMod l) (z:ZMod l) ∧
      1+quadraticChar (ZMod l) (z:ZMod l) ≤ 2 := by
    by_cases h : (z:ZMod l) = 0
    · rw [h,MulChar.map_zero]; decide
    · rcases quadraticChar_dichotomy h with a|a <;> rw [a] <;> decide
  exact ⟨mul_nonneg (value p).1 (value q).1, mul_le_mul (value p).2 (value q).2 (value q).1 (by decide)⟩

theorem cell_caps {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (cop : p.Coprime q)
    (hp : 5 ≤ p) (hq : 5 ≤ q) {u v : ℤ} (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    4*cells (p*q) u v ≤ p*q ∧
    (13≤p → 13≤q → p*q ≤ 8*cells (p*q) u v) := by
  have hist := histogram cop (by omega) (by omega) hu hv
  obtain ⟨b0,b4⟩ := bias_bounds 2 p q
  obtain ⟨m0,m4⟩ := bias_bounds (-1) p q
  have x : (5:ℤ) ≤ p := by exact_mod_cast hp
  have y : (5:ℤ) ≤ q := by exact_mod_cast hq
  have err : -12 ≤ (u+v)*bias 2 p q + u*v*bias (-1) p q ∧
      (u+v)*bias 2 p q + u*v*bias (-1) p q ≤12 := by
    rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> constructor <;> linarith
  constructor
  · exact_mod_cast (show 4*(cells (p*q) u v : ℤ) ≤ (p:ℤ)*q by linarith [err.2])
  · intro hp13 hq13
    have xp : (13:ℤ) ≤ p := by exact_mod_cast hp13
    have yq : (13:ℤ) ≤ q := by exact_mod_cast hq13
    exact_mod_cast (show (p:ℤ)*q ≤ 8*(cells (p*q) u v:ℤ) by
      nlinarith only [hist, err.1, mul_nonneg (sub_nonneg.mpr xp) (sub_nonneg.mpr yq), xp, yq])

private theorem J_mod {n : ℕ} {x y : ℤ} (same : (x:ZMod n)=(y:ZMod n)) : J n x = J n y := by
  apply jacobiSym.mod_left'
  apply (ZMod.intCast_eq_intCast_iff' _ _ n).1
  simp only [Int.cast_sub, Int.cast_pow, Int.cast_ofNat,same]

noncomputable def tripleCell (n : ℕ) [NeZero n] (u v w : ℤ) :=
  (univ.filter (fun s : ZMod n => J n (2*(s.val:ℤ)-2)=u ∧ J n (2*(s.val:ℤ)+2)=v ∧ J n s.val=w)).card

/-- Every supported nonzero pair extends uniquely by taking its product. -/
theorem third {n : ℕ} [NeZero n] (odd : Nat.Coprime 2 n) {u v w : ℤ}
    (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    tripleCell n u v w = if w=u*v then cells n u v else 0 := by
  classical
  let e := (ZMod.unitOfCoprime 2 odd).mulLeft
  have cast (s : ZMod n) : ((↑(e s).val : ℤ) : ZMod n) = ↑(2*(s.val:ℤ):ℤ) := by
    simp only [Int.cast_natCast,ZMod.natCast_zmod_val,Int.cast_mul,Int.cast_ofNat]
    change (ZMod.unitOfCoprime 2 odd:ZMod n)*s = 2*s
    rw [ZMod.coe_unitOfCoprime]; rfl
  have sub (s : ZMod n) : J n ((↑(e s).val:ℤ)-2)=J n (2*(s.val:ℤ)-2) :=
    J_mod (by simp only [Int.cast_sub,Int.cast_ofNat,cast s])
  have add (s : ZMod n) : J n ((↑(e s).val:ℤ)+2)=J n (2*(s.val:ℤ)+2) :=
    J_mod (by simp only [Int.cast_add,Int.cast_ofNat,cast s])
  have eq (s : ZMod n) (hs : J n (2*(s.val:ℤ)-2)=u) (hs' : J n (2*(s.val:ℤ)+2)=v) :
        J n s.val = u*v := by
    have h := triangle n (s.val:ℤ)
    rw [hs,hs'] at h
    have uv : u*v ≠ 0 := mul_ne_zero (by omega) (by omega)
    rcases jacobiSym.trichotomy (4*(s.val:ℤ)) n with d|d|d <;> simp only [d,zero_pow (by decide : 2≠0),zero_mul,one_pow,one_mul,neg_one_sq] at h
    · exact (uv h).elim
    · exact h.symm
    · exact h.symm
  by_cases ww : w=u*v
  · rw [if_pos ww]
    unfold tripleCell cells
    apply Finset.card_equiv e
    intro s
    simp only [mem_filter,mem_univ,true_and,sub s,add s]
    exact ⟨fun h => ⟨h.1,h.2.1⟩, fun h => ⟨h.1,h.2,(eq s h.1 h.2).trans ww.symm⟩⟩
  · rw [if_neg ww]
    apply Finset.card_eq_zero.mpr
    apply Finset.filter_eq_empty_iff.mpr
    intro s _ hh
    exact ww (hh.2.2.symm.trans (eq s hh.1 hh.2.1))

/-- Eight times N times the shared mass of the three-query sign transcript and three fair bits. -/
noncomputable def overlap8 (n : ℕ) [NeZero n] : ℕ :=
  ∑ z : Bool × Bool × Bool, min (8*tripleCell n (coin z.1) (coin z.2.1) (coin z.2.2)) n

/-- In the full-size range the exact overlap is 1/2, so the total variation distance is also 1/2. -/
theorem exact_half {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (cop : p.Coprime q)
    (hp : 13 ≤ p) (hq : 13 ≤ q) : overlap8 (p*q) = 4*(p*q) := by
  have odd : Nat.Coprime 2 (p*q) := by
    apply Nat.Coprime.mul_right
    · exact (Nat.coprime_primes Nat.prime_two Fact.out).mpr (by omega)
    · exact (Nat.coprime_primes Nat.prime_two Fact.out).mpr (by omega)
  have coins (b : Bool) : coin b=1 ∨ coin b= -1 := by cases b <;> decide
  let good (z : Bool × Bool × Bool) := coin z.2.2=coin z.1*coin z.2.1
  have val (z : Bool × Bool × Bool) :
      min (8*tripleCell (p*q) (coin z.1) (coin z.2.1) (coin z.2.2)) (p*q) =
        if good z then p*q else 0 := by
    rw [third odd (coins _) (coins _)]
    change min (8*(if good z then _ else 0)) (p*q) = _
    by_cases g : good z
    · rw [if_pos g,if_pos g,min_eq_right ((cell_caps cop (by omega) (by omega) (coins _) (coins _)).2 hp hq)]
    · simp [g]
  unfold overlap8
  simp_rw [val]
  rw [Finset.sum_ite]
  simp only [Finset.sum_const, nsmul_eq_mul,Finset.sum_const_zero,add_zero]
  congr 1


/-- Four times N times the shared mass with two independent fair signs. -/
noncomputable def overlap4 (n : ℕ) [NeZero n] : ℕ :=
    min (4*cells n (-1) (-1)) n + min (4*cells n (-1) 1) n +
    min (4*cells n 1 (-1)) n + min (4*cells n 1 1) n

theorem pair_overlap {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (cop : p.Coprime q)
    (hp : 5≤p) (hq : 5≤q) : (overlap4 (p*q) : ℤ) = 4*((p:ℤ)-3)*((q:ℤ)-3) := by
  have hn : (-1:ℤ) = 1 ∨ (-1:ℤ) = -1 := Or.inr rfl
  have ho : (1:ℤ) = 1 ∨ (1:ℤ) = -1 := Or.inl rfl
  have caps {u v : ℤ} (a : u=1 ∨ u= -1) (b : v=1 ∨ v= -1) := (cell_caps cop hp hq a b).1
  simp only [overlap4, min_eq_left (caps hn hn), min_eq_left (caps hn ho),
    min_eq_left (caps ho hn),min_eq_left (caps ho ho), Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
  have hist {u v : ℤ} (a : u=1 ∨ u= -1) (b : v=1 ∨ v= -1) := histogram cop (by omega) (by omega) a b
  linear_combination hist hn hn + hist hn ho + hist ho hn + hist ho ho

/-- Shared mass with k independent copies of (U,V,UV), scaled by (4n)^k. The
reference law is supported only on these four-point patterns in each draw. -/
noncomputable def parityOverlap (n : ℕ) [NeZero n] (k : ℕ) : ℕ :=
  ∑ z : Fin k → Bool × Bool, min (∏ i, 4 * tripleCell n (coin (z i).1) (coin (z i).2)
      (coin (z i).1 * coin (z i).2)) (n^k)

theorem parity_overlap {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (cop : p.Coprime q)
    (hp : 5≤p) (hq : 5≤q) (k : ℕ) :
    parityOverlap (p*q) k = (4*(p-3)*(q-3))^k := by
  have odd : Nat.Coprime 2 (p*q) := ((Nat.coprime_primes Nat.prime_two Fact.out).mpr (by omega : 2≠p)).mul_right
    ((Nat.coprime_primes Nat.prime_two Fact.out).mpr (by omega : 2≠q))
  have coins (b : Bool) : coin b=1 ∨ coin b= -1 := by cases b <;> decide
  let count (z : Bool × Bool) := 4*cells (p*q) (coin z.1) (coin z.2)
  have cap (z : Bool × Bool) : count z ≤ p*q := (cell_caps cop hp hq (coins _) (coins _)).1
  have pattern (z : Bool × Bool) : 4 * tripleCell (p*q) (coin z.1) (coin z.2) (coin z.1 * coin z.2) = count z := by
    rw [third odd (coins _) (coins _),if_pos rfl]
  have row : (∑ z : Bool × Bool, count z) = 4*(p-3)*(q-3) := by
    have h3p : 3≤p := by omega
    have h3q : 3≤q := by omega
    have eq : overlap4 (p*q) = 4*(p-3)*(q-3) := by
      apply Nat.cast_inj (R:=ℤ) |>.mp
      simpa only [Nat.cast_mul,Nat.cast_ofNat,Nat.cast_sub h3p,Nat.cast_sub h3q] using pair_overlap cop hp hq
    change min (count (false,false)) (p*q)+min (count (false,true)) (p*q)+
      min (count (true,false)) (p*q)+min (count (true,true)) (p*q) = _ at eq
    simp only [min_eq_left (cap _)] at eq
    rw [←eq,Fintype.sum_prod_type,Fintype.sum_bool,Fintype.sum_bool,Fintype.sum_bool]
    omega
  unfold parityOverlap
  simp_rw [pattern]
  have bound (z : Fin k → Bool × Bool) : (∏ i, count (z i)) ≤ (p*q)^k := by
    simpa using (Finset.prod_le_prod' (s:=univ) (g:=fun (_:Fin k) => p*q) (fun i _ => cap (z i)))
  simp_rw [min_eq_left (bound _)]
  rw [←Fintype.prod_sum]
  simp [row]

set_option exponentiation.threshold 2048 in
/-- The distance from the factor-independent parity model stays below 2⁻⁹⁸⁰
for at most 2⁴⁰ uniform independent triple samples from 1024-bit primes. -/
theorem full_size {p q : ℕ} (left : 2^1023 ≤ p) (right : 2^1023 ≤ q)
    (k : ℕ) (budget : k≤2^40) :
    (2:ℝ)^980 * (1-((((p:ℝ)-3)*(q-3))/((p:ℝ)*q))^k) < 1 := by
  have a : (2:ℝ)^1023 ≤ p := by exact_mod_cast left
  have b : (2:ℝ)^1023 ≤ q := by exact_mod_cast right
  have p3 : (3:ℝ) ≤ p := by linarith only [a]
  have q3 : (3:ℝ) ≤ q := by linarith only [b]
  have np : (0:ℝ) < (p:ℝ)*q := mul_pos (by linarith) (by linarith)
  let x : ℝ := ((p-3:ℝ)*(q-3))/(p*q)
  have xn : 0 ≤ x := div_nonneg (mul_nonneg (sub_nonneg.mpr p3) (sub_nonneg.mpr q3)) np.le
  have xu : x≤1 := (div_le_one np).mpr (by linarith)
  have loss : (2:ℝ)^1020*(1-x)<1 := by
    dsimp [x]
    rw [one_sub_div np.ne',←mul_div_assoc,div_lt_one np]
    nlinarith only [mul_le_mul_of_nonneg_right a (show 0≤(q:ℝ) by positivity),
                    mul_le_mul_of_nonneg_left b (show 0≤(p:ℝ) by positivity),np]
  have u := JacobiHistogramSamples.missed xn xu k
  have kn : (k:ℝ)≤2^40 := by exact_mod_cast budget
  have y := mul_le_mul_of_nonneg_right kn (sub_nonneg.mpr xu)
  change (2:ℝ)^980*(1-x^k)<1
  nlinarith only [mul_le_mul_of_nonneg_left (u.trans y) (by positivity : (0:ℝ)≤2^980), loss]

/-- Fixed products used by the bounded enumeration. -/
theorem fixture_products :
    Nat.Prime 7 ∧ Nat.Prime 11 ∧ 7*11=77 ∧ Nat.Prime 13 ∧ Nat.Prime 17 ∧ 13*17=221 := by
  decide +kernel

end PrimeFactors.NeighboringJacobiSamples
