import PrimeFactors.PuncturedTrace
import PrimeFactors.NormOrbit
import Mathlib.Tactic.NormNum.LegendreSymbol

namespace PrimeFactors.MarkedSupportBox

open ExtensionTrace PuncturedTrace

/-- A marked summand equals its smooth counterpart at a unit marker, and vanishes elsewhere. -/
theorem marked_ite (n : ℕ) [NeZero n] (d x y : ℤ) :
    jacobiSym (markedNorm d x y) n =
      if ((x-2)^2-d*y^2).gcd n = 1 then jacobiSym (normCubic 0 (-1) 0 d x y) n else 0 := by
  unfold markedNorm
  rw [jacobiSym.mul_left]
  split_ifs with h
  · rw [jacobiSym.sq_one' h,one_mul]
  · rw [jacobiSym.pow_left,(jacobiSym.eq_zero_iff_not_coprime.mpr h),zero_pow (by decide),zero_mul]

/-- A point in the positive search rectangle hits the zero-norm locus modulo p. -/
def Hits (p U V : ℕ) (d : ZMod p) : Prop :=
  ∃ u v : ℕ, 1 ≤ u ∧ u ≤ U ∧ 1 ≤ v ∧ v ≤ V ∧ (u : ZMod p)^2=d*(v : ZMod p)^2

private theorem nonzero_cast {p k : ℕ} (pos : 0 < k) (small : k < p) :
    (k : ZMod p) ≠ 0 := fun h => Nat.not_dvd_of_pos_of_lt pos small
      ((ZMod.natCast_zmod_eq_zero_iff_dvd ..).mp h)

/-- Dirichlet's bounded slope gives the sharp rectangular upper threshold. -/
theorem rectangle_hit {p U V : ℕ} [hp : Fact p.Prime] (vp : 0 < V) (vs : V < p)
    (large : p < (U+1)*(V+1)) {s : ZMod p} (sn : s ≠ 0) : Hits p U V (s^2) := by
  obtain ⟨v,vp',vs',j,close⟩ := boundedSlope_exists p V (s.val : ℤ) hp.out.pos vp
  let t := (v : ℤ)*s.val-(p : ℤ)*j
  have precise : |t| *((V : ℤ)+1) ≤ p := close
  have limit : (p : ℤ) < ((U : ℤ)+1)*((V : ℤ)+1) := by exact_mod_cast large
  have small := lt_of_mul_lt_mul_right (precise.trans_lt limit) (by positivity : 0 ≤ (V : ℤ)+1)
  have cast : (t : ZMod p) = v*s := by dsimp [t]; push_cast; simp
  have tn : t ≠ 0 := by
    intro z
    have zero : (v : ZMod p)*s=0 := by rw [←cast,z,Int.cast_zero]
    exact mul_ne_zero (nonzero_cast vp' (vs'.trans_lt vs)) sn zero
  refine ⟨t.natAbs,v,Int.natAbs_pos.mpr tn,?_,vp',vs',?_⟩
  · rw [← Int.natCast_natAbs] at small
    omega
  · have h : ((t.natAbs : ℤ)^2) = t^2 := by simp only [Int.natCast_natAbs,sq_abs]
    have h' := congrArg (fun z : ℤ => (z : ZMod p)) h
    simp only [Int.cast_pow, Int.cast_natCast] at h'
    rw [h',cast]
    ring

/-- If the rectangle falls short, choosing the local square root U+1 avoids every leaf. -/
theorem rectangle_miss {p U V : ℕ} [Fact p.Prime] (us : U < p)
    (small : (U+1)*(V+1) ≤ p) : ¬ Hits p U V (((U+1 : ℕ) : ZMod p)^2) := by
  rintro ⟨u,v,up,ub,vp,vb,eq⟩
  let k := (U+1)*v
  have gap : u < k := by dsimp [k]; nlinarith [Nat.mul_le_mul_left (U+1) vp]
  have top : k+u < p := by
    calc
      k+u ≤ (U+1)*V+U := Nat.add_le_add (Nat.mul_le_mul_left (U+1) vb) ub
      _ < (U+1)*(V+1) := by rw [Nat.mul_add,Nat.mul_one]; omega
      _ ≤ p := small
  have cast : (u : ZMod p)^2=(k : ZMod p)^2 := by simpa [k,mul_pow] using eq
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp cast with pos | neg
  · have same := ((ZMod.natCast_eq_natCast_iff ..).mp pos).eq_of_lt_of_lt (ub.trans_lt us) (by omega)
    omega
  · have zero : ((u+k : ℕ) : ZMod p)=0 := by push_cast; rw [neg,neg_add_cancel]
    exact nonzero_cast (by omega : 0<u+k) (by omega : u+k<p) zero

/-- For a fixed prime and rectangle, all nonzero square selectors are hit exactly at this
threshold. The adversarial selector can depend on the prime and rectangle. -/
theorem rectangle_iff {p U V : ℕ} [Fact p.Prime] (us : U < p) (vp : 0 < V) (vs : V < p) :
    (∀ s : ZMod p, s ≠ 0 → Hits p U V (s^2)) ↔ p < (U+1)*(V+1) := by
  refine ⟨?_,fun h _ sn => rectangle_hit vp vs h sn⟩
  intro all
  by_contra! small
  have sep : U+1 < p := by
    have : (U+1)*2 ≤ (U+1)*(V+1) := Nat.mul_le_mul_left _ (by omega)
    omega
  exact rectangle_miss us small (all _ (nonzero_cast (by omega : 0 < U+1) sep))

/-- Raw leaf count is minimized by a single row, whereas balanced axes minimize their sum. -/
theorem rectangle_cost {p U V : ℕ} (up : 0 < U) (vp : 0 < V) (wide : p < (U+1)*(V+1)) :
    p ≤ 2*(U*V)+1 ∧ 4*(p+1) ≤ (U+V+2)^2 := by
  obtain ⟨u,rfl⟩ := Nat.exists_eq_succ_of_ne_zero up.ne'
  obtain ⟨v,rfl⟩ := Nat.exists_eq_succ_of_ne_zero vp.ne'
  constructor
  · nlinarith
  · have h : (4 : ℤ)*((p:ℤ)+1) ≤ 4*((u+2 : ℕ) : ℤ)*(v+2 : ℕ) := by
      have : p+1 ≤ (u+2)*(v+2) := wide
      exact_mod_cast (show 4*(p+1) ≤ 4*(u+2)*(v+2) by nlinarith only [this])
    zify
    push_cast at h ⊢
    nlinarith [sq_nonneg ((u:ℤ)-(v:ℤ))]

/-- CRT makes the missed local square an actual Jacobi-negative selector at the composite.
This is existence of an adversarial selector for the given rectangle and fixed pair of primes. -/
theorem separating_miss {p q U V : ℕ} [Fact p.Prime] [Fact q.Prime] [NeZero (p*q)]
    (cop : p.Coprime q) (qo : q ≠ 2) (vp : 0 < V) (small : (U+1)*(V+1) ≤ p) :
    ∃ d : ℤ, jacobiSym d (p*q) = -1 ∧ ¬ Hits p U V (d : ZMod p) := by
  have size : U+1 < p := by
    have : (U+1)*2 ≤ (U+1)*(V+1) := Nat.mul_le_mul_left _ (by omega)
    omega
  have sn := nonzero_cast (by omega : 0<U+1) size
  obtain ⟨t,neg⟩ := quadraticChar_exists_neg_one (F := ZMod q) (by rwa [ZMod.ringChar_zmod_n])
  let e := ZMod.chineseRemainder cop
  let z := e.symm ((((U+1 : ℕ) : ZMod p)^2),t)
  have crt : e (z.val : ZMod (p*q)) = ((((U+1 : ℕ) : ZMod p)^2),t) := by
    rw [ZMod.natCast_zmod_val]
    exact e.apply_symm_apply _
  rw [map_natCast] at crt
  have left := congrArg Prod.fst crt
  have right := congrArg Prod.snd crt
  change (z.val : ZMod p) = _ at left
  change (z.val : ZMod q) = t at right
  refine ⟨(z.val : ℤ),?_,?_⟩
  · rw [jacobi_crt,Int.cast_natCast,Int.cast_natCast,left,right,quadraticChar_sq_one' sn,neg,one_mul]
  · rw [Int.cast_natCast,left]
    exact rectangle_miss (by omega) small

private theorem factor_norm {R : Type*} [CommRing R] (d x y : R) :
    normCubic 0 (-1) 0 d x y =
      (x^2-d*y^2)*((x-1)^2-d*y^2)*((x+1)^2-d*y^2) := by
  unfold normCubic
  ring

private theorem root_repr {p : ℕ} [Fact p.Prime] {z : ZMod p} (zero : cubic 0 (-1) 0 z = 0) :
    ∃ j : ℤ, -1≤j ∧ j≤1 ∧ z=j := by
  rw [show cubic 0 (-1) 0 z = z*(z-1)*(z+1) by unfold cubic; ring] at zero
  rcases mul_eq_zero.mp zero with h | h
  · rcases mul_eq_zero.mp h with l | r
    · exact ⟨0, by decide, by decide, by simpa using l⟩
    · exact ⟨1, by decide, by decide, by simpa using sub_eq_zero.mp r⟩
  · exact ⟨-1, by decide, by decide, by simpa using eq_neg_of_add_eq_zero_left h⟩

/-- At least one of the two other split coordinates avoids all three roots of the cubic. -/
private theorem visible_sign {p : ℕ} [Fact p.Prime] (large : 6 < p) (u : ZMod p) :
    cubic 0 (-1) 0 (2+2*u) ≠ 0 ∨ cubic 0 (-1) 0 (2-2*u) ≠ 0 := by
  by_contra! both
  obtain ⟨i,il,iu,hi⟩ := root_repr both.1
  obtain ⟨j,jl,ju,hj⟩ := root_repr both.2
  have zero : ((4-i-j : ℤ) : ZMod p)=0 := by
    push_cast
    linear_combination hi+hj
  have div := Int.natCast_dvd.mp ((ZMod.intCast_zmod_eq_zero_iff_dvd ..).mp zero)
  have pos : 0<(4-i-j).natAbs := Int.natAbs_pos.mpr (by omega)
  have bound := Nat.le_of_dvd pos div
  omega

/-- The norm gcd at a hit already gives the split prime, even when the cubic character vanishes. -/
theorem hit_gcd {p q : ℕ} [Fact p.Prime] [hq : Fact q.Prime] (d u v : ℤ)
    (hit : (u : ZMod p)^2=(d : ZMod p)*(v : ZMod p)^2)
    (inert : ¬ IsSquare (d : ZMod q)) (vn : (v : ZMod q) ≠ 0) :
    (u^2-d*v^2).natAbs.gcd (p*q) = p := by
  have div : p ∣ (u^2-d*v^2).natAbs := by
    apply Int.natCast_dvd.mp
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd ..).mp
    push_cast
    exact sub_eq_zero.mpr hit
  have miss : ¬ q ∣ (u^2-d*v^2).natAbs := by
    intro divides
    have zero := (ZMod.intCast_zmod_eq_zero_iff_dvd ..).mpr (Int.natCast_dvd.mpr divides)
    push_cast at zero
    exact NormOrbit.inert_leaf _ _ _ vn inert zero
  rw [Nat.gcd_comm, Nat.mul_comm p q]
  exact Nat.gcd_mul_of_coprime_of_dvd (hq.out.coprime_iff_not_dvd.mpr miss) div

/-- At a norm hit one of the two publicly testable signs changes the actual marked character.
Both signs have the same marker gcd. -/
theorem marked_change {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (large : 6<p)
    (d u v : ℤ) (hit : (u : ZMod p)^2=(d : ZMod p)*(v : ZMod p)^2)
    (inert : ¬ IsSquare (d : ZMod q)) (vn : (v : ZMod q) ≠ 0) :
    ∃ w : ℤ, (w=u ∨ w= -u) ∧
      jacobiSym (markedNorm d (2+w) v) (p*q) = 0 ∧
      jacobiSym (normCubic 0 (-1) 0 d (2+w) v) (p*q) ≠ 0 := by
  obtain ⟨w,sign,good⟩ : ∃ w : ℤ, (w=u ∨ w= -u) ∧
      cubic 0 (-1) 0 (2+2*(w : ZMod p)) ≠ 0 := by
    rcases visible_sign large (u : ZMod p) with plus | minus
    · exact ⟨u,Or.inl rfl,plus⟩
    · exact ⟨-u,Or.inr rfl,by simpa [sub_eq_add_neg] using minus⟩
  have square : (d : ZMod p)*(v : ZMod p)^2 = (w : ZMod p)^2 := by
    rcases sign with rfl | rfl <;> simpa using hit.symm
  have six : (6 : ZMod p) ≠ 0 := nonzero_cast (by decide : 0<6) large
  have left : normCubic 0 (-1) 0 (d : ZMod p) (2+w) v ≠ 0 := by
    rw [factor_norm,square]
    convert mul_ne_zero six good using 1
    unfold cubic
    ring
  have right : normCubic 0 (-1) 0 (d : ZMod q) (2+w) v ≠ 0 := by
    rw [factor_norm]
    exact mul_ne_zero (mul_ne_zero (NormOrbit.inert_leaf _ _ _ vn inert)
      (NormOrbit.inert_leaf _ _ _ vn inert)) (NormOrbit.inert_leaf _ _ _ vn inert)
  have cast (r : ℕ) :
      ((normCubic 0 (-1) 0 d (2+w) v : ℤ) : ZMod r) =
      normCubic 0 (-1) 0 (d : ZMod r) (2+w) v := by simp [normCubic]
  refine ⟨w,sign,?_,?_⟩
  · rw [jacobi_crt]
    have zero : ((markedNorm d (2+w) v : ℤ) : ZMod p)=0 := by
      unfold markedNorm
      push_cast
      rw [square]
      ring
    simp [zero]
  · rw [jacobi_crt,cast,cast]
    have char_ne {r : ℕ} [Fact r.Prime] {x : ZMod r} (nonzero : x ≠ 0) :
        quadraticChar (ZMod r) x ≠ 0 := by
      rcases quadraticChar_dichotomy nonzero with pos | neg <;> simp [*]
    exact mul_ne_zero (char_ne left) (char_ne right)

/-- A unit multiplier cannot hit the same square at two different positive indices
strictly below p/2. This is a search without replacement in the local square classes. -/
theorem unique_half_index {p i j : ℕ} [Fact p.Prime] {a : ZMod p} (an : a ≠ 0)
    (ip : 0 < i) (jp : 0 < j) (ib : 2*i < p) (jb : 2*j < p)
    (same : (a*(i : ZMod p))^2=(a*(j : ZMod p))^2) : i=j := by
  rw [mul_pow,mul_pow,mul_right_inj' (pow_ne_zero 2 an)] at same
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp same with pos | neg
  · exact ((ZMod.natCast_eq_natCast_iff ..).mp pos).eq_of_lt_of_lt (by omega) (by omega)
  · have zero : ((i+j : ℕ) : ZMod p)=0 := by push_cast; rw [neg,neg_add_cancel]
    exact (nonzero_cast (by omega : 0 < i+j) (by omega : i+j < p) zero).elim

/-- Every positive index below p/2 is the first hit for precisely two possible nonzero
multipliers modulo p, with the selector fixed in advance. -/
theorem first_hit_fiber {p i : ℕ} [Fact p.Prime] {s : ZMod p} (sn : s ≠ 0)
    (odd : p ≠ 2) (ip : 0 < i) (ib : 2*i < p) :
    (Finset.univ.filter (fun a : ZMod p => a ≠ 0 ∧ (a*(i : ZMod p))^2=s^2 ∧
      ∀ j ∈ Finset.Ico 1 i, (a*(j : ZMod p))^2≠s^2)).card = 2 := by
  have iz : (i : ZMod p) ≠ 0 := nonzero_cast ip (by omega)
  have oi : ringChar (ZMod p) ≠ 2 := by rwa [ZMod.ringChar_zmod_n]
  have units : s/(i : ZMod p) ≠ 0 := div_ne_zero sn iz
  have diff : s/(i : ZMod p) ≠ -(s/(i : ZMod p)) := fun e =>
    units ((Ring.eq_self_iff_eq_zero_of_char_ne_two oi).mp e.symm)
  have fiber : Finset.univ.filter (fun a : ZMod p => a ≠ 0 ∧ (a*(i : ZMod p))^2=s^2 ∧
      ∀ j ∈ Finset.Ico 1 i, (a*(j : ZMod p))^2≠s^2) = {s/i,-(s/i)} := by
    ext a
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert,Finset.mem_singleton]
    constructor
    · rintro ⟨_,hit,_⟩
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp hit with pos | neg
      · exact Or.inl ((eq_div_iff iz).mpr pos)
      · exact Or.inr (by rw [←neg_div]; exact (eq_div_iff iz).mpr neg)
    · intro signs
      have an : a ≠ 0 := by rcases signs with rfl | rfl; exact units; exact neg_ne_zero.mpr units
      have hit : (a*(i : ZMod p))^2=s^2 := by
        rcases signs with rfl | rfl
        · rw [div_mul_cancel₀ _ iz]
        · rw [neg_mul,div_mul_cancel₀ _ iz,neg_sq]
      refine ⟨an,hit,?_⟩
      intro j inside another
      obtain ⟨jp,small⟩ := Finset.mem_Ico.mp inside
      have := unique_half_index an ip jp ib (by omega) (hit.trans another.symm)
      omega
  rw [fiber, Finset.card_pair diff]

/-- Extending a multiplier to the other prime gives q−1 independent choices. -/
theorem crt_first_hit_fiber {p q i : ℕ} [Fact p.Prime] [Fact q.Prime] {s : ZMod p} (sn : s ≠ 0)
    (odd : p ≠ 2) (ip : 0 < i) (ib : 2*i < p) :
    (Finset.univ.filter (fun a : ZMod p × ZMod q => a.2 ≠ 0 ∧ a.1 ≠ 0 ∧
      (a.1*(i : ZMod p))^2=s^2 ∧ ∀ j ∈ Finset.Ico 1 i, (a.1*(j : ZMod p))^2≠s^2)).card =
      2*(q-1) := by
  let first := Finset.univ.filter (fun a : ZMod p => a ≠ 0 ∧ (a*(i : ZMod p))^2=s^2 ∧
      ∀ j ∈ Finset.Ico 1 i, (a*(j : ZMod p))^2≠s^2)
  let second := (Finset.univ : Finset (ZMod q)).erase 0
  have prod : Finset.univ.filter (fun a : ZMod p × ZMod q => a.2 ≠ 0 ∧ a.1 ≠ 0 ∧
      (a.1*(i : ZMod p))^2=s^2 ∧ ∀ j ∈ Finset.Ico 1 i, (a.1*(j : ZMod p))^2≠s^2)
      = first ×ˢ second := by
    ext a
    simp only [first,second,Finset.mem_product,Finset.mem_filter,Finset.mem_univ,true_and,
      Finset.mem_erase, and_true]
    tauto
  rw [prod,Finset.card_product,show first.card=2 from first_hit_fiber sn odd ip ib]
  simp [second,ZMod.card]

/-- At seven a smooth zero hides the negative sign, while the positive sign changes.
The same marker gcd at either position is seven. -/
theorem sign_example :
    jacobiSym (normCubic 0 (-1) 0 8 1 1) 77 = 0 ∧ jacobiSym (markedNorm 8 1 1) 77 = 0 ∧
    jacobiSym (normCubic 0 (-1) 0 8 3 1) 77 = -1 ∧ jacobiSym (markedNorm 8 3 1) 77 = 0 ∧
      Nat.gcd 7 77 = 7 := by norm_num [markedNorm, normCubic, Nat.gcd]

end PrimeFactors.MarkedSupportBox
