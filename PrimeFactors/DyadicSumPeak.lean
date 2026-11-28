import PrimeFactors.PrimePowerPairWeight
import PrimeFactors.PrimePowerSumFilter
import PrimeFactors.DyadicFactorOrbitCount
import PrimeFactors.ConditionalStride
import PrimeFactors.JointSumGuessFloor

/-! Peak multiplicity of a sum in the uniform local ordered-pair model
at a fixed odd product modulo a power of two. -/
namespace PrimeFactors.DyadicSumPeak

open PrimeSquareSumWeights
open private PrimeFactors.JointSumGuessFloor.sum_labels from PrimeFactors.JointSumGuessFloor

noncomputable def roots (e : ℕ) (D : ZMod (2^e)) := Nat.card {x : ZMod (2^e) // x^2=D}

/-- Centering a pair of sum 2h avoids dividing by two in the residue ring. -/
theorem midpoint (e N : ℕ) (h : ZMod (2^e)) :
    weight N (2*h)=roots e (h^2-N) := by
  let f (v : {z : Pairs N (2^e) // sumOf z=2*h}) :
      {x : ZMod (2^e) // x^2=h^2-N} := ⟨v.val.val.1-h,by
    have sum : v.val.val.1+v.val.val.2=2*h := v.property
    linear_combination v.val.val.1*sum-v.val.property⟩
  let g (x : {y : ZMod (2^e) // y^2=h^2-N}) :
      {z : Pairs N (2^e) // sumOf z=2*h} :=
    ⟨⟨(h+x.val,h-x.val),by change (h+x.val)*(h-x.val)=N; linear_combination -x.property⟩,by
      change h+x.val+(h-x.val)=2*h; ring⟩
  apply Nat.card_congr (Equiv.mk f g ?_ ?_)
  · intro v
    apply Subtype.ext ∘ Subtype.ext
    apply Prod.ext
    · change h+(v.val.val.1-h)=v.val.val.1; ring
    · change h-(v.val.val.1-h)=v.val.val.2
      have sum : v.val.val.1+v.val.val.2=2*h := v.property
      linear_combination -sum
  · intro x
    apply Subtype.ext
    change h+x.val-h=x.val
    ring

private theorem roots_unit (e : ℕ) (u : (ZMod (2^e))ˣ) :
    roots e u=FactorOrbitGuessRanks.fixed u := by
  classical
  let lift {x : ZMod (2^e)} (hx : x^2=u.val) : IsUnit x :=
    (isUnit_pow_iff (by decide : 2≠0)).mp (hx ▸ u.isUnit)
  let eq : {x : ZMod (2^e) // x^2=u.val} ≃ {x : (ZMod (2^e))ˣ // x^2=u} := {
    toFun := fun x => ⟨(lift x.property).unit,Units.ext (by
      rw [Units.val_pow_eq_pow_val,IsUnit.unit_spec]; exact x.property)⟩
    invFun := fun x => ⟨x.val.val,by simpa only [Units.val_pow_eq_pow_val] using congrArg Units.val x.property⟩
    left_inv := fun x => Subtype.ext (IsUnit.unit_spec (lift x.property))
    right_inv := fun x => Subtype.ext (Units.ext (IsUnit.unit_spec (lift
      (by simpa only [Units.val_pow_eq_pow_val] using congrArg Units.val x.property)))) }
  rw [roots,Nat.card_congr eq,Nat.card_eq_fintype_card,Fintype.card_subtype,FactorOrbitGuessRanks.fixed]
  apply congrArg Finset.card
  ext x
  simp only [Finset.mem_filter]

private theorem odd_roots_le {e : ℕ} {x : ZMod (2^e)} (odd : Odd x.val) :
    roots e (x^2)≤4 := by
  have ux : IsUnit x := ZMod.natCast_zmod_val x ▸
    (ZMod.isUnit_iff_coprime _ _).mpr (odd.coprime_two_right.pow_right _)
  have eq : x^2=(↑(ux.unit^2):ZMod _) := by rw [Units.val_pow_eq_pow_val,IsUnit.unit_spec]
  rw [eq,roots_unit]
  have cap := strideUnitRoots_two_pow_le_four e (ux.unit^2)
  refine le_trans (le_of_eq ?_) cap
  unfold FactorOrbitGuessRanks.fixed strideUnitRoots
  apply congrArg Finset.card
  ext y
  simp only [Finset.mem_filter]

theorem scale (t j d : ℕ) :
    roots (2*t+j) ((2^(2*t)*d:ℕ):ZMod (2^(2*t+j))) =
      roots j (d:ZMod (2^j))*2^t := by
  unfold roots
  rw [show (2:ℕ)^(2*t)=(2^t)^2 by rw [←pow_mul,Nat.mul_comm],Nat.cast_mul,Nat.cast_pow]
  exact PrimePowerPairWeight.roots_scaled _ _ _ _ rfl

private theorem small : (∀ x : ZMod (2^0),roots 0 x≤1) ∧
    (∀ x : ZMod (2^1),roots 1 x≤2) ∧ (∀ x : ZMod (2^2),roots 2 x≤2) ∧
    roots 2 1=2 ∧ roots 3 1=4 := by
  simp only [roots,Nat.card_eq_fintype_card,Fintype.card_subtype]
  decide +kernel

/-- Uniform upper bound over every squared residue, including zero. -/
theorem roots_le (e : ℕ) (D : ZMod (2^e)) : roots e D≤2^((e+1)/2) := by
  classical
  induction e using Nat.twoStepInduction with
  | zero => exact small.1 D
  | one => exact small.2.1 D
  | more e ih _ =>
    by_cases zero : e=0
    · subst e; exact small.2.2.1 D
    by_cases has : ∃ x : ZMod (2^(e+2)),x^2=D
    · obtain ⟨x,rfl⟩ := has
      rcases Nat.even_or_odd x.val with ⟨z,hz⟩|odd
      · have repr : x^2=((2^(2*1)*z^2:ℕ):ZMod (2^(e+2))) := by
          rw [←ZMod.natCast_zmod_val x,hz]; push_cast; ring
        rw [repr,show e+2=2*1+e by omega,scale]
        have pw : (2*1+e+1)/2=(e+1)/2+1 := by omega
        rw [pw,pow_succ,pow_one]
        exact Nat.mul_le_mul_right 2 (ih _)
      · have large : (2:ℕ)^2≤2^((e+2+1)/2) := Nat.pow_le_pow_right (by decide) (by omega)
        exact (odd_roots_le odd).trans large
    · have empty : IsEmpty {x : ZMod (2^(e+2)) // x^2=D} := ⟨fun x => has ⟨x.val,x.property⟩⟩
      change Nat.card _≤_
      rw [Nat.card_eq_zero.mpr (Or.inl empty)]
      exact Nat.zero_le _

private theorem exists_midpoint {e N : ℕ} (pos : 0<e) (odd : Odd N) {s : ZMod (2^e)}
    (occurs : 0<weight N s) : ∃ h, s=2*h := by
  obtain ⟨v⟩ := (Nat.card_pos_iff.mp occurs).1
  let a := v.val.val.1.val
  let b := v.val.val.2.val
  have prod : a*b ≡ N [MOD 2^e] := (ZMod.natCast_eq_natCast_iff ..).mp
    (by simpa only [a,b,Nat.cast_mul,ZMod.natCast_zmod_val] using v.val.property)
  have parity := prod.of_dvd (dvd_pow_self 2 pos.ne')
  change (a*b)%2=N%2 at parity
  have both := Nat.odd_mul.mp (Nat.odd_iff.mpr (parity.trans (Nat.odd_iff.mp odd)))
  obtain ⟨c,eq⟩ := both.1.add_odd both.2
  refine ⟨(c:ZMod (2^e)),?_⟩
  have val := congrArg (fun z : ℕ => (z:ZMod (2^e))) eq
  simpa only [a,b,Nat.cast_add,ZMod.natCast_zmod_val,←two_mul,Nat.cast_mul,Nat.cast_ofNat,
    ←v.property,sumOf] using val

theorem weight_le {e N : ℕ} (pos : 0<e) (odd : Odd N) (s : ZMod (2^e)) :
    weight N s≤2^((e+1)/2) := by
  by_cases hit : 0<weight N s
  · obtain ⟨h,rfl⟩ := exists_midpoint pos odd hit
    rw [midpoint]
    exact roots_le _ _
  · rw [Nat.eq_zero_of_not_pos hit]; exact Nat.zero_le _

private theorem realize {t j N : ℕ} (large : 2≤t) (levels : j=2 ∨ j=3) (good : N%8=1) :
    ∃ s : ZMod (2^(2*t+j)),weight N s=2^((2*t+j+1)/2) := by
  have div : 8∣(2:ℕ)^(2*t) := pow_dvd_pow 2 (by omega : 3≤2*t)
  have gate : (N+2^(2*t))%8=1 := by rw [Nat.add_mod,good,Nat.mod_eq_zero_of_dvd div]
  obtain ⟨h,hh⟩ := PrimePowerSumFilter.normalizing_unit gate (2*t+j)
  let x : ZMod (2^(2*t+j)) := h
  have center : x^2-N=((2^(2*t):ℕ):ZMod (2^(2*t+j))) := by
    rw [Nat.cast_add] at hh
    dsimp [x]; rw [sq,hh,add_sub_cancel_left]
  have law := scale t j 1
  simp only [Nat.mul_one,Nat.cast_one] at law
  refine ⟨2*x,?_⟩
  rw [midpoint,center,law]
  rcases levels with rfl|rfl
  · rw [small.2.2.2.1,show (2*t+2+1)/2=t+1 by omega,pow_succ,mul_comm]
  · rw [small.2.2.2.2,show (2*t+3+1)/2=t+2 by omega,pow_add,mul_comm]
    rfl

/-- The best single sum guess in the uniform local model has exactly
this many ordered pairs when the product is one modulo eight. -/
theorem square_product_peak {e N : ℕ} (large : 6≤e) (good : N%8=1) :
    IsGreatest (Set.range (weight (m:=2^e) N)) (2^((e+1)/2)) := by
  let t := (e-2)/2
  let j := e%2+2
  have size : e=2*t+j := by dsimp [t,j]; omega
  have attained := realize (N:=N) (show 2≤t by dsimp [t]; omega)
    (show j=2 ∨ j=3 by dsimp [j]; omega) good
  rw [←size] at attained
  refine ⟨attained,?_⟩
  rintro _ ⟨s,rfl⟩
  exact weight_le (by omega) (Nat.odd_iff.mpr (by omega)) s

private theorem four_scale (e d : ℕ) :
    roots (e+2) ((4*d:ℕ):ZMod (2^(e+2)))=roots e (d:ZMod (2^e))*2 := by
  rw [show e+2=2*1+e by omega]
  exact scale 1 e d

private theorem raise_menu {ι : Type*} {e L : ℕ} (d : ι → ℕ) (big : 4<L*2)
    (prev : ∀ D : ZMod (2^e), roots e D=L ↔ ∃ i,D=(d i:ℕ)) (D : ZMod (2^(e+2))) :
    roots (e+2) D=L*2 ↔ ∃ i, D=((4*d i:ℕ):ZMod (2^(e+2))) := by
  constructor
  · intro eq
    have positive : 0<roots (e+2) D := eq ▸ (by omega)
    obtain ⟨⟨x,rfl⟩⟩ := (Nat.card_pos_iff.mp positive).1
    rcases Nat.even_or_odd x.val with ⟨z,hz⟩|odd
    · have repr : x^2=((4*z^2:ℕ):ZMod _) := by rw [←ZMod.natCast_zmod_val x,hz]; push_cast; ring
      rw [repr,four_scale] at eq
      obtain ⟨i,h⟩ := (prev _).mp (Nat.eq_of_mul_eq_mul_right (by decide : 0<2) eq)
      refine ⟨i,?_⟩
      have congr := ((ZMod.natCast_eq_natCast_iff ..).mp h).mul_left' 4
      rw [repr,ZMod.natCast_eq_natCast_iff]
      simpa only [pow_add, Nat.reducePow,mul_comm (2^e) 4] using congr
    · exact False.elim (not_le_of_gt big (eq ▸ odd_roots_le odd))
  · rintro ⟨i,rfl⟩; rw [four_scale,(prev _).mpr ⟨i,rfl⟩]

private theorem step_unique {e d L : ℕ} (big : 4<L*2)
    (prev : ∀ D : ZMod (2^e), roots e D=L ↔ D=(d:ℕ)) (D : ZMod (2^(e+2))) :
    roots (e+2) D=L*2 ↔ D=((4*d:ℕ):ZMod (2^(e+2))) := by
  simpa using raise_menu (fun _ : Unit => d) big (fun D => by simpa using prev D) D

/-- At odd depth there is just one discriminant value of maximum
multiplicity. The initial case at depth three has four roots of one. -/
theorem odd_roots_iff (t : ℕ) (D : ZMod (2^(2*t+3))) :
    roots (2*t+3) D=2^(t+2) ↔ D=((2^(2*t):ℕ):ZMod _) := by
  induction t with
  | zero =>
    revert D
    simp only [roots,Nat.card_eq_fintype_card,Fintype.card_subtype]
    decide +kernel
  | succ t ih =>
    have big : 4<2^(t+2)*2 := by
      have l : (2:ℕ)^2≤2^(t+2) := Nat.pow_le_pow_right (by decide) (by omega)
      omega
    have high : 2^(2*(t+1))=4*(2:ℕ)^(2*t) := by
      rw [show 2*(t+1)=2+2*t by omega,pow_add]; rfl
    rw [show t+1+2=t+2+1 by omega,pow_succ,high]
    revert D
    rw [show 2*(t+1)+3=(2*t+3)+2 by omega]
    exact step_unique big ih

theorem odd_midpoint_iff (t N : ℕ) (h : ZMod (2^(2*t+3))) :
    weight N (2*h)=2^(t+2) ↔ h^2=(N:ZMod _)+((2^(2*t):ℕ):ZMod _) := by
  rw [midpoint,odd_roots_iff]
  exact ⟨fun eq => by linear_combination eq,fun eq => by linear_combination eq⟩

/-- The four square residues modulo sixteen, before scaling to higher precision. -/
def digit (i : Fin 4) : ℕ := ![0,1,4,9] i

theorem even_roots_iff (t : ℕ) (D : ZMod (2^(2*t+4))) :
    roots (2*t+4) D=2^(t+2) ↔ ∃ i, D=((2^(2*t)*digit i:ℕ):ZMod _) := by
  induction t with
  | zero =>
    revert D
    simp only [roots,Nat.card_eq_fintype_card,Fintype.card_subtype]
    decide +kernel
  | succ t ih =>
    have big : 4<2^(t+2)*2 := by
      have l : (2:ℕ)^2≤2^(t+2) := Nat.pow_le_pow_right (by decide) (by omega)
      omega
    have high : 2^(2*(t+1))=4*(2:ℕ)^(2*t) := by
      rw [show 2*(t+1)=2+2*t by omega,pow_add]; rfl
    rw [show t+1+2=t+2+1 by omega,pow_succ,high]
    revert D
    rw [show 2*(t+1)+4=(2*t+4)+2 by omega]
    simpa only [Nat.mul_assoc] using raise_menu (fun i => 2^(2*t)*digit i) big ih

open Finset
open scoped Classical

/-- Distinct doubled roots as sums, counting h and h plus half a period once. -/
noncomputable def doubles (e n : ℕ) : Finset (ZMod (2^e)) :=
  univ.filter (fun s => ∃ h : ZMod (2^e), s=2*h ∧ h^2=n)

theorem doubles_count {j n : ℕ} (large : 3≤j) (good : n%8=1) :
    (doubles (j+1) n).card=2 := by
  have odd : Odd n := Nat.odd_iff.mpr (by omega)
  have size := SingularDyadicClueSuffixes.card_menu large odd (N:=n)
  rw [if_pos good] at size
  refine Eq.trans (Eq.symm ?_) size
  let f (a : ℕ) := ((2*a:ℕ):ZMod (2^(j+1)))
  have bound {a : ℕ} (ha : a∈SingularDyadicClueSuffixes.menu j n) :
      2*a<2^(j+1) := by have := (SingularDyadicClueSuffixes.mem_menu.mp ha).1; rw [pow_succ]; omega
  apply card_bij (fun a _ => f a)
  · intro a ha
    have root := (ZMod.natCast_eq_natCast_iff ..).mpr (SingularDyadicClueSuffixes.mem_menu.mp ha).2
    exact mem_filter.mpr ⟨mem_univ _,(a:ZMod _),by simp [f],by simpa only [Nat.cast_pow] using root⟩
  · intro a ha b hb eq
    have vals := congrArg ZMod.val eq
    change ((2*a:ℕ):ZMod (2^(j+1))).val=((2*b:ℕ):ZMod (2^(j+1))).val at vals
    rw [ZMod.val_natCast_of_lt (bound ha),ZMod.val_natCast_of_lt (bound hb)] at vals
    omega
  · intro s hs
    obtain ⟨h,rfl,root⟩ := (mem_filter.mp hs).2
    have high : h.val^2 ≡ n [MOD 2^(j+1)] := (ZMod.natCast_eq_natCast_iff ..).mp
      (by simpa only [Nat.cast_pow,ZMod.natCast_zmod_val] using root)
    have parity := high.of_dvd (dvd_pow_self 2 (Nat.succ_ne_zero j))
    change h.val^2%2=n%2 at parity
    have ho : Odd h.val := (Nat.odd_mul.mp (show Odd (h.val*h.val) from
      Nat.odd_iff.mpr (by simpa only [←sq] using parity.trans (Nat.odd_iff.mp odd)))).1
    have self := (SingularDyadicClueSuffixes.true_suffix (k:=j) (p:=h.val) (q:=h.val) (by omega) ho).mpr
      (Nat.ModEq.refl _)
    have sqsame := (SingularDyadicClueSuffixes.mem_menu.mp self).2
    rw [←sq] at sqsame
    refine ⟨h.val%2^j,SingularDyadicClueSuffixes.mem_menu.mpr
      ⟨Nat.mod_lt _ (by positivity),sqsame.trans high⟩,?_⟩
    have dble := (Nat.mod_modEq h.val (2^j)).mul_left' 2
    have val : f (h.val%2^j)=((2*h.val:ℕ):ZMod (2^(j+1))) := (ZMod.natCast_eq_natCast_iff ..).mpr
      (by simpa only [pow_succ,Nat.mul_comm (2^j) 2] using dble)
    simpa only [Nat.cast_mul,Nat.cast_ofNat,ZMod.natCast_zmod_val] using val

noncomputable def winners (e N : ℕ) : Finset (ZMod (2^e)) :=
  univ.filter (fun s => weight N s=2^((e+1)/2))

/-- The two maximizing sums are precisely the doubled roots of a publicly
shifted product. The condition counts the two residues together. -/
theorem odd_winners {t N : ℕ} (large : 2≤t) (good : N%8=1) :
    winners (2*t+3) N=doubles (2*t+3) (N+2^(2*t)) ∧ (winners (2*t+3) N).card=2 := by
  have eq : winners (2*t+3) N=doubles (2*t+3) (N+2^(2*t)) := by
    ext s
    simp only [winners,doubles,mem_filter,mem_univ,true_and,show (2*t+3+1)/2=t+2 by omega,Nat.cast_add]
    constructor
    · intro hit
      obtain ⟨h,rfl⟩ := exists_midpoint (by omega : 0<2*t+3) (Nat.odd_iff.mpr (by omega) : Odd N)
        (s:=s) (hit ▸ (by positivity : 0<2^(t+2)))
      exact ⟨h,rfl,(odd_midpoint_iff t N h).mp hit⟩
    · rintro ⟨h,rfl,root⟩
      exact (odd_midpoint_iff t N h).mpr root
  refine ⟨eq,?_⟩
  rw [eq]
  have div : 8∣(2:ℕ)^(2*t) := pow_dvd_pow 2 (by omega : 3≤2*t)
  exact doubles_count (by omega) (by rw [Nat.add_mod,good,Nat.mod_eq_zero_of_dvd div])

private theorem square_of_double {k : ℕ} (kp : 1≤k) {x y : ZMod (2^(k+1))}
    (double : 2*x=2*y) : x^2=y^2 := by
  have eq : 2*x.val ≡ 2*y.val [MOD 2*2^k] := by
    rw [mul_comm 2 (2^k),←pow_succ]
    apply (ZMod.natCast_eq_natCast_iff ..).mp
    simpa only [Nat.cast_mul,Nat.cast_ofNat,ZMod.natCast_zmod_val] using double
  have low := eq.mul_left_cancel' (by decide : 2≠0)
  have diff := (Int.natCast_modEq_iff.mpr low).dvd
  push_cast at diff
  have parity : (2:ℤ)∣(y.val:ℤ)-x.val := (dvd_pow_self 2 (by omega : k≠0)).trans diff
  have sum : (2:ℤ)∣(y.val:ℤ)+x.val := by
    obtain ⟨z,hz⟩ := parity; exact ⟨z+x.val,by linarith⟩
  have modSq : (x.val:ℤ)^2 ≡ (y.val:ℤ)^2 [ZMOD (2:ℤ)^(k+1)] := by
    apply Int.modEq_iff_dvd.mpr
    rw [pow_succ,show (y.val:ℤ)^2-(x.val:ℤ)^2=(y.val-x.val)*(y.val+x.val) by ring]
    exact mul_dvd_mul diff sum
  have natural : x.val^2 ≡ y.val^2 [MOD 2^(k+1)] := Int.natCast_modEq_iff.mp (by exact_mod_cast modSq)
  simpa only [Nat.cast_pow,ZMod.natCast_zmod_val] using (ZMod.natCast_eq_natCast_iff ..).mpr natural

private theorem doubles_disjoint {k a b : ℕ} (kp : 1≤k) (distinct : ¬a ≡ b [MOD 2^(k+1)]) :
    Disjoint (doubles (k+1) a) (doubles (k+1) b) := by
  apply disjoint_left.mpr
  intro s ha hb
  obtain ⟨x,hx,px⟩ := (mem_filter.mp ha).2
  obtain ⟨y,hy,py⟩ := (mem_filter.mp hb).2
  exact distinct ((ZMod.natCast_eq_natCast_iff ..).mp (px.symm.trans ((square_of_double kp
    (hx.symm.trans hy)).trans py)))

/-- At even depths at least eight, four disjoint discriminant classes
each yield two maximizing sums. -/
theorem even_winners {t N : ℕ} (large : 2≤t) (good : N%8=1) :
    winners (2*t+4) N = univ.biUnion (fun i : Fin 4 => doubles (2*t+4) (N+2^(2*t)*digit i)) ∧
    (winners (2*t+4) N).card=8 := by
  let A := (2:ℕ)^(2*t)
  let lane (i : Fin 4) := doubles (2*t+4) (N+A*digit i)
  have eq : winners (2*t+4) N=univ.biUnion lane := by
    ext s
    simp only [winners,lane,doubles,mem_filter,mem_univ,true_and,mem_biUnion,Nat.cast_add,
      show (2*t+4+1)/2=t+2 by omega]
    constructor
    · intro hit
      obtain ⟨h,rfl⟩ := exists_midpoint (by omega : 0<2*t+4) (Nat.odd_iff.mpr (by omega) : Odd N)
        (s:=s) (hit ▸ (by positivity : 0<2^(t+2)))
      rw [midpoint,even_roots_iff] at hit
      obtain ⟨i,hi⟩ := hit
      exact ⟨i,h,rfl,by dsimp [A]; linear_combination hi⟩
    · rintro ⟨i,h,rfl,hi⟩
      rw [midpoint,even_roots_iff]
      exact ⟨i,by dsimp [A] at hi; linear_combination hi⟩
  refine ⟨eq,?_⟩
  rw [eq,card_biUnion]
  · have each (i : Fin 4) : (lane i).card=2 := by
      apply doubles_count (by omega)
      have div : 8∣A*digit i := dvd_mul_of_dvd_left (pow_dvd_pow 2 (by omega : 3≤2*t)) _
      rw [Nat.add_mod,good,Nat.mod_eq_zero_of_dvd div]
    simp [each]
  · intro i _ j _ ne
    apply doubles_disjoint (by omega)
    intro same
    have diff := Nat.ModEq.add_left_cancel' N same
    have bounds (v : Fin 4) : A*digit v < 2^(2*t+4) := by
      change 2^(2*t)*digit v<2^(2*t+4)
      rw [pow_add]
      exact Nat.mul_lt_mul_of_pos_left ((by decide +kernel : ∀ v : Fin 4,digit v<16) v) (by positivity)
    have vals := Nat.eq_of_mul_eq_mul_left (by positivity : 0<A) (diff.eq_of_lt_of_lt (bounds _) (bounds _))
    exact ne ((by decide +kernel : ∀ i j : Fin 4, digit i=digit j → i=j) _ _ vals)

private theorem odd_square_roots {e : ℕ} (large : 3≤e) {x : ZMod (2^e)}
    (odd : Odd x.val) : roots e (x^2)=4 := by
  by_cases eq3 : e=3
  · subst e
    have base : ∀ x : ZMod (2^3), x.val%2=1 → roots 3 (x^2)=4 := by
      simp only [roots,Nat.card_eq_fintype_card,Fintype.card_subtype]
      decide +kernel
    exact base x (Nat.odd_iff.mp odd)
  have ux : IsUnit x := ZMod.natCast_zmod_val x ▸
    (ZMod.isUnit_iff_coprime _ _).mpr (odd.coprime_two_right.pow_right _)
  have eq : x^2=(↑(ux.unit^2):ZMod _) := by rw [Units.val_pow_eq_pow_val,IsUnit.unit_spec]
  rw [eq,roots_unit,DyadicFactorOrbitCount.fixed_count (by omega),if_pos]
  rw [Units.val_pow_eq_pow_val,IsUnit.unit_spec,←ZMod.natCast_zmod_val x,←Nat.cast_pow,
    ZMod.val_natCast,Nat.mod_mod_of_dvd _ (show 8∣2^e from pow_dvd_pow 2 large)]
  have base : ∀ z : ZMod 8,z.val%2=1 → (z^2).val=1 := by decide +kernel
  have good := base (x.val:ZMod 8) (by rw [ZMod.val_natCast,Nat.mod_mod_of_dvd _ (by decide : 2∣8)]; exact Nat.odd_iff.mp odd)
  rwa [←Nat.cast_pow,ZMod.val_natCast] at good

private theorem shape {e N : ℕ} (large : 3≤e) {h x : ZMod (2^e)}
    (square : x^2=h^2-N) : (N%4=3 → Odd x.val) ∧ (N%8=5 → x.val%4=2) := by
  have high : h.val^2 ≡ N+x.val^2 [MOD 2^e] := (ZMod.natCast_eq_natCast_iff ..).mp (by
    simp only [Nat.cast_add,Nat.cast_pow,ZMod.natCast_zmod_val]
    linear_combination -square)
  have low := (ZMod.natCast_eq_natCast_iff ..).mpr (high.of_dvd (by exact pow_dvd_pow 2 large : 8∣2^e))
  simp only [Nat.cast_add,Nat.cast_pow] at low
  have table : ∀ u v n : ZMod 8, u^2=n+v^2 →
      (n.val%4=3 → v.val%2=1) ∧ (n.val=5 → v.val%4=2) := by decide +kernel
  have both := table _ _ _ low
  simpa only [ZMod.val_natCast,Nat.mod_mod_of_dvd _ (by decide : 4∣8),
    Nat.mod_mod_of_dvd _ (by decide : 2∣8),Nat.odd_iff] using both

/-- For product 3 modulo 4, every attainable sum has the same four
ordered presentations. -/
theorem three_weight {e N : ℕ} (large : 3≤e) (cl : N%4=3) (s : ZMod (2^e))
    (occurs : 0<weight N s) : weight N s=4 := by
  obtain ⟨h,rfl⟩ := exists_midpoint (by omega) (Nat.odd_iff.mpr (by omega) : Odd N) occurs
  rw [midpoint] at occurs ⊢
  obtain ⟨⟨x,square⟩⟩ := (Nat.card_pos_iff.mp occurs).1
  exact square ▸ odd_square_roots large ((shape large square).1 cl)

/-- For product 5 modulo 8, every attainable sum has eight ordered
presentations starting at depth five. -/
theorem five_weight {e N : ℕ} (large : 5≤e) (cl : N%8=5) (s : ZMod (2^e))
    (occurs : 0<weight N s) : weight N s=8 := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le' (show 2≤e by omega)
  obtain ⟨h,rfl⟩ := exists_midpoint (by omega) (Nat.odd_iff.mpr (by omega) : Odd N) occurs
  rw [midpoint] at occurs ⊢
  obtain ⟨⟨x,square⟩⟩ := (Nat.card_pos_iff.mp occurs).1
  have val := (shape (by omega : 3≤j+2) square).2 cl
  let z := x.val/2
  have zeq : x.val=2*z := by dsimp [z]; omega
  have zo : Odd z := Nat.odd_iff.mpr (by dsimp [z]; omega)
  have zo' : Odd ((z:ZMod (2^j)).val) := Nat.odd_iff.mpr (by
    rw [ZMod.val_natCast,Nat.mod_mod_of_dvd _ (dvd_pow_self 2 (by omega : j≠0))]
    exact Nat.odd_iff.mp zo)
  have repr : x^2=((4*z^2:ℕ):ZMod _) := by rw [←ZMod.natCast_zmod_val x,zeq]; push_cast; ring
  rw [←square,repr,four_scale,Nat.cast_pow,odd_square_roots (by omega) zo']

private theorem flat_peak {e d N : ℕ} (large : d+1≤e) (odd : Odd N)
    (flat : ∀ s : ZMod (2^e),0<weight N s → weight N s=2^d) :
    IsGreatest (Set.range (weight (m:=2^e) N)) (2^d) ∧
      Fintype.card (CoprimeGuessTables.Labels (2^e) N)=2^(e-1-d) := by
  let L := CoprimeGuessTables.Labels (2^e) N
  have law (s : L) := flat s.val ((CoprimeGuessTables.positive_iff _).mpr s.property)
  refine ⟨⟨⟨(Classical.arbitrary L).val,law _⟩,?_⟩,?_⟩
  · rintro _ ⟨s,rfl⟩
    by_cases hit : 0<weight N s
    · exact (flat s hit).le
    · rw [Nat.eq_zero_of_not_pos hit]; exact Nat.zero_le _
  · have total := PrimeFactors.JointSumGuessFloor.sum_labels (m:=2^e) (n:=N)
    rw [PrimeSquareSumWeights.total ((ZMod.isUnit_iff_coprime _ _).mpr (odd.coprime_two_right.pow_right _)),
      Nat.totient_prime_pow Nat.prime_two (by omega)] at total
    simp only [law,sum_const,card_univ,nsmul_eq_mul,Nat.reduceSub,mul_one] at total
    apply Nat.eq_of_mul_eq_mul_right (by positivity : 0<2^d)
    rw [←pow_add,show e-1-d+d=e-1 by omega]
    exact total

theorem three_peak {e N : ℕ} (large : 3≤e) (cl : N%4=3) :
    IsGreatest (Set.range (weight (m:=2^e) N)) 4 ∧
      Fintype.card (CoprimeGuessTables.Labels (2^e) N)=2^(e-3) := by
  simpa only [Nat.sub_sub] using flat_peak (d:=2) large
    (Nat.odd_iff.mpr (by omega) : Odd N) (three_weight large cl)

theorem five_peak {e N : ℕ} (large : 5≤e) (cl : N%8=5) :
    IsGreatest (Set.range (weight (m:=2^e) N)) 8 ∧
      Fintype.card (CoprimeGuessTables.Labels (2^e) N)=2^(e-4) := by
  simpa only [Nat.sub_sub] using flat_peak (d:=3) (by omega : 3+1≤e)
    (Nat.odd_iff.mpr (by omega) : Odd N) (five_weight large cl)

end PrimeFactors.DyadicSumPeak
