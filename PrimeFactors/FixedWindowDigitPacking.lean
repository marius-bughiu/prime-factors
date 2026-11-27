import PrimeFactors.UniversalPackingBudget
import PrimeFactors.CyclotomicResiduePacking

/-! Exact collisions on a given finite factor-sum list, with its actual starting
position. The universal finite-modulus bound below charges one period to align a
guaranteed pair with the public interval. -/
namespace PrimeFactors.FixedWindowDigitPacking
open CyclotomicRadixLift UniversalPackingBudget FactorSumSpacing

/-- The proposed sum at the absolute index x in the forced totient progression. -/
def survives (N m : ℕ) (x : ℤ) : Prop :=
  AdmissibleSum (N : ZMod m) (((N:ℤ)+1-(stride N:ℤ)*x : ℤ) : ZMod m)

/-- One digit distinguishes the surviving indices within this particular interval. -/
def Unique (N m start C M : ℕ) : Prop := ∀ i<C, ∀ j<C,
  survives N m ((start+i:ℕ):ℤ) → survives N m ((start+j:ℕ):ℤ) →
  weight N*(start+i) ≡ weight N*(start+j) [MOD M] → i=j

private theorem period_mul (a b : ℕ) : a∣b*period b a := by
  rw [period,←Nat.mul_div_assoc _ (Nat.gcd_dvd_left ..),←Nat.gcd_comm b a]
  exact Nat.dvd_lcm_right b a

private theorem reduce_sum {D m : ℕ} (div : m∣D) {N : ℕ} {s : ℤ}
    (ok : AdmissibleSum (N : ZMod D) (s : ZMod D)) : AdmissibleSum (N : ZMod m) (s : ZMod m) := by
  let f := ZMod.castHom div (ZMod m)
  obtain ⟨x,y,hp,hs⟩ := ok
  exact ⟨f x,f y,by rw [←map_mul,hp,map_natCast],by rw [←map_add,hs,map_intCast]⟩

private theorem forced_index {N x y Q : ℕ} (odd : Odd N) (h : x*y≡N [MOD Q])
    (twelve : 12∣Q) (wq : stride N∣Q) : ∃ a : ℤ, (x:ℤ)+y=(N:ℤ)+1-stride N*a := by
  have two := h.of_dvd ((by decide : 2∣12).trans twelve)
  have d : ¬2∣x*y := fun dv => (Nat.not_even_iff_odd.mpr odd) (even_iff_two_dvd.mpr ((two.dvd_iff (dvd_refl 2)).mp dv))
  have ox : Odd x := Nat.not_even_iff_odd.mp (fun ev => d (dvd_mul_of_dvd_left (even_iff_two_dvd.mp ev) _))
  have oy : Odd y := Nat.not_even_iff_odd.mp (fun ev => d (dvd_mul_of_dvd_right (even_iff_two_dvd.mp ev) _))
  have f := divides ox oy
  have h4 : x*y%4=N%4 := h.of_dvd ((by decide : 4∣12).trans twelve)
  have h3 : x*y%3=N%3 := h.of_dvd ((by decide : 3∣12).trans twelve)
  have w : stride (x*y)=stride N := by unfold stride weight bonus; rw [h4,h3]
  rw [w] at f
  have xp : 0<x := Odd.pos ox
  have yp : 0<y := Odd.pos oy
  have ar : x*y+1=(x-1)*(y-1)+(x+y) := by
    zify [show 1≤x by omega,show 1≤y by omega]
    ring
  have e := (Nat.modEq_zero_iff_dvd.mpr f).add_right (x+y)
  rw [←ar,Nat.zero_add] at e
  have eq := e.symm.trans ((h.of_dvd wq).add_right 1)
  have eqZ : ((x+y:ℕ):ℤ)≡((N+1:ℕ):ℤ) [ZMOD (stride N:ℤ)] := Int.natCast_modEq_iff.mpr eq
  obtain ⟨a,ha⟩ := Int.modEq_iff_dvd.mp eqZ
  push_cast at ha
  exact ⟨a,by linarith only [ha]⟩

/-- A displacement guaranteed by the universal stride occurs on the forced index
progression itself. Both local factorizations lift from the larger modulus 12*m*W. -/
theorem aligned {N m : ℕ} (odd : Odd N) (mp : 0<m) (d : ℕ)
    (dv : 20160∣stride N*d) : ∃ a : ℤ, survives N m a ∧ survives N m (a+d) := by
  let Q := 12*m*stride N
  have wp : 0<stride N := by unfold stride; rcases weights N with h|h|h|h <;> rw [h] <;> decide
  have qp : 0<Q := by dsimp [Q]; positivity
  letI : NeZero Q := ⟨qp.ne'⟩
  have tdiv : 12∣Q := dvd_mul_of_dvd_left (dvd_mul_right ..) _
  have wdiv : stride N∣Q := dvd_mul_left ..
  have mdiv : m∣Q := dvd_mul_of_dvd_left (dvd_mul_left ..) _
  have sd : (20160:ℤ)∣-((stride N:ℤ)*d) := dvd_neg.mpr (by exact_mod_cast dv)
  obtain ⟨s,base,shift⟩ := UniversalSumStride.all_moduli N (-(stride N*d)) sd Q qp
  simp only [Int.cast_natCast] at base shift
  obtain ⟨x,y,xy,plus⟩ := base
  obtain ⟨r,rx⟩ := ZMod.natCast_zmod_surjective x
  obtain ⟨v,vy⟩ := ZMod.natCast_zmod_surjective y
  have prod : r*v ≡ N [MOD Q] := (ZMod.natCast_eq_natCast_iff ..).mp (by rw [Nat.cast_mul,rx,vy,xy])
  obtain ⟨a,ha⟩ := forced_index odd prod tdiv wdiv
  have eq : ((((N:ℤ)+1-(stride N:ℤ)*a):ℤ) : ZMod Q)=s := by
    rw [←ha]
    simpa only [Int.cast_add,Int.cast_natCast,rx,vy] using plus
  refine ⟨a,reduce_sum mdiv (by rw [eq]; exact ⟨x,y,xy,plus⟩),reduce_sum mdiv ?_⟩
  change AdmissibleSum (N : ZMod Q) (((N:ℤ)+1-(stride N:ℤ)*(a+d):ℤ) : ZMod Q)
  rw [show (N:ℤ)+1-stride N*(a+d)=((N:ℤ)+1-stride N*a)+(-(stride N*d)) by ring,Int.cast_add,eq]
  exact shift

/-- An arbitrary shift by the local index period leaves membership unchanged. -/
theorem translate (N m : ℕ) (x q : ℤ) :
    survives N m (x+period (stride N) m*q) ↔ survives N m x := by
  let T := period (stride N) m
  have dv : m∣stride N*T := period_mul m (stride N)
  have z := (ZMod.natCast_zmod_eq_zero_iff_dvd ..).mpr dv
  push_cast at z
  have eq : ((N:ℤ)+1-(stride N:ℤ)*(x+(T:ℤ)*q))=(N:ℤ)+1-stride N*x-(stride N*T)*q := by ring
  unfold survives
  rw [eq]
  push_cast
  rw [z,zero_mul,sub_zero]

/-- For a fixed public start, an unavoidable collision lies within the first T
phases translated from the universal pair. The resulting count bound has only an
additive local-period penalty compared with the unrestricted-start condition. -/
theorem actual_limit {N m start C M : ℕ} (odd : Odd N) (mp : 0<m) (rad : 0<M)
    (uniq : Unique N m start C M) :
    C≤period (weight N) M*repeatAfter (stride N*period (weight N) M)+(period (stride N) m-1) := by
  let W := stride N
  let P := period (weight N) M
  let T := period W m
  let K := repeatAfter (W*P)
  have tp : 0<T := Nat.div_pos (Nat.le_of_dvd mp (Nat.gcd_dvd_left ..)) (Nat.gcd_pos_of_pos_left _ mp)
  have pp : 0<P := Nat.div_pos (Nat.le_of_dvd rad (Nat.gcd_dvd_left ..)) (Nat.gcd_pos_of_pos_left _ rad)
  have kp : 0<K := Nat.div_pos (Nat.le_of_dvd (by decide) (Nat.gcd_dvd_left ..)) (Nat.gcd_pos_of_pos_left _ (by decide))
  have dk := period_mul 20160 (W*P)
  obtain ⟨a,ha,hb⟩ := aligned odd mp (P*K) (by rw [←Nat.mul_assoc]; exact dk)
  let i := ((a-start)%(T:ℤ)).toNat
  have Tpos : (0:ℤ)<T := by exact_mod_cast tp
  have ie : (i:ℤ)=(a-start)%(T:ℤ) := Int.toNat_of_nonneg (Int.emod_nonneg _ Tpos.ne')
  have il : i<T := by have := Int.emod_lt_of_pos (a-start) Tpos; omega
  let q := (a-start)/(T:ℤ)
  have represent : a=((start+i:ℕ):ℤ)+(T:ℤ)*q := by
    have h := Int.emod_add_ediv (a-start) (T:ℤ)
    dsimp only [q]
    push_cast
    omega
  have hl : survives N m ((start+i:ℕ):ℤ) := (translate N m _ q).mp (represent ▸ ha)
  have hr : survives N m ((start+(i+P*K):ℕ):ℤ) := (translate N m _ q).mp (by
    convert hb using 1
    push_cast
    push_cast at represent
    linarith only [represent])
  apply le_of_not_gt
  intro tooLong
  change P*K+(T-1)<C at tooLong
  have same := (same_digit rad (weight N) (start+i) (P*K)).mpr (dvd_mul_right ..)
  have equal := uniq i (by omega) (i+P*K) (by omega) hl hr (by rwa [←Nat.add_assoc start i (P*K)])
  have nonzero := Nat.mul_pos pp kp
  omega

/-- Subtract one local period from the position count before applying the universal
radix budget. This necessary condition uses only the actual finite-window property. -/
theorem actual_radix {N m start C M : ℕ} (odd : Odd N) (mp : 0<m) (rad : 0<M)
    (uniq : Unique N m start C M) :
    ceilDiv (C-(period (stride N) m-1)) (20160/stride N)≤M/(M.gcd 10080) := by
  have limit := actual_limit odd mp rad uniq
  rw [capacity] at limit
  have pos : 0<20160/stride N := by
    unfold stride
    rcases weights N with h|h|h|h <;> rw [h] <;> decide
  exact (ceil_iff pos).mpr (by omega)

private theorem phase (N m start i : ℕ) :
    survives N m ((start+i:ℕ):ℤ) ↔ survives N m ((start+i%period (stride N) m:ℕ):ℤ) := by
  let T := period (stride N) m
  have eq : ((start+i:ℕ):ℤ)=((start+i%T:ℕ):ℤ)+(T:ℤ)*((i/T:ℕ):ℤ) := by
    have z := congrArg (fun v : ℕ => (v : ℤ)) (Nat.mod_add_div i T)
    push_cast at z ⊢
    linarith only [z]
  exact eq ▸ translate N m _ _

private theorem move {N m start i j : ℕ} (eq : i≡j [MOD period (stride N) m]) :
    survives N m ((start+i:ℕ):ℤ) ↔ survives N m ((start+j:ℕ):ℤ) := by
  rw [phase N m start i,phase N m start j,show i%period (stride N) m=j%period (stride N) m from eq]

private theorem period_pos {m : ℕ} (mp : 0<m) (g : ℕ) : 0<period g m :=
  Nat.div_pos (Nat.le_of_dvd mp (Nat.gcd_dvd_left ..)) (Nat.gcd_pos_of_pos_left _ mp)

private theorem collision_iff {N m start C M : ℕ} (rad : 0<M) :
    Unique N m start C M ↔
      ¬∃ i h : ℕ, 0<h ∧ i+period (weight N) M*h<C ∧
        survives N m ((start+i:ℕ):ℤ) ∧ survives N m ((start+(i+period (weight N) M*h):ℕ):ℤ) := by
  let P := period (weight N) M
  have pp : 0<P := period_pos rad _
  constructor
  · rintro uni ⟨i,h,hpos,inside,l,r⟩
    have hs : weight N*(start+i) ≡ weight N*(start+(i+P*h)) [MOD M] := by
      rw [←Nat.add_assoc]
      exact (same_digit rad ..).mpr (dvd_mul_right ..)
    have same := uni i (by omega) _ inside l r hs
    have nz := Nat.mul_pos pp hpos
    change i=i+P*h at same
    omega
  · intro none
    have no_lt {i j : ℕ} (small : i<j) (bj : j<C) (a : survives N m ((start+i:ℕ):ℤ))
        (b : survives N m ((start+j:ℕ):ℤ))
        (eq : weight N*(start+i) ≡ weight N*(start+j) [MOD M]) : False := by
      obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le small.le
      rw [←Nat.add_assoc] at eq
      obtain ⟨k,rfl⟩ := (same_digit rad ..).mp eq
      exact none ⟨i,k,by cases k <;> omega,bj,a,b⟩
    intro i bi j bj a b eq
    exact le_antisymm (le_of_not_gt fun h => no_lt h bi b a eq.symm)
      (le_of_not_gt fun h => no_lt h bj a b eq)

/-- Exact finite test for a proposed radix at the given starting position.
T is the local period in candidate-index units, P is the digit period. Only the
first T starting positions and the first T/gcd(T,P) positive multiples of P can
be needed, even when C is larger. Pairs beyond the interval endpoint are skipped. -/
theorem fixed_test {N m start C M : ℕ} (mp : 0<m) (rad : 0<M) :
    let T := period (stride N) m
    let P := period (weight N) M
    Unique N m start C M ↔
      ¬∃ i h : ℕ, i<T ∧ 0<h ∧ h≤period P T ∧ i+P*h<C ∧
        survives N m ((start+i:ℕ):ℤ) ∧ survives N m ((start+(i+P*h):ℕ):ℤ) := by
  let T := period (stride N) m
  let P := period (weight N) M
  let R := period P T
  have tp : 0<T := period_pos mp _
  have rp : 0<R := period_pos tp _
  dsimp only
  rw [collision_iff rad]
  apply not_congr
  constructor
  · rintro ⟨i,h,hpos,fit,ia,ib⟩
    let j := (h-1)%R+1
    have jb : j≤R := by dsimp only [j]; have := Nat.mod_lt (h-1) rp; omega
    have dec : h=j+R*((h-1)/R) := by
      dsimp only [j]
      have := Nat.mod_add_div (h-1) R
      omega
    change i+P*h<C at fit
    have le : P*j≤P*h := Nat.mul_le_mul_left P (by omega)
    have small : i % T ≤ i := Nat.mod_le ..
    have hd : P*j≡P*h [MOD T] := by
      conv_rhs => rw [dec,Nat.mul_add,←Nat.mul_assoc P R ((h-1)/R)]
      have zero := (Nat.modEq_zero_iff_dvd.mpr (dvd_mul_of_dvd_left (period_mul T P) ((h-1)/R))).symm
      simpa only [Nat.add_zero] using zero.add_left (P*j)
    have win : i%T+P*j<C := (Nat.add_le_add small le).trans_lt fit
    refine ⟨i%T,j,Nat.mod_lt _ tp,by dsimp [j]; omega,jb,win,?_,?_⟩
    · exact (phase N m start i).mp ia
    · exact (move ((Nat.mod_modEq i T).add hd)).mpr ib
  · rintro ⟨i,h,_,hpos,_,fit,ia,ib⟩
    exact ⟨i,h,hpos,fit,ia,ib⟩

/-- Once v=P modulo the local period is fixed, the mask on the right is independent
of P. Taking the maximum of these finitely many lower bounds gives the exact threshold.
For a fixed displacement residue, only its earliest joint survivor can maximize it. -/
theorem threshold {N m start C M v : ℕ} (mp : 0<m) (rad : 0<M)
    (phase_v : v≡period (weight N) M [MOD period (stride N) m]) :
    let T := period (stride N) m
    let P := period (weight N) M
    Unique N m start C M ↔ ∀ i<T, ∀ h, 0<h → h≤T →
      survives N m ((start+i:ℕ):ℤ) → survives N m ((start+(i+v*h):ℕ):ℤ) →
      ceilDiv (C-i) h≤P := by
  let T := period (stride N) m
  let P := period (weight N) M
  have slide (i h : ℕ) : survives N m ((start+(i+v*h):ℕ):ℤ) ↔ survives N m ((start+(i+P*h):ℕ):ℤ) :=
    move ((phase_v.mul_right h).add_left i)
  constructor
  · intro uni i _ h pos _ a b
    apply (ceil_iff pos).mpr
    rw [Nat.mul_comm]
    by_contra! bad
    exact (collision_iff rad).mp uni ⟨i,h,pos,by omega,a,(slide i h).mp b⟩
  · intro test
    apply (fixed_test mp rad).mpr
    rintro ⟨i,h,il,pos,cap,fit,a,b⟩
    have bound := (ceil_iff pos).mp (test i il h pos (cap.trans (Nat.div_le_self ..)) a ((slide i h).mpr b))
    rw [Nat.mul_comm h] at bound
    omega

/-- Within one shift phase increasing P preserves uniqueness. This permits a short
minimality certificate: reject just the last smaller radix in each arithmetic class. -/
theorem monotone_in_phase {N m start C M M' : ℕ} (mp : 0<m) (rad : 0<M) (rad' : 0<M')
    (same : period (weight N) M ≡ period (weight N) M' [MOD period (stride N) m])
    (le : period (weight N) M≤period (weight N) M') :
    Unique N m start C M → Unique N m start C M' := by
  intro ok
  apply (threshold mp rad' same).mpr
  intro i il h pos bound a b
  exact ((threshold mp rad (Nat.ModEq.refl _)).mp ok i il h pos bound a b).trans le

/-- A radix is increased by g*T at a time. Its digit period grows linearly with
an increment divisible by T, so the same local phase and thresholds continue to apply. -/
theorem radix_lane (g r T j : ℕ) (positive : 0<r) :
    period g (r+g*T*j)=period g r+(g/(r.gcd g))*T*j := by
  let d := r.gcd g
  have dp : 0<d := Nat.gcd_pos_of_pos_left g positive
  have fact : g/d*d=g := Nat.div_mul_cancel (Nat.gcd_dvd_right ..)
  have step : g*(T*j)=(g/d*(T*j))*d := calc
    g*(T*j)=(g/d*d)*(T*j) := by rw [fact]
    _=_ := by ring
  unfold period
  rw [Nat.mul_assoc g T j,Nat.gcd_add_mul_left_left]
  change (r+g*(T*j))/d=r/d+g/d*T*j
  rw [step,Nat.add_mul_div_right _ _ dp,Nat.mul_assoc]

/-- For an explicit window mask it suffices to check whether its surviving residues
are distinct. A sorted list of the digits certifies this without testing all pairs. -/
theorem list_iff {N m start C M : ℕ} (mask : Fin C → Bool)
    (valid : ∀ i : Fin C, survives N m ((start+i.val:ℕ):ℤ) ↔ mask i=true) :
    Unique N m start C M ↔ ∀ i j : Fin C, mask i=true → mask j=true →
      weight N*(start+i.val) ≡ weight N*(start+j.val) [MOD M] → i=j := by
  constructor
  · intro u i j a b same
    exact Fin.ext (u _ i.isLt _ j.isLt ((valid i).mpr a) ((valid j).mpr b) same)
  · intro test i il j jl a b same
    exact congrArg Fin.val (test ⟨i,il⟩ ⟨j,jl⟩ ((valid _).mp a) ((valid _).mp b) same)

private def classes63 (s : ZMod 63) : Prop :=
  s=7 ∨ s=20 ∨ s=29 ∨ s=34 ∨ s=43 ∨ s=56

private theorem table63 (s : ZMod 63) : AdmissibleSum 7294033 s ↔ classes63 s := by
  have tab : ∀ x y : ZMod 63, x*y=7294033 → classes63 (x+y) := by unfold classes63; decide +kernel
  constructor
  · rintro ⟨x,y,xy,rfl⟩
    exact tab x y xy
  · rintro (rfl|rfl|rfl|rfl|rfl|rfl)
    · exact ⟨11,59,by decide,by decide⟩
    · exact ⟨1,19,by decide,by decide⟩
    · exact ⟨13,16,by decide,by decide⟩
    · exact ⟨5,29,by decide,by decide⟩
    · exact ⟨2,41,by decide,by decide⟩
    · exact ⟨4,52,by decide,by decide⟩

private def exampleMask (i : Fin 52) : Bool := [7,24,33,42].contains i.val

theorem example63 (i : Fin 52) :
    survives 7294033 63 ((1822107+i.val:ℕ):ℤ) ↔ exampleMask i=true := by
  have row : ∀ i : Fin 52, classes63
      (((7294033:ℤ)+1-4*(1822107+i.val):ℤ) : ZMod 63) ↔ exampleMask i=true := by
    unfold classes63 exampleMask
    decide +kernel
  unfold survives
  rw [show stride 7294033=4 by decide,show (Nat.cast (R:=ZMod 63) 7294033)=(7294033 : ZMod 63) by decide]
  simpa only [Nat.cast_add,Nat.cast_ofNat] using (table63 _).trans (row i)

private abbrev ex (m start i : ℕ) := survives 7294033 m ((start+i:ℕ):ℤ)

private theorem shifted_hit (i : ℕ) (h : i=23 ∨ i=51) : ex 63 1822108 i := by
  rcases h with rfl|rfl <;> unfold ex survives <;> rw [show stride 7294033=4 by decide]
  · exact ⟨13,16,by decide +kernel,by decide +kernel⟩
  · exact ⟨2,41,by decide +kernel,by decide +kernel⟩

/-- The public 52-index window permits radix eight; every smaller positive radix
collides there. At the very next starting index the same radix already fails. -/
theorem example_minimum :
    Unique 7294033 63 1822107 52 8 ∧
    (∀ M : ℕ, 0<M → M<8 → ¬Unique 7294033 63 1822107 52 M) ∧
    ¬Unique 7294033 63 1822108 52 8 := by
  let fits (M : ℕ) := ∀ i j : Fin 52, exampleMask i=true → exampleMask j=true →
    weight 7294033*(1822107+i.val)≡weight 7294033*(1822107+j.val) [MOD M] → i=j
  have eq (M : ℕ) : Unique 7294033 63 1822107 52 M ↔ fits M := list_iff exampleMask example63
  have yes : fits 8 := by unfold fits exampleMask; decide +kernel
  have no : ∀ j : Fin 8, 0<j.val → ¬fits j.val := by unfold fits exampleMask; decide +kernel
  refine ⟨(eq _).mpr yes,fun M mp mb => fun u => no ⟨M,mb⟩ mp ((eq _).mp u),?_⟩
  intro u
  have bad := u 23 (by decide) 51 (by decide) (shifted_hit _ (Or.inl rfl)) (shifted_hit _ (Or.inr rfl)) (by decide +kernel)
  contradiction

/-- Adding the product's residue modulo five leaves a singleton in the same actual
window. These local witnesses use only small residues. The factor certificate checks
the decoded result independently. -/
theorem example315 (i : Fin 52) : ex 315 1822107 i.val ↔ i.val=33 := by
  constructor
  · intro a
    have small := (example63 i).mp (reduce_sum (by decide : 63∣315) a)
    simp [exampleMask] at small
    have five : ∀ x y : ZMod 5, x*y=7294033 → x+y=1 ∨ x+y=4 := by decide +kernel
    obtain ⟨x,y,xy,hs⟩ := reduce_sum (by decide : 5∣315) a
    have res := hs ▸ five x y xy
    rcases small with s|s|s|s
    · rw [s] at res; exfalso; revert res; decide +kernel
    · rw [s] at res; exfalso; revert res; decide +kernel
    · exact s
    · rw [s] at res; exfalso; revert res; decide +kernel
  · intro s
    unfold ex survives
    rw [s]
    exact ⟨31,88,by decide +kernel,by decide +kernel⟩

/-- The 52-index example uses exactly the width-derived endpoints and recovers
the sum of the two primes already certified for this public product. -/
theorem worked :
    ProductDeficitBand.lower 7294033 2048=5401 ∧ ProductDeficitBand.upper 7294033 2048=5608 ∧
    bottom 7294033 (stride 7294033) 5608=1822107 ∧
    choices 7294033 (stride 7294033) 5401 5608=52 ∧
    (∀ i : Fin 52, survives 7294033 315 ((1822107+i.val:ℕ):ℤ) ↔ i.val=33) ∧
    7294033+1-stride 7294033*(1822107+33)=5474 ∧
    Nat.Prime 2293 ∧ Nat.Prime 3181 ∧ 2293*3181=7294033 ∧ 2293+3181=5474 := by
  obtain ⟨lo,hi,count,_,_,_,_,_,_,pp,qp,pair⟩ := CyclotomicResiduePacking.worked_example
  exact ⟨lo,hi,by decide +kernel,count,example315,by decide +kernel,pp,qp,pair,by decide⟩

end PrimeFactors.FixedWindowDigitPacking
