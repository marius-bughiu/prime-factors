import PrimeFactors.SharedRootSigns
import PrimeFactors.OffsetProjectiveSlopes
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Tactic.NormNum.Prime

namespace PrimeFactors.OffsetCRTReconstruction

/-- For the primes where the slope is infinity, their product I divides k.
All finite projective slopes lift to R modulo the remaining product m. -/
def Compatible (I m R j k : ℕ) : Prop := I ∣ k ∧ j ≡ R*k [MOD m]

/-- Combine local tests without requiring the denominator to be a unit at
primes where the chosen line is infinity. Empty lists contribute modulus one. -/
theorem lift_of_local {inf fin : List ℕ} (ci : inf.Pairwise Nat.Coprime)
    (cf : fin.Pairwise Nat.Coprime) (r : ℕ → ℕ) {j k : ℕ}
    (infinite : ∀ p ∈ inf, p ∣ k) (finite : ∀ p ∈ fin, j ≡ r p*k [MOD p]) :
    ∃ R, (∀ p ∈ fin, R ≡ r p [MOD p]) ∧ Compatible inf.prod fin.prod R j k := by
  let R := Nat.chineseRemainderOfList r id fin cf
  refine ⟨R,R.property,⟨Nat.modEq_zero_iff_dvd.mp ((Nat.modEq_list_prod_iff ci).mpr (fun i =>
    Nat.modEq_zero_iff_dvd.mpr (infinite _ (List.get_mem inf i)))),?_⟩⟩
  refine (Nat.modEq_list_prod_iff cf).mpr fun i => ?_
  have hi := List.get_mem fin i
  exact (finite _ hi).trans (((R.property _ hi).mul_right k).symm)

theorem compatible_of_local {inf fin : List ℕ} (ci : inf.Pairwise Nat.Coprime)
    (cf : fin.Pairwise Nat.Coprime) (r : ℕ → ℕ) {j k : ℕ}
    (infinite : ∀ p ∈ inf, p ∣ k) (finite : ∀ p ∈ fin, j ≡ r p*k [MOD p]) :
    ∃ R, Compatible inf.prod fin.prod R j k := by
  obtain ⟨R,_,ok⟩ := lift_of_local ci cf r infinite finite
  exact ⟨R,ok⟩

private theorem split {I m R j k : ℕ} (match_ : Compatible I m R j k) :
    ∃ v, k=I*v ∧ j ≡ (R*I%m)*v [MOD m] := by
  obtain ⟨⟨v,hv⟩,slope⟩ := match_
  rw [hv,←Nat.mul_assoc] at slope
  exact ⟨v,hv,slope.trans (((Nat.mod_modEq (R*I) m).mul_right v).symm)⟩

/-- For every primitive box point on this CRT line, the public rational
(RI mod m)/m has a convergent whose denominator reconstructs k and whose
signed remainder reconstructs j. The factor two is Legendre's strict bound. -/
theorem reconstruct {I m R j k J K : ℕ} (ip : 0<I) (mp : 0<m) (kp : 0<k)
    (cop : j.Coprime k) (boxJ : j≤J) (boxK : k≤K) (room : 2*J*K<I*m)
    (match_ : Compatible I m R j k) :
    let a := R*I%m
    ∃ i, let u := ((a:ℝ)/m).convergent i
         k=I*u.den ∧ (j:ℤ)=(a:ℤ)*u.den-u.num*m := by
  obtain ⟨v,kv,slope⟩ := split match_
  let a := R*I%m
  have vp : 0<v := Nat.pos_of_ne_zero (fun zero => kp.ne' (by simp [kv,zero]))
  have cv : j.Coprime v := cop.coprime_dvd_right (kv ▸ dvd_mul_left v I)
  obtain ⟨w,eq⟩ := slope.dvd
  change ((a*v:ℕ):ℤ)-j=(m:ℤ)*w at eq
  push_cast at eq
  have wv : IsCoprime w (v:ℤ) := by
    obtain ⟨x,y,bez⟩ := cv.isCoprime
    refine ⟨-x*m,x*a+y,?_⟩
    linear_combination x*eq+bez
  have wvc : w.natAbs.Coprime v := by
    have eqone := Int.isCoprime_iff_gcd_eq_one.mp wv
    simpa only [Int.gcd,Int.natAbs_natCast] using eqone
  let u : ℚ := ⟨w,v,vp.ne',wvc⟩
  have short : 2*v*j<m := by
    apply (Nat.mul_lt_mul_left ip).mp
    calc I*(2*v*j) = 2*j*k := by rw [kv];ring
         _ ≤ 2*J*K := Nat.mul_le_mul (Nat.mul_le_mul_left _ boxJ) boxK
         _ < _ := room
  obtain ⟨i,eqi⟩ := SharedRootSigns.short_fraction_convergent (u:=u) (r:=a) (b:=(j:ℤ)) mp (by
    change (v:ℤ)*a-w*m=j
    linarith only [eq]) (by
    change 2*(v:ℤ)*|(j:ℤ)|<m
    rw [abs_of_nonneg (Int.natCast_nonneg j)]
    exact_mod_cast short)
  refine ⟨i,?_⟩
  change k=I*(((a:ℝ)/m).convergent i).den ∧ _
  rw [←eqi]
  exact ⟨kv,by change (j:ℤ)=(a:ℤ)*v-w*m;linarith only [eq]⟩

/-- A single tuple of lines labels at most one primitive positive pair in
the box whenever the total modulus exceeds its area. -/
theorem unique {I m R j k j' k' J K : ℕ} (ip : 0<I) (jp : 0<j)
    (cop : j.Coprime k) (cop' : j'.Coprime k') (boxJ : j≤J) (boxK : k≤K)
    (boxJ' : j'≤J) (boxK' : k'≤K) (room : J*K<I*m)
    (one : Compatible I m R j k) (two : Compatible I m R j' k') : j=j' ∧ k=k' := by
  obtain ⟨v,kv,first⟩ := split one
  obtain ⟨w,kw,second⟩ := split two
  have limit {a b c : ℕ} (aJ : a≤J) (bK : b≤K) (bc : b=I*c) : a*c<m := by
    apply (Nat.mul_lt_mul_left ip).mp
    calc I*(a*c) = a*b := by rw [bc];ring
         _ ≤ J*K := Nat.mul_le_mul aJ bK
         _ < _ := room
  have near : j*w ≡ j'*v [MOD m] := by
    have h := first.mul_right w
    have rev : j'*v ≡ (R*I%m)*v*w [MOD m] := by
      simpa only [Nat.mul_right_comm (R*I%m) w v] using second.mul_right v
    exact h.trans rev.symm
  have eq := near.eq_of_lt_of_lt (limit boxJ boxK' kw) (limit boxJ' boxK kv)
  have cv := cop.coprime_dvd_right (kv ▸ dvd_mul_left v I)
  have cw := cop'.coprime_dvd_right (kw ▸ dvd_mul_left w I)
  have jj := Nat.dvd_antisymm (cv.dvd_of_dvd_mul_right (eq ▸ dvd_mul_right j w))
    (cw.dvd_of_dvd_mul_right (eq.symm ▸ dvd_mul_right j' v))
  subst j'
  obtain rfl := Nat.eq_of_mul_eq_mul_left jp eq
  exact ⟨rfl,kv.trans kw.symm⟩

/-- Membership of a natural representative in the actual finite projective alphabet. -/
def Allowed (p N T : ℕ) (r : Option ℕ) : Prop :=
  ∃ prime : p.Prime, letI : Fact p.Prime := ⟨prime⟩
    (r.map (fun a => (a:ZMod p))) ∈ OffsetProjectiveSlopes.localSlopes p N T

private noncomputable def residue (j k p : ℕ) : ℕ :=
  if prime : p.Prime then letI : Fact p.Prime := ⟨prime⟩; ((j:ZMod p)/k).val else 0

private theorem finite_square_label {p N T j k d : ℕ} (prime : p.Prime) (odd : p≠2)
    (unit : ¬p∣N) (finite : ¬p∣k) (square : (j+2*T*k)^2=4*k^2*N+d^2) :
    Allowed p N T (some (residue j k p)) ∧ j ≡ residue j k p*k [MOD p] := by
  letI : Fact p.Prime := ⟨prime⟩
  have kp := mt (ZMod.natCast_zmod_eq_zero_iff_dvd k p).mp finite
  have np := mt (ZMod.natCast_zmod_eq_zero_iff_dvd N p).mp unit
  have eq := congrArg (fun z:ℕ => (z:ZMod p)) square
  push_cast at eq
  have chosen := OffsetProjectiveSlopes.mem_of_square odd np eq
  rw [if_neg kp] at chosen
  have cast : (residue j k p : ZMod p)=(j:ZMod p)/k := by simp [residue,prime,ZMod.natCast_zmod_val]
  refine ⟨⟨prime,?_⟩,(ZMod.natCast_eq_natCast_iff ..).mp ?_⟩
  · change some (residue j k p : ZMod p) ∈ OffsetProjectiveSlopes.localSlopes p N T
    rwa [cast]
  · rw [Nat.cast_mul,cast,div_mul_cancel₀ _ kp]

/-- A winning position is produced by a tuple the enumeration actually visits:
the lists partition the wheel, all labels pass their projective test, R is
the finite CRT lift, and a convergent gives the original position exactly. -/
def Recoverable (ps : List ℕ) (N T j k : ℕ) : Prop :=
  ∃ (inf fin : List ℕ) (r : ℕ → ℕ) (R : ℕ), (inf++fin).Perm ps ∧
    (∀ p ∈ inf, Allowed p N T none ∧ p∣k) ∧
    (∀ p ∈ fin, Allowed p N T (some (r p)) ∧ R ≡ r p [MOD p] ∧ j ≡ r p*k [MOD p]) ∧
    Compatible inf.prod fin.prod R j k ∧
    let a := R*inf.prod%fin.prod
    ∃ i, let u := ((a:ℝ)/fin.prod).convergent i
         k=inf.prod*u.den ∧ (j:ℤ)=(a:ℤ)*u.den-u.num*fin.prod

/-- Every square giving a primitive position inside the rectangle can be
reconstructed from the enumerable local alphabets for *any* suitable wheel. -/
theorem recoverable_of_square {ps : List ℕ} (distinct : ps.Nodup) {N T j k d J K : ℕ}
    (ok : ∀ p ∈ ps, p.Prime ∧ p≠2 ∧ ¬p∣N) (kp : 0<k) (cop : j.Coprime k)
    (boxJ : j≤J) (boxK : k≤K) (room : 2*J*K<ps.prod)
    (square : (j+2*T*k)^2=4*k^2*N+d^2) : Recoverable ps N T j k := by
  let divs (p : ℕ) := decide (p∣k)
  let inf := ps.filter divs
  let fin := ps.filter (fun p => !divs p)
  have perm : (inf++fin).Perm ps := List.filter_append_perm divs ps
  have cp : ps.Pairwise Nat.Coprime := distinct.pairwise_of_forall_ne fun p hp q hq ne =>
    (Nat.coprime_primes (ok _ hp).1 (ok _ hq).1).mpr ne
  have infinity (p : ℕ) (hp : p ∈ inf) : Allowed p N T none ∧ p∣k := by
    obtain ⟨mem,dv⟩ := List.mem_filter.mp hp
    have prime := (ok _ mem).1
    letI : Fact p.Prime := ⟨prime⟩
    exact ⟨⟨prime,OffsetProjectiveSlopes.infinity_mem ..⟩,of_decide_eq_true dv⟩
  have finite (p : ℕ) (hp : p ∈ fin) : Allowed p N T (some (residue j k p)) ∧
      j ≡ residue j k p*k [MOD p] := by
    obtain ⟨mem,dv⟩ := List.mem_filter.mp hp
    obtain ⟨prime,odd,unit⟩ := ok _ mem
    apply finite_square_label prime odd unit _ square
    simpa [divs] using dv
  obtain ⟨R,lift,compat⟩ := lift_of_local (inf:=inf) (fin:=fin) (.filter _ cp) (.filter _ cp)
    (residue j k) (fun p hp => (infinity p hp).2) (fun p hp => (finite p hp).2)
  have total : inf.prod*fin.prod=ps.prod := by simpa only [List.prod_append] using perm.prod_eq
  rw [←total] at room
  have pos : 0 < inf.prod ∧ 0 < fin.prod := by
    constructor
    · apply Nat.pos_of_ne_zero; intro eq; rw [eq,zero_mul] at room; omega
    · apply Nat.pos_of_ne_zero; intro eq; rw [eq,mul_zero] at room; omega
  exact ⟨inf,fin,residue j k,R,perm,infinity,fun p h => ⟨(finite p h).1,lift p h,(finite p h).2⟩,
    compat,reconstruct pos.1 pos.2 kp cop boxJ boxK room compat⟩

private theorem square_of_hit {N T j k f : ℕ} (hit : CompleteOffsetSearch.probe N T j k=some f) :
    ∃ d : ℕ, (j+2*T*k)^2=4*k^2*N+d^2 := by
  unfold CompleteOffsetSearch.probe at hit
  dsimp only at hit
  split at hit
  next pass => exact ⟨_,by rw [pass.2.1];omega⟩
  next => contradiction

/-- Every successful sharp primitive position for two distinct 1024-bit prime
factors is reconstructed from the fixed 130-prime wheel's accepted tuples. -/
theorem target_of_hit {N P Q j k f : ℕ} (pair : P*Q=N) (pp : P.Prime) (qp : Q.Prime)
    (pbits : 2^1023≤P ∧ P<2^1024) (qbits : 2^1023≤Q ∧ Q<2^1024)
    (short : 3*j^2≤4*(N-N.sqrt^2)) (dom : CompleteOffsetSearch.InSchedule N.sqrt (N-N.sqrt^2) j k)
    (hit : CompleteOffsetSearch.probe N N.sqrt j k=some f) :
    Recoverable OffsetProjectiveSlopes.primes130 N N.sqrt j k := by
  let T := N.sqrt
  let h := N-T^2
  let J := CompleteOffsetWork.height h
  let K := T*J/h+1
  have bound : 743 < (2:ℕ)^1023 := by decide +kernel
  have ok (l : ℕ) (mem : l∈OffsetProjectiveSlopes.primes130) : l.Prime ∧ l≠2 ∧ ¬l∣N := by
    obtain ⟨prime,odd,small⟩ := OffsetProjectiveSlopes.primes131_checked.2.2 l (List.mem_cons_of_mem 3 mem)
    refine ⟨prime,odd,?_⟩
    rw [←pair]
    intro div
    rcases prime.dvd_mul.mp div with lp|lq
    · exact ((Nat.prime_dvd_prime_iff_eq prime pp).mp lp).not_lt ((small.trans_lt bound).trans_le pbits.1)
    · exact ((Nat.prime_dvd_prime_iff_eq prime qp).mp lq).not_lt ((small.trans_lt bound).trans_le qbits.1)
  have nod := (List.nodup_cons.mp OffsetProjectiveSlopes.primes131_checked.2.1).2
  have upper : N<2^2048 := calc N=P*Q := pair.symm
                               _ < 2^1024*2^1024 := Nat.mul_lt_mul_of_lt_of_lt pbits.2 qbits.2
                               _ = _ := by decide +kernel
  have off : N.sqrt^2<N := by
    by_contra! bad
    rw [Nat.sub_eq_zero_of_le bad] at short
    have jp := dom.1
    nlinarith only [short,Nat.le_mul_self j,jp]
  have room : 2*J*K<OffsetProjectiveSlopes.primes130.prod := OffsetProjectiveSlopes.target_modulus130 upper off
  have jle : j≤J := Nat.le_sqrt'.mpr ((Nat.le_div_iff_mul_le (by decide : 0<3)).mpr (by
    change j^2*3≤4*(N-N.sqrt^2);omega))
  have kle : k≤K := dom.2.2.2.1.trans (Nat.succ_le_succ (Nat.div_le_div_right (Nat.mul_le_mul_left T jle)))
  obtain ⟨d,square⟩ := square_of_hit hit
  exact recoverable_of_square nod ok dom.2.2.1 dom.2.2.2.2 jle kle room square

/-- On every target semiprime, at least one visited tuple reconstructs a
successful factor-producing slot. The local alphabet product has the finite
upper bound proved by OffsetProjectiveSlopes.target_semiprime_counts. -/
theorem target_complete {N P Q : ℕ} (pair : P*Q=N) (pp : P.Prime) (qp : Q.Prime)
    (ne : P≠Q) (pbits : 2^1023≤P ∧ P<2^1024) (qbits : 2^1023≤Q ∧ Q<2^1024) :
    ∃ j k, Recoverable OffsetProjectiveSlopes.primes130 N N.sqrt j k ∧
      3*j^2≤4*(N-N.sqrt^2) ∧ CompleteOffsetSearch.InSchedule N.sqrt (N-N.sqrt^2) j k ∧
      (CompleteOffsetSearch.probe N N.sqrt j k=some P ∨ CompleteOffsetSearch.probe N N.sqrt j k=some Q) := by
  obtain ⟨j,k,short,dom,found⟩ := CompleteOffsetSearch.complete_1024_bit_factors pair pp qp ne pbits qbits
  refine ⟨j,k,?_,short,dom,found⟩
  exact found.elim (target_of_hit pair pp qp pbits qbits short dom)
    (target_of_hit pair pp qp pbits qbits short dom)

private theorem probe_at_root {N T j k d f : ℕ} (square : (j+2*T*k)^2=4*k^2*N+d^2)
    (label : N.gcd ((j+2*T*k-d)/2)=f) (low : 1<f) (high : f<N) :
    CompleteOffsetSearch.probe N T j k=some f := by
  have pos : 4*k^2*N≤(j+2*T*k)^2 := by omega
  have eq : (j+2*T*k)^2-4*k^2*N=d^2 := by omega
  unfold CompleteOffsetSearch.probe
  dsimp only
  rw [eq,Nat.sqrt_eq',label]
  simp only [pos,low,high,and_self,if_true]

/-- In the product-only run on 134683853, the winning denominator is zero
modulo both 5 and 7. The remaining CRT modulus comprises 11, 13, 17. -/
theorem mixed_example : Compatible 35 2431 418 44 35 ∧ 2*102*152<35*2431 ∧
    3*44^2≤4*7828 ∧ CompleteOffsetSearch.InSchedule 11605 7828 44 35 ∧
    CompleteOffsetSearch.probe 134683853 11605 44 35=some 8231 ∧
    8231*16363=134683853 ∧ Nat.Prime 8231 ∧ Nat.Prime 16363 := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  · unfold Compatible;decide +kernel
  · decide +kernel
  · decide +kernel
  · exact ⟨by decide,Nat.le_sqrt'.mpr (by decide),by decide,by decide,by decide⟩
  · exact probe_at_root (d:=5756) (by decide +kernel) (by decide +kernel) (by decide) (by decide)
  · decide +kernel
  · norm_num
  · norm_num

end PrimeFactors.OffsetCRTReconstruction
