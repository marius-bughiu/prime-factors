import PrimeFactors.ShiftedEndpointPopulation

/-! Counting successful predictions when both signed carries are bounded and
the dyadic radix is at most the square root of a target prime. -/

namespace PrimeFactors.ShiftedSmallRadices
open Finset ShiftedEndpointPopulation PredictedTraceCarries

set_option exponentiation.threshold 8192
set_option maxRecDepth 2048

/-- Two small carries constrain both the signed residual product and the
linear combination of residuals, including accidental probe successes. -/
private theorem short_of_probe {p q D f : ℕ} {h k : ℤ} (pp : p.Prime) (qp : q.Prime) (ne : p≠q)
    (dp : 0<D) (hc : |h|≤4) (kc : |k|≤4) (hit : probe (p*q) D h k=some f) :
    ∃ a b : ℕ, let x := (p:ℤ)-a*D; let y := (q:ℤ)-b*D
      |x*y|≤5*D ∧ |(p:ℤ)*y+q*x|≤10*(D:ℤ)^2 := by
  obtain ⟨a,b,coef,tr⟩ := probe_allocation pp qp ne hit
  let x := (p:ℤ)-a*D
  let y := (q:ℤ)-b*D
  have d₀ : (0:ℤ)<D := by exact_mod_cast dp
  have trace : (b:ℤ)*p+a*q=(a:ℤ)*b*D+nearest ((p:ℤ)*q) D-k := by
    rw [←tr,label,coef,Nat.cast_mul]
  have low := residual dp (nearest_error (n:=(p:ℤ)*q) d₀) trace kc
  have low' : |x*y|≤5*D := by dsimp [x,y];rw [abs_mul];linarith only [low,d₀]
  have high := nearest_error (n:=(p:ℤ)*q) (sq_pos_of_pos d₀)
  have corr : nearest ((p:ℤ)*q) ((D:ℤ)^2)+h=(a:ℤ)*b := by
    simpa only [coefficient,Nat.cast_mul] using coef
  have id : (p:ℤ)*y+q*x =
      ((p:ℤ)*q-(D:ℤ)^2*nearest ((p:ℤ)*q) ((D:ℤ)^2)) - (D:ℤ)^2*h + x*y := by
    dsimp [x,y]
    linear_combination (D:ℤ)^2*corr
  have ha := abs_add_le ((p:ℤ)*q-(D:ℤ)^2*nearest ((p:ℤ)*q) ((D:ℤ)^2)-(D:ℤ)^2*h) (x*y)
  have hb := abs_add_le ((p:ℤ)*q-(D:ℤ)^2*nearest ((p:ℤ)*q) ((D:ℤ)^2)) (-((D:ℤ)^2*h))
  have hc' := mul_le_mul_of_nonneg_left hc (sq_nonneg (D:ℤ))
  rw [←sub_eq_add_neg,abs_neg,abs_mul,abs_of_nonneg (sq_nonneg (D:ℤ))] at hb
  have ds : (D:ℤ)≤(D:ℤ)^2 := by nlinarith only [mul_nonneg d₀.le (show (0:ℤ)≤D-1 by omega)]
  exact ⟨a,b,low',id ▸ (by linarith only [ha,hb,hc',high,low',ds,sq_nonneg (D:ℤ)])⟩

/-- Upper allowed coefficient of D in q=y+D*b, from the signed linear inequality. -/
private def top (p D : ℕ) (x y : ℤ) : ℤ :=
  let constant := ((p:ℤ)+x)*y
  (10*(D:ℤ)^2 - (if x<0 then -constant else constant)) / ((D:ℤ)*|x|)

private theorem slot {p D b : ℕ} {x y : ℤ} (dp : 0<D) (nz : x≠0)
    (span : |(p:ℤ)*y+(y+D*b)*x|≤10*(D:ℤ)^2) :
    0≤top p D x y-b ∧ top p D x y-b≤((20*D/x.natAbs:ℕ):ℤ) := by
  let c := if x<0 then -(((p:ℤ)+x)*y) else ((p:ℤ)+x)*y
  have ab : abs (c+(D:ℤ)*|x| * b)≤10*(D:ℤ)^2 := by
    dsimp [c]
    split
    next neg =>
      rw [abs_of_neg neg,show -(((p:ℤ)+x)*y)+D*(-x)*b = -((p:ℤ)*y+(y+D*b)*x) by ring,abs_neg]
      exact span
    next nonneg =>
      rw [abs_of_nonneg (le_of_not_gt nonneg),show ((p:ℤ)+x)*y+D*x*b = (p:ℤ)*y+(y+D*b)*x by ring]
      exact span
  let U := top p D x y
  have defU : U=(10*(D:ℤ)^2-c)/((D:ℤ)*|x|) := rfl
  have d : (0:ℤ)<D := by exact_mod_cast dp
  have width := abs_pos.mpr nz
  have dd := mul_pos d width
  obtain ⟨lo,hi⟩ := abs_le.mp ab
  have bu : (b:ℤ)≤U := by rw [defU];apply (Int.le_ediv_iff_mul_le dd).mpr; linarith only [hi]
  have topbound : U*((D:ℤ)*|x|)≤10*(D:ℤ)^2-c := by rw [defU]; exact Int.ediv_mul_le _ dd.ne'
  have diff : (U-b)*|x|≤20*D := by
    apply le_of_mul_le_mul_left (a:=(D:ℤ)) _ d
    nlinarith only [topbound,lo]
  refine ⟨by change 0≤U-b;omega,?_⟩
  rw [Int.natCast_ediv, Nat.cast_mul, Nat.cast_ofNat, Int.natCast_natAbs]
  exact (Int.le_ediv_iff_mul_le width).mpr diff

private def offsets (p D : ℕ) (s : ℤ) := (p:ℤ)%D+s*D

/-- Partners for one first-prime residue and one possible signed displacement.
The second offset and its admissible quotient index determine q directly. -/
private def row (p D : ℕ) (x : ℤ) : Finset ℕ :=
  (Icc (-(2*|x|+20)) (2*|x|+20)).biUnion fun y : ℤ =>
    (range (20*D/x.natAbs+1)).image fun j : ℕ =>
      (y+(D:ℤ)*(top p D x y-(j:ℕ))).toNat

private theorem row_count {p D : ℕ} {x : ℤ} (dp : 0<D) (cap : x.natAbs≤7*D) :
    (row p D x).card≤1000*D := by
  let t := x.natAbs
  have ycount : (Icc (-(2*|x|+20)) (2*|x|+20)).card=4*t+41 := by
    rw [Int.card_Icc,←Int.natCast_natAbs]
    dsimp [t];omega
  have total : (row p D x).card≤(4*t+41)*(20*D/t+1) := by
    unfold row
    refine card_biUnion_le.trans ?_
    calc
      _ ≤ ∑ _y ∈ Icc (-(2*|x|+20)) (2*|x|+20), (20*D/t+1) :=
        sum_le_sum fun _ _ => card_image_le.trans_eq (card_range _)
      _ = _ := by rw [sum_const,nsmul_eq_mul,ycount]; rfl
  apply total.trans
  have h := Nat.div_mul_le_self (20*D) t
  have h' := Nat.div_le_self (20*D) t
  change t≤7*D at cap
  nlinarith only [h,h',cap,dp]

private def directions (p D : ℕ) := (Icc (-6:ℤ) 6).biUnion fun s => row p D (offsets p D s)

private theorem directions_count (p D : ℕ) (dp : 0<D) : (directions p D).card≤13000*D := by
  have d : (0:ℤ)<D := by exact_mod_cast dp
  have cap (s : ℤ) (hs : s∈Icc (-6:ℤ) 6) : (offsets p D s).natAbs≤7*D := by
    obtain ⟨lo,hi⟩ := mem_Icc.mp hs
    have al := mul_le_mul_of_nonneg_right lo d.le
    have au := mul_le_mul_of_nonneg_right hi d.le
    have r0 := Int.emod_nonneg (p:ℤ) d.ne'
    have ru := Int.emod_lt_of_pos (p:ℤ) d
    have cc : |offsets p D s|≤(7*D:ℕ) := by
      apply abs_le.mpr; unfold offsets;push_cast; constructor <;> linarith
    exact_mod_cast (show ((offsets p D s).natAbs:ℤ)≤(7*D:ℕ) by rwa [Int.natCast_natAbs])
  calc
    _ ≤ _ := card_biUnion_le
    _ ≤ ∑ _s ∈ Icc (-6:ℤ) 6, 1000*D := sum_le_sum fun s h => row_count dp (cap s h)
    _ = _ := by rw [sum_const,nsmul_eq_mul,show (Icc (-6:ℤ) 6).card=13 by decide];ring


private theorem covered {p q D a b : ℕ} (dp : 0<D) (even : Even D) (op : Odd p) (oq : Odd q)
    (pp : 0<p) (balanced : q≤2*p) (size : D^2≤2*p)
    (low : |((p:ℤ)-a*D)*((q:ℤ)-b*D)|≤5*D)
    (high : |(p:ℤ)*((q:ℤ)-b*D)+q*((p:ℤ)-a*D)|≤10*(D:ℤ)^2) :
    q∈directions p D := by
  let x := (p:ℤ)-a*D
  let y := (q:ℤ)-b*D
  have d : (0:ℤ)<D := by exact_mod_cast dp
  have nz {z a' : ℕ} (odd : Odd z) : (z:ℤ)-a'*D≠0 := by
    intro h
    have zz : z=a'*D := by exact_mod_cast (show (z:ℤ)=a'*D by omega)
    exact (Nat.not_even_iff_odd.mpr odd) (zz ▸ even.mul_left _)
  have xn : x≠0 := nz op
  have yn : y≠0 := nz oq
  change |x*y|≤5*D at low
  rw [abs_mul] at low
  have wy : (1:ℤ)≤|y| := by have := abs_pos.mpr yn;omega
  have xbound : |x|≤5*D := (le_mul_of_one_le_right (abs_nonneg x) wy).trans low
  have xr := Int.emod_nonneg (p:ℤ) d.ne'
  have xu := Int.emod_lt_of_pos (p:ℤ) d
  let s := (p:ℤ)/D-a
  have xeq : x=offsets p D s := by
    dsimp [x,s,offsets]
    linear_combination -(Int.emod_add_ediv (p:ℤ) D)
  have ss : s∈Icc (-6:ℤ) 6 := by
    obtain ⟨l,u⟩ := abs_le.mp xbound
    rw [xeq] at l u
    unfold offsets at l u
    apply mem_Icc.mpr
    constructor
    · apply le_of_mul_le_mul_right (a:= (D:ℤ)) _ d
      linarith only [l,xu]
    · apply le_of_mul_le_mul_right (a:= (D:ℤ)) _ d
      linarith only [u,xr,d]
  change |(p:ℤ)*y+q*x|≤10*(D:ℤ)^2 at high
  have eq : (p:ℤ)*y=(p*y+q*x)+ -(q*x) := by ring
  have ybound : |y|≤2*|x|+20 := by
    have triangle := abs_add_le ((p:ℤ)*y+q*x) (-(q*x))
    rw [←eq,abs_neg,abs_mul,abs_mul,abs_of_nonneg (Int.natCast_nonneg p),
      abs_of_nonneg (Int.natCast_nonneg q)] at triangle
    have qcap : (q:ℤ)≤2*p := by exact_mod_cast balanced
    have dcap : (D:ℤ)^2≤2*p := by exact_mod_cast size
    have h := mul_le_mul_of_nonneg_right qcap (abs_nonneg x)
    apply le_of_mul_le_mul_left (a:=(p:ℤ)) _ (by exact_mod_cast pp)
    linarith only [triangle,high,dcap,h]
  have byeq : y+(D:ℤ)*b=q := by dsimp [y];ring
  obtain ⟨jlo,jhi⟩ := slot dp xn (show |(p:ℤ)*y+(y+D*b)*x|≤10*(D:ℤ)^2 by rwa [byeq])
  apply mem_biUnion.mpr
  refine ⟨s,ss,?_⟩
  rw [←xeq]
  apply mem_biUnion.mpr
  refine ⟨y,mem_Icc.mpr (abs_le.mp ybound),?_⟩
  let j := (top p D x y-b).toNat
  have jval : (j:ℤ)=top p D x y-b := Int.toNat_of_nonneg jlo
  apply mem_image.mpr
  refine ⟨j,mem_range.mpr (by omega),?_⟩
  rw [jval,show top p D x y-(top p D x y-b)=(b:ℤ) by ring,byeq,Int.toNat_natCast]

private def smallPool (p : ℕ) : Finset ℕ :=
  (range 512).biUnion fun i => directions p (2^(i+1))

attribute [local irreducible] directions

private theorem small_mem {p q e f : ℕ} {h k : ℤ}
    (pp : p.Prime) (qp : q.Prime) (ne : p≠q) (pl : 2^1023≤p) (ql : 2^1023≤q) (qu : q<2^1024)
    (lo : 1≤e) (hi : e≤512) (hc : |h|≤4) (kc : |k|≤4) (hit : probe (p*q) (2^e) h k=some f) :
    q∈smallPool p := by
  obtain ⟨a,b,low,high⟩ := short_of_probe pp qp ne (by positivity) hc kc hit
  have pow : ((2:ℕ)^e)^2≤2^1024 := by rw [←pow_mul]; exact Nat.pow_le_pow_right (by decide) (by omega)
  have lower : 2^1024≤2*p := (by decide : (2:ℕ)^1024=2*2^1023) ▸ (Nat.mul_le_mul_left 2 pl)
  have pOdd := pp.odd_of_ne_two (by omega)
  have qOdd := qp.odd_of_ne_two (by omega)
  have ev : Even ((2:ℕ)^e) := by
    rw [show e=(e-1)+1 by omega,pow_succ]
    exact even_two.mul_left _
  have cell := covered (show 0<(2:ℕ)^e by positivity) ev pOdd qOdd pp.pos
    (qu.le.trans lower) (pow.trans lower) low high
  unfold smallPool
  apply mem_biUnion.mpr
  exact ⟨e-1,mem_range.mpr (by omega),by rwa [Nat.sub_add_cancel lo]⟩

set_option maxRecDepth 12000 in
private theorem small_count (p : ℕ) : (smallPool p).card≤2^527 := by
  unfold smallPool
  apply card_biUnion_le.trans
  calc
    _ ≤ ∑ i ∈ range 512, (13000:ℕ)*2^(i+1) := sum_le_sum fun i _ => directions_count p _ (by positivity)
    _ ≤ _ := by decide +kernel

attribute [local irreducible] smallPool ShiftedEndpointPopulation.cost

/-- Every low-radix hit requires one of fewer than 2^527 integer partners
per first prime even if all 512 possible exponents can be used. -/
theorem small_count_of_hits {pairs : Finset (ℕ × ℕ)} {pool : Finset ℕ}
    (hits : ∀ x∈pairs, x.1∈pool ∧ x.1.Prime ∧ x.2.Prime ∧ x.1≠x.2 ∧
      2^1023≤x.1 ∧ 2^1023≤x.2 ∧ x.2<2^1024 ∧ ∃ e, 1≤e ∧ e≤512 ∧
      ∃ h k : ℤ, |h|≤4 ∧ |k|≤4 ∧ ∃ f, probe (x.1*x.2) (2^e) h k=some f) :
    pairs.card≤pool.card*2^527 := by
  let S := pool.biUnion fun p => (smallPool p).image (p,·)
  have sub : pairs⊆S := by
    intro x hx
    obtain ⟨pm,pp,qp,ne,pl,ql,qu,e,lo,hi,h,k,hc,kc,f,hit⟩ := hits x hx
    exact mem_biUnion.mpr ⟨x.1,pm,mem_image.mpr
      ⟨x.2,small_mem pp qp ne pl ql qu lo hi hc kc hit,Prod.ext rfl rfl⟩⟩
  calc
    _ ≤ _ := card_le_card sub
    _ ≤ _ := card_biUnion_le
    _ ≤ ∑ _p ∈ pool, (2:ℕ)^527 := sum_le_sum fun p _ => card_image_le.trans (small_count p)
    _ = _ := by rw [sum_const,nsmul_eq_mul];rfl

private theorem scale {X P H K T B C : ℕ} (den : X*P<C*T)
    (count : H≤P*K) (price : B*C*K≤X) (kp : 0<K) (bp : 0<B) : B*H<T := by
  apply Nat.lt_of_mul_lt_mul_left (a:=X)
  calc
    _ ≤ X*(B*(P*K)) := Nat.mul_le_mul_left X (Nat.mul_le_mul_left B count)
    _ = (X*P)*(B*K) := by ring
    _ < (C*T)*(B*K) := Nat.mul_lt_mul_of_pos_right den (Nat.mul_pos bp kp)
    _ = (B*C*K)*T := by ring
    _ ≤ _ := Nat.mul_le_mul_right T price

/-- Simultaneously searching every power of two from 2 to 2^1024 still reaches
fewer than one in 2^234 target pairs under the published population inequality.
There is no high-carry bound for e≥513. For e≤512 the high budget is four. -/
theorem all_radices {pairs : Finset (ℕ × ℕ)} {pool : Finset ℕ} {pop : ℕ}
    (den : 2^1023*pool.card<44331*pop)
    (eligible : ∀ x∈pairs, x.1∈pool ∧ x.2∈pool ∧ x.1.Prime ∧ x.2.Prime ∧ x.1≠x.2 ∧
      2^1023≤x.1 ∧ x.1<2^1024 ∧ 2^1023≤x.2 ∧ x.2<2^1024)
    (hit : ∀ x∈pairs, ∃ e, 1≤e ∧ e≤1024 ∧ ∃ h k : ℤ, (e≤512 → |h|≤4) ∧ |k|≤4 ∧
      ∃ f, probe (x.1*x.2) (2^e) h k=some f) : 2^234*pairs.card<pop := by
  classical
  let small := pool.biUnion fun p => (smallPool p).image (p,·)
  have sc : small.card≤pool.card*2^550 := calc
    _ ≤ _ := card_biUnion_le
    _ ≤ ∑ _p ∈ pool, (2:ℕ)^550 := sum_le_sum fun p _ => card_image_le.trans ((small_count p).trans (by decide))
    _ = _ := by rw [sum_const,nsmul_eq_mul];rfl
  have large := geometric_count (pairs:=pairs\small) (pool:=pool) (by
    intro x hx
    obtain ⟨xm,out⟩ := mem_sdiff.mp hx
    obtain ⟨p,q,pp,qp,ne,pl,pu,ql,qu⟩ := eligible x xm
    obtain ⟨e,lo,hi,h,k,hc,kc,f,found⟩ := hit x xm
    by_cases low : e≤512
    · exact False.elim (out (mem_biUnion.mpr ⟨x.1,p,mem_image.mpr
        ⟨x.2,small_mem pp qp ne pl ql qu lo low (hc low) kc found,Prod.ext rfl rfl⟩⟩))
    · exact ⟨p,q,pl,pu,ql,qu,e,by omega,hi,near_of_probe pp qp ne kc found⟩)
  have parts : pairs ⊆ (pairs\small)∪small := by
    intro x hx
    by_cases h : x∈small
    · exact mem_union_right _ h
    · exact mem_union_left _ (mem_sdiff.mpr ⟨hx,h⟩)
  have count := (card_le_card parts).trans ((card_union_le _ _).trans (Nat.add_le_add large sc))
  rw [←Nat.mul_add] at count
  exact scale den count reserve (Nat.add_pos_right _ (by decide : 0<(2:ℕ)^550)) (by decide)

end PrimeFactors.ShiftedSmallRadices
