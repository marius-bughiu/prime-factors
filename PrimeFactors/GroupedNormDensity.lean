import PrimeFactors.GroupedNormFrequency
import Mathlib.Data.Real.Sqrt

namespace PrimeFactors.GroupedNormDensity
open GroupedNormFactors Finset

/-- Product from the determinant-one coordinates (a,b,u,v)=(1,1,u,u+1). -/
def input (T u : ℕ) := T^2+(T-u*(u+1))

/-- The positive offset puts the factorization in the open branch, and fitting
u(u+1) inside that offset makes k=1 the public top multiplier. -/
theorem one_accepts {T u : ℕ} (hu : 0<u) (fits : 2*(u*(u+1))≤T) :
    (input T u).sqrt=T ∧
    topProbe (input T u)=some (u^2+(T-u*(u+1)), (u+1)^2+(T-u*(u+1))) := by
  let z := u*(u+1)
  let h := T-z
  have zp : 0<z := Nat.mul_pos hu (by omega)
  have hl : z≤T := by dsimp [z] at *; omega
  have dec : T=z+h*1 := by dsimp [h]; omega
  have cap : z≤h := by dsimp [h,z]; omega
  have sq : (input T u).sqrt=T := by
    apply (Nat.eq_sqrt.mpr ⟨?_,?_⟩).symm
    · simp [input,pow_two]
    · unfold input
      have hle : T-u*(u+1) ≤ T := Nat.sub_le ..
      nlinarith
  refine ⟨sq, ?_⟩
  have off : input T u-T^2=h := by simp [input,h,z]
  have hit := topProbe_accepts sq off (by decide : 0<1) dec zp cap (by simp [z] : u*(u+1)=1*z)
  simpa [fromRoot,h,z] using hit

/-- The floor square root recovers T; the offset then uniquely determines u. -/
theorem input_injective {T S u v : ℕ} (hu : 0<u) (hv : 0<v)
    (fitU : 2*(u*(u+1))≤T) (fitV : 2*(v*(v+1))≤S) (same : input T u=input S v) :
    T=S ∧ u=v := by
  have ts := (one_accepts hu fitU).1.symm.trans ((congrArg Nat.sqrt same).trans (one_accepts hv fitV).1)
  subst S
  have h1 : u*(u+1)≤T := by omega
  have h2 : v*(v+1)≤T := by omega
  unfold input at same
  have eq : u*(u+1)=v*(v+1) := by omega
  refine ⟨rfl, le_antisymm (le_of_not_gt ?_) (le_of_not_gt ?_)⟩ <;> intro lt <;>
    nlinarith [show 0≤(u:ℤ)^2 by positivity, show 0≤(v:ℤ)^2 by positivity,
      Nat.pow_lt_pow_left lt (by decide : 2≠0)]

/-- The explicit size can be evaluated directly for arbitrary root bound U. -/
noncomputable def lowerInputs (U : ℕ) : Finset ℕ :=
  ((Ico ((U+1)/2) U) ×ˢ (Icc 1 (U.sqrt/4))).image (fun p => input p.1 p.2)

private theorem rectangle_fits {U T u : ℕ} (lo : (U+1)/2 ≤ T) (hu : 0<u) (hi : u≤U.sqrt/4) :
    2*(u*(u+1))≤T := by
  have root := Nat.sqrt_le U
  have bound : 4*u≤U.sqrt := by omega
  have sq := Nat.mul_le_mul bound bound
  have half : U≤2*T := by omega
  nlinarith [Nat.le_mul_of_pos_right u hu]

theorem lower_card (U : ℕ) : (lowerInputs U).card = (U/2)*(U.sqrt/4) := by
  unfold lowerInputs
  rw [card_image_of_injOn]
  · rw [card_product, Nat.card_Ico,Nat.card_Icc]
    have eq : U-(U+1)/2=U/2 := by omega
    rw [eq]
    congr 1
  · rintro ⟨T,u⟩ left ⟨S,v⟩ right same
    obtain ⟨Tlo,_⟩ := mem_Ico.mp (mem_product.mp left).1
    obtain ⟨ulo,uhi⟩ := mem_Icc.mp (mem_product.mp left).2
    obtain ⟨Slo,_⟩ := mem_Ico.mp (mem_product.mp right).1
    obtain ⟨vlo,vhi⟩ := mem_Icc.mp (mem_product.mp right).2
    obtain ⟨ts,uv⟩ := input_injective ulo vlo (rectangle_fits Tlo ulo uhi)
      (rectangle_fits Slo vlo vhi) same
    exact Prod.ext ts uv

theorem lower_success {U n : ℕ} (mem : n ∈ lowerInputs U) :
    (U+1)/2≤n.sqrt ∧ n.sqrt<U ∧ ∃ p q, probe n 1=some (p,q) ∧
      topProbe n=some (p,q) ∧ 1<p ∧ 1<q ∧ p*q=n := by
  obtain ⟨⟨T,u⟩,inRange,rfl⟩ := mem_image.mp mem
  obtain ⟨Tlo,Thi⟩ := mem_Ico.mp (mem_product.mp inRange).1
  obtain ⟨ulo,uhi⟩ := mem_Icc.mp (mem_product.mp inRange).2
  change (U+1)/2≤T at Tlo
  change T<U at Thi
  change 1≤u at ulo
  change u≤U.sqrt/4 at uhi
  have fits := rectangle_fits Tlo ulo uhi
  obtain ⟨root,top⟩ := one_accepts ulo fits
  let z := u*(u+1)
  let h := T-z
  have zp : 0<z := Nat.mul_pos ulo (by omega)
  have dec : T=z+h*1 := by dsimp [h,z];omega
  have cap : z≤h := by dsimp [h,z];omega
  have mult := top_multiplier dec zp cap
  have one := top
  unfold topProbe at one
  rw [root,show input T u-T^2=h by simp [input,h,z],mult] at one
  exact ⟨by simpa only [root] using Tlo, by simpa only [root] using Thi,_,_,one,top,topProbe_sound top⟩

private abbrev Code (U : ℕ) :=
  Σ i : Fin U, Σ j : Fin U,
    Fin (U/((i.val+1)*(j.val+1))) × Fin ((U/((i.val+1)*(j.val+1))).sqrt+1)

private abbrev Witness := GroupedNormFrequency.Witness

private noncomputable def encode {s U : ℕ} (w : Witness s) (small : w.u*w.v+w.h*(w.a*w.b)<U) : Code U := by
  let z := w.u/w.a
  have hp := w.hpos
  have ap := w.apos
  have bp := w.bpos
  have abpos := Nat.mul_pos ap bp
  have prod := (Nat.le_add_left (w.h*(w.a*w.b)) (w.u*w.v)).trans_lt small
  have ab := (Nat.le_mul_of_pos_left (w.a*w.b) hp).trans_lt prod
  have al := (Nat.le_mul_of_pos_right _ bp).trans_lt ab
  have bl := (Nat.le_mul_of_pos_left _ ap).trans_lt ab
  let i : Fin U := ⟨w.a-1,by omega⟩
  let j : Fin U := ⟨w.b-1,by omega⟩
  refine ⟨i,j,?_⟩
  have ai : i.val+1=w.a := Nat.sub_add_cancel ap
  have bj : j.val+1=w.b := Nat.sub_add_cancel bp
  have fitsH : w.h≤U/(w.a*w.b) := (Nat.le_div_iff_mul_le abpos).mpr prod.le
  have au : w.a*z≤w.u := Nat.mul_div_le ..
  have bv : w.b*z≤w.v := by
    apply Nat.le_of_mul_le_mul_left (c:=w.a) _ ap
    calc w.a*(w.b*z) = w.b*(w.a*z) := by ring
         _ ≤ w.b*w.u := Nat.mul_le_mul_left _ au
         _ ≤ w.a*w.v := by rw [w.neighboring];omega
  have sq : z*z≤U/(w.a*w.b) := (Nat.le_div_iff_mul_le abpos).mpr (by
    calc z*z*(w.a*w.b) = (w.a*z)*(w.b*z) := by ring
         _ ≤ w.u*w.v := Nat.mul_le_mul au bv
         _ ≤ _ := (Nat.le_add_right ..).trans small.le)
  exact (⟨w.h-1,by rw [ai,bj]; omega⟩,⟨z,by rw [ai,bj];exact Nat.lt_succ_of_le (Nat.le_sqrt.mpr sq)⟩)

private theorem encode_inj {U s : ℕ} (w t : Witness s)
    (hw : w.u*w.v+w.h*(w.a*w.b)<U) (ht : t.u*t.v+t.h*(t.a*t.b)<U)
    (eq : encode w hw = encode t ht) : w.input=t.input := by
  have ao := congrArg (fun c : Code U => c.1.val) eq
  have bo := congrArg (fun c : Code U => c.2.1.val) eq
  have ho := congrArg (fun c : Code U => c.2.2.1.val) eq
  have zo := congrArg (fun c : Code U => c.2.2.2.val) eq
  change w.a-1=t.a-1 at ao
  change w.b-1=t.b-1 at bo
  change w.h-1=t.h-1 at ho
  change w.u/w.a=t.u/t.a at zo
  have a : w.a=t.a := by have := w.apos; have := t.apos; omega
  have b : w.b=t.b := by have := w.bpos; have := t.bpos; omega
  have h : w.h=t.h := by have := w.hpos; have := t.hpos; omega
  have dx := w.neighboring
  have dy := t.neighboring
  rw [← a,← b] at dy
  rw [← a] at zo
  have residue : w.u ≡ t.u [MOD w.a] := by
    apply Nat.modEq_iff_dvd.mpr
    refine ⟨(w.v:ℤ)*t.u-(t.v:ℤ)*w.u,?_⟩
    zify at dx dy
    linear_combination (w.u:ℤ)*dy-(t.u:ℤ)*dx
  have u := Nat.mod_add_div w.u w.a
  rw [show w.u%w.a=t.u%w.a from residue,zo,Nat.mod_add_div] at u
  rw [← u] at dx
  have v := Nat.mul_left_cancel w.apos (dx.trans dy.symm)
  simp [GroupedNormFrequency.Witness.input,a,b,h,u,v]

private noncomputable def weight (n : ℕ) : ℝ :=
  1 / ((n:ℝ)*Real.sqrt n)

private theorem tail_weight {x : ℝ} (hx : 1≤x) :
    1/((x+1)*Real.sqrt (x+1)) ≤ 2*(1/Real.sqrt x-1/Real.sqrt (x+1)) := by
  let a := Real.sqrt x
  let b := Real.sqrt (x+1)
  have ap : 0<a := Real.sqrt_pos.mpr (by linarith)
  have bp : 0<b := Real.sqrt_pos.mpr (by linarith)
  have ab : a≤b := Real.sqrt_le_sqrt (by linarith)
  have ha : a^2=x := Real.sq_sqrt (by linarith)
  have hb : b^2=x+1 := Real.sq_sqrt (by linarith)
  have identity : (b-a)*(b+a)=1 := by nlinarith
  have estimate : a*(b+a) ≤ 2*b^2 := by
    calc a*(b+a) ≤ b*(b+b) := by gcongr
         _ = _ := by ring
  have frac : 1/a-1/b = (b-a)/(a*b) := by field_simp
  change 1/((x+1)*b) ≤ 2*(1/a-1/b)
  rw [frac, ← mul_div_assoc]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  have first : a ≤ 2*(b-a)*b^2 := by
    calc a = (b-a)*(a*(b+a)) := by rw [show (b-a)*(a*(b+a))=a*((b-a)*(b+a)) by ring,identity,mul_one]
         _ ≤ (b-a)*(2*b^2) := mul_le_mul_of_nonneg_left estimate (by linarith)
         _ = _ := by ring
  nlinarith [mul_le_mul_of_nonneg_right first bp.le]

private theorem sum_weight (n : ℕ) : ∑ i ∈ range n, weight (i+1) ≤ 3 := by
  have full (k : ℕ) : ∑ i ∈ range (k+1), weight (i+1) ≤ 3-2/Real.sqrt (k+1:ℕ) := by
    induction k with
    | zero => norm_num [weight]
    | succ k ih =>
      rw [sum_range_succ]
      have aux := tail_weight (x := (k:ℝ)+1) (by linarith [Nat.cast_nonneg (α := ℝ) k])
      unfold weight at ih ⊢
      push_cast at ih ⊢
      simp only [div_eq_mul_inv,one_mul] at aux ih ⊢
      linarith
  cases n with
  | zero => norm_num
  | succ k => exact (full k).trans (sub_le_self _ (by positivity))

private theorem bin_bound (U a b : ℕ) (ap : 0<a) (bp : 0<b) :
    ((U/(a*b)*((U/(a*b)).sqrt+1):ℕ):ℝ) ≤
      2*(U:ℝ)*Real.sqrt U * weight a * weight b := by
  let d := U/(a*b)
  let z := d.sqrt
  change ((d*(z+1):ℕ):ℝ) ≤ _
  by_cases zero : d=0
  · simp only [zero,zero_mul,Nat.cast_zero]
    unfold weight
    positivity
  have pos : 0<z := Nat.sqrt_pos.mpr (Nat.pos_of_ne_zero zero)
  have da : d*(a*b)≤U := Nat.div_mul_le_self ..
  have za : z^2*(a*b)≤U := (Nat.mul_le_mul_right _ (show z^2≤d by
    simpa [z,pow_two] using Nat.sqrt_le d)).trans da
  let A := Real.sqrt a
  let B := Real.sqrt b
  have hA : 0<A := Real.sqrt_pos.mpr (by exact_mod_cast ap)
  have hB : 0<B := Real.sqrt_pos.mpr (by exact_mod_cast bp)
  have zz : (z:ℝ)*A*B≤Real.sqrt U := Real.le_sqrt_of_sq_le (by
    rw [mul_pow,mul_pow,show A^2=a from Real.sq_sqrt (by positivity),
      show B^2=b from Real.sq_sqrt (by positivity)]
    exact_mod_cast (show z^2*a*b≤U by rwa [mul_assoc]))
  have dd : (d:ℝ)*(a*b)≤U := by exact_mod_cast da
  have dz : (z:ℝ)+1≤2*z := by exact_mod_cast (show z+1≤2*z by omega)
  calc ((d*(z+1):ℕ):ℝ) ≤ (2*(U:ℝ)*Real.sqrt U)/(((a:ℝ)*A)*((b:ℝ)*B)) := by
         apply (le_div_iff₀ (by positivity)).mpr
         push_cast
         calc _ ≤ (d*(2*(z:ℝ)))*(((a:ℝ)*A)*((b:ℝ)*B)) := by gcongr
              _ = 2*((d:ℝ)*(a*b))*((z:ℝ)*A*B) := by ring
              _ ≤ _ := by gcongr
       _ = _ := by simp [weight,A,B,div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm]

private theorem card_code (U : ℕ) : (Fintype.card (Code U):ℝ) ≤ 18*U*Real.sqrt U := by
  let C := 2*(U:ℝ)*Real.sqrt U
  let f (i : Fin U) := weight (i.val+1)
  have pos (i : Fin U) : 0≤f i := by dsimp [f,weight];positivity
  have sf : ∑ i : Fin U, f i ≤ 3 := by
    calc _ = ∑ i ∈ range U, weight (i+1) := Fin.sum_univ_eq_sum_range (fun i => weight (i+1)) U
         _ ≤ _ := sum_weight U
  have total : ∑ i : Fin U, ∑ j : Fin U, C*f i*f j = C*(∑ i : Fin U, f i)^2 := by
    simp only [← mul_sum, ← sum_mul]
    ring
  have upper : (Fintype.card (Code U):ℝ) ≤ ∑ i : Fin U, ∑ j : Fin U, C*f i*f j := by
    simp only [Code,Fintype.card_sigma,Fintype.card_prod,Fintype.card_fin,Nat.cast_sum]
    apply sum_le_sum
    intro i _
    apply sum_le_sum
    intro j _
    exact bin_bound U _ _ (Nat.succ_pos i.val) (Nat.succ_pos j.val)
  rw [total] at upper
  have sq := pow_le_pow_left₀ (sum_nonneg (fun i _ => pos i)) sf 2
  calc (Fintype.card (Code U):ℝ) ≤ C*(∑ i : Fin U, f i)^2 := upper
       _ ≤ C*3^2 := mul_le_mul_of_nonneg_left sq (by dsimp [C]; positivity)
       _ = _ := by dsimp [C];ring

/-- A count of distinct products with represented root below U; witnesses may
be nonunique. The bound is independent of the auxiliary exponent s. -/
theorem family_card {s U : ℕ} (products : Finset ℕ)
    (covered : ∀ n ∈ products, ∃ w : GroupedNormFrequency.Witness s, w.input=n ∧
      w.u*w.v+w.h*(w.a*w.b)<U) : (products.card:ℝ) ≤ 18*U*Real.sqrt U := by
  classical
  let pick (n : ↥products) := Classical.choose (covered n.val n.property)
  have spec (n : ↥products) := Classical.choose_spec (covered n.val n.property)
  let code (n : ↥products) := encode (pick n) (spec n).2
  have inj : Function.Injective code := by
    intro n m same
    exact Subtype.ext ((spec n).1.symm.trans ((encode_inj _ _ _ _ same).trans (spec m).1))
  have count := Fintype.card_le_of_injective _ inj
  have num : products.card ≤ Fintype.card (Code U) := by simpa using count
  exact (show (products.card:ℝ) ≤ Fintype.card (Code U) by exact_mod_cast num).trans (card_code U)

/-- Any choice of successful multipliers is included in the upper count. -/
theorem successes_card {U : ℕ} (ns : Finset ℕ) (bound : ∀ n∈ns, n.sqrt<U)
    (success : ∀ n∈ns, ∃ k p q, probe n k=some (p,q)) :
    (ns.card:ℝ) ≤ 18*U*Real.sqrt U := by
  apply family_card (s:=U)
  intro n mem
  obtain ⟨k,p,q,found⟩ := success n mem
  have padded : U≤2^(2*U) := (Nat.le_of_lt Nat.lt_two_pow_self).trans
    (Nat.pow_le_pow_right (by decide : 0<2) (show U≤2*U by omega))
  obtain ⟨w,eq⟩ := GroupedNormFrequency.witness_of_probe ((bound n mem).trans_le padded) found
  refine ⟨w,eq,?_⟩
  let T := w.u*w.v+w.h*(w.a*w.b)
  have hle : w.h≤T := (Nat.le_mul_of_pos_right _ (Nat.mul_pos w.apos w.bpos)).trans
    (Nat.le_add_left ..)
  have hw : n=T^2+w.h := eq.symm
  have floor : n.sqrt=T := by
    apply (Nat.eq_sqrt.mpr ⟨?_,?_⟩).symm <;> rw [hw] <;> nlinarith
  simpa only [floor] using bound n mem

/-- In the odd family the public multiplier 12 reconstructs the original
two factors in order; coprimality of 4 and 1+8j makes the decoder explicit. -/
theorem twelve_accepts (j h : ℕ) :
    let u := 1+8*j
    let v := 1+6*j
    u*v≤h →
      topProbe ((u^2+16*h)*(v^2+9*h))=some (u^2+16*h,v^2+9*h) := by
  intro u v cap
  let T := u*v+12*h
  let N := (u^2+16*h)*(v^2+9*h)
  have det : 4*v=3*u+1 := by dsimp [u,v]; ring
  have norm : N=T^2+h := by dsimp [N,T,u,v];ring
  have floor : N.sqrt=T := by
    apply (Nat.eq_sqrt.mpr ⟨?_,?_⟩).symm <;> rw [norm] <;> dsimp [T] <;> nlinarith
  have offset : N-T^2=h := by rw [norm]; omega
  have pos : 0<u*v := by dsimp [u,v]; positivity
  have s := topProbe_accepts floor offset (show 0<12 by decide)
    (show T=u*v+h*12 by dsimp [T];ring) pos cap
    (show (3*u)*(3*u+1)=12*(u*v) by rw [←det];ring)
  have gcd : (12:ℕ).gcd (3*u)=3 := by
    rw [Nat.gcd_rec,show 3*u%12=3 by dsimp [u];omega]
    decide
  have decode : fromRoot h 12 (3*u) = (u^2+16*h,v^2+9*h) := by
    simp only [fromRoot,gcd,show 12/3=4 by decide,←det,
      Nat.mul_div_cancel_left u (by decide : 0<3),Nat.mul_div_cancel_left v (by decide : 0<4)]
    congr 1 <;> ring
  exact s.trans (congrArg some decode)

set_option exponentiation.threshold 4096 in
/-- Conservative target-width bounds and the count for the odd band with X=2^506. -/
theorem odd_band_scale :
    48≤(244:ℕ) ∧ 2048<9*244 ∧ 2048<16*244 ∧
    (8:ℕ)^2+16*248<4096 ∧ (6:ℕ)^2+9*248<4096 ∧
    (4096:ℕ)^2<2*(12*244)^2 ∧
    4096*((2:ℕ)^506)^2=2^1024 ∧ 2*((2:ℕ)^506)^3=2^1519 := by decide +kernel

set_option exponentiation.threshold 4096 in
/-- Counts in the 2,048-bit comparison with U=2^1024. The last inequality
uses the same denominator for balanced prime pairs as GroupedNormFrequency. -/
theorem scale_2048 :
    ((2:ℕ)^1024/2)*((2:ℕ)^512/4) = 2^1533 ∧
    (18:ℕ)*2^1024*2^512=18*2^1536 ∧
    2^481*2*(18*2^1536)*71000^2 < 22^2*(2:ℕ)^(2*1023) := by decide +kernel

end PrimeFactors.GroupedNormDensity
