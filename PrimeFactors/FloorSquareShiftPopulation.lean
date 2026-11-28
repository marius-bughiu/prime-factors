import PrimeFactors.FloorSquareShift
import PrimeFactors.MonotoneSumPopulation

/-! Even if all positive integer shifts are allowed, only a bounded number of factor
pairs up to a common height can have a shifted square at the public floor. -/

namespace PrimeFactors.FloorSquareShiftPopulation

open Finset FloorSquareShift

private theorem square_step {n : ℝ} (pos : 0<n) :
    1/(n+1)^2 ≤ 1/n-1/(n+1) := by
  have np : 0<n+1 := by positivity
  calc 1/(n+1)^2 ≤ 1/(n*(n+1)) := by
         apply one_div_le_one_div_of_le (by positivity)
         nlinarith only [np]
       _ = _ := by field_simp

private theorem root_step {n : ℝ} (pos : 0<n) :
    1/((n+1)*Real.sqrt (n+1)) ≤ 2/Real.sqrt n-2/Real.sqrt (n+1) := by
  let a := Real.sqrt n
  let b := Real.sqrt (n+1)
  have ap : 0<a := Real.sqrt_pos.mpr pos
  have bp : 0<b := Real.sqrt_pos.mpr (by positivity)
  have ab : a≤b := Real.sqrt_le_sqrt (by linarith)
  have eqn : (b-a)*(b+a)=1 := by
    have aa : a^2=n := Real.sq_sqrt pos.le
    have bb : b^2=n+1 := Real.sq_sqrt (by positivity)
    nlinarith only [aa,bb]
  change 1/((n+1)*b)≤2/a-2/b
  rw [←show b^2=n+1 from Real.sq_sqrt (by positivity)]
  calc
    _ ≤ 2/(a*b*(b+a)) := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      have h1 : a*(b+a)≤b*(b+b) := mul_le_mul ab (by linarith) (by positivity) bp.le
      nlinarith only [mul_le_mul_of_nonneg_right h1 bp.le]
    _ = 2/a-2/b := by
      field_simp
      linear_combination -(2*a*b)*eqn

private theorem square_sum_aux {H : ℕ} (hp : 0<H) :
    ∑ k∈Icc 1 H, 1/(k:ℝ)^2 ≤ 2-1/(H:ℝ) := by
  induction H with
  | zero => omega
  | succ n ih =>
    by_cases z : n=0
    · subst n; norm_num
    have pos : 0<n := Nat.pos_of_ne_zero z
    rw [sum_Icc_succ_top (by omega : 1≤n+1),Nat.cast_succ]
    linarith only [ih pos,square_step (n:=(n:ℝ)) (by exact_mod_cast pos)]

private theorem root_sum_aux {H : ℕ} (hp : 0<H) :
    ∑ u∈Icc 1 H, 1/((u:ℝ)*Real.sqrt u) ≤ 3-2/Real.sqrt H := by
  induction H with
  | zero => omega
  | succ n ih =>
    by_cases z : n=0
    · subst n; norm_num
    have pos : 0<n := Nat.pos_of_ne_zero z
    rw [sum_Icc_succ_top (by omega : 1≤n+1),Nat.cast_succ]
    linarith only [ih pos,root_step (n:=(n:ℝ)) (by exact_mod_cast pos)]

private noncomputable def block (H u k : ℕ) : Finset (ℕ×ℕ) :=
  ((Icc 1 ((H/u).sqrt)) ×ˢ (Icc 1 (2*H/(u*k^2)))).image fun z =>
    (z.2+u*z.1^2,z.2+u*(z.1+k)^2)

private noncomputable def properCover (H : ℕ) : Finset (ℕ×ℕ) :=
  (Icc 1 H).biUnion fun u => (Icc 1 H).biUnion fun k => block H u k

private noncomputable def edge (H : ℕ) : Finset (ℕ×ℕ) :=
  ((Icc 1 H) ×ˢ (Icc 1 2)).image fun w => (w.1,w.1+w.2)

private theorem block_bound (H u k : ℕ) :
    ((block H u k).card:ℝ)≤2*H*Real.sqrt H*(1/((u:ℝ)*Real.sqrt u))*(1/(k:ℝ)^2) := by
  have count : (block H u k).card ≤ (H/u).sqrt*(2*H/(u*k^2)) :=
    card_image_le.trans_eq (by simp only [card_product,Nat.card_Icc,Nat.add_sub_cancel])
  have hr := (Real.nat_sqrt_le_real_sqrt (a:=H/u)).trans
    (Real.sqrt_le_sqrt (Nat.cast_div_le (α:=ℝ) (m:=H) (n:=u)))
  rw [Real.sqrt_div (Nat.cast_nonneg H)] at hr
  have hq : ((2*H/(u*k^2):ℕ):ℝ)≤(2*(H:ℝ))/((u:ℝ)*k^2) := by
    calc _ ≤ ((2*H:ℕ):ℝ)/((u*k^2:ℕ):ℝ) := Nat.cast_div_le
         _ = _ := by push_cast; ring
  have hc : ((block H u k).card:ℝ) ≤ ((H/u).sqrt:ℝ)*(2*H/(u*k^2):ℕ) := by exact_mod_cast count
  apply hc.trans ((mul_le_mul hr hq (by positivity) (by positivity)).trans_eq ?_)
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

private theorem proper_count (H : ℕ) (hp : 0<H) :
    ((properCover H).card:ℝ)≤12*H*Real.sqrt H := by
  have base : (properCover H).card≤∑ u∈Icc 1 H, ∑ k∈Icc 1 H, (block H u k).card :=
    card_biUnion_le.trans (sum_le_sum fun _ _ => card_biUnion_le)
  have baseR := (Nat.cast_le (α:=ℝ)).mpr base
  push_cast at baseR
  apply baseR.trans
  let C : ℝ := 2*H*Real.sqrt H
  let f (u : ℕ) := 1/((u:ℝ)*Real.sqrt u)
  let g (k : ℕ) := 1/(k:ℝ)^2
  have both : (∑ u∈Icc 1 H, f u)*(∑ k∈Icc 1 H, g k)≤3*2 := by
    apply mul_le_mul _ _ (by dsimp [g]; positivity) (by norm_num)
    · exact (root_sum_aux hp).trans (sub_le_self _ (by positivity))
    · exact (square_sum_aux hp).trans (sub_le_self _ (by positivity))
  calc _ ≤ ∑ u∈Icc 1 H, ∑ k∈Icc 1 H, C*f u*g k :=
           sum_le_sum fun u _ => sum_le_sum fun k _ => block_bound H u k
       _ = C*((∑ u∈Icc 1 H, f u)*(∑ k∈Icc 1 H, g k)) := by
         simp_rw [←mul_sum]
         rw [←sum_mul,←mul_sum,mul_assoc]
       _ ≤ C*(3*2) := mul_le_mul_of_nonneg_left both (by dsimp [C]; positivity)
       _ = _ := by dsimp [C]; ring

private theorem in_cover {p q h H : ℕ} (lt : p<q) (height : q≤H) (hs : shift p q h) :
    (p,q)∈properCover H ∪ edge H := by
  by_cases prop : h<p
  · obtain ⟨u,x,k,up,xp,kp,P,Q,_,_,bound⟩ := coordinates lt prop hs
    have xq : u*x^2≤H := by omega
    have zq : u*(x+k)^2≤H := by omega
    have usmall := (Nat.le_mul_of_pos_right u (pow_pos xp 2)).trans xq
    have ksmall : k≤H := calc
      k ≤ x+k := Nat.le_add_left _ _
      _ ≤ (x+k)^2 := Nat.le_self_pow (by decide) _
      _ ≤ u*(x+k)^2 := Nat.le_mul_of_pos_left _ up
      _ ≤ H := zq
    have hbound : h≤2*H/(u*k^2) := by
      apply (Nat.le_div_iff_mul_le (Nat.mul_pos up (pow_pos kp 2))).mpr
      rw [←mul_assoc]
      apply bound.trans (Nat.mul_le_mul_left 2 _)
      exact (Nat.sqrt_le_sqrt ((Nat.mul_le_mul_right q lt.le).trans
        (Nat.mul_le_mul height height))).trans_eq (Nat.sqrt_eq H)
    have xbound : x≤(H/u).sqrt :=
      Nat.le_sqrt'.mpr ((Nat.le_div_iff_mul_le up).mpr (by simpa [mul_comm] using xq))
    apply mem_union_left
    exact mem_biUnion.mpr ⟨u,mem_Icc.mpr ⟨up,usmall⟩,
      mem_biUnion.mpr ⟨k,mem_Icc.mpr ⟨kp,ksmall⟩,mem_image.mpr
        ⟨(x,h),mem_product.mpr ⟨mem_Icc.mpr ⟨xp,xbound⟩,mem_Icc.mpr ⟨hs.1,hbound⟩⟩,
          Prod.ext P.symm Q.symm⟩⟩⟩
  · obtain ⟨hp,hle,hit⟩ := hs
    have hpEq : h=p := by omega
    subst h
    have rlo : p≤(p*q).sqrt := Nat.le_sqrt'.mpr (by simpa [pow_two] using Nat.mul_le_mul_left p lt.le)
    have zero : ((p*q).sqrt-p)^2=0 := by simpa only [Nat.sub_self,zero_mul] using hit.symm
    have eqn : (p*q).sqrt=p := by
      by_contra ne
      exact (pow_pos (Nat.sub_pos_of_lt (by omega : p<(p*q).sqrt)) 2).ne' zero
    have top := Nat.lt_succ_sqrt' (p*q)
    rw [eqn] at top
    have small : q≤p+2 := Nat.le_of_mul_le_mul_left (by nlinarith only [top] : p*q≤p*(p+2)) hp
    exact mem_union_right _ (mem_image.mpr ⟨(p,q-p),mem_product.mpr
      ⟨mem_Icc.mpr ⟨hp,lt.le.trans height⟩,mem_Icc.mpr ⟨by omega,by omega⟩⟩,
      Prod.ext rfl (by dsimp; omega)⟩)

/-- A finite height bound for all shifted-square witnesses, including equality at h=p. -/
theorem finite_count (A : Finset (ℕ×ℕ)) {H : ℕ} (hp : 0<H)
    (data : ∀ v∈A, v.1<v.2 ∧ v.2≤H ∧ ∃ h, shift v.1 v.2 h) :
    (A.card:ℝ) ≤ 12*H*Real.sqrt H+2*H := by
  have sub : A⊆properCover H ∪ edge H := by
    rintro ⟨p,q⟩ hv
    obtain ⟨lt,high,h,hs⟩ := data _ hv
    exact in_cover lt high hs
  have cardEdge : (edge H).card≤2*H :=
    card_image_le.trans_eq (by simp only [card_product,Nat.card_Icc,Nat.add_sub_cancel,Nat.mul_comm])
  have h := (card_le_card sub).trans ((card_union_le _ _).trans (Nat.add_le_add_left cardEdge _))
  have hr := (Nat.cast_le (α:=ℝ)).mpr h
  push_cast at hr
  linarith only [hr,proper_count H hp]

open MixedPrefixSample
open private PrimeFactors.MonotoneSumPopulation.data from PrimeFactors.MonotoneSumPopulation

attribute [local irreducible] eligible MixedPrefixSample.primes
set_option exponentiation.threshold 4096

noncomputable def successes : Finset (ℕ×ℕ) := by
  classical
  exact eligible.filter fun v => ∃ h, shift v.1 v.2 h

/-- Among the full-size eligible prime pairs, even granting every possible shift,
the fraction admitting a successful witness is less than one in 2^482. -/
theorem full_width : 2^482*successes.card < eligible.card := by
  classical
  have count := finite_count successes (H:=2^1024) (by decide +kernel) (by
    intro v hv
    obtain ⟨ok,test⟩ := mem_filter.mp hv
    obtain ⟨lt,hi⟩ := PrimeFactors.MonotoneSumPopulation.data ok
    exact ⟨lt,hi.le,test⟩)
  have rt : Real.sqrt (((2^1024:ℕ):ℝ))=(2:ℝ)^512 := by
    rw [show (2^1024:ℕ)=(2^512)^2 by decide +kernel,Nat.cast_pow,
      Real.sqrt_sq (Nat.cast_nonneg _),Nat.cast_pow,Nat.cast_ofNat]
  rw [rt,Nat.cast_pow,Nat.cast_ofNat] at count
  have hn : successes.card≤12*(2:ℕ)^1024*2^512+2*2^1024 := by exact_mod_cast count
  have room : 21000000*(2^482*(12*(2:ℕ)^1024*2^512+2*2^1024))≤2^2046 := by decide +kernel
  exact Nat.lt_of_mul_lt_mul_left ((Nat.mul_le_mul_left 21000000 (Nat.mul_le_mul_left _ hn)).trans_lt
    (room.trans_lt ChebyshevPrimeSample.eligible_count))

end PrimeFactors.FloorSquareShiftPopulation
