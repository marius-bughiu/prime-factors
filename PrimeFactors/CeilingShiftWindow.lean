import PrimeFactors.CeilingShiftPopulation

/-! A union bound for every center among the first T, allowing any positive
shift magnitude and counting each prime pair once. -/

namespace PrimeFactors.CeilingShiftWindow
open Finset MixedPrefixSample CeilingShiftPopulation
open private PrimeFactors.FloorSquareShiftPopulation.square_sum_aux
  PrimeFactors.FloorSquareShiftPopulation.root_sum_aux from PrimeFactors.FloorSquareShiftPopulation
open private PrimeFactors.MonotoneSumPopulation.data from PrimeFactors.MonotoneSumPopulation

set_option exponentiation.threshold 4096

def InWindow (T p q m : ℕ) : Prop := ceilSqrt (p*q)≤m ∧ m<ceilSqrt (p*q)+T

noncomputable def successes (T : ℕ) : Finset (ℕ×ℕ) := by
  classical exact eligible.filter fun z => ∃ m a, InWindow T z.1 z.2 m ∧ Hit z.1 z.2 m a

/-- The square excess throughout the first T centers is less than 2mT. -/
private theorem near {T p q m : ℕ} (pos : 0<p*q) (mem : InWindow T p q m) :
    m^2 < p*q+2*m*T := by
  let r := ceilSqrt (p*q)
  have rp : 0<r := by
    by_contra! h
    have := ceilSqrt_le_iff.mp h
    have bound : p*q≤0 := by simpa using this
    omega
  have lower : (r-1)^2<p*q := lt_of_not_ge fun h =>
    (by omega : ¬r≤r-1) (ceilSqrt_le_iff.mpr h)
  obtain ⟨lo,hi⟩ := mem
  change r≤m at lo
  change m<r+T at hi
  let i := m-(r-1)
  have rel : m=(r-1)+i := by dsimp [i]; omega
  have cap : i≤T := by dsimp [i]; omega
  have diff : m^2+i^2=(r-1)^2+2*m*i := by
    calc m^2+i^2 = ((r-1)+i)^2+i^2 := congrArg (fun t => t^2+i^2) rel
         _ = (r-1)^2+2*((r-1)+i)*i := by ring
         _ = _ := by rw [←rel]
  have comp := Nat.mul_le_mul_left (2*m) cap
  omega

private theorem coordinates {p q m a : ℕ} (order : p<q) (hit : Hit p q m a) :
    ∃ u x k, 0<u ∧ 0<x ∧ 0<k ∧ p+a=u*x^2 ∧ q+a=u*(x+k)^2 ∧
      p+q=2*m+u*k^2 ∧ m^2=p*q+a*u*k^2 := by
  obtain ⟨ap,test⟩ := hit
  obtain ⟨u,b,c,x,z,up,bp,cp,xp,zp,P,Q,_,one,_,_⟩ :=
    SquareScalePairCoordinates.coordinates (L:=1) (t:=1) (y:=m+a)
      (by omega : 0<p+a) (by omega : 0<q+a) zero_lt_one le_rfl (by simpa using test)
  have bc := Nat.eq_one_of_dvd_one one
  obtain rfl : b=1 := Nat.eq_one_of_dvd_one (bc ▸ dvd_mul_right b c)
  simp only [one_mul] at bc
  subst c
  simp only [mul_one] at P Q
  have lt : x<z := by
    by_contra! h
    have := Nat.mul_le_mul_left u (Nat.pow_le_pow_left h 2)
    omega
  let k := z-x
  have zk : z=x+k := by dsimp [k]; omega
  rw [zk] at Q
  have rt : m+a=u*x*(x+k) := by
    apply (Nat.pow_left_inj (by decide : 2≠0)).mp
    rw [←test,P,Q]
    ring
  have gap : p+q=2*m+u*k^2 := by nlinarith only [P,Q,rt]
  refine ⟨u,x,k,up,xp,Nat.sub_pos_of_lt lt,P,Q,gap,?_⟩
  nlinarith only [congrArg (·*a) gap,test]

private noncomputable def block (A D c l u v : ℕ) : Finset (ℕ×ℕ) :=
  ((Icc 1 ((A/u).sqrt)) ×ˢ (Icc 1 (D/(u*v^2)))).image fun w =>
    (c*u*w.1^2-w.2,c*u*(w.1+l*v)^2-w.2)

private noncomputable def cover (K A D c l : ℕ) : Finset (ℕ×ℕ) :=
  (Icc 1 K).biUnion fun u => (Icc 1 K).biUnion fun v => block A D c l u v

private theorem cover_count {K : ℕ} (kp : 0<K) (A D c l : ℕ) :
    ((cover K A D c l).card:ℝ)≤6*D*Real.sqrt A := by
  let f (u : ℕ) := 1/((u:ℝ)*Real.sqrt u)
  let g (v : ℕ) := 1/(v:ℝ)^2
  let C : ℝ := D*Real.sqrt A
  have block_cost (u v : ℕ) : ((block A D c l u v).card:ℝ)≤C*f u*g v := by
    have count : (block A D c l u v).card≤(A/u).sqrt*(D/(u*v^2)) :=
      card_image_le.trans_eq (by simp only [card_product,Nat.card_Icc,Nat.add_sub_cancel])
    have hr := (Real.nat_sqrt_le_real_sqrt (a:=A/u)).trans
      (Real.sqrt_le_sqrt (Nat.cast_div_le (α:=ℝ) (m:=A) (n:=u)))
    rw [Real.sqrt_div (Nat.cast_nonneg A)] at hr
    have hd : ((D/(u*v^2):ℕ):ℝ)≤(D:ℝ)/((u:ℝ)*v^2) := by
      calc _ ≤ (D:ℝ)/((u*v^2:ℕ):ℝ) := Nat.cast_div_le
           _ = _ := by push_cast; rfl
    have hc : ((block A D c l u v).card:ℝ)≤((A/u).sqrt:ℝ)*(D/(u*v^2):ℕ) := by exact_mod_cast count
    apply hc.trans ((mul_le_mul hr hd (by positivity) (by positivity)).trans_eq ?_)
    dsimp only [C,f,g]
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  have total : (cover K A D c l).card≤∑ u∈Icc 1 K, ∑ v∈Icc 1 K, (block A D c l u v).card :=
    card_biUnion_le.trans (sum_le_sum fun _ _ => card_biUnion_le)
  have realTotal := (Nat.cast_le (α:=ℝ)).mpr total
  push_cast at realTotal
  have bound : (∑ u∈Icc 1 K, f u)*(∑ v∈Icc 1 K, g v)≤3*2 := by
    apply mul_le_mul _ _ (by dsimp [g]; positivity) (by norm_num)
    · exact (PrimeFactors.FloorSquareShiftPopulation.root_sum_aux kp).trans (sub_le_self _ (by positivity))
    · exact (PrimeFactors.FloorSquareShiftPopulation.square_sum_aux kp).trans (sub_le_self _ (by positivity))
  calc _ ≤ _ := realTotal
       _ ≤ ∑ u∈Icc 1 K, ∑ v∈Icc 1 K, C*f u*g v :=
        sum_le_sum fun u _ => sum_le_sum fun v _ => block_cost u v
       _ = C*((∑ u∈Icc 1 K, f u)*(∑ v∈Icc 1 K, g v)) := by
         simp_rw [←mul_sum]; rw [←sum_mul,←mul_sum,mul_assoc]
       _ ≤ C*(3*2) := mul_le_mul_of_nonneg_left bound (by dsimp [C]; positivity)
       _ = _ := by dsimp [C]; ring

private theorem in_cover {K A D c l u v x a p q : ℕ} (up : 0<u) (vp : 0<v) (xp : 0<x)
    (ap : 0<a) (uu : u≤K) (vv : v≤K) (xx : u*x^2≤A) (aa : u*v^2*a≤D)
    (left : p+a=c*u*x^2) (right : q+a=c*u*(x+l*v)^2) : (p,q)∈cover K A D c l := by
  have xt : x≤(A/u).sqrt := Nat.le_sqrt'.mpr ((Nat.le_div_iff_mul_le up).mpr (by simpa [mul_comm] using xx))
  have at' : a≤D/(u*v^2) := (Nat.le_div_iff_mul_le (Nat.mul_pos up (pow_pos vp 2))).mpr
    (by simpa only [Nat.mul_comm a] using aa)
  refine mem_biUnion.mpr ⟨u,mem_Icc.mpr ⟨up,uu⟩,mem_biUnion.mpr ⟨v,mem_Icc.mpr ⟨vp,vv⟩,
    mem_image.mpr ⟨(x,a),mem_product.mpr ⟨mem_Icc.mpr ⟨xp,xt⟩,mem_Icc.mpr ⟨ap,at'⟩⟩,?_⟩⟩⟩
  apply Prod.ext
  · change c*u*x^2-a=p
    omega
  · change c*u*(x+l*v)^2-a=q
    omega

/-- Small magnitudes lie in two coordinate covers. A larger magnitude forces
the true midpoint into the first 2T ordinary Fermat centers. -/
private theorem classification {H T p q m a : ℕ} (p0 : 0<p) (lt : p<q) (height : q≤H)
    (op : Odd p) (oq : Odd q) (mem : InWindow T p q m) (hit : Hit p q m a) :
    (p,q)∈cover (2*H) H (H*T) 2 1 ∨ (p,q)∈cover (2*H) (2*H) (H*T/2) 1 2 ∨
    p+q∈FirstSumMenuPopulation.menu (2*T) (p*q) := by
  have earlier := before lt hit
  have mh : m≤H := by omega
  have ne := near (Nat.mul_pos p0 (p0.trans lt)) mem
  have cap := Nat.mul_le_mul_right T (Nat.mul_le_mul_left 2 mh)
  obtain ⟨u,x,k,up,xp,kp,P,Q,gap,eqn⟩ := coordinates lt hit
  have work : a*u*k^2<2*H*T := by omega
  by_cases small : a≤H
  · have boundP : u*x^2≤2*H := by omega
    have boundQ : u*(x+k)^2≤2*H := by omega
    have uu : u≤2*H := (Nat.le_mul_of_pos_right u (pow_pos xp 2)).trans boundP
    have kk : k≤2*H := calc
      k ≤ x+k := Nat.le_add_left _ _
      _ ≤ (x+k)^2 := Nat.le_self_pow (by decide) _
      _ ≤ u*(x+k)^2 := Nat.le_mul_of_pos_left _ up
      _ ≤ _ := boundQ
    have even : 2∣u*k^2 := by obtain ⟨i,hi⟩ := op; obtain ⟨j,hj⟩ := oq; omega
    rcases Nat.prime_two.dvd_mul.mp even with eu|ek
    · obtain ⟨v,rfl⟩ := eu
      apply Or.inl
      apply in_cover (u:=v) (v:=k) (x:=x) (a:=a) (by omega) kp xp hit.1 (by omega) kk
      · nlinarith only [boundP]
      · nlinarith only [work]
      · simpa only [one_mul] using P
      · simpa only [one_mul] using Q
    · obtain ⟨v,rfl⟩ := Nat.prime_two.dvd_of_dvd_pow ek
      apply Or.inr ∘ Or.inl
      apply in_cover (u:=u) (v:=v) (x:=x) (a:=a) up (by omega) xp hit.1 uu (by omega) boundP
      · apply (Nat.le_div_iff_mul_le (by decide : 0<2)).mpr
        nlinarith only [work]
      · simpa only [one_mul] using P
      · simpa only [one_mul] using Q
  · apply Or.inr ∘ Or.inr
    have less : H*(u*k^2)<H*(2*T) := calc
      _ ≤ a*(u*k^2) := Nat.mul_le_mul_right _ (by omega)
      _ < _ := by simpa only [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using work
    have short := Nat.lt_of_mul_lt_mul_left less
    obtain ⟨b,hb⟩ := op
    obtain ⟨c,hc⟩ := oq
    let M := (p+q)/2
    have mid : p+q=2*M := by dsimp [M]; omega
    refine mem_image.mpr ⟨M-ceilSqrt (p*q),mem_range.mpr ?_,?_⟩
    · obtain ⟨_,hi⟩ := mem; omega
    · change 2*(ceilSqrt (p*q)+(M-ceilSqrt (p*q)))=p+q
      obtain ⟨lo,_⟩ := mem
      omega

@[simp] theorem mem_successes {T : ℕ} {z : ℕ×ℕ} : z∈successes T ↔
    z∈eligible ∧ ∃ m a, InWindow T z.1 z.2 m ∧ Hit z.1 z.2 m a := by
  classical exact mem_filter

attribute [local irreducible] eligible MixedPrefixSample.primes cover successes sample
set_option maxRecDepth 2048
private abbrev H := 2^1024
private abbrev T := 2^40

private theorem small_count :
    (cover (2*H) H (H*T) 2 1 ∪ cover (2*H) (2*H) (H*T/2) 1 2).card≤11*2^1576 := by
  have kp : 0<2*H := by decide +kernel
  have c := cover_count kp H (H*T) 2 1
  have d := cover_count kp (2*H) (H*T/2) 1 2
  have root : Real.sqrt ((H:ℕ):ℝ)=(2:ℝ)^512 := by
    rw [show H=(2^512)^2 by decide +kernel,Nat.cast_pow,
      Real.sqrt_sq (Nat.cast_nonneg _),Nat.cast_pow,Nat.cast_ofNat]
  have root2 : Real.sqrt (((2*H:ℕ):ℝ))≤3*(2:ℝ)^511 := by
    apply (Real.sqrt_le_left (by positivity)).mpr
    norm_num [H]
  rw [root] at c
  have rr := mul_le_mul_of_nonneg_left root2 (show 0≤6*((H*T/2:ℕ):ℝ) by positivity)
  have capD := d.trans rr
  have boundC : (cover (2*H) H (H*T) 2 1).card≤6*2^1576 := by
    have num : 6*((H*T:ℕ):ℝ)*2^512=6*(2:ℝ)^1576 := by norm_num [H,T]
    exact_mod_cast c.trans_eq num
  have boundD : (cover (2*H) (2*H) (H*T/2) 1 2).card≤5*2^1576 := by
    have num : 6*((H*T/2:ℕ):ℝ)*(3*2^511)≤5*(2:ℝ)^1576 := by norm_num [H,T]
    exact_mod_cast capD.trans num
  exact (card_union_le _ _).trans ((Nat.add_le_add boundC boundD).trans_eq (by ring))

private noncomputable def smallPairs := cover (2*H) H (H*T) 2 1 ∪ cover (2*H) (2*H) (H*T/2) 1 2
private noncomputable def earlyPairs := sample (FirstSumMenuPopulation.event (2*T))

private theorem partition : successes T⊆smallPairs∪earlyPairs := by
  classical
  rintro ⟨p,q⟩ mem
  obtain ⟨ok,m,a,win,hit⟩ := mem_successes.mp mem
  obtain ⟨lt,hi⟩ := PrimeFactors.MonotoneSumPopulation.data ok
  obtain ⟨op,oq⟩ := CeilingShiftPopulation.odd_factors ok
  have p0 : 0<p := by obtain ⟨v,hv⟩ := op; change p=2*v+1 at hv; omega
  rcases classification p0 lt hi.le op oq win hit with c|d|f
  · exact mem_union_left _ (mem_union_left _ c)
  · exact mem_union_left _ (mem_union_right _ d)
  · exact mem_union_right _ (FirstSumMenuPopulation.mem_sample_iff.mpr ⟨ok,f⟩)

attribute [local irreducible] smallPairs earlyPairs

private theorem price_arithmetic {c e : ℕ} (hc : c≤11*2^1576)
    (supply : 2^2046<21000000*e) : 8*2^442*c<7*e := by
  have room : 21000000*(8*2^442*(11*2^1576))≤7*2^2046 := by decide +kernel
  have price := Nat.mul_lt_mul_of_pos_left supply (by decide : 0<7)
  apply Nat.lt_of_mul_lt_mul_left (a:=21000000)
  calc 21000000*(8*2^442*c) ≤ 21000000*(8*2^442*(11*2^1576)) :=
         Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hc)
       _ ≤ _ := room
       _ < 7*(21000000*e) := price
       _ = _ := by ring

private theorem small_price : 8*2^442*smallPairs.card<7*eligible.card := by
  apply price_arithmetic _ ChebyshevPrimeSample.eligible_count
  rw [smallPairs]
  exact small_count

private theorem large_price : 8*2^442*earlyPairs.card<eligible.card := by
  have big := CyclotomicDiagonalPopulation.menu_fraction (J:=2*T) (G:=2^534) (m:=2^445)
    (by decide +kernel) (by decide +kernel)
  rw [CyclotomicDiagonalPopulation.compatible_eq] at big
  rw [earlyPairs,show 8*2^442=2^445 by decide +kernel]
  exact big

/-- Granting an arbitrary shift and any center among the first 2^40 still
covers fewer than one in 2^442 of the eligible full-width prime pairs. -/
theorem full_width : 2^442*(successes (2^40)).card<eligible.card := by
  have count := (card_le_card partition).trans (card_union_le _ _)
  have combine {n c f e v : ℕ} (total : n≤c+f) (h1 : 8*v*c<7*e) (h2 : 8*v*f<e) :
      v*n<e := by
    have sum := Nat.mul_le_mul_left (8*v) total
    rw [Nat.mul_add] at sum
    apply Nat.lt_of_mul_lt_mul_left (a:=8)
    rw [←Nat.mul_assoc]
    omega
  exact combine count small_price large_price

end PrimeFactors.CeilingShiftWindow
