import PrimeFactors.SmallRadixPackingPopulation
import PrimeFactors.ChebyshevPrimeSample

/-! How much a menu of factor sums can cover when selected from the actual
high product word, square-root anchor, width quotients, and extra advice.
The counting argument uses the monotonicity of p(s-p) on the smaller-factor
branch. It does not make a uniformity assumption about prime residues. -/
namespace PrimeFactors.ActualWindowAdvice

open Finset MixedPrefixSample

set_option exponentiation.threshold 4096
set_option maxRecDepth 4096

/-- The information used to form the public sum interval, including an entire
high product word and the residue that determines its initial stride and phase. -/
structure View where
  high : ℕ
  root : ℕ
  leftQuot : ℕ
  rightQuot : ℕ
  residue : ℕ
deriving DecidableEq

def view (x n : ℕ) : View :=
  ⟨n/(2*x),ceilSqrt n,n/x,n/(2*x-1),n%24⟩

/-- The two observed quotients and the square-root anchor reconstruct both
endpoints of the interval used by the width search. -/
theorem endpoints (x n : ℕ) :
    ProductDeficitBand.lower n x=max (2*x+1) (2*(view x n).root-1) ∧
    ProductDeficitBand.upper n x=min (4*x)
      (2*(min (x+(view x n).leftQuot) ((2*x-1)+(view x n).rightQuot)/2)) := ⟨rfl,rfl⟩

theorem stride_from_view (x n : ℕ) :
    CyclotomicRadixLift.stride (view x n).residue=CyclotomicRadixLift.stride n := by
  simp only [view,CyclotomicRadixLift.stride,CyclotomicRadixLift.weight,CyclotomicRadixLift.bonus,
    Nat.mod_mod_of_dvd n (by decide : 4∣24),Nat.mod_mod_of_dvd n (by decide : 3∣24)]

/-- For fixed high word, both width quotients and the square-root anchor have
only a constant number of choices. -/
private noncomputable def views (x h : ℕ) : Finset View :=
  ((range 2) ×ˢ ((range 2) ×ˢ ((range 3) ×ˢ (range 24)))).image fun (r,l,u,c) =>
    ⟨h,ceilSqrt (2*x*h)+r,2*h+l,h+u,c⟩

private theorem views_card (x h : ℕ) : (views x h).card≤288 := by
  apply card_image_le.trans
  simp only [card_product,card_range]
  decide

private theorem word_bounds (n b : ℕ) (bp : 0<b) : b*(n/b)≤n ∧ n<b*(n/b)+b :=
  ⟨Nat.mul_div_le n b,by simpa only [Nat.mul_add,Nat.mul_one] using Nat.lt_mul_div_succ n bp⟩

theorem view_in_word {x n : ℕ} (xp : 1<x) (lo : 2*x^2≤n) (hi : n<(2*x)^2) :
    view x n∈views x (n/(2*x)) := by
  let b := 2*x
  let h := n/b
  let r := ceilSqrt (b*h)
  have bp : 0<b := by dsimp [b]; omega
  obtain ⟨low,high⟩ : b*h≤n ∧ n<b*h+b := word_bounds n b bp
  have hsmall : h<b := (Nat.div_lt_iff_lt_mul bp).mpr (by simpa only [b,pow_two] using hi)
  have hx : x≤h := (Nat.le_div_iff_mul_le bp).mpr (by dsimp [b]; nlinarith only [lo])
  have sq : b*h≤r^2 := ceilSqrt_le_iff.mp le_rfl
  have rx : x≤r := by
    by_contra! bad
    have less := Nat.pow_lt_pow_left bad (by decide : 2≠0)
    dsimp [b] at sq
    nlinarith only [sq,less,Nat.mul_le_mul_left x hx,Nat.zero_le (x*x)]
  have lr : r≤ceilSqrt n := ceilSqrt_le_iff.mpr (low.trans (ceilSqrt_le_iff.mp le_rfl))
  have ur : ceilSqrt n≤r+1 := ceilSqrt_le_iff.mpr (by dsimp only [b] at high sq; nlinarith only [high,sq,rx])
  have leftlo : 2*h≤n/x := (Nat.le_div_iff_mul_le (by omega)).mpr (by dsimp [b] at low; nlinarith only [low])
  have lefthi : n/x<2*h+2 := (Nat.div_lt_iff_lt_mul (by omega)).mpr (by dsimp [b] at high; nlinarith only [high])
  have bd : b=(b-1)+1 := by omega
  have rightlo : h≤n/(b-1) := (Nat.le_div_iff_mul_le (by dsimp [b]; omega)).mpr
    ((Nat.mul_le_mul_left h (Nat.sub_le b 1)).trans (by simpa [Nat.mul_comm] using low))
  have rbound : n/(b-1)<h+3 := by
    apply (Nat.div_lt_iff_lt_mul (by dsimp [b]; omega)).mpr
    calc n < b*h+b := high
         _ ≤ (h+3)*(b-1) := by
           have b2 : 2≤b := by dsimp [b]; omega
           nlinarith only [hsmall,b2,bd,congrArg (fun z => z*h) bd]
  apply mem_image.mpr
  refine ⟨(ceilSqrt n-r,n/x-2*h,n/(b-1)-h,n%24),?_,?_⟩
  · simp only [mem_product,mem_range]
    exact ⟨by omega,by omega,by omega,Nat.mod_lt _ (by decide)⟩
  · change View.mk h (r+(ceilSqrt n-r)) (2*h+(n/x-2*h)) (h+(n/(b-1)-h)) (n%24)=_
    rw [Nat.add_sub_of_le lr,Nat.add_sub_of_le leftlo,Nat.add_sub_of_le rightlo]
    rfl

/-- Two increasing smaller factors with the same sum have products separated by
at least the smaller-factor separation times a lower bound on the factor gap. -/
theorem product_spacing {a b p q u d : ℕ} (step : p+u≤a) (gap : a+d≤b)
    (sum : p+q=a+b) : p*q+u*d≤a*b := by
  obtain ⟨z,hz⟩ := Nat.exists_eq_add_of_le (show p≤a by omega)
  obtain ⟨y,hy⟩ := Nat.exists_eq_add_of_le (show p+d≤b by omega)
  have shift : q=b+z := by omega
  have scaled := Nat.mul_le_mul_right d (show u≤z by omega)
  rw [hz,shift,hy]
  nlinarith only [scaled,Nat.zero_le (y*z)]

private theorem next_residue {a b u : ℕ} (lt : a<b) (same : a%u=b%u) : a+u≤b := by
  have qlt : a/u<b/u := by
    by_contra! wrong
    have := Nat.mul_le_mul_left u wrong
    have aa := Nat.mod_add_div a u
    have bb := Nat.mod_add_div b u
    omega
  have prod := Nat.mul_le_mul_left u (show a/u+1≤b/u by omega)
  rw [Nat.mul_add,Nat.mul_one] at prod
  have aa := Nat.mod_add_div a u
  have bb := Nat.mod_add_div b u
  omega

private theorem far_unique {B U D : ℕ} (bp : 0<B) (width : B≤U*D)
    {p q a b : ℕ} (g1 : p+D≤q) (g2 : a+D≤b)
    (word : p*q/B=a*b/B) (sums : p+q=a+b) (res : p%U=a%U) : (p,q)=(a,b) := by
  have exclude {p q a b : ℕ} (smaller : p<a) (gap : a+D≤b) (eq : p*q/B=a*b/B)
      (es : p+q=a+b) (er : p%U=a%U) : False := by
    have sep := product_spacing (next_residue smaller er) gap es
    have top := (word_bounds (a*b) B bp).2
    have bot := (word_bounds (p*q) B bp).1
    rw [←eq] at top
    omega
  rcases lt_trichotomy p a with lt|eq|gt
  · exact (exclude lt g2 word sums res).elim
  · exact Prod.ext eq (by omega)
  · exact (exclude gt g1 word.symm sums.symm res.symm).elim

private theorem near_count {B D : ℕ} (S : Finset (ℕ×ℕ))
    (bounds : ∀ z∈S, z.1<B ∧ z.1≤z.2 ∧ z.2<z.1+D) : S.card≤B*D := by
  calc S.card ≤ ((range B) ×ˢ (range D)).card := by
         apply card_le_card_of_injOn (fun (z : ℕ×ℕ) => (z.1,z.2-z.1))
         · intro z hz
           obtain ⟨p,_,gap⟩ := bounds z hz
           exact mem_product.mpr ⟨mem_range.mpr p,mem_range.mpr (by omega)⟩
         · intro a ha b hb eq
           have p := congrArg Prod.fst eq
           have g := congrArg Prod.snd eq
           obtain ⟨_,oa,_⟩ := bounds a ha
           obtain ⟨_,ob,_⟩ := bounds b hb
           change a.1=b.1 at p
           change a.2-a.1=b.2-b.1 at g
           exact Prod.ext p (by omega)
       _ = _ := by rw [card_product,card_range,card_range]

private theorem far_count {B D U J : ℕ} (bp : 0<B) (up : 0<U) (width : B≤U*D)
    (S : Finset (ℕ×ℕ)) (row : ℕ → Finset ℕ) (cap : ∀ h, (row h).card≤J)
    (bounds : ∀ z∈S, z.1*z.2/B<B ∧ z.1+D≤z.2 ∧ z.1+z.2∈row (z.1*z.2/B)) :
    S.card≤B*(J*U) := by
  let code (z : ℕ×ℕ) : Σ _ : ℕ, ℕ×ℕ := ⟨z.1*z.2/B,z.1+z.2,z.1%U⟩
  calc S.card ≤ ((range B).sigma (fun h => (row h) ×ˢ (range U))).card := by
         apply card_le_card_of_injOn code
         · intro z hz
           obtain ⟨h,_,s⟩ := bounds z hz
           exact mem_sigma.mpr ⟨mem_range.mpr h,mem_product.mpr ⟨s,mem_range.mpr (Nat.mod_lt _ up)⟩⟩
         · rintro ⟨p,q⟩ ha ⟨a,b⟩ hb eq
           have heq := congrArg Sigma.fst eq
           have se := congrArg (fun (v : Σ _ : ℕ, ℕ×ℕ) => v.2.1) eq
           have re := congrArg (fun (v : Σ _ : ℕ, ℕ×ℕ) => v.2.2) eq
           exact far_unique bp width (bounds _ ha).2.1 (bounds _ hb).2.1 heq se re
       _ ≤ ∑ _h∈range B, J*U := by
         rw [card_sigma]
         apply sum_le_sum
         intro h _
         simpa only [card_product,card_range] using Nat.mul_le_mul_right U (cap h)
       _ = _ := by simp

attribute [local irreducible] ordered sample primes eligible

/-- All eligible prime pairs for which the menu contains the correct sum. -/
noncomputable def hits (menu : View → Finset ℕ) : Finset (ℕ×ℕ) :=
  eligible.filter fun z => z.1+z.2 ∈ menu (view X (z.1*z.2))

private theorem hit_data {menu : View → Finset ℕ} {z : ℕ×ℕ} (inside : z∈hits menu) :
    z.1<2*X ∧ z.1≤z.2 ∧ 2*X^2≤z.1*z.2 ∧ z.1*z.2<(2*X)^2 ∧
    z.1+z.2∈menu (view X (z.1*z.2)) := by
  rw [hits,mem_filter] at inside
  obtain ⟨pair,found⟩ := inside
  rw [eligible,sample,mem_filter] at pair
  obtain ⟨p,q,_,lo,_⟩ := (mem_ordered (z:=z) (E:=fun _ => True)).mp pair.1
  simp only [primes,mem_filter,mem_Ico] at p q
  have pos : 0<2*X := by decide +kernel
  have hi := Nat.mul_lt_mul_of_lt_of_le p.1.2 q.1.2.le pos
  exact ⟨p.1.2,pair.2.le,lo,by simpa only [pow_two] using hi,found⟩

private theorem count_parts {α : Type*} (S : Finset α) (f : α → Prop) [DecidablePred f]
    {a b : ℕ} (low : (S.filter f).card≤a) (high : (S.filter fun z => ¬f z).card≤b) :
    S.card≤a+b := by
  calc S.card = _ := (filter_card_add_filter_neg_card_eq_card (s:=S) f).symm
       _ ≤ _ := Nat.add_le_add low high

attribute [local irreducible] views

private noncomputable def wordMenu (x h : ℕ) (menu : View → Finset ℕ) :=
  (views x h).biUnion menu

private theorem word_cap (x h J : ℕ) (menu : View → Finset ℕ) (cap : ∀ v, (menu v).card≤J) :
    (wordMenu x h menu).card≤288*J :=
  (card_biUnion_le_card_mul (views x h) menu J (fun v _ => cap v)).trans
    (Nat.mul_le_mul_right J (views_card x h))

private theorem word_mem {x n s : ℕ} (menu : View → Finset ℕ) (xp : 1<x) (lo : 2*x^2≤n)
    (hi : n<(2*x)^2) (found : s∈menu (view x n)) : s∈wordMenu x (n/(2*x)) menu := by
  unfold wordMenu
  exact mem_biUnion.mpr ⟨view x n,view_in_word xp lo hi,found⟩

attribute [local irreducible] wordMenu

private theorem partition_count {x J D U : ℕ} (xp : 1<x) (up : 0<U) (width : 2*x≤U*D)
    (S : Finset (ℕ×ℕ)) (menu : View → Finset ℕ) (cap : ∀ v, (menu v).card≤J)
    (data : ∀ z∈S, z.1<2*x ∧ z.1≤z.2 ∧ 2*x^2≤z.1*z.2 ∧ z.1*z.2<(2*x)^2 ∧
      z.1+z.2∈menu (view x (z.1*z.2))) :
    S.card≤2*x*D+2*x*((288*J)*U) := by
  let close := fun z : ℕ×ℕ => z.2<z.1+D
  have low := near_count (S.filter close) (B:=2*x) (D:=D) (by
    intro z hz
    obtain ⟨inside,gap⟩ := mem_filter.mp hz
    exact ⟨(data z inside).1,(data z inside).2.1,gap⟩)
  have pos : 0<2*x := by omega
  have high := far_count pos up width (S.filter fun z => ¬close z)
    (fun h => wordMenu x h menu) (fun h => word_cap x h J menu cap) (by
    intro z hz
    obtain ⟨inside,gap⟩ := mem_filter.mp hz
    obtain ⟨_,_,lo,hi,found⟩ := data z inside
    exact ⟨(Nat.div_lt_iff_lt_mul pos).mpr (by simpa only [pow_two] using hi),
      Nat.le_of_not_gt gap,word_mem menu xp lo hi found⟩)
  exact count_parts S close low high

/-- Count all successful menus of at most J sums per observed view, separating
close pairs from the branch on which product spacing is at least U times D. -/
theorem hits_count {J D U : ℕ} (menu : View → Finset ℕ) (cap : ∀ v, (menu v).card≤J)
    (up : 0<U) (width : 2*X≤U*D) :
    (hits menu).card ≤ (2*X)*D + (2*X)*((288*J)*U) :=
  partition_count (x:=X) (by decide +kernel) up width (hits menu) menu cap
    (fun _ hz => hit_data hz)

/-- A bound for the union of all possible advice messages, allowing the
successful advice value to depend arbitrarily on the product. -/
noncomputable def pool {A : ℕ} (menu : View → Fin A → Finset ℕ) (v : View) : Finset ℕ :=
  univ.biUnion (menu v)

theorem pool_card {A K : ℕ} (menu : View → Fin A → Finset ℕ) (v : View)
    (cap : ∀ v a, (menu v a).card≤K) : (pool menu v).card≤A*K := by
  simpa only [pool,card_univ,Fintype.card_fin] using
    card_biUnion_le_card_mul (univ : Finset (Fin A)) (menu v) K (fun a _ => cap v a)

private theorem frequency {J e D U : ℕ} (menu : View → Finset ℕ)
    (cap : ∀ v, (menu v).card≤J) (up : 0<U) (width : 2*X≤U*D)
    (limit : 21000000*2^e*((2*X)*D+(2*X)*((288*J)*U))≤2^2046) :
    2^e*(hits menu).card<eligible.card := by
  have count := Nat.mul_le_mul_left (21000000*2^e) (hits_count menu cap up width)
  apply Nat.lt_of_mul_lt_mul_left (a:=21000000)
  simpa only [Nat.mul_assoc] using (count.trans limit).trans_lt ChebyshevPrimeSample.eligible_count

theorem single_guess (menu : View → Finset ℕ) (cap : ∀ v, (menu v).card≤1) :
    2^480*(hits menu).card<eligible.card :=
  frequency (D:=2^516) (U:=2^508) menu cap (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem advice_128 (menu : View → Fin (2^128) → Finset ℕ)
    (cap : ∀ v a, (menu v a).card≤2^40) :
    2^396*(hits (pool menu)).card<eligible.card :=
  frequency (D:=2^600) (U:=2^424) _ (fun v => pool_card menu v cap)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem advice_512 (menu : View → Fin (2^512) → Finset ℕ)
    (cap : ∀ v a, (menu v a).card≤2^40) :
    2^204*(hits (pool menu)).card<eligible.card :=
  frequency (D:=2^792) (U:=2^232) _ (fun v => pool_card menu v cap)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- The sums from actual prime pairs giving exactly this observed data. -/
noncomputable def feasible (v : View) : Finset ℕ :=
  (eligible.filter fun z => view X (z.1*z.2)=v).image fun z => z.1+z.2

private theorem own_sum (S : Finset (ℕ×ℕ)) (x : ℕ) (z : ℕ×ℕ) (hz : z∈S) :
    z.1+z.2∈(S.filter fun a => view x (a.1*a.2)=view x (z.1*z.2)).image (fun a => a.1+a.2) :=
  mem_image.mpr ⟨z,mem_filter.mpr ⟨hz,rfl⟩,rfl⟩

private theorem hits_all (S : Finset (ℕ×ℕ)) (x : ℕ) (menu : View → Finset ℕ)
    (all : ∀ z∈S, z.1+z.2∈menu (view x (z.1*z.2))) :
    (S.filter fun z => z.1+z.2∈menu (view x (z.1*z.2)))=S :=
  filter_eq_self.mpr all

attribute [local irreducible] hits feasible

private theorem every_sum_hits : hits feasible=eligible := by
  rw [hits]
  apply hits_all
  intro z hz
  rw [feasible]
  exact own_sum eligible X z hz

private theorem impossible_size {a b : ℕ} (eq : a=b) (bound : 2^0*a<b) : False := by
  rw [eq,pow_zero,one_mul] at bound
  exact (lt_irrefl _ bound)

private theorem cap_impossible (cap : ∀ v, (feasible v).card≤2^960) : False := by
  have bound := frequency (J:=2^960) (e:=0) (D:=2^996) (U:=2^28) feasible cap
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact impossible_size (congrArg Finset.card every_sum_hits) bound

theorem ambiguous_view : ∃ v, 2^960<(feasible v).card := by
  by_contra! cap
  exact cap_impossible cap

/-- Eligible pairs whose observed data is shared by at most J distinct true sums. -/
noncomputable def few (J : ℕ) : Finset (ℕ×ℕ) :=
  eligible.filter fun z => (feasible (view X (z.1*z.2))).card≤J

private noncomputable def clipped (J : ℕ) (v : View) : Finset ℕ :=
  if (feasible v).card≤J then feasible v else ∅

private theorem clipped_cap (J : ℕ) (v : View) : (clipped J v).card≤J := by
  unfold clipped
  split_ifs with h
  · exact h
  · exact Nat.zero_le _

private theorem clipped_mem (J : ℕ) (v : View) {s : ℕ} (inside : s∈feasible v) :
    s∈clipped J v ↔ (feasible v).card≤J := by
  unfold clipped
  split_ifs with h
  · exact iff_of_true inside h
  · simp [h]

private theorem clipped_hits (J : ℕ) : hits (clipped J)=few J := by
  unfold hits few
  apply filter_congr
  intro z hz
  apply clipped_mem
  rw [feasible]
  exact own_sum eligible X z hz

/-- Outside fewer than one in 2^30 eligible pairs, over 2^900 distinct
prime-pair sums give precisely the same observed data. -/
theorem typical_ambiguity : 2^30*(few (2^900)).card<eligible.card := by
  rw [←clipped_hits]
  exact frequency (D:=2^966) (U:=2^58) _ (clipped_cap (2^900))
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private theorem small_view {n : ℕ} (below : 749^2<n) (above : n≤750^2)
    (h : n/1024=548) (l : n/512=1097) (u : n/1023=549) (c : n%24=5) :
    view 512 n=⟨548,750,1097,549,5⟩ := by
  have root : ceilSqrt n=750 := by
    have hi := ceilSqrt_le_iff.mpr above
    by_contra! bad
    have contra := ceilSqrt_le_iff.mp (show ceilSqrt n≤749 by omega)
    exact (Nat.not_le_of_gt below) contra
  exact congrArg₂ (fun a b => View.mk a b (n/512) (n/1023) (n%24)) h root |>.trans
    (by rw [l,u,c])

/-- Three genuine prime pairs with the same high word, root, quotients and
modulo-24 phase at ten bits per factor, yet three different sums. -/
theorem small_collision :
    let v : View := ⟨548,750,1097,549,5⟩
    (Nat.Prime 557 ∧ Nat.Prime 1009 ∧ 557*1009=562013 ∧ 557+1009=1566 ∧ view 512 562013=v) ∧
    (Nat.Prime 641 ∧ Nat.Prime 877 ∧ 641*877=562157 ∧ 641+877=1518 ∧ view 512 562157=v) ∧
    (Nat.Prime 683 ∧ Nat.Prime 823 ∧ 683*823=562109 ∧ 683+823=1506 ∧ view 512 562109=v) := by
  dsimp only
  refine ⟨⟨?_,?_,rfl,rfl,?_⟩,⟨?_,?_,rfl,rfl,?_⟩,⟨?_,?_,rfl,rfl,?_⟩⟩
  all_goals first | apply small_view <;> decide +kernel | norm_num

end PrimeFactors.ActualWindowAdvice
