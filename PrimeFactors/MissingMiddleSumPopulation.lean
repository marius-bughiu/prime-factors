import PrimeFactors.HighLowSumPopulation

/-! Exact sum guesses when a single middle block of the product is hidden.
A fixed sum and leading word confine the smaller factors to an interval
shorter than the square root of the width of that word. -/
namespace PrimeFactors.MissingMiddleSumPopulation

open Finset MixedPrefixSample HighLowSumPopulation

set_option exponentiation.threshold 4096
set_option maxRecDepth 4096

/-- Inside a single product bin, two sorted pairs with the same sum cannot
have distinct smaller factors congruent modulo a step whose square spans the bin. -/
theorem square_step_unique {B U p q a b : ℕ} (pos : 0<B) (wide : B≤U^2)
    (pq : p≤q) (ab : a≤b) (word : p*q/B=a*b/B) (sum : p+q=a+b)
    (res : p%U=a%U) : (p,q)=(a,b) := by
  have exclude {p q a b : ℕ} (lt : p<a) (asc : a≤b) (same : p*q/B=a*b/B)
      (s : p+q=a+b) (modu : p%U=a%U) : False := by
    have gap := Nat.le_of_dvd (by omega : 0<a-p) ((Nat.modEq_iff_dvd' lt.le).mp modu)
    set d := a-p with hd
    have a' : a=p+d := by omega
    have q' : q=b+d := by omega
    have diff : p*q+d*(b-p)=a*b := by
      have rep : p+(b-p)=b := by omega
      rw [a',q']
      nlinarith only [congrArg (d*·) rep]
    have large := Nat.mul_le_mul gap (show U≤b-p by omega)
    rw [pow_two] at wide
    have lower := Nat.mul_div_le (p*q) B
    have upper := Nat.lt_mul_div_succ (a*b) pos
    rw [←same,Nat.mul_add,Nat.mul_one] at upper
    omega
  rcases lt_trichotomy p a with h|h|h
  · exact (exclude h ab word sum res).elim
  · exact Prod.ext h (by omega)
  · exact (exclude h pq word.symm sum.symm res.symm).elim

/-- A single factor pair whose gap is not divisible by 2^V pins every
other smaller factor to at most two disjoint positions in this bin. -/
theorem at_most_two {B k V u : ℕ} (pos : 0<B) (wide : B≤(2^u)^2)
    (budget : u+V≤k+1) (S : Finset (ℕ×ℕ)) (h r s : ℕ)
    (observed : ∀ z∈S, z.1<z.2 ∧ z.1*z.2/B=h ∧ z.1*z.2%2^k=r ∧ z.1+z.2=s)
    {anchor : ℕ×ℕ} (inside : anchor∈S) (gap : ¬2^V∣anchor.2-anchor.1) : S.card≤2 := by
  obtain ⟨order,_,res,sum⟩ := observed anchor inside
  obtain ⟨v,g,odd,decomp⟩ := Nat.exists_eq_two_pow_mul_odd (by omega : anchor.2-anchor.1≠0)
  have small : v<V := by
    by_contra! big
    exact gap ((pow_dvd_pow 2 big).trans ⟨g,decomp⟩)
  have divides : 2^u ∣ (2:ℕ)^(k-v) := pow_dvd_pow 2 (by omega)
  calc
    S.card ≤ ({anchor.1%2^u,anchor.2%2^u}:Finset ℕ).card := by
      apply card_le_card_of_injOn (fun z : ℕ×ℕ => z.1%2^u)
      · intro z hz
        obtain ⟨_,_,zr,zs⟩ := observed z hz
        rcases root_classes order.le decomp odd (sum.trans zs.symm) (res.trans zr.symm) with a|b
        · exact mem_insert.mpr (Or.inl (Nat.ModEq.of_dvd divides a))
        · exact mem_insert_of_mem (mem_singleton.mpr (Nat.ModEq.of_dvd divides b))
      · intro x hx y hy eq
        obtain ⟨ox,wx,_,sx⟩ := observed x hx
        obtain ⟨oy,wy,_,sy⟩ := observed y hy
        exact square_step_unique pos wide ox.le oy.le (wx.trans wy.symm) (sx.trans sy.symm) eq
    _ ≤ 2 := card_le_two

attribute [local irreducible] eligible sample ordered primes Finset.Ico

/-- The high word varies in an interval and the low word is odd. -/
noncomputable def wordSet (lo hi t : ℕ) : Finset (ℕ×ℕ) :=
  Ico lo hi ×ˢ ((range (2^t)).image (fun i => 2*i+1))

private theorem wordSet_card (lo hi t : ℕ) :
    (wordSet lo hi t).card≤(hi-lo)*2^t := by
  rw [wordSet,card_product,Nat.card_Ico]
  exact Nat.mul_le_mul_left _ (card_image_le.trans_eq (card_range _))

private theorem observed_words {t : ℕ} {z : ℕ×ℕ} (inside : z∈eligible) :
    (z.1*z.2/2^1024,z.1*z.2%2^(t+1)) ∈
      wordSet (2^1023) (2^1024) t := by
  obtain ⟨_,_,_,bot,top⟩ := eligible_shape (z:=z) inside
  have low : 2^1023≤z.1*z.2/2^1024 :=
    (Nat.le_div_iff_mul_le (by decide +kernel)).mpr (show 2^1023*2^1024≤z.1*z.2 from
      (by decide +kernel : 2^1023*2^1024=2*X^2) ▸ bot)
  have high : z.1*z.2/2^1024<2^1024 :=
    (Nat.div_lt_iff_lt_mul (by decide +kernel)).mpr (by simpa only [pow_two] using top)
  rw [eligible,sample,mem_filter] at inside
  have base := inside.1
  obtain ⟨pm,qm,_,_,_⟩ := mem_ordered.mp base
  have odd {p : ℕ} (hp : p∈primes) : Odd p := by
    rw [primes,mem_filter] at hp
    obtain ⟨bound,prime⟩ := hp
    exact prime.odd_of_ne_two (lt_of_lt_of_le (by decide +kernel : 2<X) (mem_Ico.mp bound).1).ne'
  have hz := Nat.odd_iff.mp ((odd pm).mul (odd qm))
  let r := z.1*z.2%2^(t+1)
  have parity : r%2=1 := (Nat.mod_mod_of_dvd _ (dvd_pow_self 2 (by omega : t+1≠0))).trans hz
  have small := Nat.mod_lt (z.1*z.2) (by positivity : 0<2^(t+1))
  change r<2^(t+1) at small
  rw [pow_succ] at small
  exact mem_product.mpr ⟨mem_Ico.mpr ⟨low,high⟩,
    mem_image.mpr ⟨r/2,mem_range.mpr (by omega),by omega⟩⟩

attribute [local irreducible] wordSet

/-- Count the regular pairs by the observed product words and the proposed sum.
The same gap hypothesis works for the whole fiber once one anchor meets it. -/
private theorem regular_count {B k V u J : ℕ} (pos : 0<B) (wide : B≤(2^u)^2)
    (budget : u+V≤k+1) (S : Finset (ℕ×ℕ)) (words : Finset (ℕ×ℕ))
    (menu : ℕ×ℕ → Finset ℕ) (cap : ∀ w, (menu w).card≤J)
    (data : ∀ z∈S, z.1<z.2 ∧ ¬2^V∣z.2-z.1 ∧
      (z.1*z.2/B,z.1*z.2%2^k)∈words ∧ z.1+z.2∈menu (z.1*z.2/B,z.1*z.2%2^k)) :
    S.card≤2*(words.card*J) := by
  classical
  let key (z : ℕ×ℕ) : Σ _ : ℕ×ℕ, ℕ := ⟨(z.1*z.2/B,z.1*z.2%2^k),z.1+z.2⟩
  have into : Set.MapsTo key S (words.sigma menu) := by
    intro z hz
    exact mem_sigma.mpr (data z hz).2.2
  have slots : (words.sigma menu).card ≤ words.card*J := by
    calc (words.sigma menu).card = _ := card_sigma ..
         _ ≤ ∑ _ ∈ words, J := sum_le_sum fun w _ => cap w
         _ = words.card*J := by simp
  have fiber (w : Σ _ : ℕ×ℕ, ℕ) : (S.filter fun z => key z=w).card≤2 := by
    let T := S.filter fun z => key z=w
    by_cases nonempty : T.Nonempty
    · obtain ⟨a,ha⟩ := nonempty
      apply at_most_two pos wide budget T w.1.1 w.1.2 w.2 ?_ ha (data a (mem_filter.mp ha).1).2.1
      intro z hz
      obtain ⟨hz',eq⟩ := mem_filter.mp hz
      exact ⟨(data z hz').1,congrArg (fun v : Σ _ : ℕ×ℕ, ℕ => v.1.1) eq,
        congrArg (fun v : Σ _ : ℕ×ℕ, ℕ => v.1.2) eq,congrArg (fun v : Σ _ : ℕ×ℕ, ℕ => v.2) eq⟩
    · change T.card≤2
      rw [not_nonempty_iff_eq_empty.mp nonempty,card_empty]
      decide
  exact (card_le_mul_card_image_of_maps_to into 2 (fun w _ => fiber w)).trans
    (Nat.mul_le_mul_left 2 slots)

/-- Any list selected from the first 1024 product bits and the last t+1
bits. The first term covers all pairs with an unusually even factor gap.
All other pairs cost at most two per observed word and proposed true sum. -/
theorem coverage {t V J : ℕ} (vmax : V≤1024) (digits : 512+V≤t+2)
    (menu : ℕ×ℕ → Finset ℕ) (cap : ∀ w, (menu w).card≤J) :
    (wordHits (t+1) menu).card ≤ 2^1024*2^(1024-V) + 2*(2^1023*2^t*J) := by
  classical
  let S := wordHits (t+1) menu
  let exceptional (z : ℕ×ℕ) := 2^V∣z.2-z.1
  have entry {z : ℕ×ℕ} (hz : z∈S) := mem_filter.mp (show z∈eligible.filter _ from hz)
  have bound := close_count (B:=2^1024) (D:=2^(1024-V)) (G:=2^V) (S.filter exceptional) (by
    intro z hz
    obtain ⟨inside,gap⟩ := mem_filter.mp hz
    obtain ⟨p,q,ord,_,_⟩ := eligible_shape (z:=z) (entry inside).1
    refine ⟨p,ord.le,gap,(Nat.div_lt_iff_lt_mul (by positivity)).mpr ?_⟩
    rw [←pow_add, Nat.sub_add_cancel vmax]
    omega)
  have count := regular_count (B:=2^1024) (k:=t+1) (V:=V) (u:=512) (by decide +kernel)
    (by decide +kernel) digits (S.filter (fun z => ¬exceptional z))
    (wordSet (2^1023) (2^1024) t) menu cap (by
      intro z hz
      obtain ⟨inside,nonexceptional⟩ := mem_filter.mp hz
      obtain ⟨h,hit⟩ := entry inside
      exact ⟨(eligible_shape (z:=z) h).2.2.1,nonexceptional,observed_words (t:=t) (z:=z) h,hit⟩)
  have size := wordSet_card (2^1023) (2^1024) t
  rw [show (2:ℕ)^1024-2^1023=2^1023 by decide +kernel] at size
  change S.card ≤ _
  rw [←filter_card_add_filter_neg_card_eq_card (s:=S) exceptional]
  exact Nat.add_le_add bound (count.trans (Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right J size)))

/-- Each additional guess increases the upper bound on the covered population
by at most the same fixed share. -/
theorem list_rate {J : ℕ} (pos : 0<J) (menu : ℕ×ℕ → Finset ℕ)
    (cap : ∀ w, (menu w).card≤J) :
    6700000*(wordHits 976 menu).card<J*eligible.card := by
  have count := coverage (t:=975) (V:=465) (by decide) (by decide) menu cap
  let E : ℕ := 2^1024*2^(1024-465)
  let F : ℕ := 2*(2^1023*2^975)
  have crude : (wordHits 976 menu).card ≤ J*(E+F) := by
    have exc := Nat.mul_le_mul_left E (show 1≤J from pos)
    dsimp only [E,F] at *
    rw [Nat.mul_one] at exc
    calc _ ≤ _ := count
         _ = 2^1024*2^(1024-465)+2*(2^1023*2^975)*J := by ring
         _ ≤ (2^1024*2^(1024-465))*J+2*(2^1023*2^975)*J := Nat.add_le_add_right exc _
         _ = _ := by ring
  have numeric : 21000000*6700000*(E+F)≤(2:ℕ)^2046 := by decide +kernel
  have total := numeric.trans_lt ChebyshevPrimeSample.eligible_count
  have scaled := (Nat.mul_le_mul_left (21000000*6700000) crude).trans_lt
    (show 21000000*6700000*(J*(E+F)) < 21000000*(J*eligible.card) by
      calc _ = J*(21000000*6700000*(E+F)) := by ring
           _ < J*(21000000*eligible.card) := Nat.mul_lt_mul_of_pos_left total pos
           _ = _ := by ring)
  exact Nat.lt_of_mul_lt_mul_left (a:=21000000) (by simpa only [Nat.mul_assoc] using scaled)

/-- With only 48 consecutive middle bits unread, even the best single exact
sum guess succeeds on fewer than one in 6.7 million eligible prime pairs. -/
theorem one_guess (menu : ℕ×ℕ → Finset ℕ) (cap : ∀ w, (menu w).card≤1) :
    6700000*(wordHits 976 menu).card<eligible.card := by
  simpa only [Nat.one_mul] using list_rate (by decide : 0<1) menu cap

/-- Any extra d-bit message may depend on the complete product, including
answers to adaptive queries. The decoder also has the two visible words. -/
noncomputable def advisedHits (d : ℕ) (message : ℕ → Fin (2^d))
    (decode : ℕ×ℕ → Fin (2^d) → ℕ) := eligible.filter fun z =>
  let n := z.1*z.2
  z.1+z.2 = decode (n/2^1024,n%2^976) (message n)

theorem advice_rate (d : ℕ) (message : ℕ → Fin (2^d)) (decode : ℕ×ℕ → Fin (2^d) → ℕ) :
    6700000*(advisedHits d message decode).card < 2^d*eligible.card := by
  let menu (w : ℕ×ℕ) := Finset.univ.image (decode w)
  have cap (w : ℕ×ℕ) : (menu w).card≤2^d := card_image_le.trans_eq (by simp)
  have sub : advisedHits d message decode ⊆ wordHits 976 menu := by
    intro z hz
    obtain ⟨base,hit⟩ := mem_filter.mp hz
    exact mem_filter.mpr ⟨base,mem_image.mpr ⟨message (z.1*z.2),mem_univ _,hit.symm⟩⟩
  exact (Nat.mul_le_mul_left _ (card_le_card sub)).trans_lt (list_rate (by positivity) menu cap)

theorem sixteen_extra_bits (message : ℕ → Fin (2^16)) (decode : ℕ×ℕ → Fin (2^16) → ℕ) :
    100*(advisedHits 16 message decode).card < eligible.card := by
  have rate := advice_rate 16 message decode
  apply Nat.lt_of_mul_lt_mul_left (a:=2^16)
  rw [←Nat.mul_assoc]
  exact (Nat.mul_le_mul_right _ (by decide +kernel : 2^16*100≤6700000)).trans_lt rate

end PrimeFactors.MissingMiddleSumPopulation
