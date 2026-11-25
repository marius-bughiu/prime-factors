import PrimeFactors.ReciprocalInverseSums
import PrimeFactors.FactorSum
import PrimeFactors.ChebyshevQuarticScale

/-! Exact recovery when the sum of two 1,024-bit primes has no prime
divisors other than 2 and 3. The source of the sum promise is unrestricted.
The executable selector takes only the product. -/

namespace PrimeFactors.SmoothSumSelector

open ReciprocalInverseSums

set_option exponentiation.threshold 4096

/-- Place the odd power of three in the dyadic interval [2^1024,2^1025). -/
def candidate (b : ℕ) : ℕ :=
  let m := 3^b
  2^(1024-m.log2)*m

theorem candidate_bounds {b : ℕ} (hb : b<647) :
    2^1024 ≤ candidate b ∧ candidate b < 2^1025 ∧ 2 ∣ candidate b := by
  let m := 3^b
  have positive : 0<m := by dsimp [m]; positivity
  have size : m<2^1024 :=
    (Nat.pow_le_pow_right (by decide : 0<3) (by omega : b≤646)).trans_lt (by decide +kernel)
  have lg : m.log2<1024 := (Nat.log2_lt positive.ne').mpr size
  have lower : 2^m.log2≤m := (Nat.le_log2 positive.ne').mp le_rfl
  have upper : m<2^(m.log2+1) := Nat.lt_log2_self
  let a := 1024-m.log2
  have add : a+m.log2=1024 := Nat.sub_add_cancel lg.le
  have add' : a+(m.log2+1)=1025 := by omega
  have l := Nat.mul_le_mul_left (2^a) lower
  have u := Nat.mul_lt_mul_of_pos_left upper (by positivity : 0<2^a)
  rw [←pow_add,add] at l
  rw [←pow_add,add'] at u
  have ha : a≠0 := by dsimp only [a]; omega
  exact ⟨l,u,dvd_mul_of_dvd_left (dvd_pow_self 2 ha) m⟩

/-- The lifting formula gives the unique sum in the specified octave with
that odd part, including its endpoints exactly as stated. -/
theorem contains {a b s : ℕ} (lower : 2^1024≤s) (upper : s<2^1025)
    (sum : s=2^a*3^b) : b<647 ∧ candidate b=s := by
  have base : 3^b≤s := by rw [sum]; exact Nat.le_mul_of_pos_left _ (by positivity)
  have cap : b<647 := by
    by_contra! no
    have big := Nat.pow_le_pow_right (by decide : 0<3) no
    exact (not_lt_of_ge (big.trans base)) (upper.trans (by decide +kernel : (2:ℕ)^1025<3^647))
  obtain ⟨cl,cu,_⟩ := candidate_bounds cap
  have upper' : (2:ℕ)^1025=2*2^1024 := by decide +kernel
  rw [upper'] at upper cu
  rw [sum] at lower upper ⊢
  have e := dyadic_unique cl cu lower upper
  exact ⟨cap,by dsimp only [candidate]; rw [e]⟩

private theorem residue {p q : ℕ} (h : 3 ∣ p+q) : (p*q)%3≠1 := by
  have table : ∀ i j : Fin 3, (i.val+j.val)%3=0 → (i.val*j.val)%3≠1 := by decide +kernel
  let i : Fin 3 := ⟨p%3,Nat.mod_lt _ (by decide)⟩
  let j : Fin 3 := ⟨q%3,Nat.mod_lt _ (by decide)⟩
  have eq := table i j (by simpa only [i,j,←Nat.add_mod] using Nat.mod_eq_zero_of_dvd h)
  simpa only [i,j,←Nat.mul_mod] using eq

/-- A pure product test eliminates the entire family when the product is one
modulo three and the target sum is strictly above the lower dyadic endpoint.
Only the lower endpoint could be a power of two in this interval. -/
theorem product_screen {p q a b : ℕ} (lower : 2^1024<p+q) (upper : p+q<2^1025)
    (sum : p+q=2^a*3^b) : (p*q)%3≠1 := by
  obtain ⟨_,same⟩ := contains lower.le upper sum
  cases b with
  | zero =>
    have small := (Nat.log2_lt (by decide : (1:ℕ)≠0)).mpr (by decide : (1:ℕ)<2^1)
    have zero : (1:ℕ).log2=0 := by omega
    have h : candidate 0=2^1024 := by simp [candidate,zero]
    omega
  | succ b =>
    apply residue
    rw [sum]
    exact dvd_mul_of_dvd_right (dvd_pow_self 3 (by omega)) _

/-- All successful discriminant tests. The search reads only the product and
has 647 public exponent choices before any range filtering. -/
noncomputable def results (n : ℕ) : List (ℕ × ℕ) :=
  (List.range 647).filterMap fun b => checkSum n (candidate b)

/-- Return the first exact split. A failed product screen terminates before
constructing the candidate sums. -/
def recover (n : ℕ) : Option (ℕ × ℕ) :=
  if n%3=1 then none else (List.range 647).findSome? fun b => checkSum n (candidate b)

private theorem check_sound {n s x y : ℕ} (hit : checkSum n s=some (x,y)) :
    1<x ∧ x≤y ∧ x*y=n := by
  simp only [checkSum,Id.run,pure] at hit
  split at hit
  · contradiction
  split at hit
  · contradiction
  split at hit
  · rename_i ok
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj hit)
    exact ⟨ok.1,Nat.div_le_div_right (by omega),ok.2⟩
  · contradiction

/-- Every 1,024-bit prime pair satisfying the sum promise is returned exactly,
independently of any relation between its two modular inverses. -/
theorem recover_eq {p q a b : ℕ} (pp : p.Prime) (qp : q.Prime) (order : p≤q)
    (lo : 2^1023≤p) (hi : q<2^1024) (promise : p+q=2^a*3^b) :
    recover (p*q)=some (p,q) := by
  have oddp := pp.odd_of_ne_two (by omega)
  have oddq := qp.odd_of_ne_two (by omega)
  obtain ⟨u,hu⟩ := oddp
  obtain ⟨v,hv⟩ := oddq
  have lower : 2^1024<p+q := by omega
  have upper : p+q<2^1025 := by omega
  obtain ⟨cap,same⟩ := contains lower.le upper promise
  have tested : (p,q) ∈ results (p*q) := by
    apply List.mem_filterMap.mpr
    exact ⟨b,List.mem_range.mpr cap,by rw [same]; exact check_true_sum pp.one_lt order (by omega) ⟨u+v+1,by omega⟩⟩
  have only {z : ℕ × ℕ} (h : z ∈ results (p*q)) : z=(p,q) := by
    obtain ⟨_,_,hit⟩ := List.mem_filterMap.mp h
    obtain ⟨hx,hxy,prod⟩ := check_sound hit
    obtain ⟨fst,snd⟩ := ordered_semiprime_pair_unique pp qp order hxy hx prod
    exact Prod.ext fst snd
  rw [recover,if_neg (product_screen lower upper promise),←List.head?_filterMap]
  change (results (p*q)).head?=some (p,q)
  cases hs : results (p*q) with
  | nil => simp [hs] at tested
  | cons z zs =>
    have eq := only (z:=z) (by rw [hs]; exact List.mem_cons_self)
    simp [eq]

/-- Both public full-size controls fail the one-remainder test. -/
theorem public_controls :
    ChebyshevQuarticScale.fresh%3=1 ∧ ChebyshevQuarticScale.crossed%3=1 ∧
    recover ChebyshevQuarticScale.fresh=none ∧ recover ChebyshevQuarticScale.crossed=none := by
  decide +kernel

/-- A factorization of the chosen product with a sum strictly inside the target
octave and with the specified small-prime support. -/
def HasInteriorSum (n : ℕ) : Prop := ∃ p q a b : ℕ,
  p*q=n ∧ 2^1024<p+q ∧ p+q<2^1025 ∧ p+q=2^a*3^b

theorem no_interior_sum {n : ℕ} (screen : n%3=1) : ¬HasInteriorSum n := by
  rintro ⟨p,q,a,b,prod,lo,hi,sum⟩
  exact product_screen lo hi sum (prod ▸ screen)

theorem controls_excluded :
    ¬HasInteriorSum ChebyshevQuarticScale.fresh ∧ ¬HasInteriorSum ChebyshevQuarticScale.crossed :=
  ⟨no_interior_sum public_controls.1,no_interior_sum public_controls.2.1⟩

/-- Under the project's explicit prime-population inequality, fewer than one
eligible pair in 2^998 can have a sum with these two allowed prime divisors. -/
theorem target_fraction {pairs : Finset (ℕ × ℕ)} {first : Finset ℕ} {population : ℕ}
    (den : 2^1023*first.card < 44331*population)
    (members : ∀ x ∈ pairs, x.1 ∈ first ∧ 2^1024 ≤ x.1+x.2 ∧ x.1+x.2 < 2^1025 ∧
      ∃ a b : ℕ, x.1+x.2=2^a*3^b) :
    2^998*pairs.card < population := by
  classical
  let sums := pairs.image fun x => x.1+x.2
  have count := dyadic_sums_card sums (fun s mem => by
    obtain ⟨x,h,rfl⟩ := Finset.mem_image.mp mem
    exact (members x h).2)
  have inject : pairs.card ≤ (first ×ˢ sums).card := by
    apply Finset.card_le_card_of_injOn (fun x : ℕ × ℕ => (x.1,x.1+x.2))
    · intro x hx
      exact Finset.mem_product.mpr ⟨(members x hx).1,Finset.mem_image_of_mem _ hx⟩
    · intro x _ y _ eq
      change (x.1,x.1+x.2)=(y.1,y.1+y.2) at eq
      obtain ⟨a,b⟩ := Prod.mk.inj eq
      exact Prod.ext (by exact a) (by omega)
  rw [Finset.card_product] at inject
  have rows := inject.trans (Nat.mul_le_mul_left first.card count)
  have left := Nat.mul_le_mul_left (2^1023*2^998) rows
  have mid := Nat.mul_lt_mul_of_pos_right den (by decide +kernel : 0<2^998*647)
  have cap := Nat.mul_le_mul_left population (by decide +kernel : 44331*(2^998*647)≤2^1023)
  apply Nat.lt_of_mul_lt_mul_left (a:=2^1023)
  calc
    _ ≤ _ := by simpa only [Nat.mul_assoc] using left
    _ = (2^1023*first.card)*(2^998*647) := by ac_rfl
    _ < _ := mid
    _ = population*(44331*(2^998*647)) := by ac_rfl
    _ ≤ _ := cap
    _ = _ := Nat.mul_comm ..

end PrimeFactors.SmoothSumSelector
