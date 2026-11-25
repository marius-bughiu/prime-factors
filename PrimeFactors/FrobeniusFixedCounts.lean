import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Ring

namespace PrimeFactors.FrobeniusFixedCounts

/-- The two component equations are a graph and its transpose. Their
intersection consists of the graph above the fixed points of f composed with f. -/
theorem graph_counts {F : Type*} [Fintype F] [DecidableEq F] (f : F → F) :
    let left := Finset.univ.image (fun x => (x,f x))
    let right := Finset.univ.image (fun x => (f x,x))
    let fixed := (Finset.univ.filter (fun x => f (f x)=x)).card
    (left ∩ right).card = fixed ∧ (left ∪ right).card+fixed = 2*Fintype.card F := by
  classical
  intro left right fixed
  have inj : Function.Injective (fun x => (x,f x)) := fun _ _ h => (Prod.mk.inj h).1
  have inj' : Function.Injective (fun x => (f x,x)) := fun _ _ h => (Prod.mk.inj h).2
  have inter : left ∩ right =
      (Finset.univ.filter (fun x => f (f x)=x)).image (fun x => (x,f x)) := by
    ext ⟨a,b⟩
    simp only [left,right,Finset.mem_inter,Finset.mem_image, Finset.mem_univ,true_and,
      Prod.mk.injEq, exists_eq_left, Finset.mem_filter]
    constructor
    · rintro ⟨first,second⟩
      obtain ⟨z, hz, rfl⟩ := second
      exact ⟨a,by rw [first]; exact hz,rfl,first⟩
    · rintro ⟨c,h,rfl,rfl⟩
      exact ⟨rfl, f c, h, rfl⟩
  have first : (left∩right).card = fixed := by
    rw [inter,Finset.card_image_of_injective _ inj]
  refine ⟨first,?_⟩
  rw [← first, Finset.card_union_add_card_inter]
  simp [left,right,Finset.card_image_of_injective _ inj,Finset.card_image_of_injective _ inj',
    two_mul]

/-- The nonzero fixed points of x ↦ x^(n+1) form a cyclic power kernel. -/
theorem cyclic_count (G : Type*) [Group G] [IsCyclic G] [Fintype G] [DecidableEq G]
    (n : ℕ) : (Finset.univ.filter (fun u : G => u^n=1)).card = n.gcd (Fintype.card G) := by
  let h := n.gcd (Fintype.card G)
  have same : (Finset.univ.filter (fun u : G => u^n=1)) =
      Finset.univ.filter (fun u : G => u^h=1) := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, ← orderOf_dvd_iff_pow_eq_one]
    exact ⟨fun hn => Nat.dvd_gcd hn orderOf_dvd_card, fun hh => hh.trans (Nat.gcd_dvd_left ..)⟩
  rw [same,← sum_card_orderOf_eq_card_pow_eq_one (Nat.gcd_pos_of_pos_right n Fintype.card_pos).ne']
  calc
    _ = ∑ d ∈ h.divisors, d.totient := Finset.sum_congr rfl fun d hd =>
      IsCyclic.card_orderOf_eq_totient ((Nat.dvd_of_mem_divisors hd).trans (Nat.gcd_dvd_right ..))
    _ = h := Nat.sum_totient _

theorem field_fixed (F : Type*) [Field F] [Fintype F] [DecidableEq F] (n : ℕ) :
    (Finset.univ.filter (fun x : F => x^(n+1)=x)).card = n.gcd (Fintype.card F-1)+1 := by
  classical
  let good := Finset.univ.filter fun u : Fˣ => u^n=1
  let values := good.image (fun u : Fˣ => (u:F))
  have eq : (Finset.univ.filter (fun x : F => x^(n+1)=x)) = insert 0 values := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,Finset.mem_insert]
    constructor
    · intro hit
      by_cases hx : x=0
      · exact Or.inl hx
      · let u := Units.mk0 x hx
        have one : x^n=1 := mul_right_cancel₀ hx (by simpa [pow_succ] using hit)
        exact Or.inr (Finset.mem_image.mpr ⟨u,Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          Units.ext (by simpa [u] using one)⟩,rfl⟩)
    · rintro (rfl|hit)
      · simp
      · obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hit
        have one : (u:F)^n=1 := by
          simpa using congrArg (fun v : Fˣ => (v:F)) (Finset.mem_filter.mp hu).2
        rw [pow_succ,one,one_mul]
  have nonzero : 0 ∉ values := by simp [values,Finset.mem_image]
  have inj : Function.Injective (fun u : Fˣ => (u:F)) := fun _ _ h => Units.ext h
  rw [eq,Finset.card_insert_of_not_mem nonzero]
  simp only [values,good,Finset.card_image_of_injective _ inj, cyclic_count,Fintype.card_units]

/-- Multiplying the local counts by the common count t in the other field
gives the square count K and the count C from the norm. -/
theorem readout {p t C K : ℕ} (ht : 0<t) (hK : K=t^2)
    (hC : C=(2*p-t)*t) (fits : t≤2*p) :
    (C/K.sqrt+K.sqrt)/2=p ∧ (C+K)/2=p*t := by
  subst K C
  rw [Nat.sqrt_eq', Nat.mul_div_cancel _ ht]
  constructor
  · rw [Nat.sub_add_cancel fits, Nat.mul_div_right _ (by decide : 0<2)]
  · have sum : (2*p-t)*t+t^2=2*(p*t) := by
      rw [pow_two,← Nat.add_mul, Nat.sub_add_cancel fits,Nat.mul_assoc]
    rw [sum,Nat.mul_div_right _ (by decide : 0<2)]

/-- Once the local fields are identified, the two observations are Cartesian
products. The same inert fixed-point set occurs in both. -/
theorem product_readout {F E : Type*} [Fintype F] [DecidableEq F] [DecidableEq E]
    (f : F → F) (tail : Finset E) (pos : tail.Nonempty)
    (same : tail.card=(Finset.univ.filter (fun x => f (f x)=x)).card) :
    let left := Finset.univ.image (fun x => (x,f x))
    let right := Finset.univ.image (fun x => (f x,x))
    let K := ((left∩right) ×ˢ tail).card
    let C := ((left∪right) ×ˢ tail).card
    K=tail.card^2 ∧ (C/K.sqrt+K.sqrt)/2=Fintype.card F := by
  classical
  intro left right K C
  obtain ⟨inter,un⟩ := graph_counts f
  change (left∩right).card = _ at inter
  change (left∪right).card + _ = _ at un
  rw [← same] at inter un
  have sq : K=tail.card^2 := by simp only [K,Finset.card_product,inter,pow_two]
  have unionSize : (left∪right).card=2*Fintype.card F-tail.card := by omega
  have normSize : C=(2*Fintype.card F-tail.card)*tail.card := by
    simp only [C,Finset.card_product,unionSize]
  exact ⟨sq,(readout (Finset.card_pos.mpr pos) sq normSize (by omega)).1⟩

/-- Odd roots of the same square one bit more accurately differ only by
sign after the top bit is dropped. -/
theorem odd_square_lifts (n : ℕ) {s t : ℤ} (hs : Odd s) (ht : Odd t)
    (squares : (2:ℤ)^(n+1) ∣ s^2-t^2) : (2:ℤ)^n ∣ s-t ∨ (2:ℤ)^n ∣ s+t := by
  have drop (a b : ℤ) (two : a%4=2) (prod : (2:ℤ)^(n+1) ∣ a*b) : (2:ℤ)^n ∣ b := by
    apply (show Prime (2:ℤ) by norm_num).pow_dvd_of_dvd_mul_left n (a:=a/2)
    · rintro ⟨c,hc⟩
      omega
    · obtain ⟨c,hc⟩ := prod
      refine ⟨c,mul_left_cancel₀ (show (2:ℤ)≠0 by decide) ?_⟩
      calc
        2*(a/2*b) = a*b := by rw [←mul_assoc, show 2*(a/2)=a by omega]
        _ = 2*(2^n*c) := hc.trans (by rw [pow_succ]; ring)
  obtain ⟨u,hu⟩ := hs
  obtain ⟨v,hv⟩ := ht
  have fac : s^2-t^2=(s-t)*(s+t) := by ring
  rw [fac] at squares
  by_cases h : (s-t)%4=2
  · exact Or.inr (drop (s-t) (s+t) h squares)
  · exact Or.inl (drop (s+t) (s-t) (by omega) (by rwa [mul_comm]))

theorem example_counts :
    let h := Nat.gcd (11-1) (7^2-1)
    let K := (h+1)^2
    let C := (2*11-(h+1))*(h+1)
    h=2 ∧ K=9 ∧ C=57 ∧ (C/K.sqrt+K.sqrt)/2=11 ∧
      Nat.Prime 11 ∧ Nat.Prime 7 ∧ (11:ℕ)*7=77 := by decide

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1500000 in
/-- All 77² public coordinate pairs, using D=3. The addition chain is
77=64+8+4+1. Both counts are evaluated by the kernel. -/
theorem example_grid :
    let mul := fun x y : ℕ × ℕ =>
      ((x.1*y.1+3*x.2*y.2)%77,(x.1*y.2+x.2*y.1)%77)
    let observe := fun a b : ℕ =>
      let z := (a,b)
      let z₂ := mul z z
      let z₄ := mul z₂ z₂
      let z₈ := mul z₄ z₄
      let z₁₆ := mul z₈ z₈
      let z₃₂ := mul z₁₆ z₁₆
      let z₆₄ := mul z₃₂ z₃₂
      let z₇₇ := mul (mul (mul z₆₄ z₈) z₄) z
      ((z₇₇.1+77-a)%77, (z₇₇.2+b)%77)
    let grid := (List.range 77).flatMap fun a => (List.range 77).map (observe a)
    let K := grid.countP fun z => z.1==0 && z.2==0
    let C := grid.countP fun z => z.1^2%77 == 3*z.2^2%77
    K=9 ∧ C=57 ∧ (C/K.sqrt+K.sqrt)/2=11 := by decide +kernel

end PrimeFactors.FrobeniusFixedCounts
