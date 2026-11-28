import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-! Reversing the three base-B digits of a factor makes its product with
the original factor palindromic before carries. When the central coefficient
is below B, its first three digits determine at most two ordered digit triples. -/

namespace PrimeFactors.ThreeBlockReversal

open Finset

abbrev Digits := ℕ×ℕ×ℕ

def word (B a b c : ℕ) := (B*a+b)*B+c
def product (B a b c : ℕ) := word B a b c*word B c b a

/-- Positive distinct outside digits fix the orientation. The middle digit can be zero. -/
def Valid (B a b c : ℕ) : Prop := 2≤B ∧ 0<a ∧ a<c ∧ a^2+b^2+c^2<B

/-- Only the lowest three ordinary base-B digits of the given number are needed. -/
def coefficients (B N : ℕ) : Digits := (N%B,N/B%B,N/B/B%B)

def middleOptions (A D C : ℕ) : ℕ×ℕ :=
  let up := (C+2*A+2*D).sqrt
  let down := (C+2*A-2*D).sqrt
  ((up-down)/2,(up+down)/2)

/-- Interpret s as the sum of the outer digits and b as the middle digit. -/
def restore (A b s : ℕ) : Digits :=
  let gap := (s^2-4*A).sqrt
  ((s-gap)/2,b,(s+gap)/2)

private def proposals (B N : ℕ) : Digits×Digits :=
  let (A,D,C) := coefficients B N
  let (x,y) := middleOptions A D C
  (restore A x y,restore A y x)

private def accepted (B N : ℕ) (t : Digits) : Bool :=
  decide (2≤B) && decide (0<t.1) && decide (t.1<t.2.2) &&
    decide (t.1^2+t.2.1^2+t.2.2^2<B) && (product B t.1 t.2.1 t.2.2==N)

/-- A product-only readout at the supplied radix, with one checked slot for each
assignment of the middle digit. These slots can coincide when b=a+c. -/
def readings (B N : ℕ) : Option Digits×Option Digits :=
  let (x,y) := proposals B N
  (if accepted B N x then some x else none,if accepted B N y then some y else none)

private noncomputable def options (B N : ℕ) : Finset Digits :=
  {(proposals B N).1,(proposals B N).2}

/-- The distinct surviving triples from both slots. -/
noncomputable def candidates (B N : ℕ) : Finset Digits :=
  (options B N).filter fun t => accepted B N t=true

theorem mem_readings (B N : ℕ) (t : Digits) :
    t∈candidates B N ↔ (readings B N).1=some t ∨ (readings B N).2=some t := by
  simp only [candidates,options,mem_filter,mem_insert,mem_singleton,readings]
  rcases proposals B N with ⟨x,y⟩
  simp only
  by_cases hx : accepted B N x=true <;> by_cases hy : accepted B N y=true <;>
    simp [hx,hy] <;> aesop

private theorem digit_step {B x : ℕ} (small : x<B) (t : ℕ) :
    (x+B*t)%B=x ∧ (x+B*t)/B=t := by
  have pos : 0<B := by omega
  rw [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt small,Nat.add_mul_div_left _ _ pos,
    Nat.div_eq_of_lt small,Nat.zero_add]
  trivial

theorem expansion (B a b c : ℕ) :
    product B a b c = a*c+B*(b*(a+c)+B*((a^2+b^2+c^2)+B*(b*(a+c)+B*(a*c)))) := by
  unfold product word
  ring

theorem carry_free {B a b c : ℕ} (v : Valid B a b c) :
    coefficients B (product B a b c)=(a*c,b*(a+c),a^2+b^2+c^2) := by
  have top := v.2.2.2
  have ac : a*c<B := by nlinarith [two_mul_le_add_sq a c]
  have bs : b*(a+c)<B := by nlinarith [two_mul_le_add_sq a b,two_mul_le_add_sq b c]
  simp only [coefficients,expansion,(digit_step ac _).1,(digit_step ac _).2,
    (digit_step bs _).1,(digit_step bs _).2,(digit_step top _).1]

/-- A power-of-two radix with at least two bits cannot fill the entire
nominal three-block width on this carry-free family. -/
theorem half_range {B a b c : ℕ} (v : Valid B a b c) (large : 4≤B) :
    2*word B a b c<B^3 ∧ 2*word B c b a<B^3 := by
  have top := v.2.2.2
  have half {t : ℕ} (sq : t^2<B) : 2*t<B := by
    by_cases small : t≤1
    · omega
    · have two : 2≤t := by omega
      exact (show 2*t≤t^2 by simpa only [pow_two] using Nat.mul_le_mul_right t two).trans_lt sq
  have ha := half (show a^2<B by omega)
  have hb := half (show b^2<B by omega)
  have hc := half (show c^2<B by omega)
  have digits {u v' t : ℕ} (h₁ : 2*u<B) (h₂ : 2*v'<B) (h₃ : 2*t<B) :
      2*word B u v' t<B^3 := by
    unfold word
    nlinarith only [Nat.mul_le_mul_right (B^2) (Nat.succ_le_of_lt h₁),
      Nat.mul_le_mul_right B (Nat.succ_le_of_lt h₂),h₃]
  exact ⟨digits ha hb hc,digits hc hb ha⟩

private theorem halves (a b : ℕ) (ab : a≤b) :
    ((a+b)-(b-a))/2=a ∧ ((a+b)+(b-a))/2=b := by omega

/-- The two roots are the sum and the absolute difference of b and a+c. -/
theorem middle_options {a b c : ℕ} :
    middleOptions (a*c) (b*(a+c)) (a^2+b^2+c^2)=(min b (a+c),max b (a+c)) := by
  have up : a^2+b^2+c^2+2*(a*c)+2*(b*(a+c))=(b+(a+c))^2 := by ring
  rw [middleOptions,up,Nat.sqrt_eq']
  by_cases order : b≤a+c
  · have down : a^2+b^2+c^2+2*(a*c)-2*(b*(a+c))=(a+c-b)^2 := by
      apply Nat.sub_eq_of_eq_add
      zify [order]
      ring
    rw [down,Nat.sqrt_eq',min_eq_left order,max_eq_right order]
    exact Prod.ext (halves b (a+c) order).1 (halves b (a+c) order).2
  · have rev : a+c≤b := by omega
    have down : a^2+b^2+c^2+2*(a*c)-2*(b*(a+c))=(b-(a+c))^2 := by
      apply Nat.sub_eq_of_eq_add
      zify [rev]
      ring
    rw [down,Nat.sqrt_eq',min_eq_right rev,max_eq_left rev,Nat.add_comm b (a+c)]
    exact Prod.ext (halves (a+c) b rev).1 (halves (a+c) b rev).2

theorem restore_true (a b c : ℕ) (order : a≤c) : restore (a*c) b (a+c)=(a,b,c) := by
  have sq : (a+c)^2-4*(a*c)=(c-a)^2 := by
    apply Nat.sub_eq_of_eq_add
    zify [order]
    ring
  simp only [restore,sq,Nat.sqrt_eq',(halves a c order).1,(halves a c order).2]

theorem mem_candidates {B N a b c : ℕ} :
    (a,b,c)∈candidates B N ↔ Valid B a b c ∧ product B a b c=N := by
  simp only [candidates,accepted,mem_filter,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq,Valid]
  constructor
  · tauto
  · rintro ⟨v,rfl⟩
    have inOptions : (a,b,c)∈options B (product B a b c) := by
      simp only [options,proposals,carry_free v,middle_options,mem_insert,mem_singleton]
      have ends := (restore_true a b c v.2.2.1.le).symm
      rcases le_total b (a+c) with h|h
      · exact Or.inl (by simpa only [min_eq_left h,max_eq_right h] using ends)
      · exact Or.inr (by simpa only [min_eq_right h,max_eq_left h] using ends)
    tauto

theorem card_le_two (B N : ℕ) : (candidates B N).card≤2 := by
  unfold candidates options
  exact card_filter_le .. |>.trans (card_insert_le .. |>.trans (by simp))

private theorem center_eq {a b c x y z : ℕ} (ac : a*c=x*z)
    (sumSq : (a+c)^2+b^2=(x+z)^2+y^2) : a^2+b^2+c^2=x^2+y^2+z^2 := by
  nlinarith only [ac,sumSq]

/-- Equality of represented integers is exactly the exchange ambiguity in the
middle digit and the sum of the outside digits, with their product fixed. -/
theorem same_product_iff {B a b c x y z : ℕ} (v : Valid B a b c) (w : Valid B x y z) :
    product B a b c=product B x y z ↔
      a*c=x*z ∧ ((b=y ∧ a+c=x+z) ∨ (b=x+z ∧ a+c=y)) := by
  constructor
  · intro same
    have eq := congrArg (coefficients B) same
    rw [carry_free v,carry_free w] at eq
    obtain ⟨ac,pair⟩ := Prod.mk.inj eq
    obtain ⟨cross,center⟩ := Prod.mk.inj pair
    have sort := middle_options (a:=a) (b:=b) (c:=c)
    rw [ac,cross,center,middle_options] at sort
    obtain ⟨least,greatest⟩ := Prod.mk.inj sort
    exact ⟨ac,by omega⟩
  · rintro ⟨ac,e⟩
    have cross : b*(a+c)=y*(x+z) := by rcases e with ⟨h,t⟩|⟨h,t⟩ <;> simp only [h,t,mul_comm,add_comm]
    have sq : (a+c)^2+b^2=(x+z)^2+y^2 := by rcases e with ⟨h,t⟩|⟨h,t⟩ <;> simp only [h,t,mul_comm,add_comm]
    rw [expansion,expansion,center_eq ac sq,ac,cross]

private theorem agrees {a b c x y z : ℕ} (ord : a≤c) (ord' : x≤z) (ac : a*c=x*z)
    (middle : b=y) (sum : a+c=x+z) : (a,b,c)=(x,y,z) := by
  rw [←restore_true a b c ord,ac,middle,sum,restore_true x y z ord']

/-- A second triple exists precisely when the original middle digit is the
sum of another distinct, ordered positive pair of divisors of the outer product. -/
theorem alternate_iff {B a b c : ℕ} (v : Valid B a b c) :
    (∃ x y z,Valid B x y z ∧ product B a b c=product B x y z ∧ (a,b,c)≠(x,y,z)) ↔
      b≠a+c ∧ ∃ x z,0<x ∧ x<z ∧ x*z=a*c ∧ x+z=b := by
  constructor
  · rintro ⟨x,y,z,w,prod,ne⟩
    obtain ⟨ac,e⟩ := (same_product_iff v w).mp prod
    rcases e with ⟨m,s⟩|⟨m,s⟩
    · exact (ne (agrees v.2.2.1.le w.2.2.1.le ac m s)).elim
    · refine ⟨?_,x,z,w.2.1,w.2.2.1,ac.symm,m.symm⟩
      intro eq
      exact ne (agrees v.2.2.1.le w.2.2.1.le ac (eq.trans s) (eq.symm.trans m))
  · rintro ⟨ne,x,z,xp,xz,ac,sum⟩
    have center : a^2+b^2+c^2=x^2+(a+c)^2+z^2 := center_eq ac.symm (by rw [sum]; ac_rfl)
    have w : Valid B x (a+c) z := ⟨v.1,xp,xz,center ▸ v.2.2.2⟩
    exact ⟨x,a+c,z,w,(same_product_iff v w).mpr ⟨ac.symm,Or.inr ⟨sum.symm,rfl⟩⟩,
      fun eq => ne (congrArg (fun t : Digits => t.2.1) eq)⟩

/-- A genuine ambiguity forces both three-digit words to factor into two
positive linear forms at every radix. It comes from two ways to group four
linear factors, and does not occur when either word is prime. -/
theorem ambiguous_words_split {B a b c : ℕ} (v : Valid B a b c)
    (second : ∃ x y z,Valid B x y z ∧ product B a b c=product B x y z ∧ (a,b,c)≠(x,y,z)) :
    ∃ i j m n : ℕ, 0 < i ∧ 0 < j ∧ 0 < m ∧ 0 < n ∧
      ∀ T : ℕ, word T a b c=(i*T+n)*(j*T+m) ∧ word T c b a=(n*T+i)*(m*T+j) := by
  obtain ⟨_,x,z,xp,xz,ac,sum⟩ := (alternate_iff v).mp second
  obtain ⟨i,j,⟨m,xm⟩,⟨n,zn⟩,ae⟩ := exists_dvd_and_dvd_of_dvd_mul (show a∣x*z from ⟨c,ac⟩)
  have ap := v.2.1
  have ip := Nat.pos_of_mul_pos_right (ae ▸ ap : 0 < i*j)
  have jp := Nat.pos_of_mul_pos_left (ae ▸ ap : 0 < i*j)
  have mp := Nat.pos_of_mul_pos_left (xm ▸ xp : 0 < i*m)
  have np := Nat.pos_of_mul_pos_left (zn ▸ xp.trans xz : 0 < j*n)
  have ce : c=m*n := Nat.eq_of_mul_eq_mul_left ap (calc
    a*c=x*z := ac.symm
    _=a*(m*n) := by rw [xm,zn,ae]; ring)
  exact ⟨i,j,m,n,ip,jp,mp,np,fun T => by rw [←sum,xm,zn,ae,ce]; unfold word; constructor <;> ring⟩

/-- One prime word already excludes the second candidate. -/
theorem unique_of_prime {B a b c x y z : ℕ} (v : Valid B a b c) (w : Valid B x y z)
    (same : product B a b c=product B x y z)
    (prime : Nat.Prime (word B a b c) ∨ Nat.Prime (word B c b a)) : (a,b,c)=(x,y,z) := by
  by_contra ne
  obtain ⟨i,j,m,n,ip,jp,mp,np,split⟩ := ambiguous_words_split v ⟨x,y,z,w,same,ne⟩
  have large {u v' : ℕ} (hu : 0<u) (hv : 0<v') : u*B+v'≠1 := by
    have low := v.1
    have ge := Nat.mul_le_mul_right B hu
    simp only [one_mul] at ge
    omega
  have eq := split B
  rcases prime with h|h
  · exact Nat.not_prime_mul' eq.1.symm (large ip np) (large jp mp) h
  · exact Nat.not_prime_mul' eq.2.symm (large np ip) (large mp jp) h

theorem example_primes : candidates 61 172659841={(3,4,4)} ∧
    word 61 3 4 4=11411 ∧ word 61 4 4 3=15131 ∧ Nat.Prime 11411 ∧ Nat.Prime 15131 := by
  exact ⟨by decide +kernel,by decide,by decide,by norm_num,by norm_num⟩

/-- Both surviving triples give different pairs of odd factors at the same radix. -/
theorem example_ambiguous : candidates 512 1048048107535={(1,8,15),(3,16,5)} ∧
    (word 512 1 8 15,word 512 15 8 1)=(266255,3936257) ∧
    (word 512 3 16 5,word 512 5 16 3)=(794629,1318915) := by decide +kernel

end PrimeFactors.ThreeBlockReversal
