import PrimeFactors.ReciprocalInverseSums
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Sym.Card

/-! A bound for successful smooth-part guesses, even when the source, gap and
small-prime cutoff are all chosen after seeing the product. -/

namespace PrimeFactors.SmallPrimeSumCoverage

open Finset

set_option exponentiation.threshold 280000

/-- The shared restriction on every candidate output by a cutoff at most 31. -/
def Supported (s : ℕ) := ∀ p, p.Prime → p ∣ s → p≤31

theorem smooth_part_supported {bases : List ℕ} (small : ∀ b ∈ bases, 0<b ∧ b≤31)
    (source : ℕ) : Supported (ReciprocalInverseSums.smoothPart bases source) := by
  induction bases with
  | nil => intro p hp h; simp [ReciprocalInverseSums.smoothPart] at h; omega
  | cons b rest ih =>
    intro p hp h
    rcases hp.dvd_mul.mp h with a|a
    · exact (Nat.le_of_dvd (small b (by simp)).1 (hp.dvd_of_dvd_pow a)).trans
        (small b (by simp)).2
    · exact ih (fun z hz => small z (by simp [hz])) p hp a

private def primeAt : Fin 10 → ℕ := ![3,5,7,11,13,17,19,23,29,31]

/-- Integer lower weights for 256 times the base-two logarithm. Only the
exact power comparisons in `weights` are needed. -/
private def weight : Fin 10 → ℕ := ![405,594,718,885,947,1046,1087,1158,1243,1268]

private noncomputable def oddPart (e : Fin 10 → ℕ) := ∏ i, primeAt i^e i

private theorem weights :
    (∀ i, 0<weight i ∧ 2^weight i≤primeAt i^256) ∧
    (∑ i, weight i)=9351 ∧ (∏ i, weight i)=300413421982319284154363284800 := by
  decide +kernel

private theorem representation {s : ℕ} (pos : s≠0) (even : 2 ∣ s) (smooth : Supported s) :
    ∃ a e, 0<a ∧ s=2^a*oddPart e := by
  let odds := univ.image primeAt
  have primes : ∀ p : Fin 32, p.val.Prime → p.val ∈ insert 2 odds := by decide +kernel
  have inside : s.primeFactors ⊆ insert 2 odds := by
    intro p hp
    obtain ⟨pp,dvd,_⟩ := Nat.mem_primeFactors.mp hp
    exact primes ⟨p,by have := smooth p pp dvd; omega⟩ pp
  have prod := Finset.prod_subset (f:=fun p => p^s.factorization p) inside (by
    intro p _ hn
    have h : s.factorization p = 0 := by
      by_contra h
      exact hn (by rw [←s.support_factorization]; exact Finsupp.mem_support_iff.mpr h)
    simp [h])
  have fact : ∏ p ∈ s.primeFactors, p^s.factorization p=s := Nat.factorization_prod_pow_eq_self pos
  have distinct : Function.Injective primeAt := by decide +kernel
  have noTwo : 2∉odds := by decide +kernel
  refine ⟨s.factorization 2,fun i => s.factorization (primeAt i),Nat.prime_two.factorization_pos_of_dvd pos even,?_⟩
  conv_lhs => rw [←fact,prod,prod_insert noTwo]
  unfold oddPart
  exact congrArg (fun z => 2^s.factorization 2*z) (Finset.prod_image (fun _ _ _ _ h => distinct h))

private theorem log_budget {a : ℕ} {e : Fin 10 → ℕ} (ha : 0<a)
    (upper : 2^a*oddPart e<2^1025) : ∑ i, weight i*e i < 262144 := by
  have two : 2≤2^a := by simpa using (Nat.pow_le_pow_right (by decide : 0<2) ha : 2^1≤2^a)
  have half : oddPart e<2^1024 := by
    have h := (Nat.mul_le_mul_right (oddPart e) two).trans_lt upper
    rw [show (2:ℕ)^1025=2*2^1024 by decide +kernel] at h
    exact Nat.lt_of_mul_lt_mul_left h
  have local_bound (i : Fin 10) : 2^(weight i*e i)≤(primeAt i^e i)^256 := by
    calc
      _ = (2^weight i)^(e i) := pow_mul ..
      _ ≤ (primeAt i^256)^(e i) := Nat.pow_le_pow_left (weights.1 i).2 _
      _ = _ := by rw [←pow_mul,←pow_mul,Nat.mul_comm 256]
  have total := Finset.prod_le_prod' (s:=univ) (fun i _ => local_bound i)
  rw [Finset.prod_pow_eq_pow_sum,Finset.prod_pow] at total
  have top := total.trans_lt (Nat.pow_lt_pow_left half (by decide : 256≠0))
  rw [←pow_mul] at top
  exact (Nat.pow_lt_pow_iff_right (by decide : 1<2)).mp top

private theorem single_shift {a b c : ℕ}
    (la : 2^1024≤2^a*c) (ha : 2^a*c<2^1025)
    (lb : 2^1024≤2^b*c) (hb : 2^b*c<2^1025) : a=b := by
  have no {u v : ℕ} (l : 2^1024≤2^u*c) (h : 2^v*c<2^1025) (lt : u<v) : False := by
    have step := Nat.mul_le_mul_right c (Nat.pow_le_pow_right (by decide : 0<2) lt : 2^(u+1)≤2^v)
    rw [pow_succ] at step
    have lower := Nat.mul_le_mul_left 2 l
    rw [show (2:ℕ)^1025=2*2^1024 by decide +kernel] at h
    rw [mul_comm (2^u),mul_assoc] at step
    omega
  rcases lt_trichotomy a b with h|h|h
  · exact (no la hb h).elim
  · exact h
  · exact (no lb ha h).elim

/-- Stars and bars with a slack coordinate. This only charges integer tuples
in the simplex, without constructing the enormous finite tuple list. -/
private theorem simplex {α : Type} [Fintype α] {k t : ℕ}
    (x : α → Fin k → ℕ) (inject : Function.Injective x) (size : ∀ y, ∑ i, x y i ≤ t) :
    Fintype.card α ≤ (t+k).choose k := by
  classical
  let lift (y : α) : {v : Fin (k+1) → ℕ // ∑ i, v i = t} :=
    ⟨Fin.cons (t-∑ i,x y i) (x y),by
      rw [Fin.sum_univ_succ]
      simpa using Nat.sub_add_cancel (size y)⟩
  have inj : Function.Injective lift := by
    intro y z eq
    apply inject
    funext i
    exact congrArg (fun w => w.val i.succ) eq
  let conv := (Sym.equivNatSumOfFintype (Fin (k+1)) t).symm
  have card := Fintype.card_le_of_injective (conv ∘ lift) (conv.injective.comp inj)
  rw [Sym.card_sym_eq_choose,Fintype.card_fin,show k+1+t-1=t+k by omega,Nat.choose_symm_add] at card
  exact card

/-- Number of even 1,025-bit integers whose prime divisors all lie below 32.
Both the support and the dyadic endpoints are part of the hypothesis. -/
theorem sum_count {sums : Finset ℕ}
    (valid : ∀ s ∈ sums, 2^1024≤s ∧ s<2^1025 ∧ 2∣s ∧ Supported s) :
    sums.card ≤ 1995556406373313773 := by
  classical
  have rep (s : sums) : ∃ a e, 0<a ∧ s.val=2^a*oddPart e := by
    obtain ⟨l,_,ev,sm⟩ := valid s.val s.prop
    exact representation (by omega) ev sm
  choose a e ha he using rep
  -- Allocate weight i consecutive positions to each exponent. Division and
  -- remainder reconstruct the exponent and the position inside its cell.
  let Digits := (i : Fin 10) → Fin (weight i)
  let expand (z : sums × Digits) (i : Fin 10) := weight i*e z.1 i+(z.2 i).val
  have inject : Function.Injective expand := by
    intro y z eq
    have exponent : e y.1=e z.1 := by
      funext i
      have hd := congrArg (fun f : Fin 10 → ℕ => f i / weight i) eq
      simpa [expand,Nat.mul_add_div (weights.1 i).1,Nat.div_eq_of_lt (y.2 i).isLt,
        Nat.div_eq_of_lt (z.2 i).isLt] using hd
    have code : a y.1=a z.1 := by
      have rangeY := valid _ y.1.prop
      have rangeZ := valid _ z.1.prop
      apply single_shift (c:=oddPart (e z.1))
      · simpa only [←exponent,←he] using rangeY.1
      · simpa only [←exponent,←he] using rangeY.2.1
      · simpa only [←he] using rangeZ.1
      · simpa only [←he] using rangeZ.2.1
    apply Prod.ext
    · apply Subtype.ext
      rw [he y.1,he z.1,code,exponent]
    · funext i
      apply Fin.ext
      have hm := congrArg (fun f : Fin 10 → ℕ => f i % weight i) eq
      simpa only [expand,Nat.mul_add_mod,Nat.mod_eq_of_lt (y.2 i).isLt,Nat.mod_eq_of_lt (z.2 i).isLt] using hm
  have room (z : sums × Digits) : ∑ i, expand z i ≤ 271485 := by
    have size := log_budget (ha z.1) (by rw [←he z.1]; exact (valid _ z.1.prop).2.1)
    have small := sum_le_sum (s:=univ) (fun (i : Fin 10) _ => Nat.le_sub_one_of_lt (z.2 i).isLt)
    have offsets : (∑ i, (weight i-1))=9341 := by decide +kernel
    rw [offsets] at small
    simp only [expand,sum_add_distrib]
    omega
  -- Choose ten separators. Each sum occupies one cell of size ∏ i, weight i.
  have bound := simplex expand inject room
  rw [Fintype.card_prod,Fintype.card_coe] at bound
  have digits : Fintype.card Digits=300413421982319284154363284800 := by
    simp only [Digits,Fintype.card_pi,Fintype.card_fin,weights.2.2]
  rw [digits,Nat.choose_eq_descFactorial_div_factorial] at bound
  have final : (271485+10).descFactorial 10 / (Nat.factorial 10) / 300413421982319284154363284800
      = 1995556406373313773 := by decide +kernel
  rw [←final]
  exact (Nat.le_div_iff_mul_le (by decide)).mpr bound

/-- A hit from any number of product-dependent attempts must use an allowed
sum. With the first prime fixed, its sum determines the second prime. The
external prime-population comparison is an explicit assumption. -/
theorem target_fraction {pairs : Finset (ℕ × ℕ)} {first : Finset ℕ} {population : ℕ}
    (base : 2^1023*first.card<44331*population)
    (valid : ∀ x∈pairs, x.1∈first ∧ x.1.Prime ∧ x.2.Prime ∧
      2^1023≤x.1 ∧ x.1<2^1024 ∧ 2^1023≤x.2 ∧ x.2<2^1024 ∧ Supported (x.1+x.2)) :
    2^946*pairs.card<population := by
  let sums := pairs.image (fun x => x.1+x.2)
  have limits : sums.card≤1995556406373313773 := by
    apply sum_count
    intro s hs
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hs
    obtain ⟨_,p,q,pLo,pHi,qLo,qHi,sm⟩ := valid x hx
    have ⟨a,ha⟩ := p.odd_of_ne_two (by omega)
    have ⟨b,hb⟩ := q.odd_of_ne_two (by omega)
    exact ⟨by omega,by omega,⟨a+b+1,by omega⟩,sm⟩
  have count : pairs.card≤first.card*sums.card := by
    rw [←Finset.card_product]
    apply Finset.card_le_card_of_injOn (fun x : ℕ × ℕ => (x.1,x.1+x.2))
    · intro x hx
      exact mem_product.mpr ⟨(valid x hx).1,mem_image_of_mem _ hx⟩
    · rintro ⟨p,q⟩ _ ⟨u,v⟩ _ eq
      change (p,p+q)=(u,u+v) at eq
      obtain ⟨rfl,h⟩ := Prod.mk.inj eq
      simp only [Nat.add_left_cancel h]
  let cap := 1995556406373313773
  have scale : 2^946*(cap*44331)≤2^1023 := by decide +kernel
  have capPos : 0<2^946*cap := by decide +kernel
  apply Nat.lt_of_mul_lt_mul_left (a:=2^1023)
  calc
    _ ≤ 2^1023*(2^946*(first.card*cap)) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (count.trans (Nat.mul_le_mul_left _ limits)))
    _ = (2^1023*first.card)*(2^946*cap) := by ac_rfl
    _ < (44331*population)*(2^946*cap) := Nat.mul_lt_mul_of_pos_right base capPos
    _ = (2^946*(cap*44331))*population := by ac_rfl
    _ ≤ _ := Nat.mul_le_mul_right _ scale

end PrimeFactors.SmallPrimeSumCoverage
