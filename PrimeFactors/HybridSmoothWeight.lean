import Mathlib.Data.Nat.Factors
import Mathlib.Data.List.Permutation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Union
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum

/-! The finite multiplicity underlying Cogentic, *Unconditional Integer Factorization in
Time L_N[1/3,O(1)]*, Definition 3.4 and Lemma 3.5(1), published by Google Research on
2026-11-25 (paper © 2026 Google LLC, CC BY 4.0). Source snapshot:
https://github.com/google-research/google-research/blob/ff7ba34ff3028a22bd7ff3b7a89b6fdcc306b690/cogentic_research_papers/integer_factorization/paper.pdf .
The proof below is independent. There are s prime positions and one distinguished
integer position; the paper sets s=4u−1. This is a finite counting statement. -/
namespace PrimeFactors.HybridSmoothWeight
open Finset

/-- The common dyadic interval (Y/2,Y]. -/
noncomputable def band (Y : ℕ) := Ioc (Y/2) Y

/-- Ordered words of fixed length in a finite alphabet. -/
private noncomputable def words (A : Finset ℕ) : ℕ → Finset (List ℕ)
  | 0 => {[]}
  | s+1 => A.biUnion fun a => (words A s).image (List.cons a)

private theorem mem_words {A : Finset ℕ} {l : List ℕ} {s : ℕ} :
    l∈words A s ↔ l.length=s ∧ ∀ p∈l, p∈A := by
  induction s generalizing l with
  | zero => cases l <;> simp [words]
  | succ s ih =>
    cases l with
    | nil => simp [words]
    | cons h l => simp [words,ih,and_assoc,and_left_comm,and_comm]

/-- A representation is the complete ordered list, with its distinguished element first. -/
noncomputable def rows (Y s n : ℕ) : Finset (List ℕ) :=
  ((band Y).biUnion fun h => (words ((band Y).filter Nat.Prime) s).image (List.cons h)).filter
    fun l => l.prod=n

/-- The normalized weight counts representations, with repeated orderings counted once. -/
noncomputable def weight (Y s n : ℕ) : ℚ := (rows Y s n).card/(s+1).factorial

private structure Good (Y s n h : ℕ) (l : List ℕ) : Prop where
  head_mem : h∈band Y
  len : l.length=s
  tail_mem : ∀ p∈l, p∈band Y ∧ p.Prime
  product : h*l.prod=n

private theorem mem_rows {Y s n h : ℕ} {l : List ℕ} : h::l∈rows Y s n ↔ Good Y s n h l := by
  simp only [rows,mem_filter,mem_biUnion,mem_image,exists_prop,List.cons.injEq,mem_words,List.prod_cons]
  constructor
  · intro data
    apply Good.mk <;> aesop
  · rintro ⟨hm,len,ps,eq⟩
    aesop

private theorem nil_not_mem (Y s n : ℕ) : []∉rows Y s n := by simp [rows]

/-- A divisor and its positive multiple cannot be distinct when both lie in this band. -/
private theorem band_dvd_eq {Y a h : ℕ} (am : a∈band Y) (hm : h∈band Y) (div : a∣h) : h=a := by
  obtain ⟨alo,ahi⟩ := mem_Ioc.mp am
  obtain ⟨hlo,hhi⟩ := mem_Ioc.mp hm
  exact Nat.eq_of_dvd_of_lt_two_mul (by omega) div (by omega)

/-- On filtering the complete prime factor list to this band, a composite head vanishes
and a prime head survives. Every element of the tail survives. -/
private theorem prime_entries {Y s n h : ℕ} {l : List ℕ} (ok : Good Y s n h l) :
    (if h.Prime then h::l else l).Perm (n.primeFactorsList.filter (fun p => p∈band Y)) := by
  have hm := mem_Ioc.mp ok.head_mem
  have hp : 0<h := by omega
  have eq := Nat.primeFactorsList_unique (l:=h.primeFactorsList++l) (n:=n)
    (by rw [List.prod_append,Nat.prod_primeFactorsList hp.ne']; exact ok.product)
    (fun p pm => (List.mem_append.mp pm).elim Nat.prime_of_mem_primeFactorsList (fun z => (ok.tail_mem p z).2))
  have filtered := eq.filter (fun p => decide (p∈band Y))
  have lt : l.filter (fun p => decide (p∈band Y))=l := List.filter_eq_self.mpr
    (fun p pp => by simpa using (ok.tail_mem p pp).1)
  rw [List.filter_append,lt] at filtered
  split_ifs with prime
  · simpa [Nat.primeFactorsList_prime prime,ok.head_mem] using filtered
  · have empty : h.primeFactorsList.filter (fun p => decide (p∈band Y))=[] := by
      apply List.filter_eq_nil_iff.mpr
      intro p pp
      simp only [decide_eq_true_eq]
      intro pm
      exact prime (band_dvd_eq pm ok.head_mem (Nat.dvd_of_mem_primeFactorsList pp) ▸
        Nat.prime_of_mem_primeFactorsList pp)
    simpa [empty] using filtered

private theorem nodup_of_squares {l : List ℕ} (clean : ∀ p∈l, ¬p^2∣l.prod) : l.Nodup := by
  induction l with
  | nil => simp
  | cons p l ih =>
    refine List.nodup_cons.mpr ⟨?_,ih ?_⟩
    · intro pm
      exact clean p (by simp) (by rw [pow_two,List.prod_cons]; exact Nat.mul_dvd_mul_left p (List.dvd_prod pm))
    · intro q qm dvd
      exact clean q (by simp [qm]) (dvd.trans (dvd_mul_left l.prod p))

/-- Any common divisor below every prime slot must divide the distinguished integer. -/
theorem small_divisor {Y s n h g : ℕ} {l : List ℕ} (mem : h::l∈rows Y s n)
    (gp : 0<g) (small : g≤Y/2) (div : g∣n) : g∣h := by
  have ok := mem_rows.mp mem
  have cop : g.Coprime l.prod := by
    have aux (w : List ℕ) (hw : ∀ p∈w, p∈band Y ∧ p.Prime) : g.Coprime w.prod := by
      induction w with
      | nil => simp
      | cons p w ih =>
        obtain ⟨pm,prime⟩ := hw p (by simp)
        have lt : g<p := lt_of_le_of_lt small (mem_Ioc.mp pm).1
        have pc := (prime.coprime_iff_not_dvd.mpr (fun d => (not_le_of_gt lt) (Nat.le_of_dvd gp d))).symm
        exact pc.mul_right (ih (fun a ha => hw a (by simp [ha])))
    exact aux l ok.tail_mem
  exact cop.dvd_of_dvd_mul_right (ok.product ▸ div)

/-- For the gcd with a progression modulus, the forced factor can be removed
from the distinguished entry. What remains is coprime to the reduced modulus. -/
theorem local_gcd {Y s n h m : ℕ} {l : List ℕ} (mem : h::l∈rows Y s n)
    (np : 0<n) (small : n.gcd m≤Y/2) :
    n.gcd m∣h ∧ (h/n.gcd m).Coprime (m/n.gcd m) := by
  let g := n.gcd m
  have gp : 0<g := Nat.gcd_pos_of_pos_left _ np
  have forced := small_divisor mem gp small (Nat.gcd_dvd_left n m)
  have product := (mem_rows.mp mem).product
  have reduced : h/g∣n/g := by
    use l.prod
    calc n/g = (l.prod*h)/g := by rw [Nat.mul_comm l.prod,product]
         _ = l.prod*(h/g) := Nat.mul_div_assoc _ forced
         _ = (h/g)*l.prod := Nat.mul_comm ..
  exact ⟨forced,Nat.Coprime.of_dvd_left reduced (Nat.coprime_div_gcd_div_gcd gp)⟩

/-- For an all-prime representation, every permutation, and only a permutation,
is another representation of this same integer. -/
private theorem prime_rows {Y s n h : ℕ} {l : List ℕ} (ok : Good Y s n h l) (hp : h.Prime) :
    rows Y s n=(h::l).permutations.toFinset := by
  ext w
  rw [List.mem_toFinset,List.mem_permutations]
  cases w with
  | nil =>
    constructor
    · exact fun m => (nil_not_mem _ _ _ m).elim
    · intro perm
      have len := perm.length_eq
      simp at len
  | cons b t =>
    rw [mem_rows]
    constructor
    · intro other
      have perm := (prime_entries other).trans (prime_entries ok).symm
      rw [if_pos hp] at perm
      by_cases bp : b.Prime
      · simpa only [if_pos bp] using perm
      · rw [if_neg bp] at perm
        have len := perm.length_eq
        simp [ok.len,other.len] at len
    · intro perm
      have all (p : ℕ) (pm : p∈b::t) : p∈band Y ∧ p.Prime := by
        rcases List.mem_cons.mp (perm.mem_iff.mp pm) with rfl|pl
        · exact ⟨ok.head_mem,hp⟩
        · exact ok.tail_mem _ pl
      exact ⟨(all b (by simp)).1,by simpa [ok.len] using perm.length_eq,
        fun p pm => all p (by simp [pm]),perm.prod_eq.trans ok.product⟩

/-- For a composite distinguished entry, its value is forced and exactly the
permutations of the prime tail remain possible. -/
private theorem composite_rows {Y s n h : ℕ} {l : List ℕ} (ok : Good Y s n h l)
    (np : 0<n) (hc : ¬h.Prime) : rows Y s n=l.permutations.toFinset.image (List.cons h) := by
  ext w
  rw [mem_image]
  constructor
  · intro mem
    cases w with
    | nil => exact (nil_not_mem _ _ _ mem).elim
    | cons b t =>
      have other := mem_rows.mp mem
      have perm := (prime_entries other).trans (prime_entries ok).symm
      rw [if_neg hc] at perm
      by_cases bp : b.Prime
      · rw [if_pos bp] at perm
        have len := perm.length_eq
        simp [other.len,ok.len] at len
      · rw [if_neg bp] at perm
        have hprod := other.product.trans ok.product.symm
        rw [perm.prod_eq] at hprod
        have lp : 0<l.prod := Nat.pos_of_mul_pos_left (ok.product ▸ np)
        have bh := Nat.eq_of_mul_eq_mul_right lp hprod
        exact ⟨t,List.mem_toFinset.mpr (List.mem_permutations.mpr perm),by rw [bh]⟩
  · rintro ⟨t,mt,rfl⟩
    have perm := List.mem_permutations.mp (List.mem_toFinset.mp mt)
    exact mem_rows.mpr ⟨ok.head_mem,perm.length_eq.trans ok.len,
      fun p pm => ok.tail_mem p (perm.mem_iff.mp pm),by rw [perm.prod_eq,ok.product]⟩

/-- The exact rational value on nonempty support when each prime in the dyadic
band divides n at most once. Primes below the band may occur to any power. -/
theorem weight_of_row {Y s n h : ℕ} {l : List ℕ} (np : 0<n) (mem : h::l∈rows Y s n)
    (clean : ∀ p∈band Y, p.Prime → ¬p^2∣n) :
    weight Y s n = if h.Prime then 1 else 1/((s:ℚ)+1) := by
  have ok := mem_rows.mp mem
  unfold weight
  by_cases hp : h.Prime
  · have nd : (h::l).Nodup := by
      apply nodup_of_squares
      intro p pm
      rw [show (h::l).prod=n from ok.product]
      rcases List.mem_cons.mp pm with rfl|pl
      · exact clean _ ok.head_mem hp
      · exact clean p (ok.tail_mem p pl).1 (ok.tail_mem p pl).2
    rw [prime_rows ok hp,List.toFinset_card_of_nodup (List.nodup_permutations _ nd),
      List.length_permutations,List.length_cons,ok.len,if_pos hp]
    exact div_self (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
  · have dprod : l.prod∣n := ok.product ▸ dvd_mul_left l.prod h
    have nd : l.Nodup := nodup_of_squares (fun p pm dvd =>
      clean p (ok.tail_mem p pm).1 (ok.tail_mem p pm).2 (dvd.trans dprod))
    rw [composite_rows ok np hp,Finset.card_image_of_injective _ (fun _ _ e => (List.cons.inj e).2),
      List.toFinset_card_of_nodup (List.nodup_permutations _ nd),List.length_permutations,ok.len,
      if_neg hp,Nat.factorial_succ,Nat.cast_mul,Nat.cast_add_one]
    rw [mul_comm ((s:ℚ)+1) (s.factorial:ℚ),←div_div,div_self (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))]

/-- The support formulation does not require a choice of distinguished factor
in its hypothesis. -/
theorem dichotomy {Y s n : ℕ} (np : 0<n) (support : (rows Y s n).Nonempty)
    (clean : ∀ p∈band Y, p.Prime → ¬p^2∣n) :
    weight Y s n=1 ∨ weight Y s n=1/((s:ℚ)+1) := by
  obtain ⟨w,mem⟩ := support
  cases w with
  | nil => exact (nil_not_mem _ _ _ mem).elim
  | cons h l =>
    rw [weight_of_row np mem clean]
    split_ifs <;> simp

attribute [local irreducible] rows weight

/-- In (10,20], exchanging the prime 19 with the composite 15 leaves just the
six orders of the three tail primes, instead of all twenty-four permutations. -/
theorem examples :
    weight 20 3 46189=1 ∧ weight 20 3 36465=1/4 := by
  have witness (h : ℕ) (mem : h∈band 20) : h::[11,13,17]∈rows 20 3 (h*2431) := by
    apply mem_rows.mpr
    refine ⟨mem,rfl,?_,?_⟩
    · intro p pm
      simp only [List.mem_cons,List.not_mem_nil,or_false] at pm
      rcases pm with rfl|rfl|rfl <;> decide
    · rw [show [11,13,17].prod=2431 by decide]
  constructor
  · rw [weight_of_row (by decide) (witness 19 (by decide)) (by decide +kernel)]
    decide
  · rw [weight_of_row (by decide) (witness 15 (by decide)) (by decide +kernel)]
    rw [if_neg (by decide : ¬Nat.Prime 15)]
    norm_num

end PrimeFactors.HybridSmoothWeight
