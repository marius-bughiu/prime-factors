import PrimeFactors.FactorSum
import PrimeFactors.PhaseCharacters
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity

/-! Incidence counts for a fixed list of proposed factor sums while the product
ranges over the nonzero residues. The character identity underlying the pair
count is the classical Paley difference-set calculation. -/
namespace PrimeFactors.SumGuessIncidence

open Finset
open scoped Classical
variable {p : ℕ} [Fact p.Prime]

private noncomputable def flag (x : ZMod p) : ℤ := if IsSquare x then 1 else 0

/-- Integer indicator that the known product allows the proposed sum. -/
noncomputable def pass (n s : ZMod p) : ℤ := flag (-(4:(ZMod p))*n+s^2)

theorem pass_eq (odd : p ≠ 2) (n s : ZMod p) :
    pass n s = if AdmissibleSum n s then 1 else 0 := by
  rw [admissibleSum_iff_isSquare odd]
  simp only [pass,flag,neg_mul,sub_eq_add_neg,add_comm]

private theorem twice_flag (x : ZMod p) :
    2*flag x = 1+quadraticChar (ZMod p) x+(if x=0 then 1 else 0) := by
  by_cases zero : x=0
  · subst x; simp [flag,IsSquare.zero]
  by_cases square : IsSquare x
  · simp [flag,square,zero,(quadraticChar_one_iff_isSquare zero).mpr square]
  · simp [flag,square,zero,quadraticChar_neg_one_iff_not_isSquare.mpr square]

private theorem char_sum (odd : p≠2) (c : ZMod p) :
    ∑ r : ZMod p, quadraticChar (ZMod p) (r+c) = 0 :=
  (Equiv.sum_comp (Equiv.addRight c) (quadraticChar (ZMod p))).trans
    (quadraticChar_sum_zero (by rwa [ZMod.ringChar_zmod_n]))

private theorem single_flag (odd : p≠2) (c : ZMod p) :
    2*(∑ r : ZMod p, flag (r+c)) = (p:ℤ)+1 := by
  rw [mul_sum]
  simp_rw [twice_flag,add_eq_zero_iff_eq_neg]
  rw [sum_add_distrib,sum_add_distrib,char_sum odd]
  simp [ZMod.card]

private theorem pair_term (c d r : ZMod p) (ne : c≠d) :
    4*flag (r+c)*flag (r+d) = 1+quadraticChar (ZMod p) (r+c)+quadraticChar (ZMod p) (r+d)+
      quadraticChar (ZMod p) ((r+c)*(r+d))+
      (if r= -c then 1+quadraticChar (ZMod p) (d-c) else 0)+
      (if r= -d then 1+quadraticChar (ZMod p) (c-d) else 0) := by
  rw [show 4*flag (r+c)*flag (r+d)=(2*flag (r+c))*(2*flag (r+d)) by ring,
    twice_flag,twice_flag,map_mul]
  simp only [add_eq_zero_iff_eq_neg]
  by_cases rc : r= -c
  · subst r; simp [ne,sub_eq_add_neg,add_comm]; ring
  by_cases rd : r= -d
  · subst r; simp [ne.symm,sub_eq_add_neg,add_comm]; ring
  simp only [if_neg rc,if_neg rd,add_zero]
  ring

private theorem pair_flag (odd : p≠2) (c d : ZMod p) (ne : c≠d) :
    4*(∑ r : ZMod p, flag (r+c)*flag (r+d)) =
    (p:ℤ)+1+quadraticChar (ZMod p) (d-c)+quadraticChar (ZMod p) (c-d) := by
  rw [mul_sum]
  simp_rw [←mul_assoc,pair_term c d _ ne,sum_add_distrib]
  rw [char_sum odd,char_sum odd,phaseCharacters_shift_sum (by rwa [ZMod.ringChar_zmod_n]) ne]
  simp [ZMod.card]
  ring

private theorem reindex (odd : p≠2) (f : ZMod p → ℤ) :
    ∑ n : ZMod p, f (-(4:(ZMod p))*n) = ∑ r : ZMod p, f r := by
  have two : (2:(ZMod p))≠0 := Ring.two_ne_zero (by rwa [ZMod.ringChar_zmod_n])
  have four : (4:(ZMod p))≠0 := by simpa only [show (4:(ZMod p))=2*2 by ring] using mul_ne_zero two two
  exact Equiv.sum_comp (Equiv.mulLeft₀ _ (neg_ne_zero.mpr four)) f

private theorem pass_zero (s : ZMod p) : pass 0 s = 1 := by simp [pass,flag,IsSquare.sq]

/-- Every candidate passes for exactly half of the nonzero product residues. -/
theorem single (odd : p≠2) (s : ZMod p) :
    2*(∑ n ∈ univ.erase (0:(ZMod p)), pass n s) = (p:ℤ)-1 := by
  have full := reindex odd (fun r => flag (r+s^2))
  change (∑ n : ZMod p, pass n s) = _ at full
  have split := sum_erase_add (univ : Finset (ZMod p)) (fun n => pass n s) (mem_univ 0)
  dsimp only at split
  rw [pass_zero,full] at split
  linarith [single_flag odd (s^2)]

/-- For distinct squared guesses, the overlap includes the two discriminant-zero
corrections. Product zero, at which both guesses always pass, is excluded. -/
theorem pair (odd : p≠2) (s t : ZMod p) (distinct : s^2≠t^2) :
    4*(∑ n ∈ univ.erase (0:(ZMod p)), pass n s*pass n t) =
      (p:ℤ)-3+quadraticChar (ZMod p) (t^2-s^2)+quadraticChar (ZMod p) (s^2-t^2) := by
  have full := reindex odd (fun r => flag (r+s^2)*flag (r+t^2))
  change (∑ n : ZMod p, pass n s*pass n t) = _ at full
  have split := sum_erase_add (univ : Finset (ZMod p)) (fun n => pass n s*pass n t) (mem_univ 0)
  dsimp only at split
  rw [pass_zero,pass_zero,one_mul,full] at split
  linarith [pair_flag odd (s^2) (t^2) distinct]

/-- At primes 3 modulo 4 the intersection has the same size for every
pair of guesses with different squares. -/
theorem pair_three (cls : p%4=3) (s t : ZMod p) (distinct : s^2≠t^2) :
    4*(∑ n ∈ univ.erase (0:(ZMod p)), pass n s*pass n t) = (p:ℤ)-3 := by
  have minus : quadraticChar (ZMod p) (-1) = -1 := quadraticChar_neg_one_iff_not_isSquare.mpr
    (fun h => FiniteField.isSquare_neg_one_iff.mp h (by simpa [ZMod.card] using cls))
  have flip : s^2-t^2=(-1:(ZMod p))*(t^2-s^2) := by ring
  rw [pair (by omega) s t distinct,flip,map_mul,minus]
  ring

/-- Number of sums on a public list which remain locally compatible. -/
noncomputable def survivors (A : Finset (ZMod p)) (n : ZMod p) : ℤ := ∑ s ∈ A, pass n s

theorem total (odd : p≠2) (A : Finset (ZMod p)) :
    2*(∑ n ∈ univ.erase (0:(ZMod p)), survivors A n) = ((p:ℤ)-1)*A.card := by
  unfold survivors
  rw [sum_comm,mul_sum]
  simp_rw [single odd]
  simp only [sum_const,nsmul_eq_mul]
  ring

private noncomputable def center (n s : ZMod p) : ℤ := 2*pass n s-1

private theorem center_sum (A : Finset (ZMod p)) (n : ZMod p) :
    (∑ s ∈ A, center n s) = 2*survivors A n-A.card := by
  simp only [center,survivors,sum_sub_distrib,←mul_sum,sum_const,nsmul_eq_mul,mul_one]

private theorem correlation (cls : p%4=3) (s t : ZMod p) :
    (∑ n ∈ univ.erase (0:(ZMod p)), center n s*center n t) =
      (if s^2=t^2 then (p:ℤ)+1 else 0)-2 := by
  have hp := (Fact.out : p.Prime).pos
  have size : ((univ.erase (0:(ZMod p))).card:ℤ)=(p:ℤ)-1 := by
    rw [card_erase_of_mem (mem_univ _),card_univ,ZMod.card,Nat.cast_sub (by omega),Nat.cast_one]
  by_cases eq : s^2=t^2
  · rw [if_pos eq]
    have term (n : ZMod p) : center n s*center n t=1 := by
      unfold center pass flag
      rw [eq]
      split <;> decide
    simp_rw [term]
    rw [sum_const,nsmul_eq_mul,size]
    ring
  · rw [if_neg eq]
    have term (n : ZMod p) : center n s*center n t =
        4*(pass n s*pass n t)-2*pass n s-2*pass n t+1 := by unfold center; ring
    simp_rw [term,sum_add_distrib,sum_sub_distrib,←mul_sum]
    rw [pair_three cls s t eq,single (by omega),single (by omega),sum_const,nsmul_eq_mul,size]
    ring

/-- The correlation with one proposed sum reads off the number of list elements
having its square. Opposite guesses therefore count as repetitions. -/
theorem multiplicity (cls : p%4=3) (A : Finset (ZMod p)) (t : ZMod p) :
    (∑ n ∈ univ.erase (0:(ZMod p)), (2*survivors A n-A.card)*(2*pass n t-1)) =
      ((p:ℤ)+1)*(A.filter (fun s => s^2=t^2)).card-2*A.card := by
  change (∑ n ∈ univ.erase (0:(ZMod p)), (2*survivors A n-A.card)*center n t) = _
  simp_rw [←center_sum,sum_mul]
  rw [sum_comm]
  simp_rw [correlation cls,sum_sub_distrib]
  rw [←sum_filter]
  simp only [sum_const,nsmul_eq_mul]
  ring

/-- An exact measure of the variation for an arbitrary list, including both
signs of the same guess. Each ordered pair with equal squares contributes p+1. -/
theorem spread_general (cls : p%4=3) (A : Finset (ZMod p)) :
    (∑ n ∈ univ.erase (0:(ZMod p)), (2*survivors A n-A.card)^2) =
      ((p:ℤ)+1)*(∑ t ∈ A, ((A.filter (fun s => s^2=t^2)).card:ℤ))-2*(A.card:ℤ)^2 := by
  have term (n : ZMod p) : (2*survivors A n-A.card)^2 =
      ∑ s ∈ A, (2*survivors A n-A.card)*(2*pass n s-1) := by
    change _ = ∑ s ∈ A, (2*survivors A n-A.card)*center n s
    rw [←mul_sum,center_sum,pow_two]
  simp_rw [term]
  rw [sum_comm]
  simp_rw [multiplicity cls]
  rw [sum_sub_distrib,←mul_sum,sum_const,nsmul_eq_mul]
  ring

/-- Exact total squared deviation from half the list size when no two guesses
have equal squares modulo the test prime. The sum runs over every nonzero product. -/
theorem spread (cls : p%4=3) (A : Finset (ZMod p)) (inj : Set.InjOn (fun x : ZMod p => x^2) A) :
    (∑ n ∈ univ.erase (0:(ZMod p)), (2*survivors A n-A.card)^2) =
      (A.card:ℤ)*((p:ℤ)+1-2*A.card) := by
  have same (s : ZMod p) (hs : s∈A) : A.filter (fun t => t^2=s^2)={s} := by
    ext t
    simpa only [mem_filter,mem_singleton] using
      (show (t∈A ∧ t^2=s^2) ↔ t=s from
        ⟨fun ⟨ht,eq⟩ => inj ht hs eq,fun eq => by subst t; exact ⟨hs,rfl⟩⟩)
  rw [spread_general cls A]
  have count : (∑ t ∈ A, ((A.filter (fun s => s^2=t^2)).card:ℤ)) = A.card := by
    calc _ = ∑ _t ∈ A, (1:ℤ) := sum_congr rfl fun t ht => by rw [same t ht,card_singleton,Nat.cast_one]
         _ = _ := by simp
  rw [count]
  ring

/-- A half-period containing one representative of each squared guess leaves
exactly half its entries for each known nonzero product. -/
theorem exact_half (cls : p%4=3) (A : Finset (ZMod p)) (inj : Set.InjOn (fun x : ZMod p => x^2) A)
    (full : 2*A.card=p+1) {n : ZMod p} (unit : n≠0) : 2*survivors A n=A.card := by
  have sum := spread cls A inj
  have eq : 2*(A.card:ℤ)=(p:ℤ)+1 := by exact_mod_cast full
  rw [eq,sub_self,mul_zero] at sum
  have zero := (sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (2*survivors A i-A.card))).mp sum n
    (mem_erase.mpr ⟨unit,mem_univ _⟩)
  nlinarith

/-- Conversely, a nonempty list which always leaves exactly half must have
one representative for every square, including zero. -/
theorem necessary (cls : p%4=3) (A : Finset (ZMod p)) (nonempty : A.Nonempty)
    (flat : ∀ n : ZMod p, n≠0 → 2*survivors A n=A.card) :
    ∀ t : ZMod p, (A.filter (fun s => s^2=t^2)).card=1 := by
  have counts (t : ZMod p) : ((p:ℤ)+1)*(A.filter (fun s => s^2=t^2)).card=2*A.card := by
    have eq := multiplicity cls A t
    rw [sum_eq_zero (fun n hn => by rw [flat n (mem_erase.mp hn).1,sub_self,zero_mul])] at eq
    linarith
  have atZero : (A.filter (fun s => s^2=(0:(ZMod p))^2)).card ≤ 1 := by
    apply card_le_one.mpr
    intro a ha b hb
    simpa using (show a=0 from by simpa using (mem_filter.mp ha).2).trans
      (show b=0 from by simpa using (mem_filter.mp hb).2).symm
  have pos := card_pos.mpr nonempty
  have c := counts 0
  have nonzero : (A.filter (fun s => s^2=(0:(ZMod p))^2)).card≠0 := by
    intro h; rw [h,Nat.cast_zero,mul_zero] at c; omega
  have one : (A.filter (fun s => s^2=(0:(ZMod p))^2)).card=1 := by omega
  rw [one,Nat.cast_one,mul_one] at c
  intro t
  have all := (counts t).trans c.symm
  have val : ((A.filter (fun s => s^2=t^2)).card:ℤ)=1 :=
    mul_left_cancel₀ (by positivity : (p:ℤ)+1≠0) (all.trans (mul_one _).symm)
  exact_mod_cast val

/-- The lower half of a complete period gives one representative of each
square. The factor step can be any nonzero residue. -/
noncomputable def halfPeriod (p : ℕ) [Fact p.Prime] : Finset (ZMod p) :=
  univ.filter (fun x : ZMod p => 2*x.val<p)

private theorem half_card : (halfPeriod p).card=(p+1)/2 := by
  rw [←card_range ((p+1)/2)]
  refine card_bij (fun x _ => x.val) ?_ ?_ ?_
  · intro x hx
    have := (mem_filter.mp hx).2
    apply mem_range.mpr
    change x.val < (p+1)/2
    omega
  · intro a _ b _ eq
    simpa only [ZMod.natCast_zmod_val] using congrArg (fun v : ℕ => (v:(ZMod p))) eq
  · intro j hj
    have h := mem_range.mp hj
    have lt : j<p := by have := (Fact.out : p.Prime).pos; omega
    have val : (j:(ZMod p)).val=j := by rw [ZMod.val_natCast,Nat.mod_eq_of_lt lt]
    exact ⟨j,mem_filter.mpr ⟨mem_univ _,by rw [val]; omega⟩,val⟩

private theorem half_inj : Set.InjOn (fun x : ZMod p => x^2) (halfPeriod p) := by
  intro x hx y hy same
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp same with eq|eq
  · exact eq
  have small : x.val+y.val<p := by
    have := (mem_filter.mp hx).2
    have := (mem_filter.mp hy).2
    omega
  have sumz : ((x.val+y.val:ℕ):(ZMod p))=0 := by
    rw [Nat.cast_add,ZMod.natCast_zmod_val,ZMod.natCast_zmod_val,eq,neg_add_cancel]
  have h := (ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mp sumz
  have zv : x.val+y.val=0 := by
    by_contra! ne
    exact (not_le_of_gt small) (Nat.le_of_dvd (by omega) h)
  have xy : x.val=y.val := by omega
  simpa only [ZMod.natCast_zmod_val] using congrArg (fun v : ℕ => (v:(ZMod p))) xy

/-- A block of guesses starting at zero modulo p and moving in steps of w.
Both directions work, so a public interval may use either end as the anchor. -/
noncomputable def block (w : ZMod p) : Finset (ZMod p) := (halfPeriod p).image (fun j => w*j)

theorem block_exact (cls : p%4=3) {n w : ZMod p} (unit : n≠0) (step : w≠0) :
    4*survivors (block w) n = (p:ℤ)+1 := by
  have size : (block w).card=(p+1)/2 :=
    (card_image_of_injective _ (mul_right_injective₀ step)).trans half_card
  have inj : Set.InjOn (fun x : ZMod p => x^2) (block w) := by
    rintro x hx y hy eq
    obtain ⟨a,ha,rfl⟩ := mem_image.mp hx
    obtain ⟨b,hb,rfl⟩ := mem_image.mp hy
    change (w*a)^2=(w*b)^2 at eq
    rw [mul_pow,mul_pow] at eq
    rw [half_inj ha hb (mul_left_cancel₀ (pow_ne_zero 2 step) eq)]
  have count := exact_half cls (block w) inj (by rw [size]; omega) unit
  have two : 2*((block w).card:ℤ)=(p:ℤ)+1 := by exact_mod_cast (show 2*(block w).card=p+1 by rw [size]; omega)
  linarith

/-- The descending stride-four block starting at 5518 leaves eight sums.
The integer square test then selects 5474 from those eight. -/
theorem worked :
    let candidates : List ℕ := (List.range 16).map (fun i => 5518-4*i)
    let kept := candidates.filter (fun s => (List.range 31).any
      (fun d => decide (d^2%31=(s^2-4*7294033)%31)))
    let checked := kept.zip ([1127,1088,1003,936,912,888,810,783] : List ℕ)
    kept=[5518,5510,5494,5482,5478,5474,5462,5458] ∧
    checked.all (fun (s,r) => decide (r^2+4*7294033≤s^2 ∧ s^2<(r+1)^2+4*7294033))=true ∧
    checked.filter (fun (s,r) => decide (s^2=4*7294033+r^2))=[(5474,888)] ∧
    Nat.Prime 2293 ∧ Nat.Prime 3181 ∧ 2293*3181=7294033 ∧ 2293+3181=5474 := by
  dsimp only
  refine (and_iff_left_of_imp ?_).mpr (by decide +kernel)
  intro table
  rw [table]
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide,by decide⟩

end PrimeFactors.SumGuessIncidence
