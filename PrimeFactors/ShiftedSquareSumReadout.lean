import PrimeFactors.OddWidthSumPredictions
import PrimeFactors.FactorEndingSeparationControls

/-! A public shifted square root supplies one whole sum to test when the
factor-width promise puts the true sum in the upper half of the period. -/
namespace PrimeFactors.ShiftedSquareSumReadout

open OddWidthSumPredictions

set_option maxRecDepth 4096

/-- Of the two opposite predicted sum remainders, use the larger
canonical representative. It is computed from the public product. -/
def sum (N : ℕ) (j : ℕ) : ℕ :=
  let M : ℤ := 2^(2*j+3)
  let x := 2*root N j
  (max (x%M) ((-x)%M)).toNat

private theorem upper {s x M : ℤ} (pos : 0<M) (low : M≤2*s) (high : s<M) :
    (s ≡ x [ZMOD M] ∨ s ≡ -x [ZMOD M]) ↔ s=max (x%M) ((-x)%M) := by
  have bound : 0<s := by omega
  have h : s%M=s := Int.emod_eq_of_lt bound.le high
  have neg : (-s)%M=M-s := by
    have same : -s ≡ M-s [ZMOD M] := Int.modEq_iff_dvd.mpr ⟨1,by ring⟩
    exact Eq.trans same (Int.emod_eq_of_lt (by omega) (by omega))
  constructor
  · rintro (plus|minus)
    · have a : x%M=s := Eq.trans plus.symm h
      have b : (-x)%M=M-s := Eq.trans plus.neg.symm neg
      rw [a,b,max_eq_left (by omega)]
    · have a : (-x)%M=s := Eq.trans minus.symm h
      have b : x%M=M-s := Eq.trans (show x ≡ -s [ZMOD M] by simpa using minus.neg.symm) neg
      rw [a,b,max_eq_right (by omega)]
  · intro eq
    rcases le_total (x%M) ((-x)%M) with l|r
    · rw [max_eq_right l] at eq
      exact Or.inr (eq ▸ Int.mod_modEq ..)
    · rw [max_eq_left r] at eq
      exact Or.inl (eq ▸ Int.mod_modEq ..)

/-- In the upper half of the period, the candidate is the true integer
sum exactly for the specified gap class. -/
theorem sum_iff {p q j : ℕ} (hj : 2≤j) (op : Odd p) (oq : Odd q)
    (one : (p*q)%8=1) (lo : 2^(2*j+3)≤2*(p+q)) (hi : p+q<2^(2*j+3)) :
    sum (p*q) j=p+q ↔ ∃ z : ℤ, Odd z ∧ (q:ℤ)-p=2^(j+1)*z := by
  let M : ℤ := 2^(2*j+3)
  let s : ℤ := (p:ℤ)+q
  let x := 2*root ((p:ℤ)*q) j
  have mp : 0<M := by dsimp [M]; positivity
  have l : M≤2*s := by dsimp [M,s]; exact_mod_cast lo
  have h : s<M := by dsimp [M,s]; exact_mod_cast hi
  have pos : 0≤max (x%M) ((-x)%M) := (Int.emod_nonneg _ mp.ne').trans (le_max_left ..)
  have cast : (sum (p*q) j:ℤ)=max (x%M) ((-x)%M) := by
    simpa only [sum,Nat.cast_mul,x,M] using Int.toNat_of_nonneg pos
  have eq : sum (p*q) j=p+q ↔ s=max (x%M) ((-x)%M) := by
    rw [←cast]; dsimp only [s]; exact_mod_cast eq_comm
  rw [eq,←upper mp l h]
  apply true_iff hj (by exact_mod_cast op) (by exact_mod_cast oq)
  exact_mod_cast Int.natCast_modEq_iff.mpr (show p*q ≡ 1 [MOD 8] from one)

/-- Verify one candidate sum using an integer square root. A successful
answer contains two nontrivial factors with the stated product and sum. -/
def read (N j : ℕ) : Option (ℕ × ℕ) :=
  let s := sum N j
  let d := (s^2-4*N).sqrt
  let p := (s-d)/2
  let q := s-p
  if N%8=1 ∧ 1<p ∧ p≤q ∧ p*q=N then some (p,q) else none

theorem sound {N j a b : ℕ} (hit : read N j=some (a,b)) :
    1<a ∧ a≤b ∧ a*b=N ∧ a+b=sum N j := by
  simp only [read] at hit
  split_ifs at hit with ok
  · obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj hit)
    exact ⟨ok.2.1,ok.2.2.1,ok.2.2.2,by omega⟩

private theorem at_true {p q j : ℕ} (gt : 1<p) (le : p≤q) (gate : (p*q)%8=1) (eq : sum (p*q) j=p+q) :
    read (p*q) j=some (p,q) := by
  have id : (p+q)^2=4*(p*q)+(q-p)^2 := by
    obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le le
    simp only [Nat.add_sub_cancel_left]
    ring
  have delta : ((p+q)^2-4*(p*q)).sqrt=q-p := by rw [id,Nat.add_sub_cancel_left,Nat.sqrt_eq']
  simp only [read,eq,delta,show (p+q-(q-p))/2=p by omega,show p+q-p=q by omega,
    gate,gt,le,and_self,if_true]

/-- Complete recognition of the family for ordered odd primes in the
promised sum window. Every other eligible prime pair yields no split. -/
theorem read_iff {p q j : ℕ} (hj : 2≤j) (pp : p.Prime) (qp : q.Prime) (ord : p≤q)
    (op : Odd p) (oq : Odd q) (one : (p*q)%8=1)
    (lo : 2^(2*j+3)≤2*(p+q)) (hi : p+q<2^(2*j+3)) :
    (read (p*q) j).isSome=true ↔ ∃ z : ℤ, Odd z ∧ (q:ℤ)-p=2^(j+1)*z := by
  rw [←sum_iff hj op oq one lo hi]
  constructor
  · intro got
    rcases eq : read (p*q) j with _|⟨a,b⟩
    · simp [eq] at got
    · obtain ⟨gt,le,mul,same⟩ := sound eq
      obtain ⟨rfl,rfl⟩ := ordered_semiprime_pair_unique pp qp ord le gt mul
      exact same.symm
  · intro eq
    rw [at_true pp.one_lt ord one eq]
    rfl

/-- e=11 fixed in advance for ten-bit primes. These two twenty-bit
products even share their twelve low product bits. -/
theorem controls :
    sum 601049 4=1590 ∧ sum 842713 4=1590 ∧
    read 601049 4=some (619,971) ∧ read 842713 4=none := by
  have first : sum 601049 4=1590 := by decide +kernel
  have second : sum 842713 4=1590 := by decide +kernel
  have split := at_true (j:=4) (p:=619) (q:=971) (by decide) (by decide) (by decide +kernel)
  norm_num1 at split
  refine ⟨first,second,split first,?_⟩
  simp only [read,second,show (1590:ℕ)^2-4*842713=0 by decide +kernel,Nat.sqrt_zero]
  decide +kernel

end PrimeFactors.ShiftedSquareSumReadout
