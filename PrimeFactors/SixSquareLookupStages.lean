import PrimeFactors.SixSquareAuxiliarySieve

/-! Scalar lookups in the ascending six-prime-square sieve. Stage zero
contains every incoming candidate, and stage six contains the final survivors. -/
namespace PrimeFactors.SixSquareLookupStages

open Finset LocalSumMenu
open private PrimeFactors.PublicPrimeSquareCounts.second_count from PrimeFactors.PublicPrimeSquareCounts
open scoped Classical

noncomputable def bases : List ℕ := [3,7,11,13,17,19]
noncomputable def prime (i : Fin 6) := bases[i.val]'(by have h := i.isLt; exact h)
noncomputable def period (j : Fin 7) := ((bases.take j.val).map (fun p => p^2)).prod
noncomputable def cap (j : Fin 7) := ((bases.take j.val).map (fun p => p*(p-1)/2)).prod
private noncomputable def localCap (i : Fin 6) := (prime i)*(prime i-1)/2

instance (j : Fin 7) : NeZero (period j) := ⟨(by decide +kernel : ∀ j : Fin 7,period j≠0) j⟩
theorem coprime (j : Fin 7) : Nat.Coprime 100 (period j) := (by decide +kernel : ∀ j, Nat.Coprime 100 (period j)) j

private theorem rule (i : Fin 6) :
    period i.succ=period i.castSucc*(prime i)^2 ∧ cap i.succ=cap i.castSucc*localCap i ∧
    (period i.castSucc).Coprime ((prime i)^2) ∧ (prime i).Prime ∧ prime i≠2 ∧
    prime i∣SixSquareAuxiliarySieve.L := by revert i; decide +kernel

noncomputable def A (n : ℕ) (j : Fin 7) : Finset (ZMod (period j)) :=
  univ.filter (AdmissibleSum (n:ZMod (period j)))

theorem mem_A (n : ℕ) (j : Fin 7) (s : ℕ) :
    (s:ZMod (period j))∈A n j ↔ AdmissibleSum (n:ZMod (period j)) (s:ZMod (period j)) := by
  simp only [A,mem_filter,mem_univ,true_and]

theorem first (n s : ℕ) : (s:ZMod (period 0))∈A n 0 := by
  rw [mem_A]
  change AdmissibleSum (n:ZMod 1) (s:ZMod 1)
  exact ⟨0,0,Subsingleton.elim ..,Subsingleton.elim ..⟩

theorem last (n s : ℕ) : (s:ZMod (period 6))∈A n 6 ↔
    (s:ZMod SixSquareAuxiliarySieve.L)∈SixSquareAuxiliarySieve.A n := by
  rw [mem_A,SixSquareAuxiliarySieve.mem_A]

/-- Passing the next square is precisely the extra condition at the
next stage. Each candidate is charged before this test is applied. -/
theorem step (n s : ℕ) (i : Fin 6) :
    (s:ZMod (period i.succ))∈A n i.succ ↔
      (s:ZMod (period i.castSucc))∈A n i.castSucc ∧
        AdmissibleSum (n:ZMod ((prime i)^2)) (s:ZMod ((prime i)^2)) := by
  rw [mem_A,mem_A,(rule i).1]
  exact PublicWheelLookupCosts.extend_prefix (rule i).2.2.1 n s

private theorem size (n : ℕ) (j : Fin 7) : (A n j).card=count n (period j) := by
  rw [count,Nat.card_eq_fintype_card,Fintype.card_subtype]
  rfl

private theorem size_start (n : ℕ) : count n (period 0)=1 := by
  change Nat.card {s : ZMod 1 // AdmissibleSum (n:ZMod 1) s}=1
  haveI : Nonempty {s : ZMod 1 // AdmissibleSum (n:ZMod 1) s} :=
    ⟨⟨0,0,0,Subsingleton.elim ..,Subsingleton.elim ..⟩⟩
  exact Nat.card_unique

private theorem size_step (n : ℕ) (i : Fin 6) : count n (period i.succ)=
    count n (period i.castSucc)*count n ((prime i)^2) := by
  rw [(rule i).1]; exact card_admissibleSum_crt (rule i).2.2.1 n

theorem card_bound {n : ℕ} (cop : n.Coprime SixSquareAuxiliarySieve.L) (j : Fin 7) :
    (A n j).card≤cap j := by
  rw [size]
  induction j using Fin.induction with
  | zero => exact (size_start n).le
  | succ i prev =>
    obtain ⟨_,next,_,pp,odd,dvd⟩ := rule i
    have digit := PrimeFactors.PublicPrimeSquareCounts.second_count pp odd
      (pp.coprime_iff_not_dvd.mp (cop.of_dvd_right dvd).symm)
    have bound : ∀ i : Fin 6, ∀ sign : Bool, primePowerSumCount (prime i) sign 2≤localCap i := by decide +kernel
    rw [next,size_step]
    exact Nat.mul_le_mul prev (digit.le.trans (bound i _))

private instance (i : Fin 6) : NeZero (prime i) := ⟨(rule i).2.2.2.1.ne_zero⟩

private theorem valid41 : ∀ t : Fin 6, primePowerSumCount (prime t)
    (decide (∃ x : ZMod (prime t), x*x=(41:ZMod (prime t)))) 2=localCap t := by decide +kernel

/-- The product 41 attains every stage cap simultaneously. -/
theorem sharp (j : Fin 7) : (A 41 j).card=cap j := by
  rw [size]
  induction j using Fin.induction with
  | zero => exact size_start 41
  | succ i prev =>
    obtain ⟨_,next,_,pp,odd,dvd⟩ := rule i
    have nd := pp.coprime_iff_not_dvd.mp (SixSquareAuxiliarySieve.sharp.1.of_dvd_right dvd).symm
    have digit := PrimeFactors.PublicPrimeSquareCounts.second_count pp odd nd
    rw [size_step,next,prev,digit]
    exact congrArg (cap i.castSucc * ·) (valid41 i)

/-- Survivors after j tests from an arbitrary finite collection of candidates. -/
noncomputable def hits (n : ℕ) (j : Fin 7) (S : Finset ℕ) := S.filter (fun s : ℕ => (s:ZMod (period j))∈A n j)

theorem hits_step (n : ℕ) (S : Finset ℕ) (i : Fin 6) :
    hits n i.succ S = (hits n i.castSucc S).filter
      (fun s : ℕ => AdmissibleSum (n:ZMod ((prime i)^2)) (s:ZMod ((prime i)^2))) := by
  ext s
  simp only [hits,mem_filter,step,and_assoc]

/-- One scalar table lookup per candidate still present at each proper prefix. -/
noncomputable def lookupWork (n : ℕ) (S : Finset ℕ) := ∑ i : Fin 6,(hits n i.castSucc S).card

theorem density_sum : (∑ i : Fin 6,(cap i.castSucc:ℚ)/period i.castSucc)=80926/51051 := by decide +kernel
theorem cap_sum : (∑ i : Fin 6,cap i.castSucc)=37030522 := by decide +kernel

/-- One bit per possible local residue, with optional independent byte rounding. -/
theorem table_sizes : (∑ i : Fin 6,(prime i)^2)=998 ∧
    (∑ i : Fin 6,((prime i)^2+7)/8)=130 := by decide +kernel

end PrimeFactors.SixSquareLookupStages
