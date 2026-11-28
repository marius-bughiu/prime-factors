import PrimeFactors.StratifiedPointQueryLower
import PrimeFactors.Certificate

/-! A finite binary decision tree sees a known-width product through probes
of its individual bits. Four one-bit neighbors force four specified probes
on one 26-bit product, even for a single output bit of the prime-factor sum. -/

namespace PrimeFactors.ToySumBitQueries

open StratifiedPointQueryLower

abbrev Rule (w : ℕ) := Tree (fun _ : Unit => w)

private noncomputable def oracle (w n : ℕ) (_ : Unit) : Finset ℕ :=
  (Finset.range w).filter (fun j => n.testBit j = true)

noncomputable def run {w : ℕ} (t : Rule w) (n : ℕ) := t.run (oracle w n)

/-- Indices on the path for this particular input, including repeated probes. -/
def path {w : ℕ} (t : Rule w) (n : ℕ) : List ℕ :=
  match t with
  | .leaf _ => []
  | .ask _ j yes no => j.val :: (if n.testBit j.val then path yes n else path no n)

private theorem at_probe {w n : ℕ} (u : Unit) (j : Fin w) :
    j.val ∈ oracle w n u ↔ n.testBit j.val = true := by simp [oracle,j.isLt]

theorem path_length {w : ℕ} (t : Rule w) (n : ℕ) : (path t n).length = (run t n).2 := by
  unfold run
  induction t with
  | leaf b => rfl
  | ask u j yes no yh nh =>
    cases bit : n.testBit j.val <;> simp [path,Tree.run,at_probe,bit,yh,nh]

/-- Agreement on the bits read along the first path gives the same answer
and the same number of probes, including for adaptive choices. -/
theorem replay {w n n' : ℕ} (t : Rule w)
    (agree : ∀ j ∈ path t n, n.testBit j=n'.testBit j) : run t n=run t n' := by
  unfold run
  induction t with
  | leaf b => rfl
  | ask u j yes no yh nh =>
    have bit := agree j.val (by simp [path])
    cases h : n.testBit j.val
    · have h' := bit.symm.trans h
      have same := nh (fun i hi => agree i (by simp [path,h,hi]))
      simp [Tree.run,at_probe,h,h',same]
    · have h' := bit.symm.trans h
      have same := yh (fun i hi => agree i (by simp [path,h,hi]))
      simp [Tree.run,at_probe,h,h',same]

/-- If flipping a single bit changes the required answer, any correct
path on the original input must query that position. -/
theorem forced {w n i : ℕ} {t : Rule w}
    (different : (run t n).1 ≠ (run t (n ^^^ 2^i)).1) : i ∈ path t n := by
  by_contra skip
  apply different
  apply congrArg Prod.fst (replay t ?_)
  intro j seen
  have ne : i≠j := fun eq => skip (eq ▸ seen)
  simp [Nat.testBit_xor,Nat.testBit_two_pow,ne]

def center : ℕ := 40270613
def bit : Fin 4 → ℕ := ![2,3,4,22]
def left : Fin 4 → ℕ := ![6053,4943,6151,5303]
def right : Fin 4 → ℕ := ![6653,8147,6547,6803]

/-- Both distinct prime factors have 13 bits and their product has 26. -/
def Promised (n p q : ℕ) : Prop :=
  ExactFactorization n [p,q] ∧ 4096 ≤ p ∧ p < q ∧ q < 8192 ∧ 2^25 ≤ n ∧ n < 2^26

theorem center_certificate : Promised center 5897 6829 ∧ ((5897+6829 : ℕ).testBit 2=true) := by
  constructor
  · norm_num [Promised,center,ExactFactorization]
  · decide

theorem neighbor_certificate (j : Fin 4) :
    Promised (center ^^^ 2^(bit j)) (left j) (right j) ∧
      (left j+right j).testBit 2=false := by
  have pairs : ∀ i, (left i).Prime ∧ (right i).Prime := by
    intro i
    fin_cases i <;> norm_num [left,right]
  have arithmetic : ∀ i, (left i)*(right i)=center ^^^ 2^(bit i) ∧ 4096≤left i ∧
      left i<right i ∧ right i<8192 ∧ 2^25≤center ^^^ 2^(bit i) ∧ center ^^^ 2^(bit i)<2^26 ∧
      (left i+right i).testBit 2=false := by decide +kernel
  obtain ⟨product,lo,lt,hi,nlo,nhi,out⟩ := arithmetic j
  exact ⟨⟨⟨by simpa using product,by simpa using pairs j⟩,lo,lt,hi,nlo,nhi⟩,out⟩

def Correct (t : Rule 26) : Prop :=
  ∀ n p q, Promised n p q → (run t n).1 = (p+q).testBit 2

/-- On 40,270,613, any correct adaptive tree must read bits 2, 3, 4 and
22 (numbered from zero), just to return bit 2 of the factor sum. -/
theorem required_positions {t : Rule 26} (correct : Correct t) :
    ({2,3,4,22} : Finset ℕ) ⊆ (path t center).toFinset ∧ 4 ≤ (run t center).2 := by
  have all (j : Fin 4) : bit j ∈ path t center := by
    apply forced
    rw [correct _ _ _ center_certificate.1,center_certificate.2,
      correct _ _ _ (neighbor_certificate j).1,(neighbor_certificate j).2]
    decide
  have cover : ({2,3,4,22} : Finset ℕ) ⊆ (path t center).toFinset := by
    intro i h
    apply List.mem_toFinset.mpr
    simp only [Finset.mem_insert,Finset.mem_singleton] at h
    rcases h with rfl|rfl|rfl|rfl
    · exact all 0
    · exact all 1
    · exact all 2
    · exact all 3
  refine ⟨cover,?_⟩
  rw [←path_length]
  exact (show 4=({2,3,4,22} : Finset ℕ).card by decide).le.trans
    ((Finset.card_le_card cover).trans (List.toFinset_card_le _))

end PrimeFactors.ToySumBitQueries
