import PrimeFactors.FactorSumCRT

/-! Short arithmetic progressions of locally admissible factor sums.
A product in the square class of 73 modulo 315 admits a step for which a
13-term progression contains at most one possible sum, and a 45-term
progression contains at most two. Each length is optimal uniformly over the
starting point, even when the step may depend on the product. -/

namespace PrimeFactors.PrimeSumListPacking

/-- A collision can be translated so its first surviving index is zero. -/
def PairHit {m : ℕ} (n t : ZMod m) (length : ℕ) : Prop :=
  ∃ s : ZMod m, ∃ i : ℕ, 0 < i ∧ i < length ∧
    AdmissibleSum n s ∧ AdmissibleSum n (s+i*t)

/-- Three surviving terms in a translated progression, including its first. -/
def TripleHit {m : ℕ} (n t : ZMod m) (length : ℕ) : Prop :=
  ∃ s : ZMod m, ∃ i j : ℕ, 0 < i ∧ i < j ∧ j < length ∧
    AdmissibleSum n s ∧ AdmissibleSum n (s+i*t) ∧ AdmissibleSum n (s+j*t)

private theorem shift {m : ℕ} (s t : ZMod m) {i j : ℕ} (le : i ≤ j) :
    s+i*t+(j-i:ℕ)*t = s+j*t := by
  rw [Nat.cast_sub le]
  ring

/-- Every translated list, with no assumption on its initial candidate. -/
theorem distinct_pair {m L : ℕ} {n t s : ZMod m} (h : ¬PairHit n t L)
    {i j : ℕ} (ij : i<j) (jl : j<L) (first : AdmissibleSum n (s+i*t)) :
    ¬AdmissibleSum n (s+j*t) := by
  intro last
  exact h ⟨_,j-i,by omega,by omega,first, (shift s t ij.le).symm ▸ last⟩

theorem distinct_triple {m L : ℕ} {n t s : ZMod m} (h : ¬TripleHit n t L)
    {i j k : ℕ} (ij : i<j) (jk : j<k) (kl : k<L) (first : AdmissibleSum n (s+i*t))
    (second : AdmissibleSum n (s+j*t)) : ¬AdmissibleSum n (s+k*t) := by
  intro last
  exact h ⟨_,j-i,k-i,by omega,by omega,by omega,first,
    (shift s t ij.le).symm ▸ second,(shift s t (ij.trans jk).le).symm ▸ last⟩

private theorem crtNat {a b : ℕ} (h : a.Coprime b) (n s : ℕ) :
    AdmissibleSum (n : ZMod (a*b)) (s : ZMod (a*b)) ↔
    AdmissibleSum (n : ZMod a) (s : ZMod a) ∧ AdmissibleSum (n : ZMod b) (s : ZMod b) := by
  simpa only [map_natCast,Prod.fst_natCast,Prod.snd_natCast] using
    admissibleSum_crt_iff h (n : ZMod (a*b)) (s : ZMod (a*b))

private noncomputable def sumDec {m : ℕ} [NeZero m] (n s : ZMod m) :
    Decidable (AdmissibleSum n s) := by unfold AdmissibleSum; infer_instance
attribute [local instance] sumDec

/-- Every admissible sum in one complete period for the representative product. -/
def sums : List ℕ := [11,56,74,101,119,151,164,196,214,241,259,304]

private theorem localSums (s : ZMod 315) :
    AdmissibleSum 73 s ↔ s.val ∈ sums := by
  have nine : ∀ z : ZMod 9, AdmissibleSum ((73:ℕ):ZMod 9) z ↔ z=2 ∨ z=7 := by decide +kernel
  have five : ∀ z : ZMod 5, AdmissibleSum ((73:ℕ):ZMod 5) z ↔ z=1 ∨ z=4 := by decide +kernel
  have seven : ∀ z : ZMod 7, AdmissibleSum ((73:ℕ):ZMod 7) z ↔ z=0 ∨ z=3 ∨ z=4 := by decide +kernel
  have table : ∀ j : Fin 315,
      (((j.val:ZMod 9)=2 ∨ (j.val:ZMod 9)=7) ∧
       ((j.val:ZMod 5)=1 ∨ (j.val:ZMod 5)=4) ∧
       ((j.val:ZMod 7)=0 ∨ (j.val:ZMod 7)=3 ∨ (j.val:ZMod 7)=4)) ↔ j.val∈sums := by
    decide +kernel
  calc
    AdmissibleSum 73 s ↔ AdmissibleSum ((73:ℕ):ZMod (9*(5*7))) (s.val:ZMod (9*(5*7))) := by
      rw [ZMod.natCast_zmod_val]; rfl
    _ ↔ _ := by
      rw [crtNat (a:=9) (b:=5*7) (by decide),crtNat (a:=5) (b:=7) (by decide),
        nine,five,seven]
      exact table ⟨_,s.val_lt⟩

private theorem natSums (a : ℕ) :
    AdmissibleSum 73 (a : ZMod 315) ↔ a%315 ∈ sums := by
  rw [localSums,ZMod.val_natCast]

private def accepted (s : ℕ) : Bool := sums.contains (s%315)

private theorem addSums (x i t : ℕ) :
    AdmissibleSum 73 ((x:ZMod 315)+(i:ZMod 315)*(t:ZMod 315)) ↔ accepted (x+i*t) = true := by
  simpa only [Nat.cast_add,Nat.cast_mul,accepted,List.contains_iff_mem] using natSums (x+i*t)

private theorem oneStep : ¬PairHit (73 : ZMod 315) 1 13 ∧ ¬TripleHit (73 : ZMod 315) 1 45 := by
  have single : ∀ x : Fin 315, x.val∈sums → ∀ i : Fin 13, (0 < i.val) →
    accepted (x.val+i.val*1)=false := by decide +kernel
  have double : ∀ x : Fin 315, x.val∈sums → ∀ i : Fin 45, (0 < i.val) →
    accepted (x.val+i.val*1)=true → ∀ j : Fin 45, (i < j) → accepted (x.val+j.val*1)=false := by decide +kernel
  constructor
  · rintro ⟨s,i,ip,il,hs,hi⟩
    have yes := (addSums s.val i 1).mp (by simpa only [ZMod.natCast_zmod_val,Nat.cast_one] using hi)
    exact Bool.noConfusion ((single ⟨_,s.val_lt⟩ ((localSums _).mp hs) ⟨i,il⟩ ip).symm.trans yes)
  · rintro ⟨s,i,j,ip,ij,jl,hs,hi,hj⟩
    have hit (i : ℕ) (h : AdmissibleSum 73 (s+(i:ZMod 315)*1)) := (addSums s.val i 1).mp
      (by simpa only [ZMod.natCast_zmod_val,Nat.cast_one] using h)
    exact Bool.noConfusion ((double ⟨_,s.val_lt⟩ ((localSums _).mp hs) ⟨i,ij.trans jl⟩
      ip (hit i hi) ⟨j,jl⟩ ij).symm.trans (hit j hj))

/-- The first two positive offsets which land back in the twelve-element list.
The final check below verifies the returned offsets independently. -/
private def offsets (x t : ℕ) : ℕ × ℕ :=
  let hits := ((List.range 45).map (·+1)).filter (fun j => accepted (x+j*t))
  (hits[0]?.getD 0,hits[1]?.getD 0)

private def ticket (t x : ℕ) : Bool :=
  let (i,j) := offsets x t
  decide (0 < i ∧ i < 14 ∧ i < j ∧ j < 46 ∧
    accepted (x+i*t) = true ∧ accepted (x+j*t) = true)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2400000 in
private theorem allTickets : ∀ t : Fin 315, sums.any (ticket t.val) = true := by decide +kernel

private theorem sharp (t : ZMod 315) : PairHit 73 t 14 ∧ TripleHit 73 t 46 := by
  obtain ⟨x,hx,passes⟩ := List.any_eq_true.mp (allTickets ⟨_,t.val_lt⟩)
  obtain ⟨i,j,eq⟩ : ∃ i j, offsets x t.val = (i,j) := ⟨_,_,rfl⟩
  simp only [ticket,eq,decide_eq_true_eq] at passes
  obtain ⟨ip,il,ij,jl,ai,aj⟩ := passes
  have below : sums.all (fun a => decide (a < 315)) = true := by decide
  have lt (a : ℕ) (ha : a ∈ sums) : a < 315 := of_decide_eq_true (List.all_eq_true.mp below a ha)
  have base := (natSums x).mpr (by rwa [Nat.mod_eq_of_lt (lt _ hx)])
  have hit (u : ℕ) (a : accepted (x+u*t.val) = true) :
      AdmissibleSum 73 ((x:ZMod 315)+(u:ZMod 315)*t) := by
    simpa only [ZMod.natCast_zmod_val] using (addSums x u t.val).mpr a
  exact ⟨⟨x,i,ip,il,base,hit i ai⟩,⟨x,i,j,ip,ij,jl,base,hit i ai,hit j aj⟩⟩

private theorem mulSum {m : ℕ} (c : ZMod m) {n s : ZMod m} (h : AdmissibleSum n s) :
    AdmissibleSum (n*c^2) (s*c) := by
  obtain ⟨x,y,rfl,rfl⟩ := h
  exact ⟨x*c,y*c,by ring,by ring⟩

private theorem mulPair {m l : ℕ} (c : ZMod m) {n t : ZMod m} (h : PairHit n t l) :
    PairHit (n*c^2) (t*c) l := by
  obtain ⟨x,i,ip,il,hx,hi⟩ := h
  exact ⟨x*c,i,ip,il,mulSum c hx,by simpa only [add_mul,mul_assoc] using mulSum c hi⟩

private theorem mulTriple {m l : ℕ} (c : ZMod m) {n t : ZMod m} (h : TripleHit n t l) :
    TripleHit (n*c^2) (t*c) l := by
  obtain ⟨x,i,j,ip,ij,jl,hx,hi,hj⟩ := h
  exact ⟨x*c,i,j,ip,ij,jl,mulSum c hx,by simpa only [add_mul,mul_assoc] using mulSum c hi,
    by simpa only [add_mul,mul_assoc] using mulSum c hj⟩

/-- In the square class of 73 the supplied unit itself gives the packing step.
Every other step, including every nonunit, fails when one more position is added. -/
theorem optimal (u : (ZMod 315)ˣ) :
    let n := (73 : ZMod 315)*(u:ZMod 315)^2
    (¬PairHit n u 13 ∧ ¬TripleHit n u 45) ∧
    ∀ t : ZMod 315, PairHit n t 14 ∧ TripleHit n t 46 := by
  dsimp only
  have cancel : (73*(u:ZMod 315)^2)*(↑(u⁻¹):ZMod 315)^2 = 73 := by
    rw [mul_assoc,←mul_pow,Units.mul_inv,one_pow,mul_one]
  refine ⟨⟨fun h => oneStep.1 ?_,fun h => oneStep.2 ?_⟩,?_⟩
  · simpa only [cancel,Units.mul_inv] using mulPair (↑(u⁻¹):ZMod 315) h
  · simpa only [cancel,Units.mul_inv] using mulTriple (↑(u⁻¹):ZMod 315) h
  · intro t
    obtain ⟨pair,triple⟩ := sharp (t*↑(u⁻¹))
    exact ⟨by simpa only [mul_assoc,Units.inv_mul,mul_one] using mulPair (u:ZMod 315) pair,
      by simpa only [mul_assoc,Units.inv_mul,mul_one] using mulTriple (u:ZMod 315) triple⟩

/-- The class test uses just the given product. -/
def qualifies (n : ℕ) : Prop :=
  n%3=1 ∧ (n%5=2 ∨ n%5=3) ∧ (n%7=3 ∨ n%7=5 ∨ n%7=6)

def smallRoots : List ℕ := [1,2,4,8,11,13,16,17,19,23,29,32,37,38,41,43,46,86]

/-- A public list of eighteen small possible scaling factors suffices. -/
theorem chooseStep {N : ℕ} (h : qualifies N) :
    ∃ a ∈ smallRoots, a.Coprime 315 ∧ (N:ZMod 315) = 73*(a:ZMod 315)^2 := by
  have table : ∀ j : Fin 315, qualifies j.val →
      smallRoots.any (fun a => decide (a.Coprime 315 ∧ (j.val:ZMod 315) = 73*(a:ZMod 315)^2)) = true := by
    unfold qualifies
    decide +kernel
  have key : qualifies (N%315) := by
    simpa only [qualifies,Nat.mod_mod_of_dvd N (by decide : 3∣315),
      Nat.mod_mod_of_dvd N (by decide : 5∣315),Nat.mod_mod_of_dvd N (by decide : 7∣315)] using h
  obtain ⟨a,ha,passed⟩ := List.any_eq_true.mp (table ⟨N%315,Nat.mod_lt _ (by decide)⟩ key)
  simp only [decide_eq_true_eq,ZMod.natCast_mod] at passed
  exact ⟨a,ha,passed⟩

/-- All qualifying products have an explicitly selectable step. -/
theorem product {N : ℕ} (h : qualifies N) :
    (∃ t : ZMod 315, ¬PairHit (N:ZMod 315) t 13 ∧ ¬TripleHit (N:ZMod 315) t 45) ∧
    ∀ t : ZMod 315, PairHit (N:ZMod 315) t 14 ∧ TripleHit (N:ZMod 315) t 46 := by
  obtain ⟨a,_,cop,eq⟩ := chooseStep h
  let u : (ZMod 315)ˣ := ZMod.unitOfCoprime a cop
  have eq' : (N:ZMod 315) = 73*(u:ZMod 315)^2 := by simpa only [u,ZMod.coe_unitOfCoprime] using eq
  rw [eq']
  exact ⟨⟨u,(optimal u).1⟩,(optimal u).2⟩

/-- A stride-four search starting at the first possible sum above twice the
square root. Exactly two of the 45 candidates reach the final square test. -/
theorem worked :
    2738^2 < 4*1879513 ∧ 4*1879513 ≤ 2742^2 ∧
    (∀ j : Fin 45, AdmissibleSum (1879513 : ZMod 315) (2742+4*(j.val:ZMod 315)) ↔
      j.val=1 ∨ j.val=28) ∧
    149^2 < 2746^2-4*1879513 ∧ 2746^2-4*1879513 < 150^2 ∧
    2854^2 = 4*1879513+792^2 ∧
    Nat.Prime 1031 ∧ Nat.Prime 1823 ∧ 1031*1823=1879513 ∧ 1031+1823=2854 := by
  refine ⟨by decide,by decide,?_,by decide,by decide,by decide,by decide +kernel,
    by decide +kernel,by decide,by decide⟩
  have table : ∀ j : Fin 45, ((2742+4*j.val)*79)%315∈sums ↔ j.val=1 ∨ j.val=28 := by decide +kernel
  intro j
  let v := 2742+4*j.val
  change AdmissibleSum (1879513 : ZMod 315) (2742+4*(j.val:ZMod 315)) ↔ _
  have cv : (v:ZMod 315) = 2742+4*(j.val:ZMod 315) := by push_cast [v]; rfl
  rw [←cv,←table]
  change AdmissibleSum (1879513 : ZMod 315) (v:ZMod 315) ↔ (v*79)%315∈sums
  rw [←natSums,Nat.cast_mul,Nat.cast_ofNat]
  have back : (4:ZMod 315)*79=1 := by decide
  constructor
  · intro h
    simpa only [show (1879513:ZMod 315)*79^2 = 73 by decide] using mulSum 79 h
  · intro h
    simpa only [show (73:ZMod 315)*4^2 = 1879513 by decide,mul_assoc,
      show (79:ZMod 315)*4=1 from (mul_comm ..).trans back,mul_one] using mulSum 4 h

end PrimeFactors.PrimeSumListPacking
