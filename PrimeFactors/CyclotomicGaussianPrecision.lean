import PrimeFactors.CyclotomicGaussianReading
import Mathlib.Data.ZMod.Units

/-! Sum precision from the actual Gaussian reading of an odd semiprime.
Sharpness compares unit factorizations of a common product residue. -/
namespace PrimeFactors.CyclotomicGaussianPrecision

open Complex CyclotomicGaussianReading
set_option maxRecDepth 8192

/-- Codes 0, 1 and 2 represent the readings 2, −2i and 2i respectively. -/
def code (p q : ℕ) := if p%4=1 ∧ q%4=1 then 1 else if p%4=3 ∧ q%4=3 then 2 else 0

noncomputable def decode (c : ℕ) : ℂ := if c=1 then -2*I else if c=2 then 2*I else 2

theorem read_code {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (ord : p<q) (op : Odd p) (oq : Odd q) :
    reading (p*q)=decode (code p q) := by
  rw [value hp hq ord op oq]
  unfold code
  split_ifs <;> norm_num [decode]

private theorem negative_factors {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (ord : p<q)
    (op : Odd p) (oq : Odd q) : reading (p*q)= -2*I ↔ p%4=1 ∧ q%4=1 := by
  rw [value hp hq ord op oq]
  split_ifs <;> norm_num [*,Complex.ext_iff]

private theorem positive_factors {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (ord : p<q)
    (op : Odd p) (oq : Odd q) : reading (p*q)=2*I ↔ p%4=3 ∧ q%4=3 := by
  rw [value hp hq ord op oq]
  split_ifs <;> norm_num [*,Complex.ext_iff]

/-- The sign is written with a natural representative, multiplying N+1 by
m−1 for the negative sum class. -/
private def SumClass (m : ℕ) (minus : Bool) (p q : ℕ) :=
  p+q ≡ (if minus then (m-1)*(p*q+1) else p*q+1) [MOD m]

private instance (m : ℕ) (s : Bool) (a b : ℕ) : Decidable (SumClass m s a b) := by
  unfold SumClass; infer_instance

private theorem lift_class {m p q : ℕ} {s : Bool} (div : m∣32) (h : SumClass m s (p%32) (q%32)) :
    SumClass m s p q := by
  have pp := (Nat.mod_modEq p 32).of_dvd div
  have qq := (Nat.mod_modEq q 32).of_dvd div
  have prod := (pp.mul qq).add_right 1
  cases s
  · exact (pp.add qq).symm.trans (h.trans prod)
  · exact (pp.add qq).symm.trans (h.trans (prod.mul_left _))

private theorem classes (p q : ℕ) :
    (p%4=1 ∧ q%4=1 → SumClass 16 false p q ∧ ((p*q)%8=5 → SumClass 32 false p q)) ∧
    (p%4=3 ∧ q%4=3 → SumClass 16 true p q ∧ ((p*q)%8=5 → SumClass 32 true p q)) ∧
    ((p*q)%4=3 → SumClass 8 false p q) := by
  have table : ∀ a b : Fin 32,
      (a.val%4=1 ∧ b.val%4=1 → SumClass 16 false a b ∧ ((a.val*b.val)%8=5 → SumClass 32 false a b)) ∧
      (a.val%4=3 ∧ b.val%4=3 → SumClass 16 true a b ∧ ((a.val*b.val)%8=5 → SumClass 32 true a b)) ∧
      ((a.val*b.val)%4=3 → SumClass 8 false a b) := by decide +kernel
  have t := table ⟨p%32,Nat.mod_lt _ (by decide)⟩ ⟨q%32,Nat.mod_lt _ (by decide)⟩
  have prod := (Nat.mod_modEq p 32).mul (Nat.mod_modEq q 32)
  have p8 : (p%32*(q%32))%8=(p*q)%8 := prod.of_dvd (by decide)
  have p4 : (p%32*(q%32))%4=(p*q)%4 := prod.of_dvd (by decide)
  simp only [Nat.mod_mod_of_dvd _ (by decide : 4∣32),p8,p4] at t
  exact ⟨fun pp => ⟨lift_class (by decide) (t.1 pp).1, fun five => lift_class (by decide) ((t.1 pp).2 five)⟩,
    fun pp => ⟨lift_class (by decide) (t.2.1 pp).1,fun five => lift_class (by decide) ((t.2.1 pp).2 five)⟩,
    fun three => lift_class (by decide) (t.2.2 three)⟩

theorem mixed_mod_eight {p q : ℕ} (three : (p*q)%4=3) : p+q ≡ p*q+1 [MOD 8] := (classes p q).2.2 three

theorem negative_mod_sixteen {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (ord : p<q) (op : Odd p) (oq : Odd q)
    (neg : reading (p*q)= -2*I) : p+q ≡ p*q+1 [MOD 16] :=
  ((classes p q).1 ((negative_factors hp hq ord op oq).mp neg)).1

theorem negative_mod_thirtytwo {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (ord : p<q) (op : Odd p) (oq : Odd q)
    (five : (p*q)%8=5) (neg : reading (p*q)= -2*I) : p+q ≡ p*q+1 [MOD 32] :=
  ((classes p q).1 ((negative_factors hp hq ord op oq).mp neg)).2 five

theorem positive_mod_sixteen {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (ord : p<q) (op : Odd p) (oq : Odd q)
    (pos : reading (p*q)=2*I) : p+q ≡ 15*(p*q+1) [MOD 16] :=
  ((classes p q).2.1 ((positive_factors hp hq ord op oq).mp pos)).1

theorem positive_mod_thirtytwo {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (ord : p<q) (op : Odd p) (oq : Odd q)
    (five : (p*q)%8=5) (pos : reading (p*q)=2*I) : p+q ≡ 31*(p*q+1) [MOD 32] :=
  ((classes p q).2.1 ((positive_factors hp hq ord op oq).mp pos)).2 five

/-- The modulus of the determined sum residue for an odd product. -/
def modulus (N : ℕ) : ℕ := if N%4=3 then 8 else if N%8=5 then 32 else 16

private abbrev U64 := (ZMod 64)ˣ

/-- Exactly one sum residue is supplied at the precision of the public
product class. A positive imaginary reading chooses the negative sign. -/
theorem sum_class {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (ord : p<q) (op : Odd p) (oq : Odd q) :
    p+q ≡ (if reading (p*q)=2*I then (modulus (p*q)-1)*(p*q+1) else p*q+1) [MOD modulus (p*q)] := by
  have residues {x : ℕ} (o : Odd x) : x%4=1 ∨ x%4=3 := by obtain ⟨t,eq⟩ := o; omega
  have product := Nat.mul_mod p q 4
  rcases residues op with a|a <;> rcases residues oq with b|b
  · have pos : ¬reading (p*q)=2*I := by rw [positive_factors hp hq ord op oq]; omega
    have neg := (negative_factors hp hq ord op oq).mpr ⟨a,b⟩
    have one : (p*q)%4=1 := by simpa only [a,b] using product
    simp only [if_neg pos,modulus,one,show ¬1=3 by decide,if_false]
    by_cases five : (p*q)%8=5
    · simpa only [if_pos five] using negative_mod_thirtytwo hp hq ord op oq five neg
    · simpa only [if_neg five] using negative_mod_sixteen hp hq ord op oq neg
  · have pos : ¬reading (p*q)=2*I := by rw [positive_factors hp hq ord op oq]; omega
    have three : (p*q)%4=3 := by simpa only [a,b] using product
    simpa only [modulus,three,if_true,if_neg pos] using mixed_mod_eight three
  · have pos : ¬reading (p*q)=2*I := by rw [positive_factors hp hq ord op oq]; omega
    have three : (p*q)%4=3 := by simpa only [a,b] using product
    simpa only [modulus,three,if_true,if_neg pos] using mixed_mod_eight three
  · have pos := (positive_factors hp hq ord op oq).mpr ⟨a,b⟩
    have one : (p*q)%4=1 := by simpa only [a,b] using product
    simp only [if_pos pos,modulus,one,show ¬1=3 by decide,if_false]
    by_cases five : (p*q)%8=5
    · simpa only [if_pos five] using positive_mod_thirtytwo hp hq ord op oq five pos
    · simpa only [if_neg five] using positive_mod_sixteen hp hq ord op oq pos

/-- Which Gaussian codes can occur at a given odd product residue. -/
def available (N c : ℕ) : Prop := if N%4=3 then c=0 else c=1 ∨ c=2
private instance (N c : ℕ) : Decidable (available N c) := by unfold available; infer_instance

private def one (c : Fin 3) : U64 := if c.val=2 then -1 else 1
private def nine : U64 := ⟨9,57,by decide,by decide⟩
private def five : U64 := ⟨5,13,by decide,by decide⟩
private def other (r : U64) (c : Fin 3) : U64 :=
  let u := if r.val.val%8=5 then nine
    else five
  if c.val=2 then -u else u

private def localCode (a b : U64) := code a.val.val b.val.val
private def localSum (a b : U64) := (a.val+b.val).val

private def distinguishes (r : U64) (c : Fin 3) : Prop :=
    let a := one c
    let b := a⁻¹*r
    let u := other r c
    let v := u⁻¹*r
    localCode a b=c.val ∧ localCode u v=c.val ∧
    localSum a b ≡ localSum u v [MOD modulus r.val.val] ∧
    ¬localSum a b ≡ localSum u v [MOD 2*modulus r.val.val]

private instance (r : U64) (c : Fin 3) : Decidable (distinguishes r c) := by unfold distinguishes; infer_instance

private def representative (x : Fin 64) : U64 :=
  if cop : x.val.Coprime 64 then ZMod.unitOfCoprime x.val cop else 1

private theorem different (r : U64) (c : Fin 3) (ok : available r.val.val c.val) : distinguishes r c := by
  have table : ∀ (x : Fin 64) (c : Fin 3), available (representative x).val.val c.val → distinguishes (representative x) c := by decide +kernel
  let x : Fin 64 := ⟨r.val.val,r.val.val_lt⟩
  have key : representative x=r := by
    rw [representative,dif_pos (ZMod.val_coe_unit_coprime r)]
    exact Units.ext (by simp [x])
  exact key ▸ table x c (key.symm ▸ ok)

/-- Interpret the same Gaussian reading code on lifted unit classes at m. -/
def residueCode {m : ℕ} (d : 64∣m) (a b : (ZMod m)ˣ) :=
  localCode (ZMod.unitsMap d a) (ZMod.unitsMap d b)

/-- Low six sum bits of arbitrary lifted factor residues. -/
def residueSum {m : ℕ} (d : 64∣m) (a b : (ZMod m)ˣ) :=
  localSum (ZMod.unitsMap d a) (ZMod.unitsMap d b)

/-- Whatever additional product residue is revealed, every available Gaussian
reading still admits both possibilities for the next sum bit in the local model. -/
theorem sharp {m : ℕ} [NeZero m] (d : 64∣m) (N : (ZMod m)ˣ) (c : Fin 3)
    (ok : available (ZMod.unitsMap d N).val.val c.val) :
    ∃ a b u v : (ZMod m)ˣ, a*b=N ∧ u*v=N ∧ residueCode d a b=c.val ∧ residueCode d u v=c.val ∧
      residueSum d a b ≡ residueSum d u v [MOD modulus (ZMod.unitsMap d N).val.val] ∧
      ¬residueSum d a b ≡ residueSum d u v [MOD 2*modulus (ZMod.unitsMap d N).val.val] := by
  let r := ZMod.unitsMap d N
  obtain ⟨a,ha⟩ := ZMod.unitsMap_surjective d (one c)
  obtain ⟨u,hu⟩ := ZMod.unitsMap_surjective d (other r c)
  refine ⟨a,a⁻¹*N,u,u⁻¹*N,by simp,by simp,?_⟩
  simpa only [distinguishes,residueCode,residueSum,map_mul,map_inv,ha,hu,r] using different r c ok

/-- The model's residue code agrees with the actual polynomial reading
when its two unit classes contain the genuine prime factors. -/
theorem residue_reading {m p q : ℕ} (d : 64∣m) (a b : (ZMod m)ˣ) (pa : (p:ZMod m)=a.val)
    (qb : (q:ZMod m)=b.val) (hp : p.Prime) (hq : q.Prime) (ord : p<q) (op : Odd p) (oq : Odd q) :
    reading (p*q)=decode (residueCode d a b) := by
  have project {x : ℕ} {u : (ZMod m)ˣ} (eq : (x:ZMod m)=u.val) : (ZMod.unitsMap d u).val=(x:ZMod 64) := by
    change ZMod.castHom d (ZMod 64) u.val=(x:ZMod 64)
    rw [←eq,map_natCast]
  rw [read_code hp hq ord op oq,residueCode,localCode,project pa,project qb]
  simp only [ZMod.val_natCast,code,Nat.mod_mod_of_dvd _ (by decide : 4∣64)]

end PrimeFactors.CyclotomicGaussianPrecision
