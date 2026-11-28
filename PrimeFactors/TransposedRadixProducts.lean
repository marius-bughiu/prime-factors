import Mathlib.Data.Int.GCD
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic

/-! A supplied even radix B specifies the family of products of Ba+b and Bb+a.
For odd distinct blocks below B the product determines their half-sum squared
as an ordinary least residue. Two natural square roots then recover the blocks. -/

namespace PrimeFactors.TransposedRadixProducts

def factors (B a b : ℕ) : ℕ×ℕ := (B*a+b,B*b+a)

def Valid (B a b : ℕ) : Prop := 2≤B ∧ Even B ∧ Odd a ∧ Odd b ∧ a<b ∧ b<B

noncomputable instance (B a b : ℕ) : Decidable (Valid B a b) := by unfold Valid; infer_instance

private def validBlocks (B a b : ℕ) : Bool :=
  decide (2≤B) && (B%2==0) && (a%2==1) && (b%2==1) && decide (a<b) && decide (b<B)

private theorem validBlocks_iff (B a b : ℕ) : validBlocks B a b=true ↔ Valid B a b := by
  simp only [validBlocks,Valid,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq,
    Nat.even_iff,Nat.odd_iff]
  tauto

def modulus (B : ℕ) := (B-1)^2

/-- The least residue of N/(4B) modulo (B−1)², using the modular inverse. -/
def reading (B N : ℕ) : ℕ :=
  ((N:ℤ)*Nat.gcdA (4*B) (modulus B)).natMod (modulus B)

/-- Subtracting the recovered square term and dividing by (B−1)² gives ab.
The second radicand is the square of the half-difference for family members. -/
def coordinates (B N : ℕ) : ℕ×ℕ :=
  let R := reading B N
  let c := R.sqrt
  let d := (R-(N-4*B*R)/modulus B).sqrt
  (c-d,c+d)

/-- Checking both radix digits and the product prevents truncated natural
subtractions, rounded roots, or invalid radices from producing false hits. -/
def recognize (B N : ℕ) : Option (ℕ×ℕ) :=
  let ab := coordinates B N
  let pq := factors B ab.1 ab.2
  if validBlocks B ab.1 ab.2 && (pq.1*pq.2==N) then some pq else none

theorem coprime {B : ℕ} (low : 2≤B) (even : Even B) : (4*B).Coprime (modulus B) := by
  obtain ⟨j,hj⟩ := even
  have odd : Odd (B-1) := ⟨j-1,by omega⟩
  have first : Nat.Coprime 4 (B-1) := odd.coprime_two_left.pow_left 2
  have second : Nat.Coprime B (B-1) := by
    have same : (B-1+1).Coprime (B-1) := Nat.coprime_self_add_left.mpr (by simp)
    simpa only [show B-1+1=B by omega] using same
  exact (Nat.coprime_mul_iff_left.mpr ⟨first,second⟩).pow_right 2

private theorem data {B a b : ℕ} (ok : Valid B a b) :
    a+(b-a)/2=(a+b)/2 ∧ (a+b)/2+(b-a)/2=b ∧ (a+b)/2<B-1 := by
  obtain ⟨_,_,⟨x,hx⟩,⟨y,hy⟩,ord,top⟩ := ok
  omega

/-- The exact integer division and the second square used in the decoding. -/
theorem equations {B a b : ℕ} (ok : Valid B a b) :
    (factors B a b).1*(factors B a b).2 = 4*B*((a+b)/2)^2 + modulus B*(a*b) ∧
    ((a+b)/2)^2 = a*b+((b-a)/2)^2 := by
  obtain ⟨h₁,h₂,_⟩ := data ok
  have lt := ok.1
  simp only [factors,modulus]
  generalize (a+b)/2=c at *
  generalize (b-a)/2=d at *
  generalize hz : B-1=z
  have hb : B=z+1 := by omega
  rw [hb,←h₂,←h₁]
  constructor <;> ring

theorem reading_of_remainder {B N R j : ℕ} (low : 2≤B) (even : Even B)
    (eq : N=4*B*R+modulus B*j) (upper : R<modulus B) : reading B N=R := by
  let m := modulus B
  let c := 4*B
  have gcd : c.gcd m=1 := coprime low even
  have bez := Nat.gcd_eq_gcd_ab c m
  rw [gcd,Nat.cast_one] at bez
  have n : (N:ℤ)=(c:ℤ)*R+(m:ℤ)*j := by exact_mod_cast eq
  have reduction : (N:ℤ)*c.gcdA m =
      (R:ℤ)+(m:ℤ)*((j:ℤ)*c.gcdA m-(R:ℤ)*c.gcdB m) := by
    nlinarith only [congrArg (fun x : ℤ => x*(R:ℤ)) bez,
      congrArg (fun x : ℤ => x*c.gcdA m) n]
  change (((N:ℤ)*c.gcdA m)%(m:ℤ)).toNat=R
  rw [reduction,Int.add_mul_emod_self_left,Int.emod_eq_of_lt (by positivity) (by exact_mod_cast upper)]
  rfl

/-- Taking the least representative loses no digits of the half-sum squared. -/
theorem reading_eq {B a b N : ℕ} (ok : Valid B a b) (prod : (factors B a b).1*(factors B a b).2=N) :
    reading B N=((a+b)/2)^2 :=
  reading_of_remainder ok.1 ok.2.1 (prod.symm.trans (equations ok).1)
    (Nat.pow_lt_pow_left (data ok).2.2 (by decide : 2≠0))

theorem coordinates_eq {B a b N : ℕ} (ok : Valid B a b) (prod : (factors B a b).1*(factors B a b).2=N) :
    coordinates B N=(a,b) := by
  obtain ⟨h₁,h₂,_⟩ := data ok
  obtain ⟨first,second⟩ := equations ok
  have low := ok.1
  have mpos : 0<modulus B := pow_pos (by omega : 0<B-1) 2
  have div : (N-4*B*((a+b)/2)^2)/modulus B=a*b := by
    rw [←prod,first,Nat.add_sub_cancel_left,Nat.mul_div_cancel_left _ mpos]
  have sub : ((a+b)/2)^2-a*b=((b-a)/2)^2 := by omega
  simp only [coordinates,reading_eq ok prod,div,sub,Nat.sqrt_eq']
  exact Prod.ext (by dsimp; omega) (by dsimp; omega)

theorem complete {B a b N : ℕ} (ok : Valid B a b) (prod : (factors B a b).1*(factors B a b).2=N) :
    recognize B N=some (factors B a b) := by
  simp only [recognize,coordinates_eq ok prod,Bool.and_eq_true,validBlocks_iff,ok,prod,
    beq_iff_eq,eq_self,and_self,if_true]

theorem sound {B N : ℕ} {pq : ℕ×ℕ} (hit : recognize B N=some pq) :
    ∃ a b, Valid B a b ∧ factors B a b=pq ∧ pq.1*pq.2=N := by
  simp only [recognize,Bool.and_eq_true,validBlocks_iff,beq_iff_eq] at hit
  split at hit
  · rename_i h
    have e := Option.some.inj hit
    exact ⟨_,_,h.1,e,e ▸ h.2⟩
  · contradiction

theorem recognizes_iff {B N : ℕ} : (recognize B N).isSome=true ↔
    ∃ a b, Valid B a b ∧ (factors B a b).1*(factors B a b).2=N := by
  constructor
  · intro yes
    cases hit : recognize B N with
    | none => simp [hit] at yes
    | some pq =>
      obtain ⟨a,b,ok,rfl,prod⟩ := sound hit
      exact ⟨a,b,ok,prod⟩
  · rintro ⟨a,b,ok,prod⟩
    rw [complete ok prod]
    rfl

theorem reject_nonsquare {B N : ℕ} (bad : (reading B N).sqrt^2≠reading B N) :
    recognize B N=none := by
  cases hit : recognize B N with
  | none => rfl
  | some pq =>
    obtain ⟨a,b,ok,rfl,prod⟩ := sound hit
    simp only [reading_eq ok prod,Nat.sqrt_eq',ne_self_iff_false] at bad

/-- Both square roots have inputs strictly below the square of a single
radix block, including unsuccessful tests at every valid radix. -/
theorem root_bounds {B : ℕ} (low : 2≤B) (N : ℕ) :
    reading B N<modulus B ∧ reading B N-(N-4*B*reading B N)/modulus B<modulus B := by
  have mp : 0<modulus B := pow_pos (by omega : 0<B-1) 2
  have lt : reading B N<modulus B := Int.natMod_lt mp.ne'
  exact ⟨lt,(Nat.sub_le ..).trans_lt lt⟩

/-- The factor sum itself uses only the first integer square root. -/
theorem factor_sum {B a b N : ℕ} (ok : Valid B a b) (prod : (factors B a b).1*(factors B a b).2=N) :
    (factors B a b).1+(factors B a b).2=2*(B+1)*(reading B N).sqrt := by
  rw [reading_eq ok prod,Nat.sqrt_eq']
  have ⟨h₁,h₂,_⟩ := data ok
  have twice : 2*((a+b)/2)=a+b := by omega
  calc
    _ = (B+1)*(a+b) := by dsimp [factors]; ring
    _ = (B+1)*(2*((a+b)/2)) := congrArg ((B+1)*·) twice.symm
    _ = _ := by ring

/-- Valid distinct positive blocks always give an ordered proper split. -/
theorem proper {B a b : ℕ} (ok : Valid B a b) :
    1<(factors B a b).1 ∧ (factors B a b).1<(factors B a b).2 ∧
      (factors B a b).2<(factors B a b).1*(factors B a b).2 := by
  obtain ⟨low,_,⟨j,hj⟩,_,ab,_⟩ := ok
  have ap : 0<a := by omega
  obtain ⟨i,hi⟩ := Nat.exists_eq_add_of_lt ab
  have h₁ : 1<B*a+b := by nlinarith [Nat.mul_le_mul_right B ap]
  have h₂ : B*a+b<B*b+a := by rw [hi]; nlinarith
  exact ⟨h₁,h₂,by simpa only [one_mul] using Nat.mul_lt_mul_of_pos_right h₁ (by omega : 0<B*b+a)⟩

theorem example_20 : reading 32 790037=729 ∧ coordinates 32 790037=(25,29) ∧
    recognize 32 790037=some (829,953) ∧ Nat.Prime 829 ∧ Nat.Prime 953 := by
  have v : Valid 32 25 29 := by decide
  have p : (factors 32 25 29).1*(factors 32 25 29).2=790037 := by decide
  exact ⟨reading_eq v p,coordinates_eq v p,complete v p,by norm_num,by norm_num⟩

theorem example_24 : reading 64 10944151=2704 ∧ coordinates 64 10944151=(41,63) ∧
    recognize 64 10944151=some (2687,4073) ∧ Nat.Prime 2687 ∧ Nat.Prime 4073 := by
  have v : Valid 64 41 63 := by decide
  have p : (factors 64 41 63).1*(factors 64 41 63).2=10944151 := by decide
  exact ⟨reading_eq v p,coordinates_eq v p,complete v p,by norm_num,by norm_num⟩

theorem example_miss : reading 32 789827=382 ∧ recognize 32 789827=none ∧
    797*991=789827 ∧ Nat.Prime 797 ∧ Nat.Prime 991 := by
  have h : reading 32 789827=382 := reading_of_remainder (j:=771) (by decide) (by decide)
    (by decide) (by decide)
  refine ⟨h,?_,by decide,by norm_num,by norm_num⟩
  apply reject_nonsquare
  rw [h]
  decide +kernel

end PrimeFactors.TransposedRadixProducts
