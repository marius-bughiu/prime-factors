import PrimeFactors.Certificate
import PrimeFactors.QuarticLocalClassification
import PrimeFactors.TwoAdicSumSpacing

/-! A supplied answer to the local quartic tests selects a sign for the
unknown prime sum. The higher-precision support statements concern modular
factor pairs. -/
namespace PrimeFactors.QuarticLocalSumBits

open QuarticLocalClassification (Tests)
open private PrimeFactors.TwoAdicSumSpacing.sum32 from PrimeFactors.TwoAdicSumSpacing

private theorem residues {a b : ℤ} (prod : (a*b)%4=1) :
    (a%4=1 ∧ b%4=1) ∨ (a%4=3 ∧ b%4=3) := by
  have check : (a%4*(b%4))%4=1 := Eq.trans
    (show (a%4*(b%4))%4=(a*b)%4 from (Int.mod_modEq a 4).mul (Int.mod_modEq b 4)) prod
  have al : 0≤a%4 := by omega
  have ah : a%4<4 := by omega
  have bl : 0≤b%4 := by omega
  have bh : b%4<4 := by omega
  interval_cases ha : a%4 <;> interval_cases hb : b%4 <;> norm_num [ha,hb] at check ⊢

private theorem classes {a b N s : ℤ} (good : N%16=1 ∨ N%16=5)
    (prod : a*b ≡ N [ZMOD 16]) (sum : a+b ≡ s [ZMOD 16]) :
    ((a%4=1 ∧ b%4=1) ↔ s%16=(N+1)%16) ∧
    ((a%4=3 ∧ b%4=3) ↔ s%16=(-(N+1))%16) ∧
    ((a%4=1 ∧ b%4=1) ∨ (a%4=3 ∧ b%4=3)) := by
  have eq : (a*b)%16=N%16 := prod
  have split := residues (show (a*b)%4=1 by omega)
  refine ⟨?_,?_,split⟩ <;> rcases split with ⟨ha,hb⟩|⟨ha,hb⟩
  all_goals first
    | have factor : (16:ℤ)∣(a-1)*(b-1) :=
        mul_dvd_mul (show (4:ℤ)∣a-1 by omega) (show (4:ℤ)∣b-1 by omega)
      have trace : a+b ≡ a*b+1 [ZMOD 16] := Int.modEq_iff_dvd.mpr (by
        rw [show a*b+1-(a+b)=(a-1)*(b-1) by ring]; exact factor)
      have signed : s%16=(N+1)%16 := sum.symm.trans (trace.trans (prod.add_right 1))
      omega
    | have factor : (16:ℤ)∣(a+1)*(b+1) :=
        mul_dvd_mul (show (4:ℤ)∣a+1 by omega) (show (4:ℤ)∣b+1 by omega)
      have trace : -(a*b+1) ≡ a+b [ZMOD 16] := Int.modEq_iff_dvd.mpr (by
        rw [show a+b- -(a*b+1)=(a+1)*(b+1) by ring]; exact factor)
      have signed : s%16=(-(N+1))%16 := sum.symm.trans (trace.symm.trans (prod.add_right 1).neg)
      omega

/-- On a product passing the public mod-16 gate, the two local answers
are equivalent to opposite sum classes modulo 16. -/
theorem sign16 {p q : ℕ} (pp : p.Prime) (qp : q.Prime) (po : Odd p) (qo : Odd q)
    (gate : (p*q)%16=1 ∨ (p*q)%16=5) :
    (Tests (p*q) ↔ ((p:ℤ)+q)%16=((p:ℤ)*q+1)%16) ∧
    (¬Tests (p*q) ↔ ((p:ℤ)+q)%16=(-((p:ℤ)*q+1))%16) := by
  have g : ((p:ℤ)*q)%16=1 ∨ ((p:ℤ)*q)%16=5 := by exact_mod_cast gate
  obtain ⟨plus,minus,split⟩ := classes (a:=(p:ℤ)) (b:=(q:ℤ)) g (Int.ModEq.refl _) (Int.ModEq.refl _)
  have test := QuarticLocalClassification.semiprime pp qp po qo
  have ok : Tests (p*q) ↔ (p:ℤ)%4=1 ∧ (q:ℤ)%4=1 := by
    constructor
    · intro h
      obtain ⟨a,b,_⟩ := test.mp h
      exact ⟨by exact_mod_cast a,by exact_mod_cast b⟩
    · rintro ⟨a,b⟩
      exact test.mpr ⟨by exact_mod_cast a,by exact_mod_cast b,gate⟩
  exact ⟨ok.trans plus,by rw [ok,←minus]; omega⟩

/-- Both factors of a modular witness have class r modulo four. Integer
representatives make the sign condition independent of the chosen lifts
whenever four divides m. -/
def Signed (r : ℤ) (m : ℕ) (N s : ℤ) : Prop :=
  ∃ a b : ℤ, a*b ≡ N [ZMOD (m:ℤ)] ∧ a+b ≡ s [ZMOD (m:ℤ)] ∧ a%4=r ∧ b%4=r

private theorem witnesses (m : ℕ) (N s : ℤ) :
    AdmissibleSum (N : ZMod m) (s : ZMod m) ↔
    ∃ a b : ℤ, a*b ≡ N [ZMOD (m:ℤ)] ∧ a+b ≡ s [ZMOD (m:ℤ)] := by
  constructor
  · rintro ⟨x,y,prod,sum⟩
    obtain ⟨a,rfl⟩ := ZMod.intCast_surjective x
    obtain ⟨b,rfl⟩ := ZMod.intCast_surjective y
    exact ⟨a,b,(ZMod.intCast_eq_intCast_iff ..).mp (by simpa only [Int.cast_mul] using prod),
      (ZMod.intCast_eq_intCast_iff ..).mp (by simpa only [Int.cast_add] using sum)⟩
  · rintro ⟨a,b,prod,sum⟩
    exact ⟨a,b,by simpa only [Int.cast_mul] using (ZMod.intCast_eq_intCast_iff ..).mpr prod,
      by simpa only [Int.cast_add] using (ZMod.intCast_eq_intCast_iff ..).mpr sum⟩

/-- At any multiple of 16 the selected sign preserves precisely those
already admissible sums with that low residue. -/
theorem signed_support {m : ℕ} (modulus : (16:ℤ)∣m) {N s : ℤ} (good : N%16=1 ∨ N%16=5) :
    (Signed 1 m N s ↔ AdmissibleSum (N : ZMod m) (s : ZMod m) ∧ s%16=(N+1)%16) ∧
    (Signed 3 m N s ↔ AdmissibleSum (N : ZMod m) (s : ZMod m) ∧ s%16=(-(N+1))%16) := by
  rw [witnesses]
  constructor <;> constructor
  · rintro ⟨a,b,p,t,ap,bp⟩
    exact ⟨⟨a,b,p,t⟩,(classes good (p.of_dvd modulus) (t.of_dvd modulus)).1.mp ⟨ap,bp⟩⟩
  · rintro ⟨⟨a,b,p,t⟩,sgn⟩
    exact ⟨a,b,p,t,(classes good (p.of_dvd modulus) (t.of_dvd modulus)).1.mpr sgn⟩
  · rintro ⟨a,b,p,t,ap,bp⟩
    exact ⟨⟨a,b,p,t⟩,(classes good (p.of_dvd modulus) (t.of_dvd modulus)).2.1.mp ⟨ap,bp⟩⟩
  · rintro ⟨⟨a,b,p,t⟩,sgn⟩
    exact ⟨a,b,p,t,(classes good (p.of_dvd modulus) (t.of_dvd modulus)).2.1.mpr sgn⟩

/-- For N=5 modulo 16 each compatible residue in the selected class modulo
32 occurs at every higher precision, with both modular factors of that sign. -/
theorem signed32 {N s : ℤ} (good : N%16=5) (k : ℕ) :
    (Signed 1 (2^(k+5)) N s ↔ s%32=(N+1)%32) ∧
    (Signed 3 (2^(k+5)) N s ↔ s%32=(-(N+1))%32) := by
  have div : (16:ℤ)∣((2^(k+5):ℕ):ℤ) := by
    push_cast
    rw [pow_add]
    exact (show (16:ℤ)∣2^5 by decide).trans (dvd_mul_left _ _)
  obtain ⟨plus,minus⟩ := signed_support (s:=s) div (Or.inr good)
  have dyadic := PrimeFactors.TwoAdicSumSpacing.sum32 (s:=s) (N:=N) (by omega) k
  rw [plus,minus,dyadic]
  omega

/-- For the actual prime factors on the 5 mod 16 branch, the supplied Boolean
selects one residue modulo 32 for their sum. -/
theorem sign32 {p q : ℕ} (pp : p.Prime) (qp : q.Prime) (po : Odd p) (qo : Odd q)
    (five : (p*q)%16=5) :
    (Tests (p*q) ↔ ((p:ℤ)+q)%32=((p:ℤ)*q+1)%32) ∧
    (¬Tests (p*q) ↔ ((p:ℤ)+q)%32=(-((p:ℤ)*q+1))%32) := by
  have good : ((p:ℤ)*q)%16=5 := by exact_mod_cast five
  obtain ⟨plus,minus⟩ := sign16 pp qp po qo (Or.inr five)
  have pair : AdmissibleSum (((p:ℤ)*q : ℤ) : ZMod (2^(0+5))) (((p:ℤ)+q : ℤ) : ZMod _) :=
    (witnesses ..).mpr ⟨p,q,Int.ModEq.refl _,Int.ModEq.refl _⟩
  have either := (PrimeFactors.TwoAdicSumSpacing.sum32 (N:=(p:ℤ)*q) (s:=(p:ℤ)+q) (by omega) 0).mp pair
  have descend {a b : ℤ} (h : a%32=b%32) : a%16=b%16 :=
    (show a ≡ b [ZMOD 32] from h).of_dvd (by decide)
  have different : ((p:ℤ)*q+1)%16≠(-((p:ℤ)*q+1))%16 := by omega
  rcases either with eq|eq
  · have ok := plus.mpr (descend eq)
    have no : ((p:ℤ)+q)%32≠(-((p:ℤ)*q+1))%32 :=
      fun contrary => different ((descend eq).symm.trans (descend contrary))
    exact ⟨iff_of_true ok eq,iff_of_false (fun h => h ok) no⟩
  · have no := minus.mpr (descend eq)
    have bad : ((p:ℤ)+q)%32≠((p:ℤ)*q+1)%32 :=
      fun contrary => different ((descend contrary).symm.trans (descend eq))
    exact ⟨iff_of_false no bad,iff_of_true no eq⟩

/-- For the 1 mod 16 branch, both mod-32 lifts of the selected low
residue have modular witnesses. -/
theorem signed_one32 {N s : ℤ} (one : N%16=1) :
    (Signed 1 32 N s ↔ s%16=(N+1)%16) ∧
    (Signed 3 32 N s ↔ s%16=(-(N+1))%16) := by
  obtain ⟨positive,negative⟩ := signed_support (m:=32) (s:=s) (by decide) (Or.inl one)
  have lift (t : ℤ) (target : t%16=(N+1)%16) : Signed 1 32 N t := by
    by_cases base : t%32=(N+1)%32
    · refine ⟨1,N,?_,?_,by decide,by omega⟩
      · simp
      · change (1+N)%32=t%32
        omega
    · refine ⟨5,13*N,?_,?_,by decide,by omega⟩
      · change (5*(13*N))%32=N%32
        omega
      · change (5+13*N)%32=t%32
        omega
  refine ⟨⟨fun h => (positive.mp h).2,lift s⟩,fun h => (negative.mp h).2,?_⟩
  intro signed
  obtain ⟨a,b,prod,sum,ac,bc⟩ := lift (-s) (by omega)
  exact ⟨-a,-b,by simpa only [neg_mul_neg] using prod,
    by simpa only [neg_add_rev,neg_neg,add_comm] using sum.neg,by omega,by omega⟩

/-- For N=65 the positive-sign class 34 mod 64 has no modular witnesses.
The positive-sign residues 66 and 18 come from the integer pairs (1,65)
and (5,13). -/
theorem singular_control : Tests 65 ∧ Signed 1 64 65 66 ∧ Signed 1 64 65 18 ∧
    ¬Signed 1 64 65 34 := by
  have test := (QuarticLocalClassification.semiprime (p:=5) (q:=13) (by decide) (by decide)
    (by decide) (by decide)).mpr (by decide)
  refine ⟨test,⟨1,65,by decide,by decide,by decide,by decide⟩,
    ⟨5,13,by decide,by decide,by decide,by decide⟩,?_⟩
  have table : ∀ x y : ZMod 64, x*y=65 → x+y≠34 := by decide +kernel
  rintro ⟨a,b,ab,t,_⟩
  obtain ⟨x,y,prod,plus⟩ := (witnesses 64 65 34).mpr ⟨a,b,ab,t⟩
  exact table x y prod plus

/-- Both products and all four primes have the same respective bit widths.
One product bit changes, reversing the local answer and the selected sum residue. -/
theorem one_bit_control :
    ExactFactorization 2874064069 [48541,59209] ∧ ExactFactorization 2941172933 [48487,60659] ∧
    (2:ℕ)^31≤2874064069 ∧ (2941172933:ℕ)<2^32 ∧ (2:ℕ)^15≤48487 ∧ (60659:ℕ)<2^16 ∧
    ((2874064069:ℕ) ^^^ 2941172933)=2^26 ∧
    (2874064069:ℕ)%2^26=55491781 ∧ (2941172933:ℕ)%2^26=55491781 ∧
    Tests 2874064069 ∧ ¬Tests 2941172933 ∧
    ((48541:ℕ)+59209)%32=6 ∧ ((48487:ℕ)+60659)%32=26 := by
  have pos := (QuarticLocalClassification.semiprime (p:=48541) (q:=59209) (by norm_num) (by norm_num)
    (by decide) (by decide)).mpr (by decide +kernel)
  have neg := (QuarticLocalClassification.semiprime (p:=48487) (q:=60659) (by norm_num) (by norm_num)
    (by decide) (by decide)).mp.mt (by decide +kernel)
  exact ⟨by norm_num [ExactFactorization],by norm_num [ExactFactorization],by decide,by decide,by decide,by decide,
    by decide +kernel,by decide +kernel,by decide +kernel,pos,neg,by decide,by decide⟩

end PrimeFactors.QuarticLocalSumBits
