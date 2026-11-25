import PrimeFactors.GroupedOffsetRows
import PrimeFactors.ChebyshevQuarticScale
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Data.Nat.Prime.Int
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.PrincipalIdealDomain

namespace PrimeFactors.GroupedOffsetRowExamples
open GroupedOffsetRows Finset

structure Row where
  N : ℕ
  T : ℕ
  A : ℤ
  B : ℤ
  C : ℤ
  D : ℤ
  t : ℤ
  lo : ℤ
  hi : ℤ
  p : ℕ
  e : ℕ

def Row.h (s : Row) : ℤ := (s.N:ℤ)-(s.T:ℤ)^2
def Row.j (s : Row) (r : ℤ) := s.B*r+s.C*s.t
def Row.k (s : Row) (r : ℤ) := s.A*r+s.D*s.t
def Row.z (s : Row) (r : ℤ) := (s.T:ℤ)*s.j r-s.h*s.k r

def Row.InWindow (s : Row) (r : ℤ) : Prop :=
  1≤s.j r ∧ s.j r≤2^40 ∧ 1≤s.k r ∧ 1≤s.z r ∧ s.z r≤s.h

private structure Valid (s : Row) : Prop where
  sqrtBounds : s.T*s.T≤s.N ∧ s.N<(s.T+1)*(s.T+1)
  det : s.B*s.D-s.A*s.C=1
  bp : 0<s.B
  ap : 0<s.A
  hp : 0<s.h
  prime : s.p.Prime
  ep : 0<s.e
  rowIndex : s.t= -(s.p:ℤ)^s.e
  first : s.InWindow s.lo
  last : s.InWindow s.hi
  outside : s.j (s.lo-1)<1 ∧ 2^40<s.j (s.hi+1)
  rejects : ∀ x : Fin s.p, ¬((x.val:ℤ)^2 ≡ form s.T s.h s.B s.A [ZMOD s.p])

private theorem between {a b lo hi r L U : ℤ} (lower : lo≤r) (upper : r≤hi)
    (start : L≤a*lo+b ∧ a*lo+b≤U) (stop : L≤a*hi+b ∧ a*hi+b≤U) :
    L≤a*r+b ∧ a*r+b≤U := by
  rcases le_total 0 a with pos|neg
  · have := mul_le_mul_of_nonneg_left lower pos
    have := mul_le_mul_of_nonneg_left upper pos
    omega
  · have := mul_le_mul_of_nonpos_left lower neg
    have := mul_le_mul_of_nonpos_left upper neg
    omega

private theorem window_iff {s : Row} (v : Valid s) (r : ℤ) :
    s.InWindow r ↔ s.lo≤r ∧ r≤s.hi := by
  have monotone : Monotone s.j := fun _ _ h => add_le_add_right (mul_le_mul_of_nonneg_left h v.bp.le) _
  constructor
  · rintro ⟨j₁,j₂,_⟩
    have ⟨badLo,badHi⟩ := v.outside
    constructor
    · by_contra! bad
      have := monotone (by omega : r≤s.lo-1)
      omega
    · by_contra! bad
      have := monotone (by omega : s.hi+1≤r)
      omega
  · rintro ⟨rl,rh⟩
    obtain ⟨jl,jh,kl,zl,zh⟩ := v.first
    obtain ⟨jl',jh',_,zl',zh'⟩ := v.last
    have bounds := between rl rh (show 1≤s.j s.lo ∧ s.j s.lo≤2^40 from ⟨jl,jh⟩)
      (show 1≤s.j s.hi ∧ s.j s.hi≤2^40 from ⟨jl',jh'⟩)
    have kz : Monotone s.k := fun _ _ h => add_le_add_right (mul_le_mul_of_nonneg_left h v.ap.le) _
    have ze (r : ℤ) : s.z r=(s.B*s.T-s.h*s.A)*r+(s.C*s.T-s.h*s.D)*s.t := by
      unfold Row.z Row.j Row.k; ring
    rw [ze] at zl zh zl' zh'
    refine ⟨bounds.1,bounds.2,kl.trans (kz rl),?_⟩
    rw [ze]
    exact between rl rh ⟨zl,zh⟩ ⟨zl',zh'⟩

private theorem primitive_iff {s : Row} (v : Valid s) (r : ℤ) :
    IsCoprime (s.j r) (s.k r) ↔ ¬(s.p:ℤ) ∣ r := by
  rw [Row.j,Row.k,primitive_change v.det,v.rowIndex,IsCoprime.neg_right_iff,
    IsCoprime.pow_right_iff v.ep,isCoprime_comm,(Nat.prime_iff_prime_int.mp v.prime).coprime_iff_not_dvd]

/-- Every nonmultiple of p in the reported interval gives a distinct primitive
public test at its prescribed top multiplier and has nonsquare discriminant. -/
def Row.Certificate (s : Row) : Prop :=
  s.N.sqrt=s.T ∧ (∀ r, s.InWindow r ↔ s.lo≤r ∧ r≤s.hi) ∧
  ∀ r, s.lo≤r → r≤s.hi → ¬(s.p:ℤ) ∣ r →
    s.k r=((s.T:ℤ)*s.j r-1)/s.h ∧ IsCoprime (s.j r) (s.k r) ∧
      ¬∃ z : ℤ, z^2=form s.T s.h (s.j r) (s.k r)

private theorem certified {s : Row} (v : Valid s) : s.Certificate := by
  refine ⟨(Nat.eq_sqrt.mpr v.sqrtBounds).symm,window_iff v,?_⟩
  intro r lo hi unit
  have cop := (primitive_iff v r).mpr unit
  obtain ⟨_,_,_,low,high⟩ := (window_iff v r).mpr ⟨lo,hi⟩
  unfold Row.z at low high
  refine ⟨le_antisymm ((Int.le_ediv_iff_mul_le v.hp).mpr (by linarith)) ?_,cop,?_⟩
  · have h : ((s.T:ℤ)*s.j r-1)/s.h < s.k r+1 := (Int.ediv_lt_iff_lt_mul v.hp).mpr (by linarith)
    omega
  · rintro ⟨z,hit⟩
    obtain ⟨x,root⟩ := (both_squares cop v.det hit).1
    have dp : (s.p:ℤ) ∣ s.t := by rw [v.rowIndex]; exact dvd_neg.mpr (dvd_pow_self _ v.ep.ne')
    have root' := root.of_dvd dp
    have xp : (0:ℤ)<s.p := by exact_mod_cast v.prime.pos
    have small := Int.emod_lt_of_pos x xp
    have nonneg := Int.emod_nonneg x xp.ne'
    let y : Fin s.p := ⟨(x%(s.p:ℤ)).toNat,by omega⟩
    have yval : (y.val:ℤ)=x%(s.p:ℤ) := Int.toNat_of_nonneg nonneg
    apply v.rejects y
    rw [yval]
    exact ((Int.mod_modEq x _).pow 2).trans root'

/-- The actual distinct j-values rather than an independently enumerated index count. -/
noncomputable def Row.offsets (s : Row) : Finset ℤ :=
  ((Ioc (s.lo-1) s.hi).filter fun r => ¬(s.p:ℤ) ∣ r).image s.j

/-- Eliminate the row parameter: every counted offset is primitive and fails
at the multiplier computed from the input itself. -/
theorem Row.Certificate.offsets_rejected {s : Row} (cert : s.Certificate)
    (j : ℤ) (member : j ∈ s.offsets) :
    let T : ℤ := s.N.sqrt
    let h := (s.N:ℤ)-T^2
    let k := (T*j-1)/h
    1≤j ∧ j≤2^40 ∧ 1≤k ∧ IsCoprime j k ∧ ¬∃ z : ℤ, z^2=form T h j k := by
  unfold Row.offsets at member
  obtain ⟨r,hr,rfl⟩ := mem_image.mp member
  obtain ⟨index,unit⟩ := mem_filter.mp hr
  obtain ⟨lo,hi⟩ := mem_Ioc.mp index
  have lower : s.lo≤r := by omega
  obtain ⟨jlow,jhigh,kpos,_⟩ := (cert.2.1 r).mpr ⟨lower,hi⟩
  obtain ⟨chosen,coprime,reject⟩ := cert.2.2 r lower hi unit
  dsimp only
  rw [cert.1]
  change 1≤s.j r ∧ s.j r≤2^40 ∧ 1≤((s.T:ℤ)*s.j r-1)/s.h ∧
    IsCoprime (s.j r) (((s.T:ℤ)*s.j r-1)/s.h) ∧
    ¬∃ z : ℤ, z^2=form s.T s.h (s.j r) (((s.T:ℤ)*s.j r-1)/s.h)
  rw [← chosen]
  exact ⟨jlow,jhigh,kpos,coprime,reject⟩

private theorem counted {s : Row} (v : Valid s) :
    (s.offsets.card:ℤ)=(s.hi-(s.lo-1)).toNat -
      max (⌊(s.hi:ℚ)/(s.p:ℚ)⌋ - ⌊((s.lo-1:ℤ):ℚ)/(s.p:ℚ)⌋) 0 := by
  have inj : Function.Injective s.j := by
    intro x y h
    exact mul_left_cancel₀ v.bp.ne' (add_right_cancel h : s.B*x=s.B*y)
  rw [Row.offsets,card_image_of_injective _ inj]
  have split := filter_card_add_filter_neg_card_eq_card (s:=Ioc (s.lo-1) s.hi) (fun r : ℤ => (s.p:ℤ) ∣ r)
  have mult := Int.Ioc_filter_dvd_card (s.lo-1) s.hi (by exact_mod_cast v.prime.pos : 0<(s.p:ℤ))
  rw [Int.card_Ioc] at split
  push_cast at mult ⊢
  omega

def fresh : Row where
  N := ChebyshevQuarticScale.fresh
  T := 158327039176966334715448284019718823474497913662177975160442996009439310669941017429676080400185006424773254142252582891257193029659269227070095120289800339855421063931472090621260003180611046788905349147963313017385074143012442899089952314244753217806428276920663827209779196401916113023989449483782760844629
  A := 380029
  B := 307403
  C := 75109
  D := 92854
  t := -7
  lo := 2
  hi := 3576777
  p := 7
  e := 1

private theorem fresh_valid : Valid fresh := by
  constructor <;> try unfold Row.InWindow
  all_goals decide +kernel

theorem fresh_row : fresh.Certificate := certified fresh_valid

theorem fresh_count : fresh.offsets.card=3065808 := by
  have eq := counted fresh_valid
  have check : (↑(fresh.hi-(fresh.lo-1)).toNat : ℤ) -
      max (⌊(fresh.hi:ℚ)/(fresh.p:ℚ)⌋ - ⌊((fresh.lo-1:ℤ):ℚ)/(fresh.p:ℚ)⌋) 0 = 3065808 := by decide +kernel
  omega

def crossed : Row where
  N := ChebyshevQuarticScale.crossed
  T := 135037911685235586269825030135549325391376915966798636179319977077209993450011760943044181307768476527897818717675959823440307553022185653953812606479930673789391793187765141283074720630433120513417190939648203494531748575804685158519937612233285802863014656458801051235008057526662884995918450838938076904614
  A := 1213310
  B := 698413
  C := -11284
  D := -19603
  t := -130321
  lo := -2105
  hi := 1572194
  p := 19
  e := 4

private theorem crossed_valid : Valid crossed := by
  constructor <;> try unfold Row.InWindow
  all_goals decide +kernel

theorem crossed_row : crossed.Certificate := certified crossed_valid

theorem crossed_count : crossed.offsets.card=1491442 := by
  have eq := counted crossed_valid
  have check : (↑(crossed.hi-(crossed.lo-1)).toNat : ℤ) -
      max (⌊(crossed.hi:ℚ)/(crossed.p:ℚ)⌋ - ⌊((crossed.lo-1:ℤ):ℚ)/(crossed.p:ℚ)⌋) 0 = 1491442 := by decide +kernel
  omega

end PrimeFactors.GroupedOffsetRowExamples
