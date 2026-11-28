import PrimeFactors.TransposedBlockQuotient

/-! A bounded interval for one digit product when the transposed word
has a known additive offset. -/

namespace PrimeFactors.OffsetTransposeBlockWindow

/-- Last representative of the observed remainder below the public ceiling,
provided that the ceiling reaches that remainder. -/
def upper (B N t : ℕ) : ℕ :=
  N%B+B*((N/(B+1)^2+B*t-N%B)/B)

def candidate (B N t j : ℕ) : ℕ := upper B N t-B*j

/-- The shifted digit product is still the low product digit, with carries. -/
theorem residue {B a b t N : ℕ} (product : (B*a+b)*(B*b+a+t)=N) :
    N % B = (b*(a+t)) % B := by
  have eqn : (B*a+b)*(B*b+a+t) = B*(a*(B*b+a+t)+b*b)+b*(a+t) := by ring
  rw [← product, eqn, Nat.mul_add_mod]

/-- The public quotient gives a one-sided error smaller than B in one
direction and at most B*t in the other. -/
theorem bounds {B a b t N : ℕ} (ordered : a≤b) (top : b<B)
    (product : (B*a+b)*(B*b+a+t)=N) :
    b*(a+t) ≤ N/(B+1)^2+B*t ∧ N/(B+1)^2 < b*(a+t)+B := by
  have pos : 0<B := by omega
  have denom : 0<(B+1)^2 := by positivity
  have eqn : N=(B+1)^2*(a*b)+B*(b-a)^2+t*(B*a+b) := by
    rw [← product, Nat.mul_add]
    rw [← Nat.mul_comm t, ← TransposedBlockQuotient.identity ordered]
    rfl
  have base : a*b ≤ N/(B+1)^2 := by
    apply (Nat.le_div_iff_mul_le denom).mpr
    rw [eqn, Nat.mul_comm (a*b)]
    omega
  have height : B*(b-a)^2 < B*(B+1)^2 := Nat.mul_lt_mul_of_pos_left
    (Nat.pow_lt_pow_left (by omega) (by decide : 2≠0)) pos
  have small : B*a+b ≤ b*(B+1)^2 := by
    calc B*a+b ≤ B*b+b := Nat.add_le_add_right (Nat.mul_le_mul_left B ordered) _
         _ = b*(B+1) := by ring
         _ ≤ b*(B+1)^2 := Nat.mul_le_mul_left _ (by nlinarith only [Nat.zero_le (B^2)])
  constructor
  · have h := Nat.mul_le_mul_right t top.le
    rw [Nat.mul_add, Nat.mul_comm b a]
    omega
  · apply (Nat.div_lt_iff_lt_mul denom).mpr
    rw [eqn]
    calc (B+1)^2*(a*b)+B*(b-a)^2+t*(B*a+b)
          < (B+1)^2*(a*b)+B*(B+1)^2+t*(b*(B+1)^2) :=
              Nat.add_lt_add_of_lt_of_le (Nat.add_lt_add_left height _) (Nat.mul_le_mul_left t small)
         _ = (b*(a+t)+B)*(B+1)^2 := by ring

/-- A positive offset puts the hidden digit product strictly above the
quotient. This saves one position even for the smallest offset. -/
theorem below_digit {B a b t N : ℕ} (ordered : a≤b) (top : b<B)
    (digit : 0<b) (offset : 0<t) (product : (B*a+b)*(B*b+a+t)=N) :
    N/(B+1)^2 < b*(a+t) := by
  have sq : (b-a)^2 < B*b+b+(b-a) := calc
    (b-a)^2 ≤ b^2 := Nat.pow_le_pow_left (Nat.sub_le _ _) _
    _ < B*b := by simpa only [pow_two] using Nat.mul_lt_mul_of_pos_right top digit
    _ ≤ _ := by omega
  have stretch : B*b+b+(b-a) ≤ t*(B*b+b+(b-a)) := by
    simpa using Nat.mul_le_mul_right (B*b+b+(b-a)) (show 1≤t by omega)
  have gap := Nat.mul_lt_mul_of_pos_left (sq.trans_le stretch) (show 0<B by omega)
  have balance : N+B*(t*(B*b+b+(b-a)))=b*(a+t)*(B+1)^2+B*(b-a)^2 := by
    obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le ordered
    rw [← product]
    simp only [Nat.add_sub_cancel_left]
    ring
  exact (Nat.div_lt_iff_lt_mul (by positivity)).mpr (by omega)

private theorem last_eq {B C H : ℕ} (pos : 0<B) (lo : C≤H) :
    C%B+B*((H-C%B)/B) = C+B*((H-C)/B) := by
  have parts := Nat.mod_add_div C B
  have split : H-C%B=B*(C/B)+(H-C) := by omega
  rw [split, Nat.mul_add_div pos, Nat.mul_add]
  omega

/-- Every congruent nonnegative integer that fits under the ceiling is at
most the public representative. -/
theorem maximal {B N t c : ℕ} (pos : 0<B) (same : c%B=N%B)
    (below : c≤N/(B+1)^2+B*t) : c≤upper B N t := by
  rw [upper, ← same, last_eq pos below]
  omega

/-- If the ceiling reaches the remainder, the maximum itself meets the ceiling
and belongs to the observed remainder class. -/
theorem upper_spec {B N t : ℕ} (reach : N%B≤N/(B+1)^2+B*t) :
    upper B N t≤N/(B+1)^2+B*t ∧ upper B N t%B=N%B := by
  obtain h := Nat.mod_add_div (N/(B+1)^2+B*t-N%B) B
  unfold upper
  refine ⟨by omega, ?_⟩
  rw [Nat.add_comm, Nat.mul_add_mod, Nat.mod_mod]

private theorem position {B N t C : ℕ} (pos : 0<B) (same : N%B=C%B)
    (lo : C≤N/(B+1)^2+B*t) :
    candidate B N t ((N/(B+1)^2+B*t-C)/B)=C := by
  rw [candidate, upper, same, last_eq pos lo]
  omega

/-- The hidden digit product occurs among the t+1 indicated positions. -/
theorem contains {B a b t N : ℕ} (ordered : a≤b) (top : b<B)
    (product : (B*a+b)*(B*b+a+t)=N) :
    ∃ j≤t, candidate B N t j=b*(a+t) := by
  have pos : 0<B := by omega
  obtain ⟨lo,hi⟩ := bounds ordered top product
  let j := (N/(B+1)^2+B*t-b*(a+t))/B
  have close : N/(B+1)^2+B*t-b*(a+t)<(t+1)*B := by
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm t B]
    omega
  have rank : j<t+1 := (Nat.div_lt_iff_lt_mul pos).mpr close
  exact ⟨j, by omega, position pos (residue product) lo⟩

/-- For a positive offset t and nonzero b, t positions suffice. -/
theorem contains_positive {B a b t N : ℕ} (ordered : a≤b) (top : b<B)
    (digit : 0<b) (offset : 0<t) (product : (B*a+b)*(B*b+a+t)=N) :
    ∃ j<t, candidate B N t j=b*(a+t) := by
  have pos : 0<B := by omega
  obtain ⟨lo,_⟩ := bounds ordered top product
  have hi := below_digit ordered top digit offset product
  have bt : 0<B*t := Nat.mul_pos pos offset
  have close : N/(B+1)^2+B*t-b*(a+t)<t*B := by rw [Nat.mul_comm t B]; omega
  exact ⟨_, (Nat.div_lt_iff_lt_mul pos).mpr close, position pos (residue product) lo⟩

theorem offset_one {B a b N : ℕ} (ordered : a≤b) (top : b<B) (digit : 0<b)
    (product : (B*a+b)*(B*b+a+1)=N) : upper B N 1=b*(a+1) := by
  obtain ⟨j, small, hit⟩ := contains_positive ordered top digit (by decide : 0<1) product
  have zero : j=0 := by omega
  simpa [zero, candidate] using hit

theorem card_le (B N t : ℕ) :
    ((Finset.range (t+1)).image (candidate B N t)).card ≤ t+1 :=
  (Finset.card_image_le).trans_eq (Finset.card_range _)

/-- Decimal transposition gives 76 from 67; adding three gives 79.
The hidden digit product is the second of the four positions. -/
theorem control : (10*6+7)*(10*7+6+3)=5293 ∧ Nat.Prime 67 ∧ Nat.Prime 79 ∧
    5293/11^2=43 ∧ upper 10 5293 3=73 ∧ candidate 10 5293 3 1=7*(6+3) := by
  norm_num [upper, candidate]

theorem control_one : (8*2+7)*(8*7+2+1)=1357 ∧ Nat.Prime 23 ∧ Nat.Prime 59 ∧
    upper 8 1357 1=21 := by norm_num [upper]

end PrimeFactors.OffsetTransposeBlockWindow
