import PrimeFactors.ResiduePairWeights
import PrimeFactors.WideResiduePrimeSupply

/-! Conditional frequency of the two singular sum residues modulo 25 for
actual distinct primes in the upper half of the 1024-bit interval. The
analytic input is Corollary 2 of Ernvall-Hytönen and Palojärvi at the two
common endpoints, with the same logarithmic integral in every unit class. -/
namespace PrimeFactors.WidePrimePairSumFrequency

open Finset ResiduePairWeights WideResiduePrimeSupply
open private PrimeFactors.WideResiduePrimeSupply.count_add from PrimeFactors.WideResiduePrimeSupply
set_option exponentiation.threshold 4096

noncomputable def selected : Finset (ZMod 25) := {2,23}
private abbrev W : ℕ := 2^1022
private abbrev E : ℕ := 26400*2^512
private abbrev K : ℕ := 2^476
private noncomputable abbrev pop (x : ZMod 25) := population (L+1) B x

/-- There are 10 selected and 20 total ordered local solutions. The two
solutions with identical coordinates are both selected. -/
theorem local_counts :
    (cells (1:ZMod 25) selected).card=10 ∧ (cells (1:ZMod 25) univ).card=20 ∧
    ((cells (1:ZMod 25) selected).filter (fun z => z.1=z.2)).card=2 ∧
    ((cells (1:ZMod 25) univ).filter (fun z => z.1=z.2)).card=2 := by decide +kernel

theorem class_card_eq (x : ZMod 25) : pop x=(intervalPrimes 25 x.val).card := by
  apply congrArg Finset.card
  change ResiduePairMultiplicity.primes 25 (L+1) B x.val=intervalPrimes 25 x.val
  ext p
  rw [ResiduePairMultiplicity.mem_primes,mem_interval]
  constructor
  · rintro ⟨lo,hi,P,rem⟩
    exact ⟨P,rem,lo,hi.le⟩
  · rintro ⟨P,rem,lo,hi⟩
    have ne : p≠B := fun eq => (Nat.Prime.not_prime_pow (by decide : 2≤1024) (x:=2))
      ((congrArg Nat.Prime eq).mp P)
    exact ⟨lo,hi.lt_of_ne ne,P,rem⟩

private theorem endpoints_difference {a b c t d e : ℝ}
    (lo : |a-c|≤e) (hi : |b-(c+t)|≤e) (add : d+a=b) : |d-t|≤2*e := by
  rw [abs_le] at lo hi ⊢
  constructor <;> linarith

private theorem gap_bound {x y c e : ℝ} (hx : |x-c|≤e) (hy : |y-c|≤e) : x≤y+2*e := by
  linarith only [(abs_le.mp hx).2,(abs_le.mp hy).1]

/-- Every class count differs from the same real center by at most
26400·2^512. This center is independent of its residue representative. -/
theorem class_error {c : ℝ} (x : ZMod 25) (bounds : Endpoints 25 x.val c) :
    |(pop x:ℝ)-increment L W/20| ≤ E := by
  have lb := bounds.1.trans (error_cap (m:=25) (by decide) (by decide)
    (by exact_mod_cast (show 2^1023≤L by decide)) (by exact_mod_cast (show L≤B by decide)))
  have hb := bounds.2.trans (error_cap (m:=25) (by decide) (by decide)
    (by exact_mod_cast (show 2^1023≤L+W by decide)) (by exact_mod_cast (show L+W≤B by decide)))
  have card : ((inBand 25 x.val L W).card:ℝ)+(through 25 x.val L).card=(through 25 x.val (L+W)).card := by
    exact_mod_cast PrimeFactors.WideResiduePrimeSupply.count_add 25 x.val L W
  have phi : Nat.totient 25=20 := by decide +kernel
  rw [phi, Nat.cast_ofNat] at lb hb
  rw [add_div] at hb
  have error := endpoints_difference lb hb card
  rw [class_card_eq]
  exact error.trans (by norm_num [E])

private theorem common_range {c : ℝ}
    (bounds : ∀ a<25, a.Coprime 25 → Endpoints 25 a c) :
    ∃ l u : ℕ, 1≤l ∧ l≤u ∧ K*u^2≤(K+1)*(l-1)^2 ∧
      ∀ x : ZMod 25, IsUnit x → l≤pop x ∧ pop x≤u := by
  have err (x : ZMod 25) (unit : IsUnit x) := class_error x (bounds x.val x.val_lt
    ((ZMod.isUnit_iff_coprime _ _).mp (by simpa only [ZMod.natCast_zmod_val] using unit)))
  let k := pop 1
  have ref := abs_le.mp (err 1 isUnit_one)
  have min : 2^1008 ≤ k := by
    have integral := increment_lower (A:=L) (W:=W) (by decide) (by decide)
    have enough : (2:ℝ)^1008 + (E:ℝ) ≤ ((W:ℕ):ℝ)/710/20 := by norm_num [W,E]
    exact_mod_cast (show (2:ℝ)^1008 ≤ (pop 1:ℝ) by linarith only [integral,ref.1,enough])
  let d := 2*E
  let l := k-d
  let u := k+d
  have finite : d+1+2^1007≤2^1008 := by decide +kernel
  have lower : 2^1007≤l-1 := by dsimp only [l]; omega
  have room : 3*K*(2*d+1)≤l-1 := le_trans (by decide +kernel) lower
  have gap : u=(l-1)+(2*d+1) := by dsimp only [u,l]; omega
  have small : 2*d+1 ≤ l-1 := le_trans (by decide +kernel : 2*d+1 ≤ 2^1007) lower
  have square : K*u^2≤(K+1)*(l-1)^2 := by
    rw [gap]
    have g₁ := Nat.mul_le_mul_left (l-1) room
    have g₂ := Nat.mul_le_mul_left (K*(2*d+1)) small
    nlinarith only [g₁,g₂]
  refine ⟨l,u,by omega,by omega,square,?_⟩
  intro x unit
  have up : (pop x:ℝ)≤(k:ℝ)+2*(E:ℝ) := gap_bound (err x unit) (err 1 isUnit_one)
  have dn : (k:ℝ)≤(pop x:ℝ)+2*(E:ℝ) := gap_bound (err 1 isUnit_one) (err x unit)
  have up' : pop x≤k+2*E := by exact_mod_cast up
  have dn' : k≤pop x+2*E := by exact_mod_cast dn
  dsimp only [l,u,d]
  omega

/-- A cell's weight, including a diagonal cell, lies between (l−1)² and u². -/
private theorem uniform_bounds (A : Finset (ZMod 25)) (k : ℕ) :
    (cells 1 A).card*(k-1)^2 ≤ uniform 1 A k ∧ uniform 1 A k ≤ (cells 1 A).card*k^2 := by
  have bounds (v : ZMod 25 × ZMod 25) : (k-1)^2 ≤ k*(k-if v.1=v.2 then 1 else 0) ∧
      k*(k-if v.1=v.2 then 1 else 0)≤k^2 := by
    by_cases eq : v.1=v.2 <;> simp only [eq,if_pos,if_true,if_false,Nat.sub_zero,pow_two] <;>
      exact ⟨Nat.mul_le_mul (by omega) (by omega),Nat.mul_le_mul (by omega) (by omega)⟩
  constructor
  · simpa only [uniform,sum_const,smul_eq_mul] using
      (sum_le_sum (s:=cells 1 A) (fun v _ => (bounds v).1))
  · simpa only [uniform,sum_const,smul_eq_mul] using
      (sum_le_sum (s:=cells 1 A) (fun v _ => (bounds v).2))

/-- Share of all unordered distinct pairs in the band with product 1 modulo
25 whose sum is 2 or 23 modulo 25. -/
noncomputable def share : ℚ :=
  ((pairs (L+1) B (1:ZMod 25) selected).card:ℚ)/(pairs (L+1) B (1:ZMod 25) univ).card

private theorem ratio_bound {k g t : ℚ} (kp : 0<k) (tp : 0<t) (ru : k*(2*g)≤(k+1)*t)
    (rl : k*t≤(k+1)*(2*g)) : |g/t-1/2|≤1/(k*2) := by
  have lower : (k-1)*t ≤ k*(2*g) := by
    by_cases h : 2*g≤t
    · linarith only [rl,h]
    · nlinarith only [mul_le_mul_of_nonneg_left (le_of_not_ge h) kp.le,tp.le]
  have pos : 0<k*2 := mul_pos kp (by norm_num)
  have left := (div_le_div_iff₀ pos tp).mpr (show (k-1)*t ≤ g*(k*2) by linarith only [lower])
  have right := (div_le_div_iff₀ tp pos).mpr (show g*(k*2) ≤ (k+1)*t by linarith only [ru])
  have left_eq : (k-1)/(k*2)=1/2-1/(k*2) := by field_simp [kp.ne']
  have right_eq : (k+1)/(k*2)=1/2+1/(k*2) := by field_simp [kp.ne']
  rw [left_eq] at left
  rw [right_eq] at right
  exact abs_le.mpr ⟨by linarith only [left],by linarith only [right]⟩

/-- Transfer any uniform range for the twenty unit-class prime populations to
a frequency bound for this particular event, accounting for both diagonals. -/
theorem from_range {k l u : ℕ} (positive : 0<k) (lp : 1≤l) (lu : l≤u)
    (tight : k*u^2≤(k+1)*(l-1)^2)
    (popBounds : ∀ x : ZMod 25, IsUnit x → l≤population (L+1) B x ∧ population (L+1) B x≤u) :
    |share-1/2| ≤ 1/((k:ℚ)*2) := by
  let G := (pairs (L+1) B (1:ZMod 25) selected).card
  let T := (pairs (L+1) B (1:ZMod 25) univ).card
  have counts (A : Finset (ZMod 25)) := count_bounds (1:ZMod 25) isUnit_one A popBounds
  have ls := ((uniform_bounds selected l).1.trans (counts selected).1)
  have us := ((counts selected).2.trans (uniform_bounds selected u).2)
  have lt := ((uniform_bounds univ l).1.trans (counts univ).1)
  have ut := ((counts univ).2.trans (uniform_bounds univ u).2)
  rw [local_counts.1] at ls us
  rw [local_counts.2.1] at lt ut
  change 10*(l-1)^2 ≤ 2*G at ls
  change 2*G ≤ 10*u^2 at us
  change 20*(l-1)^2 ≤ 2*T at lt
  change 2*T ≤ 20*u^2 at ut
  have ub : k*(2*G) ≤ (k+1)*T := by
    nlinarith only [Nat.mul_le_mul_left k us,tight,Nat.mul_le_mul_left (k+1) lt]
  have lb : k*T ≤ (k+1)*(2*G) := by
    nlinarith only [Nat.mul_le_mul_left k ut,tight,Nat.mul_le_mul_left (k+1) ls]
  have uk : u≠0 := by omega
  have nz : (l-1)^2 ≠ 0 := by
    intro zero
    rw [zero,mul_zero] at tight
    exact (not_le_of_gt (Nat.mul_pos positive (pow_pos (Nat.pos_of_ne_zero uk) 2))) tight
  have tp : 0<T := by omega
  have pt : (0:ℚ)<T := Nat.cast_pos.mpr tp
  have ru : (k:ℚ)*(2*(G:ℚ)) ≤ ((k:ℚ)+1)*(T:ℚ) := by exact_mod_cast ub
  have rl : (k:ℚ)*(T:ℚ) ≤ ((k:ℚ)+1)*(2*(G:ℚ)) := by exact_mod_cast lb
  have kl : (0:ℚ)<k := Nat.cast_pos.mpr positive
  exact ratio_bound kl pt ru rl

/-- Under the two published endpoint estimates in every unit class, the
share is within 2^(-477) of one half. -/
theorem near_half (c : ℝ) (bounds : ∀ a<25, a.Coprime 25 → Endpoints 25 a c) :
    |share-1/2| ≤ 1/(2:ℚ)^477 := by
  obtain ⟨l,u,lp,lu,tight,popBounds⟩ := common_range bounds
  have h := from_range (by decide : 0<K) lp lu tight popBounds
  rwa [show (K:ℚ)*2=(2:ℚ)^477 by norm_num [K]] at h

private theorem round_percentage {x : ℚ} (accuracy : |x-1/2|≤1/(2:ℚ)^477) :
    49.9999 < 100*x ∧ 100*x < 50.0001 := by
  have h := abs_le.mp accuracy
  have eps : 1/(2:ℚ)^477 < 1/1000000 := by norm_num
  constructor <;> linarith only [h.1,h.2,eps]

/-- In percentages, the same share is strictly between 49.9999% and 50.0001%. -/
theorem percentage (c : ℝ) (bounds : ∀ a<25, a.Coprime 25 → Endpoints 25 a c) :
    49.9999 < 100*share ∧ 100*share < 50.0001 := round_percentage (near_half c bounds)

end PrimeFactors.WidePrimePairSumFrequency
