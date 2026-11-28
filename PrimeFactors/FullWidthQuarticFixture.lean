import PrimeFactors.CubicPlantedPrimality
import PrimeFactors.ComplementaryQuarticProducts
import PrimeFactors.Fermat
import PrimeFactors.Certificate
import Mathlib.Tactic.ReduceModChar

/-! A deliberately constructed 2,048-bit input for the branch reading the
fourth root of the quotient by four. Both 1,024-bit outputs have a common
known divisor of their predecessors. Fermat's first midpoint also succeeds. -/
namespace PrimeFactors.FullWidthQuarticFixture

set_option maxRecDepth 8192
set_option exponentiation.threshold 4096

/-- For this binary order the two digits of (n−1)/F exclude a proper split.
The low digit exceeds the high digit plus one, while a+b≤a*b+1 for positive a,b. -/
private theorem binary {n low high : ℕ} (z : ZMod n) (size : 1<n)
    (shape : n=1+2^490*(low+2^490*high)) (small : low<2^490)
    (height : high+1<2^490) (separate : high+1<low)
    (half : z^(2^489) = -1) (cop : Nat.Coprime ((-1 - 1 : ZMod n).val) n) : n.Prime := by
  apply CubicPlantedPrimality.prime_of_order (F:=2^490) z size (by decide +kernel) shape small height
  · intro a b ap bp sum prod
    obtain ⟨i,rfl⟩ := Nat.exists_eq_succ_of_ne_zero ap.ne'
    obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero bp.ne'
    nlinarith [Nat.zero_le (i*j)]
  · simpa using (Covers.cons 490 Nat.prime_two covers_one)
  · rw [show (2:ℕ)^490=2^489*2 by decide +kernel,pow_mul,half]; ring
  · intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    rw [show (2:ℕ)^490/2=2^489 by decide +kernel,half]
    exact cop


/-- The two Sophie Germain factors have predecessors 2t(t−1) and 2t(t+1). -/
theorem one_factors (t : ℕ) (pos : 0<t) : RecognizingQuarticProducts.factors 1 t=
    (2*t*(t-1)+1,2*t*(t+1)+1) := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero pos.ne'
  apply Prod.ext
  · change 1^2+2*(k+1)^2-2*1*(k+1)=2*(k+1)*((k+1)-1)+1
    rw [Nat.add_sub_cancel]
    apply (Nat.sub_eq_iff_eq_add (by nlinarith [Nat.zero_le (k^2)])).mpr
    ring
  · change 1^2+2*(k+1)^2+2*1*(k+1)=2*(k+1)*(k+1+1)+1
    ring

/-- The complementary recognizer recovers this whole positive-parameter family. -/
theorem one_y_branch (t : ℕ) (pos : 0<t) : ComplementaryQuarticProducts.recognizeY (1+4*t^4)=
    some (2*t*(t-1)+1,2*t*(t+1)+1) := by
  apply (ComplementaryQuarticProducts.completeY (by decide : 0<1) pos (by simp) ?_).trans
  · exact congrArg some (one_factors t pos)
  · nlinarith [Nat.zero_le (t^2),Nat.zero_le (t^3)]

/-- The first Fermat midpoint works for the same family, for every t. -/
theorem one_first_fermat (t : ℕ) : ceilSqrt (1+4*t^4)=2*t^2+1 ∧
    (2*t^2+1)^2=(1+4*t^4)+(2*t)^2 := by
  have eq : 1+4*t^4=(2*t^2)^2+1 := by ring
  exact ⟨by rw [eq,ceilSqrt,Nat.sqrt_eq'],by ring⟩

attribute [local irreducible] ceilSqrt ComplementaryQuarticProducts.recognizeY

/-- The first accepted parameter in the recorded bounded sweep. -/
abbrev y : ℕ := 21114860*2^487
abbrev p : ℕ := 2*y*(y-1)+1
abbrev q : ℕ := 2*y*(y+1)+1
abbrev N : ℕ := 1+4*y^4


/-- The order witness is base 17 projected to the order `2^490` subgroup. -/
theorem p_prime : Nat.Prime p := by
  let z : ZMod p := 78067354636781570753682489376366210336341428728629594958990042969889922967138986891709237391828913989944035035785371421762928076952392410051386138812520218067043432416979111960069073563707904080391319975797836796078372728896639185393016885113290013036877186297176836234068900697578699774574343444829045114002
  apply binary (low:=2^489-5278715) (high:=13932416025612) z
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · unfold z p y; reduce_mod_char
  · decide +kernel

/-- The order witness is base 3 projected to the order `2^490` subgroup. -/
theorem q_prime : Nat.Prime q := by
  let z : ZMod q := 118696021325379341477499600456969693592677580518165461861889795237964996475519396867686348715510945019614726286149594400344731211778888061096765778069642513498099002025007799158721144092213689733657096563711233762380685186614723437427748056440577324857333238748758226870715544054580558536338761939772436484659
  apply binary (low:=2^489+5278715) (high:=13932416025612) z
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · unfold z q y; reduce_mod_char
  · decide +kernel

/-- Both distinct output primes and their product have their requested widths. -/
theorem data : ExactFactorization N [p,q] ∧ 2^1023≤p ∧ p<q ∧ q<2^1024 ∧ 2^2047≤N ∧ N<2^2048 := by
  refine ⟨⟨by decide +kernel,?_⟩,by decide +kernel⟩
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  exact hr.elim (fun eq => eq ▸ p_prime) (fun eq => eq ▸ q_prime)

/-- The actual public recognizer takes N as its only input. -/
theorem quartic : N=1^4+4*y^4 ∧ ComplementaryQuarticProducts.recognizeY N=some (p,q) :=
  ⟨rfl,one_y_branch y (by decide +kernel)⟩

theorem first_fermat : ceilSqrt N=2*y^2+1 ∧ (2*y^2+1)^2=N+(2*y)^2 := one_first_fermat y

end PrimeFactors.FullWidthQuarticFixture
