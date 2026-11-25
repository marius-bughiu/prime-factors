import PrimeFactors.GroupedNormFactors
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.ModEq
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.LinearCombination

namespace PrimeFactors.GroupedNormFrequency

/-- One determinant-one representation with the public square root below 2^(2s). -/
structure Witness (s : ℕ) where
  a : ℕ
  b : ℕ
  h : ℕ
  u : ℕ
  v : ℕ
  apos : 0 < a
  bpos : 0 < b
  hpos : 0 < h
  neighboring : a*v = b*u+1
  bound : u*v + h*(a*b) < 2^(2*s)

def Witness.input {s : ℕ} (w : Witness s) : ℕ :=
  (w.u*w.v + w.h*(w.a*w.b))^2 + w.h

private def pack (base hi lo : ℕ) := base*hi+lo

private theorem unpack {base x y r s : ℕ} (hr : r<base) (hs : s<base)
    (eq : pack base x r = pack base y s) : x=y ∧ r=s := by
  have pos : 0<base := by omega
  have hi := congrArg (· / base) eq
  have lo := congrArg (· % base) eq
  simpa [pack, Nat.mul_add_div pos, Nat.mul_add_mod, Nat.div_eq_of_lt hr,
    Nat.div_eq_of_lt hs, Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt hs] using And.intro hi lo

private theorem pack_lt {b h r : ℕ} (hr : r<b) : pack b h r < b*(h+1) := by
  unfold pack
  rw [Nat.mul_succ]
  omega

private theorem interval_offset {a : ℕ} (ha : 0<a) :
    a-2^(Nat.log 2 a) < 2^(Nat.log 2 a) := by
  have lo := Nat.pow_log_le_self 2 ha.ne'
  have hi := Nat.lt_pow_succ_log_self (by decide : 1<2) a
  rw [pow_succ] at hi
  omega

private def slot (a b h : ℕ) :=
  let A := 2^(Nat.log 2 a)
  let B := 2^(Nat.log 2 b)
  pack B (pack A (h-1) (a-A)) (b-B)

private theorem slot_lt {a b h : ℕ} (ha : 0<a) (hb : 0<b) (hh : 0<h) :
    slot a b h < h*(a*b) := by
  let A := 2^(Nat.log 2 a)
  let B := 2^(Nat.log 2 b)
  have ra := interval_offset ha
  have rb := interval_offset hb
  have inner : pack A (h-1) (a-A) < A*h := by
    simpa only [Nat.sub_add_cancel hh] using pack_lt (h:=h-1) ra
  calc
    _ < B*(pack A (h-1) (a-A)+1) := pack_lt rb
    _ ≤ B*(A*h) := Nat.mul_le_mul_left _ inner
    _ = h*(A*B) := by ring
    _ ≤ _ := Nat.mul_le_mul_left h (Nat.mul_le_mul (Nat.pow_log_le_self 2 ha.ne')
      (Nat.pow_log_le_self 2 hb.ne'))

private theorem slot_injective {a b h c d k : ℕ}
    (ha : 0<a) (hb : 0<b) (hh : 0<h) (hc : 0<c) (hd : 0<d) (hk : 0<k)
    (ac : Nat.log 2 a=Nat.log 2 c) (bd : Nat.log 2 b=Nat.log 2 d)
    (eq : slot a b h=slot c d k) : a=c ∧ b=d ∧ h=k := by
  unfold slot at eq
  rw [← ac, ← bd] at eq
  have orc := interval_offset hc
  have ord := interval_offset hd
  rw [← ac] at orc
  rw [← bd] at ord
  obtain ⟨e, residB⟩ := unpack (interval_offset hb) ord eq
  obtain ⟨top, residA⟩ := unpack (interval_offset ha) orc e
  have ba := Nat.pow_log_le_self 2 ha.ne'
  have bb := Nat.pow_log_le_self 2 hb.ne'
  have bc := Nat.pow_log_le_self 2 hc.ne'
  have bD := Nat.pow_log_le_self 2 hd.ne'
  rw [← ac] at bc
  rw [← bd] at bD
  omega

private theorem quotient_lt {s : ℕ} (w : Witness s) : w.u/w.a < 2^s := by
  let z := w.u/w.a
  have az : w.a*z ≤ w.u := Nat.mul_div_le ..
  have zu : z ≤ w.u := (Nat.le_mul_of_pos_left _ w.apos).trans az
  have zv : z ≤ w.v := by
    apply Nat.le_of_mul_le_mul_left (c:=w.a) _ w.apos
    exact az.trans ((Nat.le_mul_of_pos_left _ w.bpos).trans (by rw [w.neighboring]; omega))
  have sq := Nat.mul_le_mul zu zv
  have bound := w.bound
  have less : z^2 < (2^s)^2 := by
    rw [← pow_mul, Nat.mul_comm s 2, pow_two z]
    omega
  exact lt_of_not_ge (fun h => (not_le_of_gt less) (Nat.pow_le_pow_left h 2))

private theorem continued_neighbor_unique {a b u v x y : ℕ}
    (apos : 0<a) (left : a*v=b*u+1) (right : a*y=b*x+1) (same : u/a=x/a) :
    u=x ∧ v=y := by
  have residue : u ≡ x [MOD a] := by
    apply Nat.modEq_iff_dvd.mpr
    refine ⟨(v:ℤ)*x-(y:ℤ)*u, ?_⟩
    zify at left right
    linear_combination (u:ℤ)*right - (x:ℤ)*left
  have eu := Nat.mod_add_div u a
  rw [show u%a=x%a from residue, same, Nat.mod_add_div] at eu
  subst x
  exact ⟨rfl, Nat.mul_left_cancel apos (left.trans right.symm)⟩

private theorem parameters_small {s : ℕ} (w : Witness s) :
    w.a < 2^(2*s) ∧ w.b < 2^(2*s) := by
  have ab : w.a*w.b ≤ w.h*(w.a*w.b) := Nat.le_mul_of_pos_left _ w.hpos
  have left := (Nat.le_mul_of_pos_right w.a w.bpos).trans ab
  have right := (Nat.le_mul_of_pos_left w.b w.apos).trans ab
  have := w.bound
  omega

private abbrev Code (s : ℕ) :=
  Fin (2*s) × Fin (2*s) × Fin (2^(2*s)) × Fin (2^s)

private def code {s : ℕ} (w : Witness s) : Code s :=
  (⟨Nat.log 2 w.a, Nat.log_lt_of_lt_pow w.apos.ne' (parameters_small w).1⟩,
   ⟨Nat.log 2 w.b, Nat.log_lt_of_lt_pow w.bpos.ne' (parameters_small w).2⟩,
   ⟨slot w.a w.b w.h, (slot_lt w.apos w.bpos w.hpos).trans
     ((Nat.le_add_left ..).trans_lt w.bound)⟩, ⟨w.u/w.a, quotient_lt w⟩)

private theorem code_determines {s : ℕ} (w z : Witness s) (eq : code w=code z) :
    w.input=z.input := by
  have ac := congrArg (fun c : Code s => c.1.val) eq
  have bd := congrArg (fun c : Code s => c.2.1.val) eq
  have packEq := congrArg (fun c : Code s => c.2.2.1.val) eq
  have divEq := congrArg (fun c : Code s => c.2.2.2.val) eq
  have same := slot_injective w.apos w.bpos w.hpos z.apos z.bpos z.hpos ac bd packEq
  change w.u/w.a=z.u/z.a at divEq
  rw [← same.1] at divEq
  have det := z.neighboring
  rw [← same.1, ← same.2.1] at det
  have uv := continued_neighbor_unique w.apos w.neighboring det divEq
  unfold Witness.input
  rw [same.1, same.2.1, same.2.2, uv.1, uv.2]

/-- The bound counts distinct products even when one product has many witnesses. -/
theorem family_card {s : ℕ} (products : Finset ℕ)
    (covered : ∀ n ∈ products, ∃ w : Witness s, w.input=n) :
    products.card ≤ (2*s)^2 * 2^(2*s) * 2^s := by
  classical
  let pick (n : ↥products) := Classical.choose (covered n.val n.property)
  have spec (n : ↥products) : (pick n).input=n.val := Classical.choose_spec (covered n.val n.property)
  have inj : Function.Injective (fun n : ↥products => code (pick n)) := by
    intro n m eq
    exact Subtype.ext ((spec n).symm.trans ((code_determines _ _ eq).trans (spec m)))
  have h := Fintype.card_le_of_injective _ inj
  simpa [Code, pow_two, Nat.mul_assoc] using h

/-- Any multiplier accepted by the executable puts the input in the counted family. -/
theorem witness_of_probe {n k p q s : ℕ} (size : n.sqrt < 2^(2*s))
    (found : GroupedNormFactors.probe n k = some (p,q)) :
    ∃ w : Witness s, w.input=n := by
  unfold GroupedNormFactors.probe at found
  dsimp only at found
  split at found
  next passed =>
    obtain ⟨hp,kp,room,hit⟩ := passed
    obtain ⟨a,b,u,v,ap,bp,_,_,det,_,rep⟩ := GroupedNormFactors.witness_of_hit kp room hit
    let w : Witness s := ⟨a,b,n-n.sqrt^2,u,v,ap,bp,hp,det,rep.trans_lt size⟩
    refine ⟨w, ?_⟩
    change (u*v+(n-n.sqrt^2)*(a*b))^2+(n-n.sqrt^2)=n
    rw [rep, Nat.add_sub_of_le (show n.sqrt^2 ≤ n by simpa [pow_two] using Nat.sqrt_le n)]
  next => contradiction

/-- Counts every successful product below this root bound, allowing any
multiplier, even when the successful value is chosen after inspecting n. -/
theorem successes_card {s : ℕ} (ns : Finset ℕ)
    (size : ∀ n ∈ ns, n.sqrt < 2^(2*s))
    (success : ∀ n ∈ ns, ∃ k p q, GroupedNormFactors.probe n k=some (p,q)) :
    ns.card ≤ (2*s)^2 * 2^(2*s) * 2^s := by
  apply family_card
  intro n hn
  obtain ⟨_,_,_,hit⟩ := success n hn
  exact witness_of_probe (size n hn) hit

/-- Each dyadic range of residual offsets costs at most T multiplier tests
in total, with an interval completed for each offset. -/
theorem sum_offset_cost (T n : ℕ) :
    ∑ h ∈ Finset.Ico 1 (2^n), T/h ≤ n*T := by
  induction n with
  | zero => simp
  | succ n ih =>
    have pos : 0 < 2^n := by positivity
    have step : 2^n ≤ (2:ℕ)^(n+1) := by rw [pow_succ]; omega
    rw [← Finset.sum_Ico_consecutive (fun h => T/h) pos step, Nat.succ_mul]
    apply Nat.add_le_add ih
    calc
      _ ≤ ∑ _h ∈ Finset.Ico (2^n) (2^(n+1)), T/2^n := by
        exact Finset.sum_le_sum (fun h mem => Nat.div_le_div_left (Finset.mem_Ico.mp mem).1 pos)
      _ = 2^n*(T/2^n) := by simp [Nat.card_Ico, pow_succ, Nat.mul_two]
      _ ≤ _ := Nat.mul_div_le ..

set_option exponentiation.threshold 4096 in
/-- At the target width the code space has 1,556 bits. The second inequality
uses the repository's lower bound on the population of distinct balanced
prime pairs, with the logarithm of 2^1023 bounded above by 710. -/
theorem scale_2048 :
    (2*512)^2 * (2:ℕ)^(2*512) * 2^512 = 2^1556 ∧
    2^465 * 2 * 2^1556 * 71000^2 < 22^2*(2:ℕ)^(2*1023) := by decide +kernel

/-- Completing the square gives a public ellipse for every successful test. -/
theorem ellipse {T h k d : ℤ} :
    d^2=1+4*k*(T-h*k) → (2*h*k-T)^2+h*d^2=T^2+h := by
  intro e
  rw [e]
  ring

/-- Starting above N and multiplying its known norm representation by an
integral Pell unit keeps the proposed gcd numerator in the zero class
whenever N is coprime to 2H. The two equations encode the new coordinates. -/
theorem upper_square_orbit {T H k m r t N : ℤ} (base : N=T^2-H)
    (first : T+2*H*k=T*r+H*t) (second : 2*m+1=T*t+r) :
    2*H*(k*T-m)=N*(r-1) := by
  rw [base]
  linear_combination T*first-H*second

theorem upper_square_orbit_dvd {T H k m r t N : ℤ} (base : N=T^2-H)
    (first : T+2*H*k=T*r+H*t) (second : 2*m+1=T*t+r) (unit : IsCoprime N (2*H)) :
    N ∣ k*T-m := by
  apply unit.dvd_of_dvd_mul_left
  exact ⟨r-1, upper_square_orbit base first second⟩

end PrimeFactors.GroupedNormFrequency
