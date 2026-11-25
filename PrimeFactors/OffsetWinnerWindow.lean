import PrimeFactors.OffsetSquareWitness
import Mathlib.Algebra.BigOperators.Intervals

namespace PrimeFactors.OffsetWinnerWindow
open CompleteOffsetSearch

/-- A winner is within one unit of the unknown rational slope T/p. The
proof uses p*j=(p*s−T*v)²+h*v² and the sharp offset bound j<p. -/
theorem close_to_slope {p q T h j s v : ℕ} (pp : 0<p) (digits : T^2+h=p*q)
    (small : j<p) (label : j+2*T*(s*v)=p*s^2+q*v^2) :
    p*s<T*v+p ∧ T*v<p*s+p := by
  have input : (T:ℤ)^2+h=(p:ℤ)*q := by exact_mod_cast digits
  have sum : (j:ℤ)+2*T*(s*v)=(p:ℤ)*s^2+(q:ℤ)*v^2 := by exact_mod_cast label
  have mass : (p:ℤ)*j=((p:ℤ)*s-T*v)^2+h*v^2 := by
    linear_combination (p:ℤ)*sum - (v:ℤ)^2*input
  have less : (p:ℤ)*j<p^2 := by
    simpa only [pow_two] using mul_lt_mul_of_pos_left (show (j:ℤ)<p by exact_mod_cast small)
      (show (0:ℤ)<p by exact_mod_cast pp)
  have square : ((p:ℤ)*s-T*v)^2<(p:ℤ)^2 := by
    nlinarith only [mass,less,mul_nonneg (Nat.cast_nonneg h : 0≤(h:ℤ)) (sq_nonneg (v:ℤ))]
  have close := (sq_lt_sq).mp square
  rw [abs_of_nonneg (Nat.cast_nonneg p : 0≤(p:ℤ)),abs_lt] at close
  constructor
  · exact_mod_cast (show (p:ℤ)*s<T*v+p by linarith only [close.2])
  · exact_mod_cast (show (T:ℤ)*v<p*s+p by linarith only [close.1])

/-- The public lower bound L for the smaller factor confines the possible
factorizations k=(v+d)v to a narrow interval of d. -/
theorem winner_window {p q j k f L : ℕ} (pp : p.Prime) (qp : q.Prime) (ord : p<q)
    (balance : q≤2*p) (large : 17≤p) (lo : 0<L) (lp : L≤p) (kp : 0<k) (prim : j.Coprime k)
    (sharp : 3*j^2≤4*(p*q-(p*q).sqrt^2))
    (hit : probe (p*q) (p*q).sqrt j k=some f) :
    let T := (p*q).sqrt
    ∃ v d : ℕ, 0<v ∧ (v+d).Coprime v ∧ k=(v+d)*v ∧ L*(v+d-1)<T*v ∧ d≤(T-L)*v/L+1 := by
  intro T
  obtain ⟨digits,_,cut⟩ := balanced_parameters pp qp ord balance large
  change T^2+(p*q-T^2)=p*q at digits
  have small : j<p := by
    by_contra! bad
    have sq := Nat.pow_le_pow_left bad 2
    omega
  obtain ⟨s,v,_,vp,cop,eq,sum⟩ := OffsetSquareWitness.exists_vector_of_hit pp qp ord.ne kp prim hit
  rw [eq] at sum
  obtain ⟨left,right⟩ := close_to_slope pp.pos digits small sum
  have pt : p≤T := Nat.le_sqrt'.mpr (by simpa [pow_two] using Nat.mul_le_mul_left p ord.le)
  have vs : v≤s := by
    by_contra! bad
    have a := Nat.mul_le_mul_left p (show s+1≤v from bad)
    have b := Nat.mul_le_mul_right v pt
    rw [Nat.mul_add, Nat.mul_one] at a
    omega
  have strict : L*(s-1)<T*v := by
    have reduced := Nat.mul_le_mul_right (s-1) lp
    have sp : 1≤s := vp.trans_le vs
    have restore := congrArg (fun x => p*x) (Nat.sub_add_cancel sp)
    nlinarith only [reduced,restore,left]
  obtain ⟨d,sd⟩ := Nat.exists_eq_add_of_le vs
  refine ⟨v,d,vp,sd ▸ cop,sd ▸ eq,sd ▸ strict,?_⟩
  have budget : d*L≤(T-L)*v+L := by
    by_cases zero : d=0
    · simp [zero]
    · have pd : L*(d-1)≤p*(d-1) := Nat.mul_le_mul_right _ lp
      have pv := Nat.mul_le_mul_right v lp
      have pos : 1≤d := by omega
      have one := congrArg (fun z => p*z) (Nat.sub_add_cancel pos)
      have one' := congrArg (fun z => L*z) (Nat.sub_add_cancel pos)
      have tl := congrArg (fun z => z*v) (Nat.sub_add_cancel (lp.trans pt))
      rw [sd] at left
      nlinarith only [pd,pv,one,one',tl,left]
  have le := (Nat.le_div_iff_mul_le lo).mpr budget
  simpa only [Nat.add_div_right _ lo] using le

/-- Every allowed coordinate is visited by the two integer loop ranges. -/
theorem loop_membership {s v K T L : ℕ} (vp : 0<v) (lp : 0<L) (vs : v≤s)
    (budget : s*v≤K) (window : L*(s-1)<T*v) :
    v≤K.sqrt ∧ s≤K/v ∧ s≤(T*v+L-1)/L := by
  refine ⟨Nat.le_sqrt'.mpr ?_, (Nat.le_div_iff_mul_le vp).mpr budget,
    (Nat.le_div_iff_mul_le lp).mpr ?_⟩
  · simpa [pow_two] using (Nat.mul_le_mul_right v vs).trans budget
  · have sp : 1≤s := vp.trans_le vs
    have restore := congrArg (fun x => L*x) (Nat.sub_add_cancel sp)
    have cancellation := Nat.sub_add_cancel (show 1≤T*v+L by omega)
    nlinarith only [window,restore,cancellation]

/-- Count the elementary inner-loop iterations before testing the product
bound, primitivity, or the discriminant. The index v has at most sqrt K
values since k=(v+d)v. -/
noncomputable def visits (D L K : ℕ) : ℕ :=
  ∑ i∈Finset.range K.sqrt, (D*(i+1)/L+2)

/-- Count the actual inclusive ranges used in the integer search.  The
minimum incorporates the product cap and may further shorten an inner loop. -/
theorem loop_card_le {T L : ℕ} (lp : 0<L) (lt : L≤T) (K : ℕ) :
    (∑ i∈Finset.range K.sqrt, (Finset.Icc (i+1)
      (min (K/(i+1)) ((T*(i+1)+L-1)/L))).card) ≤ visits (T-L) L K := by
  unfold visits
  apply Finset.sum_le_sum
  intro i _
  let v := i+1
  have restore := congrArg (fun x => x*v) (Nat.sub_add_cancel lt)
  have add : T*v+L-1≤((T-L)*v+L)+L*v := by
    have eq : T*v=(T-L)*v+L*v := by nlinarith only [restore]
    omega
  have roof : (T*v+L-1)/L≤(((T-L)*v+L)+L*v)/L := Nat.div_le_div_right add
  rw [Nat.add_mul_div_left _ _ lp,Nat.add_div_right _ lp] at roof
  have cap := min_le_right (K/v) ((T*v+L-1)/L)
  change (Finset.Icc v (min (K/v) ((T*v+L-1)/L))).card≤(T-L)*v/L+2
  rw [Nat.card_Icc,Nat.sub_le_iff_le_add]
  calc
    min (K/v) ((T*v+L-1)/L)+1 ≤ ((T*v+L-1)/L)+1 := Nat.add_le_add_right cap 1
    _ ≤ _ := by omega

theorem visits_bound (D L K : ℕ) : 2*L*visits D L K≤D*(K+K.sqrt)+4*L*K.sqrt := by
  let r := K.sqrt
  have each (i : ℕ) : 2*L*(D*(i+1)/L+2)≤2*D*i+(2*D+4*L) := by
    have h := Nat.div_mul_le_self (D*(i+1)) L
    nlinarith only [h]
  have sum := Finset.sum_le_sum (s:=Finset.range r) (fun i _ => each i)
  simp only [←Finset.mul_sum,Finset.sum_add_distrib,Finset.sum_const,Finset.card_range,
    nsmul_eq_mul] at sum
  have scale := congrArg (fun x => D*x) (Finset.sum_range_id_mul_two r)
  have sq : r^2≤K := Nat.sqrt_le' K
  have weighted := Nat.mul_le_mul_left D sq
  change 2*L*(∑ i∈Finset.range r,(D*(i+1)/L+2))≤D*(K+r)+4*L*r
  rcases r with _|r
  · simp
  · simp only [Nat.add_sub_cancel] at scale
    simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_range,nsmul_eq_mul] at *
    rw [←Finset.mul_sum] at sum
    nlinarith only [sum,scale,weighted]

/-- A promised upper bound on the larger prime gives a public lower bound
for the smaller one by ceiling division of the product. -/
theorem lower_from_cap {p q U : ℕ} (up : 0<U) (cap : q≤U) :
    (p*q+(U-1))/U ≤ p := by
  apply Nat.lt_succ_iff.mp
  apply (Nat.div_lt_iff_lt_mul up).mpr
  have bound := Nat.mul_le_mul_left p cap
  rw [Nat.succ_mul]
  omega

/-- Sum the per-row bounds without enumerating offsets. R is a public bound
on the integer square root of every row limit. -/
theorem aggregate_bound (D L R : ℕ) (rows : Finset ℕ) (limit : ℕ → ℕ)
    (cap : ∀ i∈rows,(limit i).sqrt≤R) :
    2*L*(∑ i∈rows,visits D L (limit i)) ≤
    D*((∑ i∈rows,limit i)+rows.card*R)+4*L*rows.card*R := by
  have row (i : ℕ) (hi : i∈rows) :
      2*L*visits D L (limit i) ≤ D*limit i+(D*R+4*L*R) := by
    have l := Nat.mul_le_mul_left D (cap i hi)
    have m := Nat.mul_le_mul_left (4*L) (cap i hi)
    nlinarith only [visits_bound D L (limit i),l,m]
  have total := Finset.sum_le_sum row
  simp only [←Finset.mul_sum,Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul] at total
  nlinarith only [total]

/-- A minimizing coordinate vector gives a strict best approximation to
the hidden rational T/p among all smaller positive denominators. -/
theorem minimum_best {p T q h s v : ℤ} (pp : 0<p) (hp : 0<h) (det : p*q-T^2=h)
    (minimal : ∀ a b : ℤ, 0<ReducedOffsetMinimum.Q p T q a b →
        ReducedOffsetMinimum.Q p T q s v≤ReducedOffsetMinimum.Q p T q a b)
    {a b : ℤ} (bp : 0<b) (smaller : b<v) : abs (p*s-T*v) < abs (p*a-T*b) := by
  have nonzero : a≠0 ∨ b≠0 := Or.inr bp.ne'
  have positive := ReducedOffsetMinimum.positive pp hp det nonzero
  have compare := mul_le_mul_of_nonneg_left (minimal a b positive) pp.le
  have identity (x y : ℤ) : p*ReducedOffsetMinimum.Q p T q x y =
    (p*x-T*y)^2+h*y^2 := by rw [←det]; unfold ReducedOffsetMinimum.Q;ring
  rw [identity,identity] at compare
  have penalty := mul_lt_mul_of_pos_left
    (pow_lt_pow_left₀ smaller bp.le (by decide : 2≠0)) hp
  apply sq_lt_sq.mp
  linarith only [compare,penalty]

end PrimeFactors.OffsetWinnerWindow
