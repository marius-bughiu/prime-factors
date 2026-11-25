import PrimeFactors.Multiplier
import PrimeFactors.IntervalGap
import PrimeFactors.ChebyshevQuarticScale

namespace PrimeFactors.WeightedDivisorExclusion

set_option exponentiation.threshold 4096
set_option maxRecDepth 10000

/-- Three public ways to bound a weighted trace from below throughout a divisor
interval: a negative discriminant, an increasing quadratic, or a decreasing one. -/
def Lower (a e z l u : ℤ) : Prop :=
  z^2<4*a*e ∨ (z≤2*a*l ∧ z*l<a*l^2+e) ∨ (2*a*u≤z ∧ z*u<a*u^2+e)

private theorem lower_bound {a e z l u d : ℤ} (ap : 0<a) (ld : l≤d) (du : d≤u)
    (cert : Lower a e z l u) : z*d<a*d^2+e := by
  rcases cert with disc|⟨rise,lo⟩|⟨fall,hi⟩
  · have pos : 0<4*a*(a*d^2+e-z*d) := by nlinarith only [disc,sq_nonneg (2*a*d-z)]
    exact sub_pos.mp ((mul_pos_iff_of_pos_left (by positivity : 0<4*a)).mp pos)
  · have derivative : 0≤a*(d+l)-z := by nlinarith only [rise,mul_le_mul_of_nonneg_left ld ap.le]
    nlinarith only [lo,mul_nonneg (sub_nonneg.mpr ld) derivative]
  · have derivative : a*(u+d)-z≤0 := by nlinarith only [fall,mul_le_mul_of_nonneg_left du ap.le]
    nlinarith only [hi,mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr du) derivative]

private theorem upper_bound {a e z l u d : ℤ} (ap : 0<a) (ld : l≤d) (du : d≤u)
    (lo : a*l^2+e<z*l) (hi : a*u^2+e<z*u) : a*d^2+e<z*d := by
  by_cases left : 2*a*d≤z
  · have derivative : a*(d+l)-z≤0 := by nlinarith only [left,mul_le_mul_of_nonneg_left ld ap.le]
    nlinarith only [lo,mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr ld) derivative]
  · have derivative : 0≤a*(u+d)-z := by nlinarith only [left,mul_le_mul_of_nonneg_left du ap.le]
    nlinarith only [hi,mul_nonneg (sub_nonneg.mpr du) derivative]

/-- Each permitted trace needs one modulus with no possible square root.
The choice of modulus can differ from row to row. -/
def rowsMiss (n a b first count : ℕ) (moduli : List ℕ) : Bool :=
  (List.range count).all fun i => moduli.any fun m =>
    decide (0<m) && (List.range m).all fun y =>
      decide ((first+2*i)^2%m ≠ (4*a*b*n+y^2)%m)

private theorem no_square {n a b first count i g : ℕ} {moduli : List ℕ}
    (miss : rowsMiss n a b first count moduli=true) (inside : i<count) :
    (first+2*i)^2≠4*a*b*n+g^2 := by
  intro square
  obtain ⟨m,_,yes⟩ := List.any_eq_true.mp (List.all_eq_true.mp miss i (List.mem_range.mpr inside))
  simp only [Bool.and_eq_true,decide_eq_true_eq] at yes
  have exclude := List.all_eq_true.mp yes.2 (g%m) (List.mem_range.mpr (Nat.mod_lt g yes.1))
  rw [decide_eq_true_eq,square] at exclude
  apply exclude
  apply Nat.ModEq.add_left (4*a*b*n)
  exact (Nat.mod_modEq g m).symm.pow 2

/-- Every divisor in [l,u] would give a parity-compatible trace a*p+b*q
between the first and last charged rows. A modular nonsquare on every
such row consequently excludes every divisor in the entire interval.
The lower certificate permits starting away from the trace minimum. -/
theorem excludes {n a b l u first count : ℕ} {moduli : List ℕ} (odd : n%2=1)
    (ap : 0<a) (lp : 0<l) (parity : first%2=(a+b)%2)
    (low : Lower a ((b:ℤ)*n) ((first:ℤ)-2) l u)
    (left : a*l^2+b*n<(first+2*count)*l) (right : a*u^2+b*n<(first+2*count)*u)
    (miss : rowsMiss n a b first count moduli=true) (p : ℕ) (pl : l≤p) (pu : p≤u) : ¬p∣n := by
  rintro ⟨q,pair⟩
  let S := a*p+b*q
  have pp : 0<(p:ℤ) := by exact_mod_cast lp.trans_le pl
  have prod : (n:ℤ)=(p:ℤ)*q := by exact_mod_cast pair
  have trace : (a:ℤ)*p^2+(b:ℤ)*n=p*(S:ℤ) := by dsimp [S]; push_cast; rw [prod]; ring
  have lz : (l:ℤ)≤p := by exact_mod_cast pl
  have uz : (p:ℤ)≤u := by exact_mod_cast pu
  have apz : (0:ℤ)<a := by exact_mod_cast ap
  have lower := lower_bound apz lz uz low
  rw [trace] at lower
  have lowerS : (first:ℤ)-2<S := (mul_lt_mul_iff_of_pos_right pp).mp (by
    simpa only [mul_comm (p:ℤ) (S:ℤ)] using lower)
  have upper := upper_bound (a:=(a:ℤ)) (e:=(b:ℤ)*n) (z:=(first:ℤ)+2*count) apz lz uz
    (by exact_mod_cast left) (by exact_mod_cast right)
  rw [trace] at upper
  have upperS : (S:ℤ)<first+2*count := (mul_lt_mul_iff_of_pos_right pp).mp (by
    simpa only [mul_comm (p:ℤ) (S:ℤ)] using upper)
  have modPair := congrArg (·%2) pair
  change n%2=(p*q)%2 at modPair
  rw [Nat.mul_mod,odd] at modPair
  have pq : p%2=1 ∧ q%2=1 := by
    rcases Nat.mod_two_eq_zero_or_one p with h|h <;>
      rcases Nat.mod_two_eq_zero_or_one q with k|k <;> simp [h,k] at modPair ⊢
  have same : S%2=first%2 := by
    simp only [S,Nat.add_mod,Nat.mul_mod a p,Nat.mul_mod b q,pq.1,pq.2,
      mul_one,Nat.mod_mod,parity]
  let i := (S-first)/2
  have index : i<count ∧ S=first+2*i := by dsimp [i];omega
  have identity := multiplier_sum_square p q a b
  change S^2=4*a*b*(p*q)+(Nat.dist (a*p) (b*q))^2 at identity
  rw [←pair,index.2] at identity
  exact no_square miss index.1 identity

private theorem control {n c count : ℕ} {moduli : List ℕ}
    (center : c*c≤4*n/5 ∧ 4*n/5<(c+1)*(c+1))
    (checks : let l:=c-2^512; let u:=c+2^512; let first:=10*c+9
      n%2=1 ∧ 0<l ∧ first%2=(5+4)%2 ∧ ((first:ℤ)-2)^2<4*5*(4*n) ∧
      5*l^2+4*n<(first+2*count)*l ∧ 5*u^2+4*n<(first+2*count)*u ∧
      rowsMiss n 5 4 first count moduli=true)
    (p : ℕ) (low : (4*n/5).sqrt-2^512≤p) (high : p≤(4*n/5).sqrt+2^512) : ¬p∣n := by
  rw [←Nat.eq_sqrt.mpr center] at low high
  obtain ⟨odd,lp,par,lower,left,right,miss⟩ := checks
  exact excludes odd (by decide : 0<5) lp par (Or.inl lower) left right miss p low high

/-- Linear weights 5,4 exclude this interior interval using 3 trace residues modulo 23. -/
theorem fresh_exclusion (p : ℕ) (low : (4*ChebyshevQuarticScale.fresh/5).sqrt-2^512≤p)
    (high : p≤(4*ChebyshevQuarticScale.fresh/5).sqrt+2^512) : ¬p∣ChebyshevQuarticScale.fresh := by
  apply control (c:=141612008910387631963158666082064823822081816230610227785041710318483841606953793675302304603455064929947326392113816447481950968709212023549647070715668977031087040319311587215579268206823472218754033006584968546925784704397715492359693779453015549054820572433657477290108069333277530311135866189335537203949)
    (count:=3) (moduli:=[23]) _ _ p low high <;> decide +kernel

/-- Linear weights 5,4 exclude this interior interval using 4 trace residues modulo 33. -/
theorem crossed_exclusion (p : ℕ) (low : (4*ChebyshevQuarticScale.crossed/5).sqrt-2^512≤p)
    (high : p≤(4*ChebyshevQuarticScale.crossed/5).sqrt+2^512) : ¬p∣ChebyshevQuarticScale.crossed := by
  apply control (c:=120781580027119982017467732148558945429337785162817183011949012701939620266896876805006839292678815441007877145710414891454986303221682597853959506976312769830327376452480451575758814872466143666520991333842225222856873239157115578950553942792521041950598842422803666996448188031882337190161187951777057437464)
    (count:=4) (moduli:=[33]) _ _ p low high <;> decide +kernel

end PrimeFactors.WeightedDivisorExclusion
