import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.Finset.Card
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-! A narrow product interval on a translated integer lattice. Subtracting
a chord bounds the area determinant. Once three points are collinear,
their product spread has an integral lower bound from a second difference. -/

namespace PrimeFactors.MixedPrefixSlab

set_option exponentiation.threshold 2048

/-- The signed determinant of the two differences based at P. -/
def det (P Q R : ℤ × ℤ) : ℤ :=
  (Q.1-P.1)*(R.2-P.2)-(R.1-P.1)*(Q.2-P.2)

/-- Scaled signed vertical distance from the chord of T/x across the slab. -/
noncomputable def chordError (B L T x₀ x y : ℚ) : ℚ :=
  B*(x₀*(x₀+L)*y+T*x-T*(2*x₀+L))

/-- The chord leaves a scaled strip of total height x₀(x₀+L)(L²+1/2).
The lower and upper errors are kept separately for reuse. -/
theorem chord_strip {B L T x₀ x y : ℚ} (bp : 0<B) (base : B≤x₀) (tp : 0≤T)
    (upper : T≤4*B^2) (left : x₀≤x) (right : x≤x₀+L)
    (low : T≤x*y) (high : x*y≤T+1/2) :
    -(x₀*(x₀+L)*L^2) ≤ chordError B L T x₀ x y ∧
      chordError B L T x₀ x y ≤ x₀*(x₀+L)*(1/2) := by
  let t := x-x₀
  let A := x₀*(x₀+L)
  let v := A*y+T*x-T*(2*x₀+L)
  have t₀ : 0≤t := sub_nonneg.mpr left
  have tL : t≤L := by dsimp [t]; linarith only [right]
  have x0p := bp.trans_le base
  have Ap : 0≤A := mul_nonneg x0p.le (by linarith only [x0p,t₀,tL])
  have scale : B^2≤A := by
    dsimp [A];rw [sq];exact mul_le_mul base (by linarith only [base,t₀,tL]) bp.le x0p.le
  have tcap : T≤4*A := upper.trans (mul_le_mul_of_nonneg_left scale (by decide))
  have bend := mul_nonneg t₀ (sub_nonneg.mpr tL)
  have quarter : t*(L-t)≤L^2/4 := by
    apply sub_nonneg.mp
    rw [show L^2/4-t*(L-t)=(2*t-L)^2/4 by ring]
    exact div_nonneg (sq_nonneg _) (by decide)
  have curved := mul_le_mul tcap quarter bend (by linarith only [Ap])
  have upperError := mul_le_mul_of_nonneg_left (show x*y-T≤1/2 by linarith only [high]) Ap
  have lowerError := mul_nonneg Ap (sub_nonneg.mpr low)
  have id : x*v=A*(x*y-T)-T*(t*(L-t)) := by dsimp [v,A,t];ring
  have lowerV : -(A*L^2)≤x*v := by
    rw [id,←zero_sub (A*L^2)]
    exact sub_le_sub lowerError (curved.trans_eq (by ring))
  have upperV : x*v≤A*(1/2) := by
    rw [id]
    exact (sub_le_self _ (mul_nonneg tp bend)).trans upperError
  change -(A*L^2)≤B*v ∧ B*v≤A*(1/2)
  have bx := base.trans left
  rcases le_total v 0 with neg|pos
  · exact ⟨lowerV.trans (mul_le_mul_of_nonpos_right bx neg),
      (mul_nonpos_of_nonneg_of_nonpos bp.le neg).trans (mul_nonneg Ap (by positivity))⟩
  · exact ⟨(neg_nonpos.mpr (mul_nonneg Ap (sq_nonneg L))).trans (mul_nonneg bp.le pos),
      (mul_le_mul_of_nonneg_right bx pos).trans upperV⟩

private theorem det_zero {B L T U x₀ ρ σ : ℚ} {d : ℤ} {P Q R : ℤ × ℤ}
    (bp : 0<B) (base : B≤x₀) (tp : 0≤T) (upper : T≤4*B^2) (maxWidth : U≤1/2)
    (size : 2*L*(1/2+L^2)<B^2) (integerScale : (d:ℚ)=B) (dvd : d∣det P Q R)
    (points : ∀ z∈[P,Q,R], x₀≤(z.1:ℚ)+ρ ∧ (z.1:ℚ)+ρ≤x₀+L ∧
      T≤((z.1:ℚ)+ρ)*((z.2:ℚ)+σ) ∧ ((z.1:ℚ)+ρ)*((z.2:ℚ)+σ)≤T+U) :
    det P Q R=0 := by
  let X (z : ℤ × ℤ) := (z.1:ℚ)+ρ
  let Y (z : ℤ × ℤ) := (z.2:ℚ)+σ
  let A := x₀*(x₀+L)
  let W (z : ℤ × ℤ) := chordError B L T x₀ (X z) (Y z)+A*L^2
  let H := A*(1/2+L^2)
  have prepared (z : ℤ × ℤ) (m : z∈[P,Q,R]) :
      x₀≤X z ∧ X z≤x₀+L ∧ 0≤W z ∧ W z≤H := by
    obtain ⟨a,b,c,dd⟩ := points z m
    obtain ⟨wl,wu⟩ := chord_strip bp base tp upper a b c (by linarith only [dd,maxWidth])
    refine ⟨a,b,?_,?_⟩ <;> dsimp only [W,H,A,X,Y] <;> nlinarith only [wl,wu]
  have ⟨pl,pu,pw,ph⟩ := prepared P (by simp)
  have ⟨ql,qu,qw,qh⟩ := prepared Q (by simp)
  have ⟨rl,ru,rw',rh⟩ := prepared R (by simp)
  have dxq : |X Q-X P|≤L := abs_le.mpr ⟨by linarith only [pu,ql],by linarith only [qu,pl]⟩
  have dxr : |X R-X P|≤L := abs_le.mpr ⟨by linarith only [pu,rl],by linarith only [ru,pl]⟩
  have dwq : |W Q-W P|≤H := abs_le.mpr ⟨by linarith only [qw,ph],by linarith only [qh,pw]⟩
  have dwr : |W R-W P|≤H := abs_le.mpr ⟨by linarith only [rw',ph],by linarith only [rh,pw]⟩
  have lp := (abs_nonneg _).trans dxq
  have m₁ := mul_le_mul dxq dwr (abs_nonneg _) lp
  have m₂ := mul_le_mul dxr dwq (abs_nonneg _) lp
  have Ap : 0<A := mul_pos (bp.trans_le base) (by linarith only [bp,base,lp])
  have id : (X Q-X P)*(W R-W P) - (X R-X P)*(W Q-W P) =
      (B*A)*(det P Q R:ℚ) := by
    dsimp only [X,Y,W,chordError,A,det];push_cast;ring
  have triangle := abs_add_le ((X Q-X P)*(W R-W P)) (-((X R-X P)*(W Q-W P)))
  rw [←sub_eq_add_neg,id,abs_mul,abs_of_nonneg (mul_nonneg bp.le Ap.le),abs_neg,
    abs_mul,abs_mul] at triangle
  have scale : |(det P Q R:ℚ)| * B ≤ 2*L*(1/2+L^2) := by
    apply le_of_mul_le_mul_right (a:=A) _ Ap
    dsimp only [H] at m₁ m₂
    nlinarith only [triangle,m₁,m₂]
  have lim : |(det P Q R:ℚ)| < B := by
    apply lt_of_mul_lt_mul_right (a:=B) _ bp.le
    simpa only [pow_two] using scale.trans_lt size
  rw [←integerScale] at lim
  have small : |det P Q R|<d := by exact_mod_cast lim
  by_contra nz
  exact (not_lt_of_ge (Int.le_of_dvd (abs_pos.mpr nz) ((dvd_abs _ _).mpr dvd))) small

/-- Consecutive collinear steps with positive first coordinates a,b and
vertical steps u,v obey a*v=b*u. The weighted second difference of their
products is b*(a+b)*u. Their product range therefore has width at least one. -/
private theorem three_products {x y a b u v T U : ℚ} (ap : 1≤a) (bp : 1≤b)
    (step : 1≤|u|) (cross : a*v=b*u) (narrow : U≤1/2)
    (first : T≤(x-a)*(y-u) ∧ (x-a)*(y-u)≤T+U)
    (middle : T≤x*y ∧ x*y≤T+U) (last : T≤(x+b)*(y+v) ∧ (x+b)*(y+v)≤T+U) : False := by
  let l := (x-a)*(y-u)-x*y
  let r := (x+b)*(y+v)-x*y
  have ll : |l|≤U := abs_le.mpr ⟨by dsimp [l];linarith only [first.1,middle.2],
    by dsimp [l];linarith only [first.2,middle.1]⟩
  have rr : |r|≤U := abs_le.mpr ⟨by dsimp [r];linarith only [last.1,middle.2],
    by dsimp [r];linarith only [last.2,middle.1]⟩
  have ab := (by linarith only [ap] : 0≤a)
  have bb := (by linarith only [bp] : 0≤b)
  have id : b*l+a*r=(a+b)*(b*u) := by
    dsimp [l,r];linear_combination (x+b)*cross
  have tri := abs_add_le (b*l) (a*r)
  rw [id,abs_mul,abs_mul,abs_mul,abs_mul,abs_of_nonneg ab,abs_of_nonneg bb,
    abs_of_nonneg (add_nonneg ab bb)] at tri
  have bound : b*|u|≤U := by
    apply le_of_mul_le_mul_left (a:=a+b) _ (by linarith only [ap,bp])
    linarith only [tri,mul_le_mul_of_nonneg_left ll bb,mul_le_mul_of_nonneg_left rr ab]
  have floor := mul_le_mul bp step (by decide : (0:ℚ)≤1) bb
  linarith only [bound,narrow,floor]


/-- At most two points for any chord slab whose area bound is less than the
integer lattice determinant. All scales and translations are public. -/
theorem card_le_two_of_chord (V : Finset (ℤ × ℤ)) (ρ σ T U x₀ L : ℚ) (d : ℤ)
    (positive : 0<(d:ℚ)) (size : 2*L*(1/2+L^2)<(d:ℚ)^2)
    (base : (d:ℚ)≤x₀) (start : 0≤T) (top : T≤4*(d:ℚ)^2) (width : U≤1/2)
    (bounds : ∀ P∈V, x₀≤(P.1:ℚ)+ρ ∧ (P.1:ℚ)+ρ≤x₀+L ∧
      T≤((P.1:ℚ)+ρ)*((P.2:ℚ)+σ) ∧ ((P.1:ℚ)+ρ)*((P.2:ℚ)+σ)≤T+U)
    (fst : Set.InjOn Prod.fst (V : Set (ℤ × ℤ))) (snd : Set.InjOn Prod.snd (V : Set (ℤ × ℤ)))
    (lattice : ∀ P∈V, ∀ Q∈V, ∀ R∈V, d∣det P Q R) : V.card≤2 := by
  have ordered (P Q R : ℤ × ℤ) (pm : P∈V) (qm : Q∈V) (rm : R∈V)
      (pq : P.1<Q.1) (qr : Q.1<R.1) : False := by
    have zero := det_zero (ρ:=ρ) (σ:=σ) positive base start top width
      size rfl (lattice P pm Q qm R rm) (by
        intro z hz
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
        rcases hz with rfl|rfl|rfl
        · exact bounds _ pm
        · exact bounds _ qm
        · exact bounds _ rm)
    let x := (Q.1:ℚ)+ρ
    let y := (Q.2:ℚ)+σ
    let a := (Q.1:ℚ)-P.1
    let b := (R.1:ℚ)-Q.1
    let u := (Q.2:ℚ)-P.2
    let v := (R.2:ℚ)-Q.2
    have ap : 1≤a := by dsimp [a];exact_mod_cast (show (1:ℤ)≤Q.1-P.1 by omega)
    have bp : 1≤b := by dsimp [b];exact_mod_cast (show (1:ℤ)≤R.1-Q.1 by omega)
    have neq : Q.2≠P.2 := fun he => (ne_of_gt pq) (congrArg Prod.fst (snd qm pm he))
    have u1 : 1≤|u| := by
      have z := abs_pos.mpr (sub_ne_zero.mpr neq)
      dsimp [u];exact_mod_cast (show (1:ℤ)≤|Q.2-P.2| by omega)
    have rel : a*v=b*u := by
      dsimp [a,v,b,u]
      exact_mod_cast (show (Q.1-P.1)*(R.2-Q.2)=(R.1-Q.1)*(Q.2-P.2) by
        unfold det at zero;linear_combination zero)
    have eqs : x-a=(P.1:ℚ)+ρ ∧ y-u=(P.2:ℚ)+σ ∧ x+b=(R.1:ℚ)+ρ ∧ y+v=(R.2:ℚ)+σ := by
      refine ⟨?_,?_,?_,?_⟩ <;> dsimp [x,y,a,u,b,v] <;> ring
    obtain ⟨e₁,e₂,e₃,e₄⟩ := eqs
    exact three_products ap bp u1 rel width (by rw [e₁,e₂];exact (bounds P pm).2.2)
      (bounds Q qm).2.2 (by rw [e₃,e₄];exact (bounds R rm).2.2)
  apply Nat.le_of_not_gt
  intro tooMany
  obtain ⟨P,pm,Q,qm,R,rm,pq,pr,qr⟩ := Finset.two_lt_card.mp tooMany
  have pq' : P.1≠Q.1 := fun h => pq (fst pm qm h)
  have pr' : P.1≠R.1 := fun h => pr (fst pm rm h)
  have qr' : Q.1≠R.1 := fun h => qr (fst qm rm h)
  rcases lt_or_gt_of_ne pq' with l|l <;> rcases lt_or_gt_of_ne pr' with m|m <;>
    rcases lt_or_gt_of_ne qr' with n|n
  all_goals first
    | exact ordered P Q R pm qm rm l n
    | exact ordered P R Q pm rm qm m n
    | exact ordered Q P R qm pm rm l m
    | exact ordered Q R P qm rm pm n m
    | exact ordered R P Q rm pm qm m l
    | exact ordered R Q P rm qm pm n l

/-- A target-width slab contains at most two possible integer pairs. The
coordinate translations need not be integral. The low-word lattice supplies
the determinant divisor and the injectivity of its coordinate projections. -/
theorem card_le_two_chord (V : Finset (ℤ × ℤ)) (ρ σ T U x₀ : ℚ)
    (base : (2:ℚ)^319≤x₀) (start : 0≤T) (top : T≤4*(2^319:ℚ)^2) (width : U≤1/2)
    (bounds : ∀ P∈V, x₀≤(P.1:ℚ)+ρ ∧ (P.1:ℚ)+ρ≤x₀+2^212 ∧
      T≤((P.1:ℚ)+ρ)*((P.2:ℚ)+σ) ∧ ((P.1:ℚ)+ρ)*((P.2:ℚ)+σ)≤T+U)
    (fst : Set.InjOn Prod.fst (V : Set (ℤ × ℤ))) (snd : Set.InjOn Prod.snd (V : Set (ℤ × ℤ)))
    (lattice : ∀ P∈V, ∀ Q∈V, ∀ R∈V, (2:ℤ)^319 ∣ det P Q R) : V.card≤2 := by
  apply card_le_two_of_chord V ρ σ T U x₀ (2^212) ((2:ℤ)^319)
  · decide +kernel
  · decide +kernel
  · exact_mod_cast base
  · exact start
  · simpa only [Int.cast_pow,Int.cast_ofNat] using top
  · exact width
  · exact bounds
  · exact fst
  · exact snd
  · exact lattice

end PrimeFactors.MixedPrefixSlab
