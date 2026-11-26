import PrimeFactors.WeightedMultiplierPoints
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! Exact normalization for multipliers a²n+b with positive intercepts. -/
namespace PrimeFactors.AffineExcess

/-- First possible small correction before the public congruence is imposed. -/
def base (a b : ℕ) := (b-1)/a + 1

def stride (t a b : ℕ) := Nat.gcd 24 (2*((a^2+1)*t+b))

/-- The i-th correction, computed from the residue t=n mod 24 alone. -/
def correction (t a b i : ℕ) :=
  let m := stride t a b
  let lo := base a b
  let h := (a-1)^2*t+b
  lo + ((m + h%m - lo%m)%m) + i*m

def slope (t a b i : ℕ) := a*correction t a b i-b

def excess (n u c : ℕ) := 4*u*n+c^2

theorem base_bounds {a b : ℕ} (ap : 0<a) (bp : 0<b) :
    a*((b-1)/a)<b ∧ b≤a*base a b ∧ base a b≤b := by
  have h := Nat.mul_div_le (b-1) a
  have j := Nat.lt_mul_div_succ (b-1) ap
  have v := Nat.div_le_self (b-1) a
  unfold base
  omega

/-- The exact ceiling square root is obtained by squaring the two adjacent
integers. The guard is automatic for the bounded intercepts used below. -/
theorem ceiling_label {n a b : ℕ} (np : 0<n) (ap : 0<a) (bp : 0<b)
    (small : ((b-1)/a)^2 < 4*n) :
    (4*(a^2*n+b)*n-1).sqrt+1 = 2*a*n+base a b := by
  obtain ⟨first,last,_⟩ := base_bounds ap bp
  let j := (b-1)/a
  have lhs : (2*a*n+j)^2 < 4*(a^2*n+b)*n := by
    have h := Nat.mul_le_mul_right (4*n) (show a*j+1≤b from first)
    change j^2 < 4*n at small
    nlinarith only [h,small]
  have rhs : 4*(a^2*n+b)*n ≤ (2*a*n+(j+1))^2 := by
    have h := Nat.mul_le_mul_right (4*n) last
    change b≤a*(j+1) at last
    change b*(4*n)≤a*(j+1)*(4*n) at h
    nlinarith only [h,Nat.zero_le ((j+1)^2)]
  have bottom := Nat.le_sqrt'.mpr (show (2*a*n+j)^2 ≤ 4*(a^2*n+b)*n-1 by omega)
  have top := Nat.sqrt_lt'.mpr (show 4*(a^2*n+b)*n-1 < (2*a*n+(j+1))^2 by
    have p : 0<4*(a^2*n+b)*n := by positivity
    omega)
  change _ = 2*a*n+(j+1)
  omega

theorem stride_positive (t a b : ℕ) : 0 < stride t a b :=
  Nat.gcd_pos_of_pos_left _ (by decide)

theorem stride_dvd (t a b : ℕ) : stride t a b ∣ 24 := Nat.gcd_dvd_left ..

theorem stride_for_product (n a b : ℕ) :
    stride (n%24) a b = Nat.gcd 24 (2*(a^2*n+b+n)) := by
  have h : n%24 ≡ n [MOD 24] := Nat.mod_modEq _ _
  have e := ((h.mul_left (a^2+1)).add_right b).mul_left 2
  unfold stride
  rw [Nat.gcd_comm 24, Nat.gcd_comm 24]
  convert e.gcd_eq using 2
  ring

theorem correction_window (t a b i : ℕ) :
    base a b + i*stride t a b ≤ correction t a b i ∧
    correction t a b i < base a b + (i+1)*stride t a b := by
  have h := Nat.mod_lt (stride t a b + ((a-1)^2*t+b)%stride t a b -
    base a b % stride t a b) (stride_positive t a b)
  dsimp only [correction]
  rw [Nat.add_mul,one_mul]
  omega

theorem correction_residue (t a b i : ℕ) :
    correction t a b i ≡ (a-1)^2*t+b [MOD stride t a b] := by
  let m := stride t a b
  let z := (a-1)^2*t+b
  let l := base a b
  have lp : l%m < m := Nat.mod_lt _ (stride_positive ..)
  have e : l%m + (m+z%m-l%m) = m+z%m := by omega
  have a₁ := (Nat.mod_modEq l m).symm.add (Nat.mod_modEq (m+z%m-l%m) m)
  have right : m+z%m ≡ z [MOD m] := by simp [Nat.ModEq]
  have ind : i*m ≡ 0 [MOD m] := Nat.modEq_zero_iff_dvd.mpr (dvd_mul_left ..)
  have merged := a₁.trans (show l%m+(m+z%m-l%m) ≡ z [MOD m] by rw [e]; exact right)
  simpa only [correction,m,l,z,Nat.add_zero] using merged.add ind

/-- The bounded offset gives the required label residue for the true large weight. -/
theorem label_residue {n a b i : ℕ} (ap : 0<a) :
    2*a*n+correction (n%24) a b i ≡ a^2*n+b+n [MOD stride (n%24) a b] := by
  let m := stride (n%24) a b
  have h : n%24 ≡ n [MOD m] := (Nat.mod_modEq n 24).of_dvd (stride_dvd ..)
  have linked := (correction_residue (n%24) a b i).trans ((h.mul_left ((a-1)^2)).add_right b)
  have aeq : a-1+1=a := by omega
  have algebra : 2*a*n+((a-1)^2*n+b) = a^2*n+b+n := by
    generalize xeq : a-1 = x at aeq ⊢
    rw [←aeq]
    ring
  exact (linked.add_left (2*a*n)).trans (algebra ▸ Nat.ModEq.refl _)

theorem row_bounds {t a b i K J : ℕ} (ap : 0<a) (bp : 0<b)
    (ak : a≤K) (bk : b≤K) (ij : i<J) :
    0<correction t a b i ∧ correction t a b i<K+24*J ∧
    b+slope t a b i=a*correction t a b i ∧ slope t a b i<24*K*J := by
  obtain ⟨raw,low,hi⟩ := base_bounds ap bp
  obtain ⟨start,last⟩ := correction_window t a b i
  have stride_cap := Nat.le_of_dvd (by decide : 0<24) (stride_dvd t a b)
  have high := last.trans_le (Nat.add_le_add_left (Nat.mul_le_mul (by omega : i+1≤J) stride_cap) _)
  have ac := Nat.mul_le_mul_left a (by omega : base a b ≤ correction t a b i)
  have ueq : b+slope t a b i=a*correction t a b i := by unfold slope; omega
  have less := Nat.mul_le_mul_left a (show correction t a b i+1 ≤ base a b+J*24 by omega)
  have expand : a*base a b=a*((b-1)/a)+a := by simp [base,Nat.mul_add]
  have cap := Nat.mul_le_mul_right (J*24) ak
  rw [Nat.mul_add,Nat.mul_one,Nat.mul_add,expand] at less
  refine ⟨?_,?_,ueq,?_⟩
  · have one : 0<base a b := by simp [base]
    omega
  · rw [Nat.mul_comm 24 J]
    omega
  · rw [show 24*K*J=K*(J*24) by ring]
    omega

theorem reduced_row {a b c u n : ℕ} (row : b+u=a*c) :
    (2*a*n+c)^2 = 4*(a^2*n+b)*n + excess n u c := by
  unfold excess
  nlinarith only [Nat.mul_le_mul_right (4*n) row.le, Nat.mul_le_mul_right (4*n) row.ge]

private theorem gcd_congr {n x y : ℤ} (h : x ≡ y [ZMOD n]) : x.gcd n=y.gcd n := by
  have step {u v : ℤ} (e : u ≡ v [ZMOD n]) : u.gcd n ∣ v.gcd n := by
    apply Int.natCast_dvd_natCast.mp
    apply Int.dvd_coe_gcd _ Int.gcd_dvd_right
    have hsub := (Int.gcd_dvd_right (a:=u) (b:=n)).trans (Int.modEq_iff_dvd.mp e)
    simpa using dvd_add hsub (Int.gcd_dvd_left (a:=u) (b:=n))
  exact Nat.dvd_antisymm (step h) (step h.symm)

/-- delta may be either z or -z. This retains the gcd signs used by both
the small expression and the two original large labels. -/
theorem reduced_gcd (n a h c d delta : ℤ) :
    ((2*a*n+c)*(2*h*n+d)+delta).gcd n = (c*d+delta).gcd n := by
  apply gcd_congr
  apply Int.modEq_iff_dvd.mpr
  exact ⟨-(4*a*h*n+2*a*d+2*h*c),by ring⟩

def coordinate (n u v c d : ℕ) := 8*u*v*n+u*d^2+v*c^2
def constant (u v c d : ℕ) := ((u:ℤ)*(d:ℤ)^2-(v:ℤ)*(c:ℤ)^2).natAbs

/-- Each fixed positive slope pair maps products injectively to the first norm coordinate. -/
theorem coordinate_injective {u v c d : ℕ} (up : 0<u) (vp : 0<v) :
    Function.Injective (fun n => coordinate n u v c d) := by
  intro n m h
  simp only [coordinate,Nat.add_right_cancel_iff] at h
  exact Nat.eq_of_mul_eq_mul_left (by positivity) h

theorem norm {n u v c d z t f : ℕ} (hit : z^2=excess n u c*excess n v d)
    (radical : u*v=t*f^2) :
    (coordinate n u v c d)^2=t*(2*f*z)^2+(constant u v c d)^2 := by
  apply (Nat.cast_inj (R:=ℤ)).mp
  push_cast
  change (((coordinate n u v c d:ℕ):ℤ))^2 = _
  simp only [coordinate,constant,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,
    Nat.cast_ofNat,Int.natCast_natAbs,sq_abs]
  have square : (z:ℤ)^2=(4*u*n+(c:ℤ)^2)*(4*v*n+(d:ℤ)^2) := by
    exact_mod_cast (show z^2=(4*u*n+c^2)*(4*v*n+d^2) from hit)
  have rad : (u:ℤ)*v=t*(f:ℤ)^2 := by exact_mod_cast radical
  linear_combination -4 * (t:ℤ) * (f:ℤ)^2 * square +
    4 * ((4*(u:ℤ)*n+c^2)*(4*v*n+d^2)) * rad

/-- If the two affine expressions are proportional, their positive square
root agrees with cd modulo n. Its two possible gcds have the same values
as those of 0 and 2cd modulo n. -/
theorem proportional {n u v c d z : ℕ} (cop : n.Coprime c) (zero : constant u v c d=0)
    (hit : z^2=excess n u c*excess n v d) : z ≡ c*d [MOD n] := by
  have eq : u*d^2=v*c^2 := by
    have h := Int.natAbs_eq_zero.mp zero
    change (u:ℤ)*(d:ℤ)^2-(v:ℤ)*(c:ℤ)^2=0 at h
    exact_mod_cast sub_eq_zero.mp h
  have rel : d^2*excess n u c=c^2*excess n v d := by
    unfold excess
    nlinarith only [Nat.mul_le_mul_right (4*n) eq.le,Nat.mul_le_mul_right (4*n) eq.ge]
  have cancel : c*z=d*excess n u c := by
    apply (Nat.pow_left_inj (by decide : 2≠0)).mp
    rw [mul_pow,mul_pow,hit]
    calc
      _ = (c^2*excess n v d)*excess n u c := by ring
      _ = _ := by rw [←rel]; ring
  apply Nat.ModEq.cancel_left_of_coprime cop
  rw [cancel]
  have red : excess n u c ≡ c^2 [MOD n] := by
    simp [excess,Nat.ModEq,Nat.add_mod]
  rw [show c*(c*d) = d*c^2 by ring]
  exact red.mul_left d

/-- For square uv, a nonzero discriminant constant must itself have square
at least the first norm coordinate. A supplied small constant rules out a hit. -/
theorem square_slopes {n u v c d z f : ℕ} (radical : u*v=f^2)
    (hit : z^2=excess n u c*excess n v d) (positive : 0<constant u v c d) :
    coordinate n u v c d ≤ (constant u v c d)^2 := by
  let x := coordinate n u v c d
  let y := 2*f*z
  let C := constant u v c d
  have eq : x^2=y^2+C^2 := by simpa [x,y,C] using norm hit (t:=1) (by simpa using radical)
  have pos : 0<C^2 := pow_pos positive _
  have yx : y<x := (Nat.pow_lt_pow_iff_left (by decide : 2≠0)).mp (by omega : y^2<x^2)
  obtain ⟨k,hk⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_of_lt yx)
  change x ≤ C^2
  rw [hk] at eq ⊢
  nlinarith only [eq, Nat.zero_le (k^2), Nat.zero_le (2*y*k), Nat.zero_le y,Nat.zero_le k]

open Finset

/-- Each product occupies a distinct Pell point at fixed normalized rows. -/
theorem fiber {u v c d H : ℕ} (up : 0<u) (vp : 0<v) (cp : 0<constant u v c d)
    (S : Finset ℕ) (fits : ∀ n∈S, coordinate n u v c d < 2^H)
    (hits : ∀ n∈S, ∃ z:ℕ, z^2=excess n u c*excess n v d) :
    S.card ≤ 2*H*((constant u v c d)^2).divisors.card := by
  classical
  obtain ⟨t,f,rad,free⟩ := Nat.sq_mul_squarefree (u*v)
  let point (n : ℕ) := (coordinate n u v c d, 2*f*(excess n u c*excess n v d).sqrt)
  have inj : Set.InjOn point S := by
    intro n _ m _ he
    exact coordinate_injective up vp (congrArg Prod.fst he)
  rw [←card_image_of_injOn inj]
  apply WeightedMultiplierPoints.points cp free _
  intro w hw
  obtain ⟨n,hn,rfl⟩ := mem_image.mp hw
  obtain ⟨z,hz⟩ := hits n hn
  have hq := norm hz (show u*v=t*f^2 by simpa only [Nat.mul_comm t] using rad.symm)
  have p : 0<coordinate n u v c d := by
    apply Nat.pos_of_ne_zero
    intro h
    rw [h] at hq
    have hC := pow_pos cp 2
    omega
  exact ⟨p,by dsimp only [point]; rw [←hz,Nat.sqrt_eq']; exact hq, fits n hn⟩

theorem constant_lt {u v c d V D : ℕ} (dp : 0<D) (uV : u<V) (vV : v<V)
    (cD : c<D) (dD : d<D) : constant u v c d < V*D^2 := by
  have U := Nat.mul_lt_mul_of_lt_of_le uV (Nat.pow_le_pow_left dD.le 2) (by positivity : 0<D^2)
  have V' := Nat.mul_lt_mul_of_lt_of_le vV (Nat.pow_le_pow_left cD.le 2) (by positivity : 0<D^2)
  apply (Nat.cast_lt (α:=ℤ)).mp
  simp only [constant,Int.natCast_natAbs,Nat.cast_mul,Nat.cast_pow,abs_lt]
  have U₁ : (u:ℤ)*(d:ℤ)^2 < (V:ℤ)*(D:ℤ)^2 := by exact_mod_cast U
  have V₁ : (v:ℤ)*(c:ℤ)^2 < (V:ℤ)*(D:ℤ)^2 := by exact_mod_cast V'
  have u₀ : (0:ℤ)≤u*(d:ℤ)^2 := by positivity
  have v₀ : (0:ℤ)≤v*(c:ℤ)^2 := by positivity
  constructor <;> omega

/-- On the worked nonsingular match both affine terms are individually nonsquare. -/
theorem example_10961 : correction (10961%24) 4 8 0=5 ∧ correction (10961%24) 1 2 1=26 ∧
    excess 10961 12 5 = 526153 ∧ excess 10961 24 26 = 1052932 ∧
    725^2 < 526153 ∧ 526153 < 726^2 ∧ 1026^2 < 1052932 ∧ 1052932 < 1027^2 ∧
    526153*1052932=744314^2 ∧ Nat.gcd (744314-5*26) 10961=97 ∧
    Nat.gcd (744314+5*26) 10961=113 ∧ 97*113=10961 ∧ Nat.Prime 97 ∧ Nat.Prime 113 := by
  decide +kernel

end PrimeFactors.AffineExcess
