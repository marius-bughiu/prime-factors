import PrimeFactors.WeightSlopeCover
import PrimeFactors.ModularHyperbola
import PrimeFactors.ConditionalStride
import Mathlib.Data.Nat.Sqrt
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.Tactic.LinearCombination

namespace PrimeFactors.AffineWindowOccupancy

/-- Occupancy of a translated rectangle by the integer graph of an affine congruence. -/
def Occupied (a c R X Y H V : ℤ) : Prop :=
  ∃ x y : ℤ, X ≤ x ∧ x < X+H ∧ |y-Y| ≤ V ∧ y ≡ a*x+c [ZMOD R]

/-- In a factor lane the affine occupancy test is exactly the product
congruence modulo R², including every signed high-digit translation. -/
theorem factor_graph {N R u w d i a c : ℤ} (hr : R≠0) (carry : N=u*w+R*d)
    (inverse : u*i ≡ 1 [ZMOD R]) (slope : a ≡ -i*w [ZMOD R])
    (offset : c ≡ i*d [ZMOD R]) (v z : ℤ) :
    (u+R*v)*(w+R*z) ≡ N [ZMOD R^2] ↔ z ≡ a*v+c [ZMOD R] := by
  rw [hyperbola_affine_partner_iff hr carry inverse]
  have eq := (slope.mul (Int.ModEq.refl v)).add offset
  rw [show -i*w*v+i*d = i*(d-w*v) by ring] at eq
  exact ⟨fun h => h.trans eq.symm, fun h => h.trans eq⟩

/-- A reduced rational approximant whose denominator is sufficiently large
constructs a point regardless of the intercept and rectangle translation. -/
theorem cover_from_approx {a R H D p q : ℤ} (hr : 0<R) (hq : 0<q) (hqH : q≤H)
    (net : R≤q*H) (cop : IsCoprime p q) (close : |a*q-R*p|≤D)
    (c X Y : ℤ) : Occupied a c R X Y H (H+D) := by
  obtain ⟨r,s,bez⟩ := cop
  let base := a*X+c
  let T := (Y-base)*q
  let t := T/R
  let v := (r*t)%q
  let k := (r*t)/q
  let y := base+a*v+R*(s*t+p*k)
  have hv : v+q*k = r*t := Int.emod_add_ediv _ _
  have v0 : 0≤v := Int.emod_nonneg _ hq.ne'
  have vq : v<q := Int.emod_lt_of_pos _ hq
  have ht : T%R + R*t = T := Int.emod_add_ediv _ _
  have rt : |T%R| ≤ R := by
    rw [abs_of_nonneg (Int.emod_nonneg _ hr.ne')]
    exact (Int.emod_lt_of_pos _ hr).le
  have pv : p*v = t-q*(s*t+p*k) := by
    linear_combination p*hv + t*bez
  have id : (y-Y)*q = (a*q-R*p)*v-T%R := by
    dsimp only [y]
    change T%R+R*t=(Y-base)*q at ht
    linear_combination R*pv + ht
  refine ⟨X+v,y,by omega,by omega,?_,?_⟩
  · have bound : |y-Y| * q ≤ (H+D)*q := calc
      _ = |(y-Y)*q| := by rw [abs_mul,abs_of_pos hq]
      _ ≤ |a*q-R*p| * |v| + |T%R| := by rw [id,← abs_mul]; exact abs_sub ..
      _ ≤ D*q+R := by
        rw [abs_of_nonneg v0]
        exact add_le_add (mul_le_mul close vq.le v0 ((abs_nonneg _).trans close)) rt
      _ ≤ _ := by linarith only [net]
    exact le_of_mul_le_mul_right bound hq
  · apply Int.modEq_iff_dvd.mpr
    refine ⟨-(s*t+p*k),?_⟩
    dsimp only [y,base]
    ring

/-- Dirichlet approximation with a reduced numerator and denominator. -/
theorem reduced_approx (a : ℤ) {R H D : ℕ} (hH : 0<H) (hD : 0<D) (split : R=H*D) :
    ∃ (p : ℤ) (q : ℕ), 0<q ∧ q≤H ∧ IsCoprime p (q:ℤ) ∧ |a*q-(R:ℤ)*p| ≤ D := by
  have hr : (0:ℝ)<R := by rw [split]; positivity
  obtain ⟨b,he,bH⟩ := Real.exists_rat_abs_sub_le_and_den_le ((a:ℝ)/R) hH
  have bd : (0:ℝ)<b.den := by exact_mod_cast b.pos
  have bc : (b:ℝ)*b.den = b.num := by rw [Rat.cast_def, div_mul_cancel₀ _ bd.ne']
  have den : (0:ℝ)<((H:ℝ)+1)*b.den := by positivity
  have h := (le_div_iff₀ den).mp he
  have identity : (a:ℝ)*b.den - R*b.num = ((a:ℝ)/R-b)*(R*b.den) := by
    rw [← bc]
    field_simp
    ring
  have scaled : |(a:ℝ)*b.den - R*b.num| * ((H:ℝ)+1) ≤ R := by
    rw [identity, abs_mul, abs_of_pos (mul_pos hr bd)]
    convert mul_le_mul_of_nonneg_right h hr.le using 1 <;> ring
  have limit : |(a:ℝ)*b.den - R*b.num| ≤ D := by
    have sr : (R:ℝ) = H*D := by exact_mod_cast split
    have hz : (0:ℝ)<H := by exact_mod_cast hH
    by_contra! bad
    nlinarith only [scaled, sr, abs_nonneg ((a:ℝ)*b.den-R*b.num), mul_pos (sub_pos.mpr bad) hz]
  refine ⟨b.num,b.den,b.pos,bH,?_,by exact_mod_cast limit⟩
  apply Int.isCoprime_iff_gcd_eq_one.mpr
  simpa [Int.gcd] using b.reduced

/-- Any unit slope having some empty rectangle of these dimensions
has a short nonzero congruence vector. The exceptional set is independent
of the translated endpoints and the intercept. -/
theorem empty_slopes {R H D : ℕ} (hH : 0<H) (hD : 0<D) (small : D<R)
    (split : R=H*D) (S : Finset ℕ) (missing : ∀ a ∈ S, a<R ∧ R.Coprime a ∧
      ∃ c X Y : ℤ, ¬ Occupied a c R X Y H (H+D)) : S.card ≤ 2*D^2 := by
  apply WeightSlopeCover.unit_slopes small
  intro a ha
  obtain ⟨hR,unit,c,X,Y,empty⟩ := missing a ha
  obtain ⟨p,q,hq,hqH,cop,close⟩ := reduced_approx (a:ℤ) hH hD split
  have qD : q<D := by
    by_contra! bad
    apply empty
    apply cover_from_approx (by exact_mod_cast (hD.trans small)) (by exact_mod_cast hq)
      (by exact_mod_cast hqH) _ cop close
    exact_mod_cast (show R≤q*H by simpa [split,mul_comm H] using Nat.mul_le_mul_right H bad)
  refine ⟨hR,unit,(q:ℤ),a*(q:ℤ)-(R:ℤ)*p,Or.inl (by exact_mod_cast hq.ne'),
    by simpa using qD.le,?_,?_⟩
  · exact_mod_cast (show ((a*(q:ℤ)-(R:ℤ)*p).natAbs : ℤ) ≤ D by simpa using close)
  · apply Int.modEq_iff_dvd.mpr
    exact ⟨-p,by ring⟩

set_option exponentiation.threshold 4096 in
theorem empty_slopes_2048 (S : Finset ℕ) (missing : ∀ a ∈ S, a<2^614 ∧
    (2^614).Coprime a ∧ ∃ c X Y : ℤ,
      ¬ Occupied a c (2^614) X Y (2^405) (2^405+2^209)) : S.card ≤ 2^419 := by
  have h := empty_slopes (H:=2^405) (D:=2^209) (R:=2^614) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) S
  convert h (by simpa only [Nat.cast_ofNat, Nat.cast_pow] using missing) using 1

/-- Each slope from an odd input has at most four oriented factor residues
on a dyadic modulus, even when its fiber is restricted to an arbitrary subset. -/
theorem dyadic_fibers (e : ℕ) (c : (ZMod (2^e))ˣ) (S : Finset ℕ)
    (T : Finset (ZMod (2^e))ˣ)
    (into : ∀ u ∈ T, (c*u⁻¹^2 : (ZMod (2^e))ˣ).val.val ∈ S) :
    T.card ≤ 4*S.card := by
  classical
  let f (u : (ZMod (2^e))ˣ) := (c*u⁻¹^2 : (ZMod (2^e))ˣ).val.val
  let fiber (a : ℕ) := T.filter (fun u => f u = a)
  have bound (a : ℕ) : (fiber a).card ≤ 4 := by
    by_cases h : (fiber a).Nonempty
    · obtain ⟨v,hv⟩ := h
      have root {u} (hu : u ∈ fiber a) : u⁻¹^2 = v⁻¹^2 := by
        apply mul_left_cancel (a:=c)
        apply Units.ext
        apply ZMod.val_injective
        exact (Finset.mem_filter.mp hu).2.trans (Finset.mem_filter.mp hv).2.symm
      apply le_trans _ (strideUnitRoots_two_pow_le_four e (v⁻¹^2))
      apply Finset.card_le_card_of_injOn Inv.inv
      · intro u hu
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, root hu⟩
      · intro u _ z _ eq
        exact inv_injective eq
    · simp [Finset.not_nonempty_iff_eq_empty.mp h]
  calc T.card ≤ (S.biUnion fiber).card := Finset.card_le_card (fun u hu =>
         Finset.mem_biUnion.mpr ⟨f u, into u hu, Finset.mem_filter.mpr ⟨hu,rfl⟩⟩)
       _ ≤ S.card*4 := Finset.card_biUnion_le_card_mul _ _ _ (fun a _ => bound a)
       _ = _ := Nat.mul_comm ..

/-- The balanced search intervals contain long consecutive runs in every
residue class. This statement includes the original integer rounding. -/
theorem balanced_windows {N : ℕ} (size : 2^2047 ≤ N) :
    ((N-1)/2).sqrt+1 + (2^614)*2^405 ≤ N.sqrt ∧
    (N-1).sqrt+1 + (2^614)*(2*(2^405+2^209)+1) ≤ (2*N).sqrt := by
  let t : ℕ := 2^1021
  have large : 4*t ≤ (N/2).sqrt := by
    apply Nat.le_sqrt.mpr
    apply (Nat.le_div_iff_mul_le (by decide : 0<2)).mpr
    exact (by decide +kernel : (4*t)*(4*t)*2 ≤ (2:ℕ)^2047).trans size
  have band (a : ℕ) (ha : 4*t ≤ a) : (a+t)*(a+t) ≤ 2*(a*a) := by
    have x := Nat.mul_le_mul_left a ha
    have y := Nat.mul_le_mul_left t (show t ≤ a by omega)
    nlinarith only [x,y]
  have rootMono : (N/2).sqrt ≤ N.sqrt := Nat.sqrt_le_sqrt (Nat.div_le_self ..)
  have first : (N/2).sqrt+t ≤ N.sqrt := Nat.le_sqrt.mpr
    ((band _ large).trans ((Nat.mul_le_mul_left 2 (Nat.sqrt_le _)).trans (Nat.mul_div_le N 2)))
  have second : N.sqrt+t ≤ (2*N).sqrt := Nat.le_sqrt.mpr
    ((band _ (large.trans rootMono)).trans (Nat.mul_le_mul_left 2 (Nat.sqrt_le _)))
  have left := Nat.sqrt_le_sqrt (Nat.div_le_div_right (Nat.sub_le N 1) : (N-1)/2≤N/2)
  have right := Nat.sqrt_le_sqrt (Nat.sub_le N 1)
  have xsize : 1+(2:ℕ)^614*2^405 ≤ t := by decide +kernel
  have ysize : 1+(2:ℕ)^614*(2*(2^405+2^209)+1) ≤ t := by decide +kernel
  omega

/-- A long physical interval supplies a consecutive block of high digits
for any chosen low remainder. -/
theorem digit_interval {lo hi u R count : ℤ} (hr : 0<R) (wide : lo+R*count≤hi) :
    ∃ X : ℤ, ∀ v, X≤v → v<X+count → lo≤u+R*v ∧ u+R*v≤hi := by
  let X := (lo-u)/R+1
  have hd := Int.emod_add_ediv (lo-u) R
  have hl := Int.emod_nonneg (lo-u) hr.ne'
  have hu := Int.emod_lt_of_pos (lo-u) hr
  refine ⟨X,fun v low high => ?_⟩
  have l := mul_le_mul_of_nonneg_left low hr.le
  have hi' := mul_le_mul_of_nonneg_left (show v ≤ X+count-1 by omega) hr.le
  dsimp [X] at l hi'
  constructor <;> linarith

/-- The same ordered factor rectangle used by the affine floor-sum search. -/
def InFactorWindow (N R : ℕ) (a c u w : ℤ) : Prop :=
  ∃ v z : ℤ, ((((N-1)/2).sqrt+1:ℕ):ℤ) ≤ u+R*v ∧ u+R*v ≤ N.sqrt ∧
    (((N-1).sqrt+1:ℕ):ℤ) ≤ w+R*z ∧ w+R*z ≤ (2*N).sqrt ∧ z ≡ a*v+c [ZMOD R]

set_option maxRecDepth 8192 in
set_option exponentiation.threshold 4096 in
theorem missing_rectangle_2048 {N : ℕ} (size : 2^2047 ≤ N) (a c u w : ℤ)
    (missing : ¬ InFactorWindow N (2^614) a c u w) :
    ∃ X Y : ℤ, ¬ Occupied a c (2^614) X Y (2^405) (2^405+2^209) := by
  let V := (2:ℤ)^405+2^209
  obtain ⟨xsize,ysize⟩ := balanced_windows size
  have xs : ((((N-1)/2).sqrt+1:ℕ):ℤ) + (2:ℤ)^614*2^405 ≤ N.sqrt := by exact_mod_cast xsize
  have ys : (((N-1).sqrt+1:ℕ):ℤ) + (2:ℤ)^614*(2*V+1) ≤ (2*N).sqrt := by
    dsimp [V]
    exact_mod_cast ysize
  obtain ⟨X,ib⟩ := digit_interval (u:=u) (by positivity) xs
  obtain ⟨Y,jb⟩ := digit_interval (u:=w) (by positivity) ys
  refine ⟨X,Y+V,?_⟩
  rintro ⟨v,z,lo,hi,center,rel⟩
  change |z-(Y+V)| ≤ V at center
  rw [abs_le] at center
  obtain ⟨xl,xh⟩ := ib v lo hi
  obtain ⟨yl,yh⟩ := jb z (by omega) (by omega)
  exact missing ⟨v,z,xl,xh,yl,yh,by simpa only [Nat.cast_pow,Nat.cast_ofNat] using rel⟩

set_option maxRecDepth 8192 in
set_option exponentiation.threshold 4096 in
/-- On the balanced 2048-bit window this many oriented unit residues, at most,
can ever return a zero floor-sum count. Allow the companion digit and intercept
to be chosen independently and adversarially for each remainder. -/
theorem excluded_remainders_2048 {N : ℕ} (size : 2^2047 ≤ N)
    (C : (ZMod (2^614))ˣ) (T : Finset (ZMod (2^614))ˣ)
    (empty : ∀ u ∈ T, ∃ c w : ℤ, ¬ InFactorWindow N (2^614)
      (C*u⁻¹^2 : (ZMod (2^614))ˣ).val.val c u.val.val w) : T.card ≤ 2^421 := by
  classical
  let slope (u : (ZMod (2^614))ˣ) := (C*u⁻¹^2 : (ZMod (2^614))ˣ).val.val
  let S := T.image slope
  have cap : S.card ≤ 2^419 := by
    apply empty_slopes_2048
    intro a ha
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨c,w,missing⟩ := empty u hu
    obtain ⟨X,Y,none⟩ := missing_rectangle_2048 size _ _ _ _ missing
    exact ⟨ZMod.val_lt _,(ZMod.val_coe_unit_coprime _).symm,c,X,Y,none⟩
  have multiple := dyadic_fibers 614 C S T (fun u hu => Finset.mem_image_of_mem _ hu)
  exact multiple.trans ((Nat.mul_le_mul_left 4 cap).trans (by decide +kernel))

end PrimeFactors.AffineWindowOccupancy
