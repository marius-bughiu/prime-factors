import PrimeFactors.RectangularMultiplierCount
import PrimeFactors.RectangularRowCost
import Mathlib.Data.Nat.Size

/-! Coordinate counts for the positive D=1 rectangular rows selected by the
odd and opposite-parity weight tables. Duplicate products in the estimates
only increase the upper bound. -/
namespace PrimeFactors.RectangularWeightCost
open Finset RectangularMultiplierCount RectangularRowCost

noncomputable def coordinates (N B H K R e : ℕ) :=
  ∑ k∈allowed K R e, (positions true N 1 B H k).card

def pairCap (K R e : ℕ) : ℕ :=
  let L := (K.sqrt+1)/2
  let T := (K/4).sqrt
  (4*R*(L+T)+2*e*L^2+e*T*(T+1))/(4*R)

private noncomputable def extra (N B H k : ℕ) := (positions true N 1 B H k).card-1

private theorem spacing {N B H a k : ℕ} (lower : a^2≤k) :
    2*N.sqrt*a*extra N B H k≤H^2 := by
  let s := positions true N 1 B H k
  by_cases h : s.Nonempty
  swap
  · have z := not_nonempty_iff_eq_empty.mp h
    change 2*N.sqrt*a*(s.card-1)≤_
    simp [z]
  let u := s.min' h
  let v := s.max' h
  have uv : u≤v := s.min'_le _ (s.max'_mem h)
  have inside (y : ℕ) (hy : y∈s) : k*N≤y^2 ∧ y^2≤k*N+H^2 := by
    simpa [positions,s] using (mem_filter.mp hy).2
  have low := (inside u (s.min'_mem h)).1
  have high := (inside v (s.max'_mem h)).2
  have us : a*N.sqrt≤u := by
    apply (Nat.pow_le_pow_iff_left (n:=2) (by decide)).mp
    rw [mul_pow]
    exact (Nat.mul_le_mul lower (by simpa [pow_two] using Nat.sqrt_le N)).trans low
  have span := RectangularRootWindows.spacing (d:=1) us uv (by simpa using high.trans (Nat.add_le_add_right low _))
  have incl : s⊆Icc u v := fun y hy => mem_Icc.mpr ⟨s.min'_le _ hy,s.le_max' _ hy⟩
  have cap := card_le_card incl
  rw [Nat.card_Icc] at cap
  have ex : s.card-1≤v-u := by omega
  change 2*N.sqrt*a*(s.card-1)≤_
  calc
    _ ≤ 2*N.sqrt*a*(v-u) := Nat.mul_le_mul_left _ ex
    _ = 1*(2*(a*N.sqrt))*(v-u) := by ring
    _ ≤ _ := span

private theorem dyadic (s : ℕ) : (∑ i∈range (2^s), (1:ℚ)/(i+1:ℕ))≤s+1 := by
  induction s with
  | zero => norm_num
  | succ n ih =>
    rw [pow_succ,Nat.mul_two,sum_range_add]
    have term (i : ℕ) : (1:ℚ)/(2^n+i+1:ℕ)≤1/(2:ℚ)^n := by
      apply one_div_le_one_div_of_le (by positivity)
      exact_mod_cast (show 2^n≤2^n+i+1 by omega)
    have tail : (∑ i∈range (2^n), (1:ℚ)/(2^n+i+1:ℕ)) ≤ 1 := calc
      _ ≤ ∑ _i∈range (2^n), (1:ℚ)/(2:ℚ)^n := sum_le_sum fun i _ => term i
      _ = _ := by simp
    push_cast at ih tail ⊢
    linarith only [ih,tail]

private theorem harmonic {n m : ℕ} (le : m≤n) :
    (∑ i∈range m,(1:ℚ)/(i+1:ℕ))≤(n.size+1:ℕ) := by
  have incl := range_mono (le.trans (Nat.lt_size_self n).le)
  calc
    _ ≤ ∑ i∈range (2^n.size),(1:ℚ)/(i+1:ℕ) := sum_le_sum_of_subset_of_nonneg incl (by intros; positivity)
    _ ≤ _ := by simpa using dyadic n.size

private theorem union_sum (f : ℕ → ℕ) (s t : Finset ℕ) :
    (∑ x∈s∪t,f x)≤(∑ x∈s,f x)+∑ x∈t,f x := by
  have h := sum_union_inter (s₁:=s) (s₂:=t) (f:=f)
  omega

private theorem table_sum (f : ℕ → ℕ) (h : ℕ) (width : ℕ → ℕ) (entry : ℕ → ℕ → ℕ) :
    (∑ x∈(range h).biUnion (fun j => (range (width j)).image (entry j)), f x)
      ≤ ∑ j∈range h, ∑ w∈range (width j), f (entry j w) := by
  induction h with
  | zero => simp
  | succ n ih =>
    rw [range_succ,biUnion_insert,sum_insert (not_mem_range_self)]
    exact (union_sum ..).trans (Nat.add_le_add (sum_image_le_of_nonneg (by intros; omega)) ih)

private theorem fiber {N B H R e a j t : ℕ} (den : j+1≤a)
    (entry : ℕ → ℕ) (low : ∀ w, (t*a)^2≤entry w) :
    (4:ℚ)*R*N.sqrt*t*(∑ w∈range (e*a/(2*R)+1),extra N B H (entry w):ℕ) ≤
      (H:ℚ)^2*((2*R:ℕ)*(1:ℚ)/(j+1:ℕ)+e) := by
  let width := e*a/(2*R)+1
  let c := ∑ w∈range width, extra N B H (entry w)
  have many : 2*N.sqrt*(t*a)*c≤width*H^2 := calc
    _ = ∑ w∈range width, 2*N.sqrt*(t*a)*extra N B H (entry w) := mul_sum ..
    _ ≤ ∑ _w∈range width,H^2 := sum_le_sum fun w _ => spacing (low w)
    _ = _ := by simp
  have wd : 2*R*width≤2*R+e*a := by
    dsimp [width]
    nlinarith only [Nat.div_mul_le_self (e*a) (2*R)]
  have scale : 4*R*N.sqrt*t*c*a≤H^2*(2*R+e*a) := by
    nlinarith only [Nat.mul_le_mul_left (2*R) many,Nat.mul_le_mul_right (H^2) wd]
  have cast : (4:ℚ)*R*N.sqrt*t*c*a≤(H:ℚ)^2*(2*R+e*a) := by exact_mod_cast scale
  have ap : (0:ℚ)<a := by exact_mod_cast (show 0<a by omega)
  have step : (4:ℚ)*R*N.sqrt*t*c≤(H:ℚ)^2*((2:ℚ)*R/a+e) := by
    apply (mul_le_mul_right ap).mp
    calc
      _ ≤ _ := cast
      _ = _ := by field_simp
  have inv := one_div_le_one_div_of_le (show (0:ℚ)<(j+1:ℕ) by positivity) (show ((j+1:ℕ):ℚ)≤a by exact_mod_cast den)
  change (4:ℚ)*R*N.sqrt*t*c≤_
  have frac : (2:ℚ)*R/(a:ℚ) ≤ ((2*R:ℕ):ℚ)*(1:ℚ)/(j+1:ℕ) := by
    push_cast at inv ⊢
    simpa only [div_eq_mul_inv,one_mul,mul_one] using
      mul_le_mul_of_nonneg_left inv (show (0:ℚ)≤2*R by positivity)
  exact step.trans (mul_le_mul_of_nonneg_left (add_le_add_right frac _) (by positivity))

private theorem family {N B H R e m n t : ℕ} (mn : m≤n)
    (a : ℕ → ℕ) (den : ∀ j, j+1≤a j) (entry : ℕ → ℕ → ℕ)
    (low : ∀ j w, (t*a j)^2≤entry j w) :
    (4:ℚ)*R*N.sqrt*t*(∑ j∈range m, ∑ w∈range (e*a j/(2*R)+1),extra N B H (entry j w):ℕ) ≤
      (H:ℚ)^2*(2*R*(n.size+1:ℕ)+e*m) := by
  let E (j : ℕ) := ∑ w∈range (e*a j/(2*R)+1),extra N B H (entry j w)
  let f (j : ℕ) : ℚ := 1/(j+1:ℕ)
  have cap := harmonic mn
  have part : (∑ j∈range m, f j)≤(n.size+1:ℕ) := cap
  calc
    _ = ∑ j∈range m, (4:ℚ)*R*N.sqrt*t*(E j) := by
      rw [←mul_sum]; congr 1; exact Nat.cast_sum ..
    _ ≤ ∑ j∈range m, ((H:ℚ)^2*(2*R)*f j + H^2*e) := by
      apply sum_le_sum
      intro j _
      apply (fiber (N:=N) (B:=B) (H:=H) (R:=R) (e:=e) (den j) (entry j) (low j)).trans_eq
      dsimp [f]; push_cast; ring
    _ = (H:ℚ)^2*(2*R)*(∑ j∈range m, f j)+(H:ℚ)^2*e*m := by
      rw [sum_add_distrib,←mul_sum]; simp; ring
    _ ≤ _ := by
      push_cast at part ⊢
      nlinarith only [mul_le_mul_of_nonneg_left part (show (0:ℚ)≤(H:ℚ)^2*(2*R) by positivity)]

/-- Public upper bound on all square-test coordinates in the eligible rows.
The first term counts distinct rows. The second term counts their extra
positions, permitting duplicate weight products in this estimate. -/
theorem bound (N B H K R e : ℕ) (np : 0<N) (rp : 0<R) :
    let L := (K.sqrt+1)/2
    let T := (K/4).sqrt
    let g := K.sqrt.size+1
    coordinates N B H K R e ≤ pairCap K R e+
      H^2*(6*R*g+2*e*L+e*T)/(8*R*N.sqrt) := by
  let L := (K.sqrt+1)/2
  let T := (K/4).sqrt
  let g := K.sqrt.size+1
  let ao (j : ℕ) := 2*j+1
  let ae (j : ℕ) := j+1
  let ko (j w : ℕ) := (2*j+1)*(2*j+1+2*w)
  let ke (j w : ℕ) := 4*(j+1)*(j+2+2*w)
  let O := ∑ j∈range L, ∑ w∈range (oddWidth R e j), extra N B H (ko j w)
  let E := ∑ j∈range T, ∑ w∈range (evenWidth R e j), extra N B H (ke j w)
  let s := allowed K R e
  let X := ∑ k∈s,extra N B H k
  have pairs : s.card≤pairCap K R e :=
    (Nat.le_div_iff_mul_le (Nat.mul_pos (by decide) rp)).mpr (by
      simpa [s,Nat.mul_comm s.card (4*R)] using RectangularMultiplierCount.bound K R e)
  have size : coordinates N B H K R e≤s.card+X := calc
    _ ≤ ∑ k∈s,(1+extra N B H k) := by
      apply sum_le_sum; intro k _; dsimp [extra]; omega
    _ = _ := by simp [X,sum_add_distrib]
  have cover : X≤O+E := by
    change (∑ k∈_∪_,extra N B H k)≤_
    exact (union_sum ..).trans (Nat.add_le_add (table_sum _ L _ ko) (table_sum _ T _ ke))
  have odd := family (N:=N) (B:=B) (H:=H) (R:=R) (e:=e) (n:=K.sqrt) (m:=L) (t:=1)
    (by dsimp [L]; omega) ao (by intro j; dsimp [ao]; omega) ko
    (by intro j w; dsimp [ao,ko]; nlinarith)
  have even := family (N:=N) (B:=B) (H:=H) (R:=R) (e:=e) (n:=K.sqrt) (m:=T) (t:=2)
    (Nat.sqrt_le_sqrt (Nat.div_le_self ..)) ae (fun _ => le_rfl) ke
    (by intro j w; dsimp [ae,ke]; nlinarith)
  change (4:ℚ)*R*N.sqrt*1*O≤(H:ℚ)^2*(2*R*g+e*L) at odd
  change (4:ℚ)*R*N.sqrt*2*E≤(H:ℚ)^2*(2*R*g+e*T) at even
  have ov : (X:ℚ)≤(O:ℚ)+E := by exact_mod_cast cover
  have scaled : (8:ℚ)*R*N.sqrt*X ≤ (H:ℚ)^2*(6*R*g+2*e*L+e*T) := by
    nlinarith only [odd,even,mul_le_mul_of_nonneg_left ov (show (0:ℚ)≤8*R*N.sqrt by positivity)]
  have intBound : X*(8*R*N.sqrt)≤H^2*(6*R*g+2*e*L+e*T) := by
    rw [Nat.mul_comm X]; exact_mod_cast scaled
  exact size.trans (Nat.add_le_add pairs ((Nat.le_div_iff_mul_le (Nat.mul_pos
    (Nat.mul_pos (by decide) rp) (Nat.sqrt_pos.mpr np))).mpr intBound))

end PrimeFactors.RectangularWeightCost
