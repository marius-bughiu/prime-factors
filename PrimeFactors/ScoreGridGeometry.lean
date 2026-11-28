import PrimeFactors.MeanSumOrderGeometry

/-! Bounds for the opposing residue group's prefix length on a normalized
factor-product rectangle. A single group of four prime residue pairs is the
unit population in the aggregate weights. -/
namespace PrimeFactors.ScoreGridGeometry

open Real Finset

abbrev M : ℕ := 256
abbrev K : ℕ := 16777216
abbrev A : ℕ := 4294967296
abbrev Q : ℕ := 18446744073709551616

noncomputable def distance (n gap r : ℝ) := sqrt (4*n+(r*gap)^2)-2*sqrt n
noncomputable def cap (n : ℝ) := (1-sqrt n)^2

theorem distance_rationalized {n : ℝ} (hn : 0 < n) (gap r : ℝ) :
    distance n gap r = (r*gap)^2/(sqrt (4*n+(r*gap)^2)+2*sqrt n) := by
  have base := sq_sqrt hn.le
  have h : 0 ≤ 4*n+(r*gap)^2 := by positivity
  apply (eq_div_iff (by positivity)).mpr
  unfold distance
  nlinarith only [sq_sqrt h, base]

/-- Increasing the gap and reducing the product only increases the distance. -/
theorem distance_mono {n₀ n₁ g₀ g₁ r : ℝ} (hp : 0 < n₀) (hn : n₀ ≤ n₁)
    (hg : 0 ≤ g₀) (gap : g₀ ≤ g₁) (hr : 0 ≤ r) :
    distance n₁ g₀ r ≤ distance n₀ g₁ r := by
  have hn' := hp.trans_le hn
  calc
    distance n₁ g₀ r ≤ distance n₀ g₀ r := by
      rw [distance_rationalized hn', distance_rationalized hp]
      apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
      exact add_le_add (sqrt_le_sqrt (by linarith only [hn]))
        (mul_le_mul_of_nonneg_left (sqrt_le_sqrt hn) (by norm_num))
    _ ≤ _ := by
      apply sub_le_sub_right (sqrt_le_sqrt _) _
      exact add_le_add_left ((sq_le_sq₀ (mul_nonneg hr hg)
        (mul_nonneg hr (hg.trans gap))).mpr (mul_le_mul_of_nonneg_left gap hr)) _

theorem cap_antitone {a b : ℝ} (hb : b ≤ 1) (ab : a ≤ b) : cap b ≤ cap a := by
  have top : sqrt b ≤ 1 := (by simpa using sqrt_le_sqrt hb)
  exact (sq_le_sq₀ (by linarith) (by linarith [sqrt_le_sqrt ab])).mpr
    (sub_le_sub_left (sqrt_le_sqrt ab) _)

private def newton (n : ℕ) : ℕ → ℕ
  | 0 => if n < 2^64 then 2^32 else if n < 2^68 then 2^34 else 2^36
  | k+1 => let x := newton n k; (x+n/x)/2

private def floorRoot (n : ℕ) : ℕ :=
  let r := newton n 7
  if r^2 ≤ n ∧ n < (r+1)^2 then r else n.sqrt

private theorem floorRoot_eq (n : ℕ) : floorRoot n = n.sqrt := by
  dsimp only [floorRoot]
  split_ifs with h
  · exact le_antisymm (Nat.le_sqrt'.mpr h.1) (Nat.le_of_lt_succ (Nat.sqrt_lt'.mpr h.2))
  · rfl

private def ceilRoot (n : ℕ) :=
  let r := floorRoot n
  if r*r = n then r else r+1

/-- The high and low rational bounds in a common denominator A for
a fixed scaled product N, gap g, and multiplicity ratio c/d. -/
def axisLength (up : Bool) (N g c d : ℕ) : ℕ :=
  let rad := K^2*(4*d^2*N + c^2*g^2)
  let root := if up then ceilRoot rad else floorRoot rad
  let base := if up then floorRoot (K^2*N) else ceilRoot (K^2*N)
  (root - 2*d*base + (if up then d-1 else 0))/d

def edgeLength (up : Bool) (N : ℕ) : ℕ :=
  let base := if up then floorRoot (K^2*N) else ceilRoot (K^2*N)
  (A-base)^2

def distHi (i j c d : ℕ) := A * axisLength true (i*j) (j+1-i) c d

def capLo (i j : ℕ) := edgeLength false ((i+1)*(j+1))
def capHi (i j : ℕ) := edgeLength true (i*j)

def globalGain (i j : ℕ) := 2*(capLo i j - distHi i j 5 2)
def globalLoss (i j : ℕ) := 5*distHi i j 2 5
def squareGlobal (i j : ℕ) := 7*distHi i j 1 1 + 2*capHi i j
def otherCost (i j : ℕ) := 20*distHi i j 1 1

theorem scale_eq : Q = 65536 * MeanSumOrderGeometry.Q := by decide

private theorem real_roots (n : ℕ) :
    (floorRoot n : ℝ) ≤ sqrt n ∧ sqrt n ≤ (ceilRoot n : ℝ) := by
  have lo : (floorRoot n : ℝ)^2 ≤ n := by
    exact_mod_cast (floorRoot_eq n ▸ Nat.sqrt_le' n : (floorRoot n)^2 ≤ n)
  have next : (n:ℝ) ≤ ((floorRoot n : ℝ)+1)^2 := by
    rw [floorRoot_eq]; exact_mod_cast (Nat.lt_succ_sqrt' n).le
  refine ⟨(sq_le_sq₀ (by positivity) (sqrt_nonneg _)).mp (by rwa [sq_sqrt (Nat.cast_nonneg n)]),?_⟩
  dsimp only [ceilRoot]
  split_ifs with h
  · have eq : (floorRoot n:ℝ)^2 = n := by exact_mod_cast (by simpa [pow_two] using h : (floorRoot n)^2=n)
    exact (sq_le_sq₀ (sqrt_nonneg _) (by positivity)).mp (by rw [sq_sqrt (Nat.cast_nonneg n),eq])
  · rw [Nat.cast_add,Nat.cast_one]
    exact (sq_le_sq₀ (sqrt_nonneg _) (by positivity)).mp (by rwa [sq_sqrt (Nat.cast_nonneg n)])

private theorem sqrt_scale (n : ℕ) :
    (A:ℝ)*sqrt ((n:ℝ)/M^2) = sqrt (K^2*n:ℕ) := by
  apply (sq_eq_sq₀ (by positivity) (by positivity)).mp
  rw [mul_pow,sq_sqrt (by positivity),sq_sqrt (Nat.cast_nonneg _)]
  push_cast
  norm_num [M,K,A]
  ring

private theorem rad_scale (n g c d : ℕ) (hd : 0 < d) :
    (d:ℝ)*A*sqrt (4*((n:ℝ)/M^2)+((c:ℝ)/d*((g:ℝ)/M))^2) =
      sqrt (K^2*(4*d^2*n + c^2*g^2):ℕ) := by
  apply (sq_eq_sq₀ (by positivity) (by positivity)).mp
  rw [mul_pow,sq_sqrt (by positivity),sq_sqrt (Nat.cast_nonneg _)]
  push_cast
  have nz : (d:ℝ) ≠ 0 := by positivity
  norm_num [K,M,A]
  field_simp [nz]
  ring

private theorem axis_upper (n g c d : ℕ) (hd : 0 < d) :
    (A:ℝ)*distance ((n:ℝ)/M^2) ((g:ℝ)/M) ((c:ℝ)/d) ≤ (axisLength true n g c d:ℝ) := by
  let rad := K^2*(4*d^2*n+c^2*g^2)
  let u := ceilRoot rad
  let b := floorRoot (K^2*n)
  let z := u - 2*d*b + (d-1)
  have count := Nat.mod_add_div z d
  have rem := Nat.mod_lt z hd
  have round : u ≤ d*(z/d)+2*d*b := by dsimp only [z] at *; omega
  have round' : (u:ℝ) ≤ (d:ℝ)*(axisLength true n g c d:ℝ) + 2*d*(b:ℝ) := by exact_mod_cast round
  have high := (real_roots rad).2
  have low := (real_roots (K^2*n)).1
  change sqrt (K^2*(4*d^2*n+c^2*g^2):ℕ) ≤ (u:ℝ) at high
  change (b:ℝ) ≤ _ at low
  rw [←rad_scale n g c d hd] at high
  rw [←sqrt_scale n] at low
  apply (mul_le_mul_iff_of_pos_left (by exact_mod_cast hd : 0 < (d:ℝ))).mp
  unfold distance
  nlinarith only [high,round',mul_le_mul_of_nonneg_left low (Nat.cast_nonneg d : (0:ℝ) ≤ d)]

private theorem cap_lower (n : ℕ) (h : (n:ℝ)/M^2 ≤ 1) :
    (edgeLength false n:ℝ) ≤ (Q:ℝ)*cap ((n:ℝ)/M^2) := by
  let c := ceilRoot (K^2*n)
  have root := (real_roots (K^2*n)).2
  rw [←sqrt_scale] at root
  change _ ≤ (c:ℝ) at root
  have pos : 0 ≤ 1-sqrt ((n:ℝ)/M^2) := sub_nonneg.mpr (by simpa using sqrt_le_sqrt h)
  have le : ((A-c:ℕ):ℝ) ≤ (A:ℝ)*(1-sqrt ((n:ℝ)/M^2)) := by
    by_cases hc : c ≤ A
    · rw [Nat.cast_sub hc]; linarith only [root]
    · rw [Nat.sub_eq_zero_of_le (le_of_not_ge hc),Nat.cast_zero]
      positivity
  have sq := (sq_le_sq₀ (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) pos)).mpr le
  change (((A-c)^2:ℕ):ℝ) ≤ (Q:ℝ)*_
  rw [Nat.cast_pow]
  convert sq using 1
  unfold cap
  norm_num [A,Q]
  ring

/-- For each clipped rectangle the ordinary target's saved tail and favored
target's paid prefix have these scaled bounds. Both admit either box edge. -/
theorem global_corners {i j : ℕ} (im : i ∈ MeanSumOrderGeometry.indices)
    (jm : j ∈ MeanSumOrderGeometry.indices) {x y : ℝ}
    (xl : i ≤ (M:ℝ)*x) (xu : (M:ℝ)*x ≤ i+1)
    (yl : j ≤ (M:ℝ)*y) (yu : (M:ℝ)*y ≤ j+1) (sorted : x ≤ y) :
    (globalGain i j:ℝ) ≤ 2*Q*max 0 (cap (x*y)-distance (x*y) (y-x) (5/2)) ∧
    5*Q*distance (x*y) (y-x) (2/5) ≤ (globalLoss i j:ℝ) := by
  obtain ⟨ilo,ihi⟩ := mem_Ico.mp im
  obtain ⟨jlo,jhi⟩ := mem_Ico.mp jm
  change i < M at ihi
  change j < M at jhi
  have xp : 0 ≤ x := by change (i:ℝ) ≤ 256*x at xl; linarith only [xl,Nat.cast_nonneg (α:=ℝ) i]
  have yp := xp.trans sorted
  have ij : i ≤ j+1 := by
    exact_mod_cast xl.trans ((mul_le_mul_of_nonneg_left sorted (Nat.cast_nonneg _)).trans yu)
  let l := i*j
  let h := (i+1)*(j+1)
  let g := j+1-i
  have lp : (0:ℝ) < l/M^2 := by
    have : 0 < l := Nat.mul_pos (by omega) (by omega)
    positivity
  have low : (l:ℝ)/M^2 ≤ x*y := by
    apply (div_le_iff₀ (by positivity)).mpr
    have v := mul_le_mul xl yl (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) xp)
    dsimp [l]
    push_cast
    norm_num only [M,Nat.cast_ofNat] at v
    nlinarith only [v]
  have high : x*y ≤ (h:ℝ)/M^2 := by
    apply (le_div_iff₀ (by positivity)).mpr
    have v := mul_le_mul xu yu (mul_nonneg (Nat.cast_nonneg _) yp) (by positivity)
    dsimp [h]
    push_cast
    norm_num only [M,Nat.cast_ofNat] at v
    nlinarith only [v]
  have top : (h:ℝ)/M^2 ≤ 1 := by
    have ub : h ≤ M^2 := by exact Nat.mul_le_mul (by omega : i+1≤M) (by omega : j+1≤M)
    apply (div_le_iff₀ (by positivity)).mpr
    simpa only [one_mul] using (by exact_mod_cast ub : (h:ℝ) ≤ (M:ℝ)^2)
  have gap : y-x ≤ (g:ℝ)/M := by
    apply (le_div_iff₀ (by positivity)).mpr
    change _ ≤ ((j+1-i:ℕ):ℝ)
    rw [Nat.cast_sub ij,Nat.cast_add,Nat.cast_one]
    change (i:ℝ) ≤ 256*x at xl
    change 256*y ≤ (j:ℝ)+1 at yu
    change (y-x)*256 ≤ _
    linarith only [xl,yu]
  have dist (c d : ℕ) (hd : 0 < d) :
      (Q:ℝ)*distance (x*y) (y-x) ((c:ℝ)/d) ≤ (distHi i j c d:ℝ) := by
    have mono := distance_mono lp low (sub_nonneg.mpr sorted) gap (by positivity : 0 ≤ (c:ℝ)/d)
    have upper := axis_upper l g c d hd
    have unit : (Q:ℝ)=(A:ℝ)*A := by norm_num [A,Q]
    rw [unit,mul_assoc]
    change _ ≤ ((A*axisLength true l g c d:ℕ):ℝ)
    rw [Nat.cast_mul]
    exact mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_left mono (Nat.cast_nonneg _)).trans upper)
      (Nat.cast_nonneg _)
  have ec : (capLo i j:ℝ) ≤ (Q:ℝ)*cap (x*y) :=
    (cap_lower h top).trans (mul_le_mul_of_nonneg_left (cap_antitone top high) (Nat.cast_nonneg _))
  have big := dist 5 2 (by decide)
  have small := dist 2 5 (by decide)
  norm_num only [Nat.cast_ofNat] at big small
  constructor
  · by_cases enough : distHi i j 5 2 ≤ capLo i j
    · simp only [globalGain,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_sub enough]
      have upper := mul_le_mul_of_nonneg_left (le_max_right 0 (cap (x*y)-distance (x*y) (y-x) (5/2)))
        (Nat.cast_nonneg (α:=ℝ) Q)
      norm_num only [Q,Nat.cast_ofNat] at ec upper
      linarith only [ec,big,upper]
    · simp only [globalGain,Nat.sub_eq_zero_of_le (le_of_not_ge enough),Nat.mul_zero,Nat.cast_zero]
      positivity
  · simp only [globalLoss,Nat.cast_mul,Nat.cast_ofNat]
    linarith only [small]

set_option maxRecDepth 16384 in
theorem grid_totals :
    MeanSumOrderGeometry.sumFull globalGain = 1852539810826416807574 ∧
    MeanSumOrderGeometry.sumPossible globalLoss = 1102550953394375229440 ∧
    MeanSumOrderGeometry.sumPossible squareGlobal = 17683550253563239285648 ∧
    MeanSumOrderGeometry.sumPossible otherCost = 27296829377615180595200 := by
  decide +kernel

end PrimeFactors.ScoreGridGeometry
