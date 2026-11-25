import PrimeFactors.MixedHeights
import PrimeFactors.BinomialAnalyticWindow
import Mathlib.Data.Real.Pi.Bounds

namespace PrimeFactors.BoundaryWindowSelection

/- The elementary trigonometric estimates used in the earlier quadratic schedule. -/
open private PrimeFactors.find_phase_band PrimeFactors.sin_band PrimeFactors.sin_separated
  PrimeFactors.cos_gap from PrimeFactors.MixedHeights

/-- Read all dyadic heights, then choose the first whose recorded cosine falls below 25/32.
K+1 is a sentinel when none of the K+1 readings crosses the threshold. -/
noncomputable def reference (K : ℕ) (y : ℕ → ℝ) : ℕ := by
  classical
  exact if hit : ∃ i, i≤K ∧ y (2^i)<25/32 then Nat.find hit else K+1

def DyadFits (K : ℕ) (y : ℕ → ℝ) (d : ℝ) : Prop :=
  ∀ i≤K, |Real.cos ((2:ℝ)^i*d)-y (2^i)|≤1/16

def ShiftFits (K j : ℕ) (y : ℕ → ℝ) (d : ℝ) : Prop :=
  ∀ i≤K, |Real.cos (((2:ℝ)^i+2^j)*d)-y (2^i+2^j)|≤1/16

/-- Both batches contain only integer heights. Without a crossing the second batch is empty. -/
def Fits (K : ℕ) (y : ℕ → ℝ) (d : ℝ) : Prop :=
  0≤d ∧ d≤Real.pi/6 ∧ DyadFits K y d ∧
    (reference K y≤K → ShiftFits K (reference K y) y d)

private lemma before {K : ℕ} (y : ℕ → ℝ) {i : ℕ} (le : i≤K) (lt : i<reference K y) :
    25/32≤y (2^i) := by
  classical
  by_contra! crosses
  have hit : ∃ j, j≤K ∧ y (2^j)<25/32 := ⟨i,le,crosses⟩
  rw [reference,dif_pos hit] at lt
  exact (not_le_of_gt lt) (Nat.find_min' hit ⟨le,crosses⟩)

private lemma crossed {K : ℕ} (y : ℕ → ℝ) (hit : reference K y≤K) :
    y (2^(reference K y))<25/32 := by
  classical
  unfold reference at hit ⊢
  split_ifs with h
  · exact (Nat.find_spec h).2
  · simp only [dif_neg h] at hit
    omega

private lemma prior_phase {K : ℕ} {y : ℕ → ℝ} {d : ℝ} (fit : Fits K y d) :
    ∀ i≤K, i≤reference K y → (2:ℝ)^i*d≤Real.pi/2 := by
  intro i
  induction i with
  | zero =>
    intro _ _
    rw [pow_zero,one_mul]
    linarith [fit.2.1,Real.pi_pos]
  | succ i ih =>
    intro ik beforeHit
    have ik' : i≤K := by omega
    have prev := ih ik' (by omega)
    have lb := before y ik' (by omega : i<reference K y)
    have err := (abs_le.mp (fit.2.2.1 i ik')).1
    have strict : Real.cos (Real.pi/4) < Real.cos ((2:ℝ)^i*d) := by
      rw [Real.cos_pi_div_four]
      have sqrt := Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
      nlinarith [Real.sqrt_nonneg (2:ℝ)]
    have a : (2:ℝ)^i*d < Real.pi/4 := by
      by_contra! reversed
      have := Real.cos_le_cos_of_nonneg_of_le_pi (by linarith [Real.pi_pos] : 0≤Real.pi/4)
        (show (2:ℝ)^i*d ≤ Real.pi by linarith [Real.pi_pos]) reversed
      linarith
    rw [pow_succ]
    linarith

/-- The index chosen from the first batch traps every compatible phase in [π/6,π/2].
If no index was chosen the final dyadic phase is at most π/2. -/
theorem reference_band {K : ℕ} {y : ℕ → ℝ} {d : ℝ} (fit : Fits K y d)
    (hit : reference K y≤K) :
    Real.pi/6≤(2:ℝ)^(reference K y)*d ∧ (2:ℝ)^(reference K y)*d≤Real.pi/2 := by
  let j := reference K y
  refine ⟨?_,prior_phase fit _ hit le_rfl⟩
  have upper := (abs_le.mp (fit.2.2.1 j hit)).2
  have hitValue := crossed y hit
  change y (2^j)<_ at hitValue
  have cc : Real.cos ((2:ℝ)^j*d)<Real.cos (Real.pi/6) := by
    rw [Real.cos_pi_div_six]
    have sq := Real.sq_sqrt (by norm_num : (0:ℝ)≤3)
    nlinarith [Real.sqrt_nonneg (3:ℝ)]
  by_contra! low
  have := Real.cos_le_cos_of_nonneg_of_le_pi (mul_nonneg (by positivity) fit.1)
    (show Real.pi/6≤Real.pi by linarith [Real.pi_pos]) low.le
  linarith

private theorem near_reading {a b y : ℝ} (left : |a-y|≤1/16) (right : |b-y|≤1/16) :
    |a-b|<1/4 := by
  have bound := abs_sub_le a y b
  rw [abs_sub_comm y b] at bound
  linarith

/-- A single scale resolves any pair left in the previous interval. This also applies
to convex hulls of earlier feasible sets in the interval decoder. -/
theorem separated_at_scale {u v h t : ℝ} (hh : 0≤h) (ord : u≤v)
    (uBand : Real.pi/6≤h*u ∧ h*u≤Real.pi/2) (vBand : Real.pi/6≤h*v ∧ h*v≤Real.pi/2)
    (il : Real.pi/6≤t*((v-u)/2)) (iu : t*((v-u)/2)≤Real.pi/3) :
    1/4≤|Real.cos (t*u)-Real.cos (t*v)| ∨
      1/4≤|Real.cos ((t+h)*u)-Real.cos ((t+h)*v)| := by
  let d := (v-u)/2
  let m := (v+u)/2
  have hm : Real.pi/6≤h*m ∧ h*m≤Real.pi/2 := by dsimp [m]; constructor <;> linarith
  have hd : 0≤h*d ∧ h*d≤Real.pi/6 := by
    constructor
    · exact mul_nonneg hh (by dsimp [d]; linarith)
    · dsimp [d]; linarith [uBand.1,vBand.2]
  change Real.pi/6≤t*d at il
  change t*d≤Real.pi/3 at iu
  have refSin := PrimeFactors.sin_band hm.1 (by linarith [hm.2,Real.pi_pos])
  have ueq : u=m-d := by dsimp [m,d]; ring
  have veq : v=m+d := by dsimp [m,d]; ring
  rcases PrimeFactors.sin_separated (x:=t*m) refSin with strong|shifted
  · left
    rw [ueq,veq]
    exact PrimeFactors.cos_gap strong (PrimeFactors.sin_band il (by linarith [Real.pi_pos]))
  · right
    rw [←add_mul] at shifted
    have gd : Real.pi/6≤(t+h)*d ∧ (t+h)*d≤2*Real.pi/3 := by
      rw [add_mul]; constructor <;> linarith [hd.1,hd.2,Real.pi_pos]
    rw [ueq,veq]
    exact PrimeFactors.cos_gap shifted (PrimeFactors.sin_band gd.1 gd.2)

private theorem separate_pair {K : ℕ} {y : ℕ → ℝ} {u v : ℝ} (fu : Fits K y u)
    (fv : Fits K y v) (ord : u≤v) (hit : reference K y≤K)
    (gap : Real.pi/6≤2^K*((v-u)/2)) : False := by
  have dmax : (v-u)/2≤Real.pi/3 := by linarith [fu.1,fv.2.1,Real.pi_pos]
  obtain ⟨i,ik,il,iu⟩ := PrimeFactors.find_phase_band K dmax gap
  rcases separated_at_scale (by positivity) ord (reference_band fu hit) (reference_band fv hit)
    il iu with first|second
  · exact (not_lt_of_ge first) (near_reading (fu.2.2.1 i ik) (fv.2.2.1 i ik))
  · exact (not_lt_of_ge second) (near_reading (fu.2.2.2 hit i ik) (fv.2.2.2 hit i ik))

/-- Resolution from at most two parallel batches and 2(K+1) readings, including the
near-equal-factor case where a dyadic-only ladder may exhibit reflection ambiguity. -/
theorem resolution {K : ℕ} {y : ℕ → ℝ} {u v : ℝ} (fu : Fits K y u) (fv : Fits K y v)
    (ord : u≤v) : 2^K*(v-u)<Real.pi/3 := by
  by_cases hit : reference K y≤K
  · by_contra! bad
    exact separate_pair fu fv ord hit (by linarith)
  · have hi := prior_phase fv K le_rfl (by omega)
    have lb := before y (le_refl K) (by omega : K<reference K y)
    have read := (abs_le.mp (fv.2.2.1 K le_rfl)).1
    have cosLt : Real.cos (Real.pi/3)<Real.cos ((2:ℝ)^K*v) := by rw [Real.cos_pi_div_three]; linarith
    have bound : (2:ℝ)^K*v < Real.pi/3 := by
      by_contra! rev
      have := Real.cos_le_cos_of_nonneg_of_le_pi (by linarith [Real.pi_pos] : 0≤Real.pi/3)
        (show 2^K*v≤Real.pi by linarith [Real.pi_pos]) rev
      linarith
    nlinarith [mul_nonneg (show 0≤(2:ℝ)^K by positivity) fu.1]

/-- The actual integer heights requested from the boundary evaluator, with duplicates removed. -/
noncomputable def queries (K : ℕ) (y : ℕ → ℝ) : Finset ℕ := by
  let base := (Finset.range (K+1)).image (fun i => 2^i)
  exact if reference K y≤K then base ∪ base.image (fun h => h+2^(reference K y)) else base

theorem query_count (K : ℕ) (y : ℕ → ℝ) : (queries K y).card≤2*(K+1) := by
  let base := (Finset.range (K+1)).image (fun i => 2^i)
  have length : base.card≤K+1 := Finset.card_image_le.trans (Finset.card_range _).le
  unfold queries
  split_ifs
  · exact (Finset.card_union_le _ _).trans ((Nat.add_le_add length (Finset.card_image_le.trans length)).trans_eq
      (two_mul (K+1)).symm)
  · exact length.trans (by omega)

theorem query_heights {K t : ℕ} {y : ℕ → ℝ} (mem : t∈queries K y) : 0<t ∧ t≤2^(K+1) := by
  have base {i : ℕ} (hi : i∈Finset.range (K+1)) : 0<2^i ∧ (2:ℕ)^i≤2^K :=
    ⟨by positivity,Nat.pow_le_pow_right (by decide) (by simpa only [Finset.mem_range,Nat.lt_succ_iff] using hi)⟩
  simp only [queries] at mem
  rw [pow_succ]
  split_ifs at mem with hit
  · rcases Finset.mem_union.mp mem with h|h
    · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp h
      have both := base hi
      omega
    · obtain ⟨a,ha,e⟩ := Finset.mem_image.mp h
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp ha
      subst t
      have both := base hi
      have bound := Nat.pow_le_pow_right (by decide : 0<2) hit
      exact ⟨by positivity,(Nat.add_le_add both.2 bound).trans_eq (Nat.mul_two _).symm⟩
  · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp mem
    have both := base hi
    omega

/-- The lower endpoint depends only on the recorded transcript. -/
noncomputable def left (K : ℕ) (y : ℕ → ℝ) : ℝ := sInf {d | Fits K y d}

theorem enclosure {K : ℕ} {y : ℕ → ℝ} {v : ℝ} (fv : Fits K y v) :
    left K y≤v ∧ v≤left K y+Real.pi/(3*2^K) := by
  have pos : (0:ℝ)<2^K := by positivity
  have width : 0≤Real.pi/(3*2^K) := by positivity
  refine ⟨csInf_le (show BddBelow {d | Fits K y d} from ⟨0,fun _ hd => hd.1⟩) fv,?_⟩
  have lower : v-Real.pi/(3*2^K)≤left K y := by
    apply le_csInf (show ({d | Fits K y d} : Set ℝ).Nonempty from ⟨v,fv⟩)
    intro u fu
    by_cases ord : u≤v
    · have e := resolution fu fv ord
      have gap : v-u≤Real.pi/(3*2^K) := (le_div_iff₀ (by positivity)).mpr (by linarith)
      linarith
    · linarith
  linarith

/-- Normalize a supplied B(t) using the known product-dependent phase. -/
noncomputable def wave (n : ℕ) (read : ℕ → ℝ) (t : ℕ) : ℝ :=
  Real.cos (t*Real.log n/2)-read t/2

theorem fits_readings {p q K : ℕ} (hp : p.Prime) (hq : q.Prime) (ord : p<q)
    (balance : q≤2*p) [NeZero (p*q)] (read : ℕ → ℝ)
    (error : ∀ t∈queries K (wave (p*q) read), |read t-boundaryProbe (p*q) t|≤1/8) :
    Fits K (wave (p*q) read) ((Real.log q-Real.log p)/2) := by
  let y := wave (p*q) read
  have pp : 0<(p:ℝ) := by exact_mod_cast hp.pos
  have qq : 0<(q:ℝ) := by exact_mod_cast hq.pos
  have lo := Real.log_le_log pp (by exact_mod_cast ord.le : (p:ℝ)≤q)
  have hi := Real.log_le_log qq (by exact_mod_cast balance : (q:ℝ)≤2*p)
  rw [Real.log_mul (by norm_num) pp.ne'] at hi
  have sample {t : ℕ} (mem : t∈queries K y) :
      |Real.cos (t*((Real.log q-Real.log p)/2))-y t|≤1/16 := by
    have pos := (query_heights mem).1
    have exp := ratioWave_semiprime hp hq ord.ne (t:=(t:ℝ)) (by exact_mod_cast pos)
    dsimp only [ratioWave] at exp
    have eq : Real.cos (t*((Real.log q-Real.log p)/2))-y t=
        (read t-boundaryProbe (p*q) t)/2 := by dsimp [y,wave]; linarith
    rw [eq,abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
    linarith [error _ mem]
  have base {i : ℕ} (ik : i≤K) : 2^i∈(Finset.range (K+1)).image (fun j => (2:ℕ)^j) :=
    Finset.mem_image.mpr ⟨i,Finset.mem_range.mpr (by omega),rfl⟩
  refine ⟨by linarith,by linarith [Real.pi_gt_three,Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)],?_,?_⟩
  · intro i ik
    have mem : 2^i∈queries K y := by
      unfold queries; split_ifs; exact Finset.mem_union_left _ (base ik); exact base ik
    simpa only [Nat.cast_pow,Nat.cast_ofNat] using sample mem
  · intro hit i ik
    have mem : 2^i+2^(reference K y)∈queries K y := by
      unfold queries; rw [if_pos hit]
      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨2^i,base ik,rfl⟩)
    simpa only [Nat.cast_add,Nat.cast_pow,Nat.cast_ofNat] using sample mem

set_option exponentiation.threshold 4096 in
/-- The physical diameter allows one full unit of outward endpoint rounding. -/
theorem target_budget :
    (2:ℝ)^1024*(Real.pi/(3*2^499))+1≤4*(BinomialAnalyticWindow.window:ℝ) := by
  norm_num [BinomialAnalyticWindow.window,FeasibleDivisorCover.radius,FeasibleDivisorCover.S]
  linarith [Real.pi_lt_d2]

set_option exponentiation.threshold 4096 in
/-- One public center contains the larger prime, and a nonzero, bounded-degree polynomial
covers it. All boundary accuracies in the hypotheses refer to the actual requested heights. -/
theorem selected_window {n : ℕ} [NeZero n] (big : 2^2047≤n) (parity : Odd n)
    (read : ℕ → ℝ) (error : ∀ t∈queries 499 (wave n read), |read t-boundaryProbe n t|≤1/8) :
    let X := AnalyticDivisorWindow.lowerValue n (left 499 (wave n read))
    let C := AnalyticDivisorWindow.center X BinomialAnalyticWindow.window
    ∃ F : Polynomial ℤ, F≠0 ∧ F.roots.toFinset.card≤24575 ∧
      ∀ p q : ℕ, p*q=n → p.Prime → q.Prime → p<q → q≤2*p → q<2^1024 →
      ∃ x : ℤ, (q:ℤ)=(C:ℤ)+2*x ∧ |x|≤(BinomialAnalyticWindow.window:ℤ) ∧ F.eval x=0 := by
  let a := left 499 (wave n read)
  let X := AnalyticDivisorWindow.lowerValue n a
  let C := AnalyticDivisorWindow.center X BinomialAnalyticWindow.window
  obtain ⟨F,nz,rank,works⟩ := CenteredBinomialDivisorWindow.at_center big parity false C
    (AnalyticDivisorWindow.center_odd ..)
  refine ⟨F,nz,rank,?_⟩
  intro p q pair hp hq ord bal cap
  subst n
  have fit := fits_readings hp hq ord bal read error
  obtain ⟨lo,hi⟩ := enclosure fit
  have shift : Real.log q-Real.log (p*q:ℕ)/2=(Real.log q-Real.log p)/2 := by
    rw [Nat.cast_mul,Real.log_mul (by exact_mod_cast hp.ne_zero) (by exact_mod_cast hq.ne_zero)]
    ring
  rw [←shift] at lo hi
  obtain ⟨lb,dist⟩ := AnalyticDivisorWindow.lowerValue_bounds (by exact_mod_cast hq.pos)
    (by exact_mod_cast cap.le : (q:ℝ)≤(2:ℝ)^1024) lo hi
  have room : (q:ℝ)-X≤4*(BinomialAnalyticWindow.window:ℝ) := by linarith [target_budget]
  obtain ⟨x,pos,near⟩ := AnalyticDivisorWindow.center_contains (Nat.odd_mul.mp parity).2 (Real.exp_pos _).le lb room
  have low : FeasibleDivisorCover.divisorFloor (p*q) false≤q := by
    change (p*q)/2^1024+1≤q
    apply Nat.succ_le_of_lt
    apply (Nat.div_lt_iff_lt_mul (by positivity : 0<2^1024)).mpr
    rw [Nat.mul_comm p q]
    exact Nat.mul_lt_mul_of_pos_left (ord.trans cap) hq.pos
  have dsize : FeasibleDivisorCover.dimension-1<q := by
    have le : 2^1023≤(p*q)/2^1024 := (Nat.le_div_iff_mul_le (by positivity)).mpr (by
      rw [←pow_add]; exact big)
    change (p*q)/2^1024+1 ≤ q at low
    have h : FeasibleDivisorCover.dimension-1<2^1023 := by decide +kernel
    omega
  exact ⟨x,pos,near,works x q hq dsize (dvd_mul_left ..) pos low near⟩

set_option exponentiation.threshold 4096 in
/-- Height alone limits uniform resolution in the continuous observation model. -/
theorem continuous_height_limit :
    let u := (1/8:ℝ)
    let v := u+(1/2)^498
    0≤u ∧ v≤Real.pi/6 ∧ Real.pi/(3*2^499)<v-u ∧
    ∃ response : ℝ → ℝ, ∀ t, 0≤t → t≤2^495 →
      |response t-Real.cos (t*u)|≤1/16 ∧ |response t-Real.cos (t*v)|≤1/16 := by
  dsimp only
  refine ⟨by norm_num,?_,?_,ratioWave_common_responses (by
    rw [show (1/8:ℝ)-(1/8+(1/2)^498) = -((1/2)^498) by ring,abs_neg,abs_of_nonneg (by positivity)]
    norm_num)⟩
  · have h := Real.pi_gt_three
    norm_num at *
    linarith
  · have h := Real.pi_lt_d2
    norm_num at *
    linarith

/-- Arithmetic verification for the product-only numerical illustration. -/
theorem sample_factors : (7:ℕ).Prime ∧ (11:ℕ).Prime ∧ 7*11=77 := by decide +kernel

end PrimeFactors.BoundaryWindowSelection
