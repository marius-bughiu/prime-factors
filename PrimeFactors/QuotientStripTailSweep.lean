import PrimeFactors.QuotientStripTailIndices
import PrimeFactors.QuotientStripTailCost
import PrimeFactors.QuotientStripTailCover

namespace PrimeFactors.QuotientStripTailSweep

open QuotientStripScheduleCost QuotientStripTailIndices QuotientStripTailCost
set_option exponentiation.threshold 4096
set_option maxRecDepth 8000
set_option maxHeartbeats 1600000

/-- The integer endpoints used by chord_levels, specialized to u=v=1. -/
def denom (a b : ℤ) := 4*a^2*b
def leftNum (N a b : ℤ) := 4*a*b*(a^2+N)
def rightNum (N a b : ℤ) := 4*a^2*(b^2+N)
def labelLow (N a b : ℤ) :=
  -((-(min (leftNum N a b) (rightNum N a b) - N*(b-a)^2))/denom a b)
def labelHigh (N a b : ℤ) := (max (leftNum N a b) (rightNum N a b))/denom a b

private theorem integer_endpoints {N a b z : ℤ} (ap : 0<a) (bp : 0<b)
    (low : f N b - pad N a b ≤ (z:ℚ)) (high : (z:ℚ) ≤ f N a) :
    labelLow N a b ≤ z ∧ z ≤ labelHigh N a b := by
  have dp : 0 < denom a b := by unfold denom; positivity
  have pos : 0 < ((denom a b:ℤ):ℚ) := by exact_mod_cast dp
  have aq : (a:ℚ) ≠ 0 := by exact_mod_cast ap.ne'
  have bq : (b:ℚ) ≠ 0 := by exact_mod_cast bp.ne'
  have l : ((leftNum N a b:ℤ):ℚ) = f N a*(denom a b:ℚ) := by
    dsimp only [leftNum,f,denom]; push_cast; field_simp; ring
  have r : ((rightNum N a b - N*(b-a)^2:ℤ):ℚ) = (f N b - pad N a b)*(denom a b:ℚ) := by
    dsimp only [rightNum,f,pad,denom]; push_cast; field_simp; ring
  have hzlo : rightNum N a b - N*(b-a)^2 ≤ z*denom a b := by
    exact_mod_cast r.le.trans (mul_le_mul_of_nonneg_right low pos.le)
  have hzhi : z*denom a b ≤ leftNum N a b := by
    exact_mod_cast (mul_le_mul_of_nonneg_right high pos.le).trans l.ge
  constructor
  · unfold labelLow
    apply neg_le.mpr
    apply (Int.le_ediv_iff_mul_le dp).mpr
    have h := min_le_right (leftNum N a b) (rightNum N a b)
    linarith only [h,hzlo]
  · exact (Int.le_ediv_iff_mul_le dp).mpr (hzhi.trans (le_max_left ..))

/-- The first Euclidean quotient is one. Either the rational has terminated
there, or the second quotient is already above the public denominator cap.
Thus the capped ordinary continued fraction actually returns 1/1. -/
def EuclidUnit (N S Q : ℤ) : Prop :=
  N/S = 1 ∧ (N%S = 0 ∨ Q < S/(N%S))

private theorem euclid_unit {N S Q : ℤ} (sp : 0<S) (qc : Q+1≤2^343)
    (lo : (1:ℚ)≤(N:ℚ)/S) (hi : (N:ℚ)/S-1 < 1/2^343) : EuclidUnit N S Q := by
  have sqpos : (0:ℚ)<S := by exact_mod_cast sp
  have bot : S≤N := by
    exact_mod_cast (show (S:ℚ)≤(N:ℚ) by simpa only [one_mul] using (le_div_iff₀ sqpos).mp lo)
  have top := (div_lt_iff₀ sqpos).mp (sub_lt_iff_lt_add.mp hi)
  have small : (2:ℤ)^343*(N-S)<S := by
    exact_mod_cast (show (2:ℚ)^343*((N:ℚ)-(S:ℚ))<S by
      norm_num1 at top ⊢
      linarith only [top])
  have firstQ : N/S = 1 := (Int.ediv_eq_iff_of_pos sp).mpr (by
    rw [one_mul]
    constructor
    · exact bot
    · omega)
  have remainder : N%S = N-S := by
    have h := Int.emod_add_ediv N S
    rw [firstQ,mul_one] at h
    omega
  refine ⟨firstQ,?_⟩
  by_cases finalQ : N%S=0
  · exact Or.inl finalQ
  · right
    have rp : 0 < N%S := by have := Int.emod_nonneg N sp.ne'; omega
    have nextQ : Q+1≤S/(N%S) := (Int.le_ediv_iff_mul_le rp).mpr <|
      (mul_le_mul_of_nonneg_right qc rp.le).trans (remainder ▸ small.le)
    omega

/-- The witnesses identify full blocks of the fixed public schedule and
use its original rounded endpoints. A certified primitive direction in each
of these blocks is necessarily 1/1. -/
def Admitted (n : ℕ) (k z : ℤ) : Prop :=
  let a := start (first n) (width n) k
  let b := stop (first n) (width n) k
  let Q := (b-a)/2
  0 ≤ k ∧ 0 < a ∧ a ≤ b ∧ b ≤ n.sqrt ∧
    0 < Q ∧ |a*b-(n:ℤ)| *(Q+1) ≤ a*b ∧
    (∀ u v : ℕ, 0<v → (v:ℤ)≤Q → u.Coprime v →
      |(u:ℤ)*(a*b)-(v:ℤ)*n| *(Q+1) ≤ a*b → u=1 ∧ v=1) ∧
    EuclidUnit n (a*b) Q ∧ labelLow n a b ≤ z ∧ z ≤ labelHigh n a b

private theorem certify_direction {n : ℕ} {a b : ℤ} (ap : 0<a) (bp : 0<b)
    (full : b-a=2*(roundedSixth n:ℤ)-1)
    (rl : 2^341 ≤ roundedSixth n) (rh : roundedSixth n ≤ 2^342)
    (low : (1:ℚ) ≤ (n:ℚ)/((a:ℚ)*(b:ℚ)))
    (high : (n:ℚ)/((a:ℚ)*(b:ℚ))-1 < 1/2^343) :
    let Q := (b-a)/2
    0 < Q ∧ |a*b-(n:ℤ)| *(Q+1) ≤ a*b ∧
      ∀ u v : ℕ, 0<v → (v:ℤ)≤Q → u.Coprime v →
        |(u:ℤ)*(a*b)-(v:ℤ)*n| *(Q+1) ≤ a*b → u=1 ∧ v=1 := by
  let r := roundedSixth n
  let Q := (b-a)/2
  let S : ℚ := (a:ℚ)*(b:ℚ)
  have sp : 0<S := by dsimp only [S]; exact_mod_cast mul_pos ap bp
  have qeq : Q+1 = (r:ℤ) := by dsimp only [Q,r]; omega
  have qr : (3:ℚ) ≤ r := by exact_mod_cast (show 3 ≤ r by omega)
  have rmax : (r:ℚ) ≤ 2^342 := by exact_mod_cast rh
  have rp : (0:ℚ)<r := by linarith
  change 1 ≤ (n:ℚ)/S at low
  change (n:ℚ)/S-1 < 1/2^343 at high
  change 0<Q ∧ _ ∧ _
  refine ⟨by omega,?_,?_⟩
  · rw [qeq]
    have h : |(1:ℚ)-(n:ℚ)/S| *(r:ℚ) ≤ 1 := by
      rw [abs_of_nonpos (by linarith only [low])]
      have scale := mul_le_mul_of_nonneg_right high.le rp.le
      have top := mul_le_mul_of_nonneg_left rmax (show (0:ℚ)≤1/2^343 by norm_num)
      norm_num1 at scale top
      nlinarith only [scale,top]
    have scaled := mul_le_mul_of_nonneg_right h sp.le
    have form : |1-(n:ℚ)/S| *(r:ℚ)*S = |S-n| *(r:ℚ) := by
      rw [mul_right_comm,← abs_of_pos sp,← abs_mul,abs_of_pos sp]
      congr 2
      field_simp
    rw [form,one_mul] at scaled
    dsimp only [S] at scaled
    exact_mod_cast scaled
  · intro u v vp cap cop close
    apply unique_direction qr rmax vp (by exact_mod_cast (show (v:ℤ)≤r by omega)) low high _ cop
    rw [le_div_iff₀ rp]
    rw [qeq] at close
    have close' : |(u:ℚ)*S-(v:ℚ)*n| *(r:ℚ) ≤ S := by dsimp only [S]; exact_mod_cast close
    apply le_of_mul_le_mul_right _ sp
    rw [one_mul,mul_right_comm]
    have form : |(u:ℚ)-(v:ℚ)*((n:ℚ)/S)| *S = |(u:ℚ)*S-(v:ℚ)*n| := by
      calc
        _ = |((u:ℚ)-(v:ℚ)*((n:ℚ)/S))*S| := by rw [abs_mul,abs_of_pos sp]
        _ = _ := by congr 1; field_simp
    rw [form]
    exact close'

/-- Count distinct nonnegative discriminants admitted by the unit-slope
chord bounds and the residue 1+N modulo 24 in a complete scheduled sweep.
A label can be admitted without its discriminant being a square. -/
theorem full_sweep {n : ℕ} (low : 2^2047 ≤ n) (high : n < 2^2048) :
    ∃ z : Fin (2^328) → ℤ,
      Function.Injective (fun j => (z j)^2-4*(n:ℤ)) ∧
      ∀ j, z j ≡ 1+(n:ℤ) [ZMOD 24] ∧ 0 ≤ (z j)^2-4*(n:ℤ) ∧
        ∃ k : ℤ, Admitted n k (z j) := by
  obtain ⟨tl,th,rl,rh⟩ := root_bounds low high
  let L : ℤ := first n
  let W : ℤ := width n
  let T : ℤ := n.sqrt
  let r := roundedSixth n
  have weq : W=2*(r:ℤ) := by dsimp only [W,width,r]; push_cast; rfl
  have wp : 0<W := by omega
  have wl : W≤2^343 := by omega
  have room := band_begins_before tl
  obtain ⟨i,j,ip,ij,istart,iend,jstart,jend⟩ := full_indices
    (L:=L) (W:=W) (T:=T) (H:=2^679) wp room (by omega)
  let m := (j-i).toNat
  let A (k : ℕ) := start L W (i+k)
  let B (k : ℕ) := stop L W (i+k)
  have endeq : i+(m:ℤ)=j := by dsimp only [m]; omega
  have length (k : ℕ) : B k-A k=2*(r:ℤ)-1 := by
    dsimp only [A,B,start,stop]
    linarith only [weq]
  have ab (k : ℕ) : A k ≤ B k := by have := length k; omega
  have inTail (k : ℕ) (km : k≤m) : T-2^679 ≤ A k ∧ B k ≤ T := by
    have lo := mul_le_mul_of_nonneg_right (show i ≤ i+k by omega) wp.le
    have hi := mul_le_mul_of_nonneg_right (show i+(k:ℤ)+1 ≤ j+1 by omega) wp.le
    dsimp only [A,B,start,stop] at istart jend ⊢
    constructor <;> linarith only [istart,lo,jend,hi]
  have initial : A 0 = start L W i := by simp [A]
  have finalEq : B m = stop L W j := by simp only [B,endeq]
  have next (k : ℕ) : A (k+1)=B k+1 := by
    dsimp only [A,B,start,stop]
    push_cast
    ring
  have tlq : (11*2^1020:ℚ) ≤ (T:ℚ) := by dsimp only [T]; exact_mod_cast tl
  have thq : (T:ℚ) ≤ 2^1024 := by dsimp only [T]; exact_mod_cast th.le
  have tsq : (T:ℚ)^2 ≤ (n:ℚ) := by dsimp only [T]; exact_mod_cast Nat.sqrt_le' n
  have tn : (n:ℚ) < ((T:ℚ)+1)^2 := by dsimp only [T]; exact_mod_cast Nat.lt_succ_sqrt' n
  have rlq : (2^341:ℚ) ≤ (r:ℚ) := by exact_mod_cast rl
  have wq : (W:ℚ) ≤ 2^343 := by exact_mod_cast wl
  have fp (k : ℕ) (km : k≤m) : 0<A k := by
    have x := (inTail k km).1
    dsimp only [T] at x
    omega
  have gap (k : ℕ) (km : k≤m) := direction_and_gap (a:=(A k:ℚ)) (b:=(B k:ℚ)) tlq tn
    (by exact_mod_cast (inTail k km).1) (by exact_mod_cast ab k)
  have padFloor (k : ℕ) (km : k≤m) := pad_bound (a:=(A k:ℚ)) (b:=(B k:ℚ)) tlq thq tsq rlq
    (by exact_mod_cast (inTail k km).1) (by exact_mod_cast (inTail k km).2) (by exact_mod_cast length k)
  let lower (k : ℕ) := f n (B k) - pad n (A k) (B k)
  let upper (k : ℕ) := f n (A k)
  have firstVal := first_value (a:=(A 0:ℚ)) tlq thq tsq wq
    (by exact_mod_cast (inTail 0 (Nat.zero_le _)).1)
    (by exact_mod_cast ((initial.trans_lt iend).le))
  have endAt : T-2*W ≤ B m := by rw [finalEq]; omega
  have lastVal := last_value (b:=(B m:ℚ)) tlq tn wq
    (by exact_mod_cast (inTail m le_rfl).2) (by exact_mod_cast endAt)
  let base : ℚ := 2*(T:ℚ)+4
  have basePos : 0<base := by dsimp only [base]; linarith only [tlq]
  obtain ⟨z,injective,eligible⟩ := QuotientStripTailCover.many_distinct_labels lower upper m
    (2^328) base (1+n) n basePos (by
      change f n (B m)-pad n (A m) (B m) ≤ 2*(T:ℚ)+4
      linarith only [lastVal,padFloor m le_rfl]) (by
      change 2*(T:ℚ)+4+24*((2^328:ℕ):ℚ) ≤ f n (A 0)
      norm_num1 at firstVal ⊢
      linarith only [firstVal]) (by
      intro k hk
      have h := (gap k hk.le).2
      change f n (B k)-pad n (A k) (B k) ≤ f n (A (k+1))
      rw [next]
      push_cast
      linarith only [h,padFloor k hk.le])
  refine ⟨z,injective,?_⟩
  intro s
  obtain ⟨res,lb,k,km,zl,zu⟩ := eligible s
  have zbig : 2*(T:ℚ)+4 ≤ (z s:ℚ) := lb
  have nonneg : 0 ≤ (z s)^2-4*(n:ℤ) := by
    have step : 2*((T:ℚ)+1) ≤ (z s:ℚ) := by linarith only [zbig]
    have sq := pow_le_pow_left₀ (by linarith only [tlq] : 0≤2*((T:ℚ)+1)) step 2
    exact_mod_cast (show (0:ℚ) ≤ (z s:ℚ)^2-4*(n:ℚ) by nlinarith only [sq,tn])
  refine ⟨res,nonneg,i+k,?_⟩
  change 0 ≤ i+(k:ℤ) ∧ 0<A k ∧ A k≤B k ∧ B k≤(n.sqrt:ℤ) ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _
  have ap := fp k km
  have bp := ap.trans_le (ab k)
  have Bt := (inTail k km).2
  have aq : (0:ℚ)<A k := by exact_mod_cast ap
  have bq : (0:ℚ)<B k := by exact_mod_cast bp
  have below : (1:ℚ) ≤ (n:ℚ)/((A k:ℚ)*(B k:ℚ)) := by
    apply (le_div_iff₀ (mul_pos aq bq)).mpr
    rw [one_mul]
    have bT : (B k:ℚ) ≤ (T:ℚ) := by exact_mod_cast Bt
    have aT : (A k:ℚ) ≤ (T:ℚ) := by exact_mod_cast (ab k).trans Bt
    exact (mul_le_mul aT bT bq.le (aq.le.trans aT)).trans (by simpa [sq] using tsq)
  obtain ⟨qp,yes,onlyUnit⟩ := certify_direction ap bp (length k) rl rh below (gap k km).1
  obtain ⟨loInt,hiInt⟩ := integer_endpoints ap bp zl zu
  have upperCap : (B k-A k)/2+1 ≤ (2:ℤ)^343 := by have := length k; omega
  have euclid : EuclidUnit n (A k*B k) ((B k-A k)/2) := by
    apply euclid_unit (mul_pos ap bp) upperCap
    · simpa only [Int.cast_mul,Int.cast_natCast] using below
    · simpa only [Int.cast_mul,Int.cast_natCast] using (gap k km).1
  exact ⟨by omega,ap,ab k,Bt,qp,yes,onlyUnit,euclid,loInt,hiInt⟩

end PrimeFactors.QuotientStripTailSweep
