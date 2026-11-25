import PrimeFactors.OffsetCRTReconstruction
import PrimeFactors.GroupedOffsetRows

namespace PrimeFactors.OffsetLatticeBatches
open GroupedOffsetRows

/-- The affine-looking slope restrictions form a homogeneous index-I*m lattice. -/
def OnLine (I m R j k : ℤ) : Prop := I∣k ∧ j ≡ R*k [ZMOD m]

theorem compatible_cast {I m R j k : ℕ} (ok : OffsetCRTReconstruction.Compatible I m R j k) :
    OnLine I m R j k :=
  ⟨Int.natCast_dvd_natCast.mpr ok.1,by simpa only [Nat.cast_mul] using Int.natCast_modEq_iff.mpr ok.2⟩

/-- An explicit seed basis exists at every leaf, even for an empty prefix
or a slope that is infinity at every prefix prime. -/
theorem seed_basis {I m R : ℤ} : OnLine I m R m 0 ∧ OnLine I m R (R*I%m) I ∧
    m*I-0*(R*I%m)=I*m := by
  refine ⟨⟨dvd_zero _,?_⟩,⟨dvd_refl _,Int.mod_modEq ..⟩,by ring⟩
  rw [mul_zero]
  exact Int.modEq_zero_iff_dvd.mpr (dvd_refl _)

/-- A prime-power direction can put a partial power into the denominator:
then k=I*v and j=A*v modulo m, even if I and m share a prime. Every
unimodular basis change in the (v,quotient) variables still visits precisely
the points in that lattice. -/
theorem normalized_coordinates {I m A a b c d j k : ℤ} (det : a*d-b*c=1) :
    (∃ v : ℤ, k=I*v ∧ j ≡ A*v [ZMOD m]) ↔
    ∃ w u : ℤ, j=(A*a+m*b)*w+(A*c+m*d)*u ∧ k=(I*a)*w+(I*c)*u := by
  constructor
  · rintro ⟨v,rfl,h⟩
    obtain ⟨z,hz⟩ := Int.modEq_iff_dvd.mp h
    obtain ⟨first,second⟩ := GroupedOffsetRows.coordinates det v (-z)
    refine ⟨d*v-c*(-z),a*(-z)-b*v,?_,?_⟩
    · linear_combination -A*first-m*second-hz
    · linear_combination -I*first
  · rintro ⟨w,u,rfl,rfl⟩
    exact ⟨a*w+c*u,by ring,Int.modEq_iff_dvd.mpr ⟨-(b*w+d*u),by ring⟩⟩

/-- Unimodular basis updates made by the reducer stay inside the same lattice. -/
theorem on_line_linear {I m R a b c d : ℤ} (first : OnLine I m R a b)
    (second : OnLine I m R c d) (w u : ℤ) : OnLine I m R (a*w+c*u) (b*w+d*u) := by
  refine ⟨dvd_add (dvd_mul_of_dvd_left first.1 w) (dvd_mul_of_dvd_left second.1 u),?_⟩
  exact ((first.2.mul_right w).add (second.2.mul_right u)).trans (by ring_nf; rfl)

/-- All oriented determinants of compatible points are divisible by the entire
partial wheel, including the primes at which the denominator vanishes. -/
theorem det_dvd {I m R a b j k : ℤ} (one : OnLine I m R a b) (two : OnLine I m R j k) :
    I*m ∣ a*k-b*j := by
  obtain ⟨⟨v,bv⟩,first⟩ := one
  obtain ⟨⟨w,kw⟩,second⟩ := two
  obtain ⟨r,ar⟩ := Int.modEq_iff_dvd.mp first
  obtain ⟨s,js⟩ := Int.modEq_iff_dvd.mp second
  rw [bv] at ar ⊢
  rw [kw] at js ⊢
  exact ⟨v*s-w*r,by linear_combination -(I*w)*ar+(I*v)*js⟩

/-- Cramer's rule gives integer coordinates in every oriented basis with the
right determinant. Thus no canonical residue case needs separate enumeration. -/
theorem coordinates {I m R a b c d j k : ℤ} (positive : 0<I*m)
    (first : OnLine I m R a b) (second : OnLine I m R c d) (point : OnLine I m R j k)
    (basis : a*d-b*c=I*m) :
    ∃ w u : ℤ, j=a*w+c*u ∧ k=b*w+d*u ∧
      w=(j*d-c*k)/(I*m) ∧ u=(a*k-b*j)/(I*m) := by
  obtain ⟨w,ww⟩ := det_dvd point second
  obtain ⟨u,uu⟩ := det_dvd first point
  have adjW : j*d-c*k=I*m*w := by linarith only [ww]
  refine ⟨w,u,?_,?_,by rw [adjW, Int.mul_ediv_cancel_left _ positive.ne'],
    by rw [uu,Int.mul_ediv_cancel_left _ positive.ne']⟩
  · apply mul_left_cancel₀ positive.ne'
    linear_combination -j*basis+a*adjW+c*uu
  · apply mul_left_cancel₀ positive.ne'
    linear_combination -k*basis+b*adjW+d*uu

/-- Scanning the ragged intersection of the five linear inequalities is
exactly the original box cut by the public multiplier cap. -/
theorem row_constraints (a b c d w u J K T h : ℤ) :
    (1≤a*w+c*u ∧ a*w+c*u≤J ∧ 1≤b*w+d*u ∧ b*w+d*u≤K ∧ h*(b*w+d*u)≤T*(a*w+c*u)+h) ↔
    (1-c*u≤a*w ∧ c*u-J≤(-a)*w ∧ 1-d*u≤b*w ∧ d*u-K≤(-b)*w ∧
      (h*d-T*c)*u-h≤(T*a-h*b)*w) := by
  constructor <;> rintro ⟨a₁,a₂,a₃,a₄,a₅⟩ <;> refine ⟨?_,?_,?_,?_,?_⟩ <;> linarith only [a₁,a₂,a₃,a₄,a₅]

/-- Primitivity is preserved in this direction even for determinant larger than one. -/
theorem primitive_coefficients {a b c d w u : ℤ} (primitive : IsCoprime (a*w+c*u) (b*w+d*u)) :
    IsCoprime w u := by
  obtain ⟨x,y,eq⟩ := primitive
  exact ⟨x*a+y*b,x*c+y*d,by linear_combination eq⟩

theorem axis_only_units {a b w : ℤ} (primitive : IsCoprime (a*w) (b*w)) : w=1 ∨ w= -1 := by
  obtain ⟨x,y,eq⟩ := primitive
  exact Int.isUnit_iff.mp (isUnit_iff_dvd_one.mpr ⟨x*a+y*b,by linear_combination -eq⟩)

/-- A single forbidden residue at any divisor of the row index eliminates
that entire row, even for a non-unimodular partial-wheel basis. -/
theorem pivot_at_divisor {T h a b c d w u z l : ℤ} (primitive : IsCoprime (a*w+c*u) (b*w+d*u))
    (hit : z^2=form T h (a*w+c*u) (b*w+d*u)) (div : l∣u) :
    ∃ s : ℤ, s^2 ≡ form T h a b [ZMOD l] := by
  obtain ⟨x,y,bez⟩ := primitive_coefficients primitive
  apply Exists.intro (x*z)
  apply Int.ModEq.of_dvd div
  apply Int.modEq_iff_dvd.mpr
  refine ⟨y*(x*w+1)*form T h a b-x^2*(w*(2*a*c+4*T*(b*c+a*d)-8*h*b*d)+u*form T h c d),?_⟩
  rw [mul_pow,hit,GroupedOffsetRows.bilinear]
  linear_combination -(x*w+1)*form T h a b*bez

private theorem linear_interval {a k K : ℤ} (lo : 0≤k) (hi : k≤K) :
    min 0 (a*K)≤a*k ∧ a*k≤max 0 (a*K) := by
  rcases le_total 0 a with pos|neg
  · exact ⟨(min_le_left ..).trans (mul_nonneg pos lo),(mul_le_mul_of_nonneg_left hi pos).trans (le_max_right ..)⟩
  · exact ⟨(min_le_right ..).trans (mul_le_mul_of_nonpos_left hi neg),(mul_nonpos_of_nonpos_of_nonneg neg lo).trans (le_max_left ..)⟩

theorem row_window {a b j k J K M u : ℤ} (coords : M*u=a*k-b*j)
    (jl : 0≤j) (ju : j≤J) (kl : 0≤k) (ku : k≤K) :
    min 0 (a*K)-max 0 (b*J)≤M*u ∧ M*u≤max 0 (a*K)-min 0 (b*J) := by
  have x := linear_interval (a:=a) kl ku
  have y := linear_interval (a:=b) jl ju
  omega

/-- The projection interval contains zero. Its count of nonzero row indices
is at most its width divided by M (before taking floors). -/
theorem nonzero_row_count {M A B : ℤ} (mp : 0<M) :
    M*(A/M+B/M)≤A+B := by
  have x := Int.ediv_mul_le A mp.ne'
  have y := Int.ediv_mul_le B mp.ne'
  nlinarith only [x,y]

/-- Apply the row count to the actual projected rectangle bounds. -/
theorem projected_count {a b J K M : ℤ} (mp : 0<M) :
    M*((max 0 (b*J)-min 0 (a*K))/M + (max 0 (a*K)-min 0 (b*J))/M) ≤ |K*a|+|J*b| := by
  have h := nonzero_row_count (A:=max 0 (b*J)-min 0 (a*K)) (B:=max 0 (a*K)-min 0 (b*J)) mp
  apply h.trans_eq
  rw [mul_comm K a,mul_comm J b]
  rcases le_total 0 (a*K) with x|x <;> rcases le_total 0 (b*J) with y|y <;>
    simp [min_eq_left,min_eq_right,max_eq_left,max_eq_right,x,y,abs_of_nonneg,abs_of_nonpos] <;> ring

private theorem coord_span {a b lo hi J : ℤ}
    (first : 0≤a*lo+b ∧ a*lo+b≤J) (last : 0≤a*hi+b ∧ a*hi+b≤J) :
    |a| * (hi-lo)≤J := by
  rcases le_total 0 a with pos|neg
  · rw [abs_of_nonneg pos];linarith only [first.1,last.2]
  · rw [abs_of_nonpos neg];linarith only [first.2,last.1]

/-- Every nonempty intercept has at most one more point than L divided by
the largest scaled component. The proof uses its two endpoints. -/
theorem intercept_span {a b c d lo hi u J K : ℤ} (jl : 0≤J) (kl : 0≤K)
    (jlo : 0≤a*lo+c*u ∧ a*lo+c*u≤J) (jhi : 0≤a*hi+c*u ∧ a*hi+c*u≤J)
    (klo : 0≤b*lo+d*u ∧ b*lo+d*u≤K) (khi : 0≤b*hi+d*u ∧ b*hi+d*u≤K) :
    (hi-lo+1)*max |K*a| |J*b|≤max |K*a| |J*b|+J*K := by
  obtain low|high := le_total |K*a| |J*b|
  · rw [max_eq_right low,abs_mul,abs_of_nonneg jl]
    nlinarith only [mul_le_mul_of_nonneg_left (coord_span klo khi) jl]
  · rw [max_eq_left high,abs_mul,abs_of_nonneg kl]
    nlinarith only [mul_le_mul_of_nonneg_left (coord_span jlo jhi) kl]

/-- The reduced Gram conditions bound the norm of the first scaled vector. -/
theorem reduced_norm {A B C M L : ℤ} (ordered : A≤B) (ap : 0≤A) (nearest : 2*|C|≤A)
    (gram : A*B-C^2=(M*L)^2) : 3*A^2≤4*(M*L)^2 := by
  have bound := pow_le_pow_left₀ (show 0≤2*|C| by positivity) nearest 2
  rw [mul_pow,sq_abs] at bound
  nlinarith only [bound,gram,mul_le_mul_of_nonneg_left ordered ap]

/-- X and Y are the absolute components of the first basis vector after
scaling the J by K box to a square of side L=JK. With M≤L, the number of
nonzero rows is at most 2L/M. Even charging a full longest intercept to each
such row accounts for at most 4L/M point visits. The zero row costs at most
two further sign checks. -/
theorem reduced_batch_work {X Y M L rows width : ℤ} (xp : 0≤X) (yp : 0≤Y) (lp : 0<L)
    (mp : 0<M) (smallMod : M≤L) (pivot : 0<max X Y) (rp : 0≤rows)
    (rowWidth : M*rows≤X+Y) (intercept : width*max X Y≤max X Y+L)
    (normBound : 3*(X^2+Y^2)^2≤4*(M*L)^2) :
    M*rows≤2*L ∧ M*rows*width≤4*L := by
  have apos : 0≤X^2+Y^2 := by positivity
  have bound : X^2+Y^2≤2*(M*L) := (sq_le_sq₀ apos (by positivity)).mp (by
    nlinarith only [normBound,sq_nonneg (M*L)])
  have sumBound : X+Y≤2*L := (sq_le_sq₀ (add_nonneg xp yp) (by positivity)).mp (by
    nlinarith only [bound,sq_nonneg (X-Y),mul_le_mul_of_nonneg_right smallMod lp.le])
  have twice : X+Y≤2*max X Y := by linarith only [le_max_left X Y,le_max_right X Y]
  have raw := mul_le_mul_of_nonneg_left intercept (mul_nonneg mp.le rp)
  have sum := mul_le_mul_of_nonneg_right rowWidth (by linarith only [lp,pivot] : 0≤max X Y+L)
  have cap := mul_le_mul_of_nonneg_right sumBound pivot.le
  have cap' := mul_le_mul_of_nonneg_right twice lp.le
  refine ⟨rowWidth.trans sumBound,(mul_le_mul_iff_of_pos_right pivot).mp ?_⟩
  nlinarith only [raw,sum,cap,cap']

/-- If a partial wheel of modulus M is extended by a prime p to the
single-candidate reconstruction threshold, the batched method pays for at
most six elementary row/point visits per old full tuple on average across
that prime's g children. Each parent pays for just one basis reduction. -/
theorem deferred_prime_events {M L p g rows width : ℤ} (mp : 0<M)
    (room : 2*L<M*p) (alphabet : p+1≤2*g) (rowCap : M*rows≤2*L)
    (pointCap : M*rows*width≤4*L) : rows+rows*width+3≤6*g := by
  have limited : rows+rows*width<3*p := by
    apply (mul_lt_mul_iff_of_pos_left mp).mp
    nlinarith only [room,rowCap,pointCap]
  omega

/-- The one-deferred-prime comparison also covers a partial modulus larger
than the box area: enlarging L to M costs at most nine visits per parent. -/
theorem one_prime_work {X Y M L p g rows width : ℤ} (xp : 0≤X) (yp : 0≤Y)
    (lp : 0<L) (mp : 0<M) (pivot : 0<max X Y) (rp : 0≤rows) (oddPrimeSize : 3≤p)
    (room : 2*L<M*p) (alphabet : p+1≤2*g) (rowWidth : M*rows≤X+Y)
    (intercept : width*max X Y≤max X Y+L) (normBound : 3*(X^2+Y^2)^2≤4*(M*L)^2) :
    rows+rows*width+3≤6*g := by
  rcases le_total M L with sm|lg
  · have ⟨r,pt⟩ := reduced_batch_work xp yp lp mp sm pivot rp rowWidth intercept normBound
    exact deferred_prime_events mp room alphabet r pt
  · have bound : 3*(X^2+Y^2)^2≤4*(M*M)^2 := normBound.trans (by
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_nonneg mp.le lp.le)
        (mul_le_mul_of_nonneg_left lg mp.le) 2) (by decide))
    have ⟨r,pt⟩ := reduced_batch_work xp yp mp mp le_rfl pivot rp rowWidth
      (intercept.trans (add_le_add_left lg _)) bound
    have rr : rows≤2 := (mul_le_mul_iff_of_pos_left mp).mp (by linarith only [r])
    have pts : rows*width≤4 := (mul_le_mul_iff_of_pos_left mp).mp (by nlinarith only [pt])
    omega

/-- Projecting any allowed full tuple onto an arbitrary retained subwheel
preserves the chosen line and every finite or infinite local test. The
partial modulus need not reach a single-point reconstruction threshold. -/
def Batch (ps : List ℕ) (N T j k : ℕ) : Prop :=
  ∃ (inf fin : List ℕ) (r : ℕ → ℕ) (R : ℕ), (inf++fin).Perm ps ∧
    (∀ p ∈ inf, OffsetCRTReconstruction.Allowed p N T none ∧ p∣k) ∧
    (∀ p ∈ fin, OffsetCRTReconstruction.Allowed p N T (some (r p)) ∧
      R ≡ r p [MOD p] ∧ j ≡ r p*k [MOD p]) ∧ OnLine inf.prod fin.prod R j k

theorem project {ps : List ℕ} {N T j k : ℕ} (keep : ℕ → Bool)
    (full : OffsetCRTReconstruction.Recoverable ps N T j k) : Batch (ps.filter keep) N T j k := by
  obtain ⟨inf,fin,r,R,perm,zero,finite,compat,_⟩ := full
  have first : (inf.filter keep).prod∣inf.prod := List.filter_sublist.prod_dvd_prod
  have second : (fin.filter keep).prod∣fin.prod := List.filter_sublist.prod_dvd_prod
  exact ⟨_,_,r,R,by simpa only [List.filter_append] using perm.filter keep,
    fun p mem => zero p (List.mem_filter.mp mem).1,
    fun p mem => finite p (List.mem_filter.mp mem).1,
    compatible_cast ⟨first.trans compat.1,compat.2.of_dvd second⟩⟩

/-- The same projection works for an input-selected full wheel whenever its
checked array of distinct odd primes and its measured modulus meet the bound. -/
theorem batch_of_square {ps : List ℕ} {N T j k d J K : ℕ} (keep : ℕ → Bool)
    (distinct : ps.Nodup) (ok : ∀ p ∈ ps, p.Prime ∧ p≠2 ∧ ¬p∣N) (kp : 0<k)
    (cop : j.Coprime k) (boxJ : j≤J) (boxK : k≤K) (room : 2*J*K<ps.prod)
    (square : (j+2*T*k)^2=4*k^2*N+d^2) : Batch (ps.filter keep) N T j k :=
  project keep (OffsetCRTReconstruction.recoverable_of_square distinct ok kp cop boxJ boxK room square)

/-- Every balanced 2048-bit factor search admits a winning batch for every
choice of retained primes in the fixed wheel. Row enumeration within that
batch recovers its exact coordinates by `coordinates` and `row_constraints`. -/
theorem target_complete {N P Q : ℕ} (pair : P*Q=N) (pp : P.Prime) (qp : Q.Prime) (ne : P≠Q)
    (pbits : 2^1023≤P ∧ P<2^1024) (qbits : 2^1023≤Q ∧ Q<2^1024) (keep : ℕ → Bool) :
    ∃ j k, Batch (OffsetProjectiveSlopes.primes130.filter keep) N N.sqrt j k ∧
      3*j^2≤4*(N-N.sqrt^2) ∧ CompleteOffsetSearch.InSchedule N.sqrt (N-N.sqrt^2) j k ∧
      (CompleteOffsetSearch.probe N N.sqrt j k=some P ∨ CompleteOffsetSearch.probe N N.sqrt j k=some Q) := by
  obtain ⟨j,k,full,small,domain,hit⟩ := OffsetCRTReconstruction.target_complete pair pp qp ne pbits qbits
  exact ⟨j,k,project keep full,small,domain,hit⟩

end PrimeFactors.OffsetLatticeBatches
