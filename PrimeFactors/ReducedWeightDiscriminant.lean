import PrimeFactors.ModularHyperbola
import Mathlib.Data.Int.GCD
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace PrimeFactors.ReducedWeightDiscriminant

/-- The lifted low digit may be any representative of the computed carry modulo R. -/
theorem stationary_lift {R N u w k i y a b : ℤ}
    (carry : N = u*w + R*k) (inverse : u*i ≡ 1 [ZMOD R])
    (lift : y ≡ w + R*(i*k) [ZMOD R^2]) (weight : b ≡ a*i*w [ZMOD R]) :
    R^2 ∣ u*y-N ∧ R ∣ a*y-b*u := by
  obtain ⟨j,hj⟩ := Int.modEq_iff_dvd.mp inverse
  obtain ⟨l,hl⟩ := Int.modEq_iff_dvd.mp lift
  obtain ⟨h,hh⟩ := Int.modEq_iff_dvd.mp weight
  constructor
  · refine ⟨-k*j-u*l, ?_⟩
    linear_combination -carry - R*k*hj - u*hl
  · refine ⟨a*w*j + a*i*k - a*R*l + h*u, ?_⟩
    linear_combination a*w*hj - a*hl + u*hh

/-- Every candidate trace has the square divisor, even if the candidate yields no factors. -/
theorem divides {R N u y a b t : ℤ} (lift : R^2 ∣ u*y-N)
    (weight : R ∣ a*y-b*u) (trace : t ≡ a*y+b*u [ZMOD R^2]) :
    R^2 ∣ t^2-4*a*b*N := by
  obtain ⟨c,hc⟩ := lift
  obtain ⟨d,hd⟩ := weight
  obtain ⟨j,hj⟩ := Int.modEq_iff_dvd.mp trace
  refine ⟨d^2 + 4*a*b*c - j*(a*y+b*u+t), ?_⟩
  linear_combination 4*a*b*hc + (a*y-b*u+R*d)*hd - (a*y+b*u+t)*hj

/-- Integer square equivalence includes zero and negative discriminants. -/
theorem square_iff {R D : ℤ} (nonzero : R ≠ 0) (divisible : R^2 ∣ D) :
    (∃ x : ℤ, D=x^2) ↔ ∃ s : ℤ, D/R^2=s^2 := by
  have mulback := Int.ediv_mul_cancel divisible
  constructor
  · rintro ⟨x,hx⟩
    obtain ⟨s,hs⟩ := (Int.pow_dvd_pow_iff (by decide : 2≠0)).mp (hx ▸ divisible)
    refine ⟨s, ?_⟩
    apply mul_right_cancel₀ (pow_ne_zero 2 nonzero)
    rw [mulback,hx,hs,mul_pow,mul_comm]
  · rintro ⟨s,hs⟩
    exact ⟨R*s, by rw [mul_pow, ← hs, mul_comm, mulback]⟩

/-- Uniform bound over every trace in the full midpoint/half-gap rectangle.
The three public endpoint inequalities follow by bounding the midpoint by
3*sqrt(N/8) and the half-gap by sqrt(N/8). -/
theorem envelope {N U G t a b : ℤ}
    (mid : 8*U^2 ≤ 9*N) (mixed : 8*U*G ≤ 3*N) (gap : 8*G^2 ≤ N)
    (trace : |t| ≤ U*|a+b|+G*|a-b|) :
    8*(t^2-4*a*b*N) ≤ N*(|a+b|+3*|a-b|)^2 := by
  have ts := mul_self_le_mul_self (abs_nonneg t) trace
  have ms := mul_le_mul_of_nonneg_right mid (sq_nonneg |a+b|)
  have gs := mul_le_mul_of_nonneg_right gap (sq_nonneg |a-b|)
  have xs := mul_le_mul_of_nonneg_right mixed (mul_nonneg (abs_nonneg (a+b)) (abs_nonneg (a-b)))
  have ab : 4*a*b*N = (|a+b|^2-|a-b|^2)*N := by rw [sq_abs,sq_abs]; ring
  rw [← sq, sq_abs] at ts
  rw [ab]
  linarith only [ms,gs,xs,ts]

/-- The bound is uniform in the orbit and uses only its one-trace width criterion. -/
theorem reduced_bound {R N H G t a b : ℤ} (nPos : 0<N) (radix : R ≠ 0)
    (hPos : 0 ≤ H) (shape : 3*H ≤ 2*G) (width : H*|a+b|+2*G*|a-b| < R^2)
    (bound : 8*(t^2-4*a*b*N) ≤ N*(|a+b|+3*|a-b|)^2)
    (divisible : R^2 ∣ t^2-4*a*b*N) :
    8*H^2*((t^2-4*a*b*N)/R^2) < N*R^2 := by
  have positive : 0 < R^2 := sq_pos_of_ne_zero radix
  have sh := mul_le_mul_of_nonneg_right shape (abs_nonneg (a-b))
  have smaller : H*(|a+b|+3*|a-b|) < R^2 := by linarith
  have sqSmaller := mul_self_lt_mul_self (by positivity : 0 ≤ H*(|a+b|+3*|a-b|)) smaller
  have strict := mul_lt_mul_of_pos_left sqSmaller nPos
  have weak := mul_le_mul_of_nonneg_left bound (sq_nonneg H)
  refine Int.lt_of_mul_lt_mul_right ?_ positive.le
  have cancel := Int.ediv_mul_cancel divisible
  calc
    8*H^2*((t^2-4*a*b*N)/R^2)*R^2 = 8*H^2*(t^2-4*a*b*N) := by rw [mul_assoc,cancel]
    _ < N*R^2*R^2 := by linarith only [weak,strict]

set_option exponentiation.threshold 2048 in
/-- Public arithmetic for midpoint-weights-capped-2048. The first three bounds
identify the integer endpoints by bracketing their squares. The remaining
inequalities instantiate the uniform 1,369-bit bound before any orbit is visited. -/
theorem midpoint_control :
    let n : ℕ := 18235237592309485695022717500584076834228742012137848692162518020978118330670298290562456426810101243915588566219126668755415360373629950817644531102840147168807721411128576610077370297128672185922697990174697797877023148638300250217898029403807743399403470882749087896494117442930327898728993236265159221191304843910091543703340279881486076234533009216452089916355489317599474401910447859622267052036598859256561156192908144641101500840415742300094826816004821857915899867583179777285615085535823553451865231616820876501603740836250921424292114568739597717105285840494859549175008035791093210162150329267779081863169
    let R : ℕ := 14761412789877398598231539921630752927114724257085462292775441282901779146702882788113242727951170230912592535838426537678698613706588500426220468432340332442832710042048152380233157473717127431625366432490
    let U : ℕ := 143229334604850313138566489055709596701722479803431094785265819716304424479127451881454356391104988176774099293512862660501771928861576349259845104697153888164258937620889789878230157790402912337412721815919608999715426107609948309504501939611886845518020670241294895979000307457040375470980378805598825072269
    let G : ℕ := 47743111534950104379522163018569865567240826601143698261755273238768141493042483960484785463701662725591366431170954220167257309620525449753281701565717962721419645873629929959410052596800970779137573938639869666571808702536649436501500646537295615172673556747098298659666769152346791823660126268532941690756
    let L : ℕ := 135037911685235586269825030135549325391376915966798636179319977077209993450011760943044181307768476527897818717675959823440307553022185653953812606479930673789391793187765141283074720630433120513417190939648203494531748575804685158519937612233285802863014656458801051235008057526662884995918450838938076904615
    let H := U-L
    ((L-1)^2<n ∧ n≤L^2) ∧ (8*U^2≤9*n ∧ 9*n<8*(U+1)^2) ∧
      (8*G^2≤n ∧ n<8*(G+1)^2) ∧ 0<H ∧ 8*U*G≤3*n ∧ 3*H≤2*G ∧
      n*R^2≤8*H^2*2^1369 := by decide +kernel

end PrimeFactors.ReducedWeightDiscriminant
