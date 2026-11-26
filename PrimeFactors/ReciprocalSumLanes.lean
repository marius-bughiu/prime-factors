import PrimeFactors.ReciprocalWheel
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Prime.Basic

/-! Price a complementary wheel lane and its factor sums using the first and
last actual candidates in a single smaller-factor residue class. -/

namespace PrimeFactors.ReciprocalSumLanes

/-- Signed difference of endpoint quotients for one inclusive arithmetic
progression. When L ≤ U+1 this is the number of its positions. -/
def slots (L U W r : ℤ) : ℤ := (U-r)/W - (L-1-r)/W

theorem slot_index {W : ℤ} (wp : 0<W) (L U r j : ℤ) :
    (L ≤ r+W*j ∧ r+W*j ≤ U) ↔ (L-1-r)/W < j ∧ j ≤ (U-r)/W := by
  rw [Int.ediv_lt_iff_lt_mul wp,Int.le_ediv_iff_mul_le wp,mul_comm j W]
  omega

theorem slot_card (L U W r : ℤ) (ordered : L ≤ U+1) (wp : 0<W) :
    ((Finset.Ioc ((L-1-r)/W) ((U-r)/W)).card : ℤ) = slots L U W r := by
  rw [Int.card_Ioc,slots,Int.toNat_of_nonneg]
  exact sub_nonneg.mpr (Int.ediv_le_ediv wp (by omega))

/-- If the lower lane begins at a and ends m wheel steps later at b,
the sum-lane count is the upper-lane count minus those m steps. The sums
are congruent to a+s. L and U are the rounded lower and upper partner endpoints. -/
theorem count_identity {a b W m : ℤ} (wp : 0<W) (last : b=a+W*m) (L U s : ℤ) :
    slots L U W s = m + slots (b+L) (a+U) W (a+s) := by
  unfold slots
  rw [show a+U-(a+s)=U-s by ring,
    show b+L-1-(a+s)=(L-1-s)+W*m by rw [last]; ring,
    Int.add_mul_ediv_left _ _ wp.ne']
  omega

/-- Directly check the entire smaller lane is impossible if switching to
the partner would cost fewer than its m+1 positions. -/
theorem empty_of_cheaper_partner {a b W m L U s : ℤ} (wp : 0<W) (last : b=a+W*m)
    (cheaper : slots L U W s < m+1) (i : ℤ) :
    ¬ (b+L ≤ (a+s)+W*i ∧ (a+s)+W*i ≤ a+U) := by
  intro member
  obtain ⟨low,high⟩ := (slot_index wp (b+L) (a+U) (a+s) i).mp member
  have h := count_identity wp last L U s
  unfold slots at h cheaper
  omega

/-- Real-valued factor sum at a guessed smaller divisor. -/
noncomputable def factorSum (n x : ℝ) := x+n/x

theorem difference (n : ℝ) {x y : ℝ} (xp : x≠0) (yp : y≠0) :
    (factorSum n x-factorSum n y)*(x*y) = (y-x)*(n-x*y) := by
  unfold factorSum
  field_simp
  ring

/-- On the balanced half of the hyperbola the sum decreases by at most the
distance moved, strictly less between distinct lower endpoints. -/
theorem variation {n x y : ℝ} (xp : 0<x) (order : x≤y) (small : y^2≤n)
    (balanced : n≤2*x^2) :
    0≤factorSum n x - factorSum n y ∧ factorSum n x - factorSum n y ≤ y-x ∧
      (x<y → factorSum n x - factorSum n y < y-x) := by
  have yp := xp.trans_le order
  have pos := mul_pos xp yp
  have dx : 0≤y-x := sub_nonneg.mpr order
  have id := difference n xp.ne' yp.ne'
  have nonneg : 0≤n-x*y := by nlinarith only [small,mul_nonneg dx yp.le]
  have bound : n-x*y≤x*y := by nlinarith only [balanced,mul_nonneg dx xp.le]
  refine ⟨(mul_nonneg_iff_of_pos_right pos).mp (by rw [id]; exact mul_nonneg dx nonneg),
    le_of_mul_le_mul_right (a:=x*y) (by rw [id]; exact mul_le_mul_of_nonneg_left bound dx) pos, ?_⟩
  intro strict
  have dxp := sub_pos.mpr strict
  have tighter : n-x*y<x*y := by nlinarith only [balanced,mul_pos dxp xp]
  exact lt_of_mul_lt_mul_right (a:=x*y) (by rw [id]; exact mul_lt_mul_of_pos_left tighter dxp) pos.le

/-- From any actual divisor pair in the balanced subinterval, its sum is
inside the rounded endpoints used in count_identity. -/
theorem sum_survives {n a b p q : ℤ} (ap : 0<a) (left : a≤p) (right : p≤b)
    (small : b^2≤n) (balanced : n≤2*a^2) (product : p*q=n) :
    b+⌈(n:ℝ)/b⌉ ≤ p+q ∧ p+q ≤ a+⌊(n:ℝ)/a⌋ := by
  have A : (0:ℝ)<a := by exact_mod_cast ap
  have L : (a:ℝ)≤p := by exact_mod_cast left
  have R : (p:ℝ)≤b := by exact_mod_cast right
  have P := A.trans_le L
  have lower : (b:ℝ)^2≤n := by exact_mod_cast small
  have upper : (n:ℝ)≤2*a^2 := by exact_mod_cast balanced
  have lo := (variation P R lower (upper.trans (by nlinarith only [sq_le_sq' (by linarith : -(p:ℝ)≤a) L]))).1
  have hi := (variation A L ((sq_le_sq' (by linarith : -(b:ℝ)≤p) R).trans lower) upper).1
  have value : factorSum n p = ((p+q:ℤ):ℝ) := by
    unfold factorSum
    rw [←product, Int.cast_mul,Int.cast_add, mul_div_cancel_left₀ _ P.ne']
  rw [value] at lo hi
  constructor
  · rw [add_comm b, ←Int.ceil_add_intCast, Int.ceil_le]
    simpa only [factorSum, add_comm (b : ℝ)] using sub_nonneg.mp lo
  · rw [←Int.floor_intCast_add,Int.le_floor]
    exact sub_nonneg.mp hi

/-- The actual integer product cannot occur in this entire directed lane
when its rounded upper-factor count beats the m+1 smaller positions. -/
theorem excludes_product {n a b W m s : ℤ} (ap : 0<a) (wp : 0<W) (last : b=a+W*m)
    (small : b^2≤n) (balanced : n≤2*a^2)
    (cheaper : slots ⌈(n:ℝ)/b⌉ ⌊(n:ℝ)/a⌋ W s < m+1)
    (u v : ℤ) (left : a≤a+W*u) (right : a+W*u≤b) :
    (a+W*u)*(s+W*v)≠n := by
  intro product
  have bounds := sum_survives ap left right small balanced product
  apply empty_of_cheaper_partner wp last cheaper (u+v)
  convert bounds using 2 <;> ring

/-- A public complementary residue a*s≡n determines every actual partner
because a is a unit. Thus the sparse-partner test rules out divisibility by
every smaller candidate without checking individual remainders. -/
theorem excludes_divisor {n a b W m s : ℤ} (ap : 0<a) (wp : 0<W) (last : b=a+W*m)
    (small : b^2≤n) (balanced : n≤2*a^2) (coprime : Int.gcd W a=1)
    (partner : a*s ≡ n [ZMOD W])
    (cheaper : slots ⌈(n:ℝ)/b⌉ ⌊(n:ℝ)/a⌋ W s < m+1)
    (u : ℤ) (left : a≤a+W*u) (right : a+W*u≤b) : ¬ (a+W*u) ∣ n := by
  rintro ⟨q,product⟩
  have lower : a ≡ a+W*u [ZMOD W] := Int.modEq_iff_dvd.mpr ⟨u,by ring⟩
  have same : a*s ≡ a*q [ZMOD W] := by
    rw [product] at partner
    exact partner.trans (lower.mul_right q).symm
  have upper : s ≡ q [ZMOD W] := by simpa [coprime] using same.cancel_left_div_gcd wp
  obtain ⟨v,hv⟩ := Int.modEq_iff_dvd.mp upper
  have qrep : q=s+W*v := by linarith
  apply excludes_product ap wp last small balanced cheaper u v left right
  rw [←qrep,←product]

/-- The lower-only sieve costs no more divisor positions than choosing
the cheaper side. It saves every would-be upper position each time an
empty sum lane is identified. -/
theorem lower_only_cost {m h : ℕ} :
    (if h<m+1 then 0 else m+1) + (if h<m+1 then h else 0) = min (m+1) h := by
  split <;> omega

/-- On a nonsingleton balanced lane, the number of square tests is at most
m, where the original lower progression has m+1 positions. -/
theorem square_test_bound {n a b W m s : ℤ} (ap : 0<a) (wp : 0<W)
    (many : 0<m) (last : b=a+W*m) (small : b^2≤n) (balanced : n≤2*a^2) :
    0 ≤ slots (b+⌈(n:ℝ)/b⌉) (a+⌊(n:ℝ)/a⌋) W (a+s) ∧
      slots (b+⌈(n:ℝ)/b⌉) (a+⌊(n:ℝ)/a⌋) W (a+s) ≤ m := by
  have ab : a<b := by have := mul_pos wp many; omega
  have real_ab : (a:ℝ)<b := by exact_mod_cast ab
  have diff := variation (show (0:ℝ)<a by exact_mod_cast ap) real_ab.le
    (show (b:ℝ)^2≤n by exact_mod_cast small) (show (n:ℝ)≤2*a^2 by exact_mod_cast balanced)
  have floor_a : ⌊factorSum n a⌋ = a+⌊(n:ℝ)/a⌋ := Int.floor_intCast_add ..
  have ceil_b : ⌈factorSum n b⌉ = b+⌈(n:ℝ)/b⌉ := by
    rw [factorSum,add_comm (b:ℝ),Int.ceil_add_intCast,add_comm]
  have order := (Int.ceil_le_floor_add_one (factorSum n b)).trans
    (add_le_add_right (Int.floor_mono (sub_nonneg.mp diff.1)) 1)
  rw [floor_a,ceil_b] at order
  have drop := diff.2.2 real_ab
  have hi := Int.floor_le (factorSum n a)
  have lo := Int.le_ceil (factorSum n b)
  rw [floor_a] at hi
  rw [ceil_b] at lo
  have span : ((a+⌊(n:ℝ)/a⌋:ℤ):ℝ) - ((b+⌈(n:ℝ)/b⌉:ℤ):ℝ) < (b:ℝ)-a := by linarith
  have length : (a+⌊(n:ℝ)/a⌋)-(b+⌈(n:ℝ)/b⌉) < b-a := by exact_mod_cast span
  unfold slots
  constructor
  · exact sub_nonneg.mpr (Int.ediv_le_ediv wp (by omega))
  · have upper : a+⌊(n:ℝ)/a⌋-(a+s) ≤ (b+⌈(n:ℝ)/b⌉-1-(a+s))+W*m := by omega
    have ratio := Int.ediv_le_ediv wp upper
    rw [Int.add_mul_ediv_left _ _ wp.ne'] at ratio
    omega

/-- A lower bound on the number of wheel steps and the larger block endpoint B
can certify the entire block needs no empty-lane pricing. Every sum residue
then occurs in each tightened sum interval. -/
theorem guard {n a b B W m k : ℤ} (ap : 0<a) (wp : 0<W) (kp : 0≤k) (km : k≤m)
    (last : b=a+W*m) (within : b≤B) (below : B^2≤n) (enough : B^2 ≤ k*(n-B^2))
    (s : ℤ) : ∃ i : ℤ, b+⌈(n:ℝ)/b⌉ ≤ (a+s)+W*i ∧ (a+s)+W*i ≤ a+⌊(n:ℝ)/a⌋ := by
  have mp := kp.trans km
  have ab : a≤b := by have := mul_nonneg wp.le mp; omega
  have bp := ap.trans_le ab
  have cap : a*b≤B^2 := by
    rw [pow_two]
    exact mul_le_mul (ab.trans within) within bp.le (bp.le.trans within)
  have price : a*b≤m*(n-a*b) := calc
    a*b ≤ B^2 := cap
    _ ≤ k*(n-B^2) := enough
    _ ≤ m*(n-B^2) := mul_le_mul_of_nonneg_right km (sub_nonneg.mpr below)
    _ ≤ m*(n-a*b) := mul_le_mul_of_nonneg_left (by omega) mp
  have A : (0:ℝ)<a := by exact_mod_cast ap
  have Y : (0:ℝ)<b := by exact_mod_cast bp
  have Wpos : (0:ℝ)<W := by exact_mod_cast wp
  have cost : (a:ℝ)*b≤m*((n:ℝ)-a*b) := by exact_mod_cast price
  have length : (b:ℝ)-a=(W:ℝ)*m := by exact_mod_cast (show b-a=W*m by omega)
  have width : (W:ℝ)≤factorSum n a-factorSum n b := by
    apply le_of_mul_le_mul_right (a:=(a:ℝ)*b) _ (mul_pos A Y)
    rw [difference _ A.ne' Y.ne', length, mul_assoc]
    exact mul_le_mul_of_nonneg_left cost Wpos.le
  let t : ℝ := (factorSum n b - (a+s:ℤ))/W
  refine ⟨⌈t⌉, ?_, ?_⟩
  · have le : factorSum n b-(a+s:ℤ) ≤ (⌈t⌉:ℝ)*W := (div_le_iff₀ Wpos).mp (Int.le_ceil t)
    rw [add_comm b,←Int.ceil_add_intCast,Int.ceil_le]
    push_cast at le ⊢
    unfold factorSum at le
    linarith only [le,mul_comm (⌈t⌉:ℝ) (W:ℝ)]
  · have lt : (⌈t⌉:ℝ)-1<t := by linarith only [Int.ceil_lt_add_one t]
    have le := (lt_div_iff₀ Wpos).mp lt
    rw [←Int.floor_intCast_add,Int.le_floor]
    push_cast at le ⊢
    unfold factorSum at le width
    linarith only [le,width,mul_comm (⌈t⌉:ℝ) (W:ℝ)]

/-- Trimming both ends of a balanced band by less than one wheel period
retains every sum with its predecessor and successor in the original band. -/
theorem interior_survives {n a b lo hi w z : ℝ} (ap : 0<a)
    (first : a≤lo) (inside : lo≤hi) (last : hi≤b) (small : b^2≤n) (balanced : n≤2*a^2)
    (left_trim : lo-a<w) (right_trim : b-hi<w)
    (prev : factorSum n b≤z-w) (next : z+w≤factorSum n a) :
    factorSum n hi≤z ∧ z≤factorSum n lo := by
  have lp := ap.trans_le first
  have hp := lp.trans_le inside
  have lb : lo^2≤n := (sq_le_sq' (by linarith) (inside.trans last)).trans small
  have hb : n≤2*hi^2 := by
    nlinarith only [balanced,sq_le_sq' (by linarith : -hi≤a) (first.trans inside)]
  have L := (variation ap first lb balanced).2.1
  have H := (variation hp last small hb).2.1
  constructor <;> linarith

/-- In the wheel-30 example, the lower candidates 91 and 121 have only the
partner 139 in the rounded companion lane. The sum lane has no candidate. -/
theorem empty_example :
    slots 125 165 30 19 = 1 ∧ slots (121+125) (91+165) 30 (91+19) = 0 ∧
      15049 ≤ 121*125 ∧ 121*124 < 15049 ∧ 91*165 ≤ 15049 ∧ 15049 < 91*166 := by
  decide +kernel

/-- Complete product-only replay on the balanced band. For unit x, the
congruence x*z=x²+n asks for exactly the sum class x+n/x. -/
theorem small_sieve :
    (Finset.Icc 87 122).filter (fun x : ℕ =>
      x.Coprime 30 ∧
      let a := 87+(x+30-87%30)%30
      let b := 122-(122+30-x%30)%30
      0 < ((Finset.Icc (b+(15049+b-1)/b) (a+15049/a)).filter
        fun z => x*z%30=(x*x+15049)%30).card) =
      {89,101,119} := by decide +kernel

/-- The gcd of the three surviving smaller candidates in the wheel-30
example gives the smaller prime. -/
theorem small_factors :
    Nat.gcd (89*101*119) 15049 = 101 ∧ Nat.Prime 101 ∧ Nat.Prime 149 ∧ 101*149=15049 := by
  decide +kernel

end PrimeFactors.ReciprocalSumLanes
