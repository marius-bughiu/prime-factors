import PrimeFactors.ConicTangentReceipt
import Mathlib.Data.Nat.GCD.BigOperators

/-! Uniform block-count comparison in the 2048-bit signed charts. -/
namespace PrimeFactors.ConicTangentUniform

set_option exponentiation.threshold 4096

theorem rate {X W h phi cap ordinary : ℕ} (hp : 0<h) (wp : 0<W) (xp : 0<X)
    (small : 10000*h≤W) (long : 10000*h*W≤X)
    (density : 1000*phi≤649*h)
    (capEq : cap=phi*((X-1)/(h*(W-h+1))+1))
    (ordEq : ordinary=(X-1)/W+1) : 100*cap≤65*ordinary := by
  let step := h*(W-h+1)
  have diff : W-h+1+h=W+1 := by omega
  have ls : 9999*h*W ≤ 10000*step := by
    dsimp [step]
    calc
      _ = h*(9999*W) := by ring
      _ ≤ h*(10000*(W-h+1)) := Nat.mul_le_mul_left _ (by omega)
      _ = _ := by ring
  have smax : 10000*step ≤ X := calc
    _ = (10000*h)*(W-h+1) := by dsimp [step]; ring
    _ ≤ (10000*h)*W := Nat.mul_le_mul_left _ (by omega)
    _ ≤ X := long
  have ceilOrd : X ≤ ordinary*W := by
    rw [ordEq, Nat.add_mul,one_mul]
    have div := Nat.mod_add_div (X-1) W
    have mlt := Nat.mod_lt (X-1) wp
    rw [mul_comm W] at div
    omega
  have hull : ((X-1)/step+1)*step ≤ X+step := by
    have := Nat.div_mul_le_self (X-1) step
    rw [Nat.add_mul,one_mul]
    omega
  have capStep : cap*step ≤ phi*(X+step) := by
    rw [capEq]
    change (phi*((X-1)/step+1))*step ≤ _
    rw [mul_assoc]
    exact Nat.mul_le_mul_left _ hull
  have weight : cap*(9999*h*W) ≤ phi*(10001*X) := calc
    _ ≤ cap*(10000*step) := Nat.mul_le_mul_left _ ls
    _ = 10000*(cap*step) := by ring
    _ ≤ 10000*(phi*(X+step)) := Nat.mul_le_mul_left _ capStep
    _ = phi*(10000*(X+step)) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ (by omega)
  have big : (100*cap)*(1000*9999*h*W) ≤ (65*ordinary)*(1000*9999*h*W) := calc
    _ = 100000*(cap*(9999*h*W)) := by ring
    _ ≤ 100000*(phi*(10001*X)) := Nat.mul_le_mul_left _ weight
    _ = (1000*phi)*(100*10001*X) := by ring
    _ ≤ (649*h)*(100*10001*X) := Nat.mul_le_mul_right _ density
    _ = (649*100*10001)*(h*X) := by ring
    _ ≤ (65*1000*9999)*(h*X) := Nat.mul_le_mul_right _ (by decide)
    _ ≤ (65*1000*9999)*(h*(ordinary*W)) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ ceilOrd)
    _ = _ := by ring
  exact Nat.le_of_mul_le_mul_right big (by positivity)

theorem geometric_sizes {N M a b k X W : ℕ} (nlo : 2^2047≤N) (nhi : N<2^2048)
    (ma : N≤M) (mb : M≤2*N) (ap : 1≤a) (a6 : a≤6) (bp : 1≤b) (b6 : b≤6) (kp : 1≤k)
    (xhi : k*N < 2*a*(X+1)^2)
    (wlo : (8*a*W^3)^2≤b*M) (whi : b*M<(8*a*(W+1)^3)^2) :
    2^1000≤X ∧ 2^330≤W ∧ W≤2^350 := by
  have bm : N≤b*M := ma.trans (by simpa using Nat.mul_le_mul_right M bp)
  have ub : b*M≤12*N := calc
    _ ≤ 6*(2*N) := Nat.mul_le_mul b6 mb
    _ = _ := by ring
  constructor
  · by_contra! bad
    have upper : 2*a*(X+1)^2 ≤ 2*6*(2^1000)^2 :=
      Nat.mul_le_mul (Nat.mul_le_mul_left 2 a6) (Nat.pow_le_pow_left (by omega) _)
    have lower : N≤k*N := by simpa using Nat.mul_le_mul_right N kp
    omega
  constructor
  · by_contra! bad
    have upper : (8*a*(W+1)^3)^2 ≤ (8*6*(2^330)^3)^2 :=
      Nat.pow_le_pow_left (Nat.mul_le_mul (Nat.mul_le_mul_left _ a6)
        (Nat.pow_le_pow_left (by omega) _)) _
    omega
  · by_contra! bad
    have lower : (8*1*(2^350)^3)^2 ≤ (8*a*W^3)^2 :=
      Nat.pow_le_pow_left (Nat.mul_le_mul (Nat.mul_le_mul_left _ ap)
        (Nat.pow_le_pow_left (by omega) _)) _
    omega

theorem totient_prod (l : List ℕ) (primes : ∀ p ∈ l, p.Prime) (cop : l.Pairwise Nat.Coprime) :
    Nat.totient l.prod=(l.map (fun p => p-1)).prod := by
  induction l with
  | nil => simp
  | cons p l ih =>
    rcases List.pairwise_cons.mp cop with ⟨head,tail⟩
    rw [List.prod_cons,List.map_cons,List.prod_cons,Nat.totient_mul
      (Nat.coprime_list_prod_right_iff.mpr head),Nat.totient_prime (primes _ (by simp)),
      ih (fun r h => primes _ (by simp [h])) tail]

/-- The seven signed discriminants, in public candidate order. Each row
contains its distinct split primes through 257 and one CRT square root of D. -/
structure Wheel where
  d : ℤ
  factors : List ℕ
  root : ℕ
  deriving DecidableEq

def wheel : Fin 7 → Wheel :=
  ![⟨-1,[5, 13, 17, 29, 37, 41, 53, 61, 73, 89, 97, 101, 109, 113, 137, 149, 157, 173, 181, 193, 197, 229, 233, 241, 257],742644383806859876361750016013018808307160623817⟩,
    ⟨2,[7, 17, 23, 31, 41, 47, 71, 73, 79, 89, 97, 103, 113, 127, 137, 151, 167, 191, 193, 199, 223, 233, 239, 241, 257],11379454721581492012389780110113602046970076447290⟩,
    ⟨-2,[3, 11, 17, 19, 41, 43, 59, 67, 73, 83, 89, 97, 107, 113, 131, 137, 139, 163, 179, 193, 211, 227, 233, 241, 251, 257],109894279116142578028328381354413011144742235022514⟩,
    ⟨3,[11, 13, 23, 37, 47, 59, 61, 71, 73, 83, 97, 107, 109, 131, 157, 167, 179, 181, 191, 193, 227, 229, 239, 241, 251],28503353719524254956266599421872666104090232681443⟩,
    ⟨-3,[7, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241],216132796399842124563474406770216741941928530818⟩,
    ⟨6,[5, 19, 23, 29, 43, 47, 53, 67, 71, 73, 97, 101, 139, 149, 163, 167, 173, 191, 193, 197, 211, 239, 241],17535796660148054169022132130756365909425696⟩,
    ⟨-6,[5, 7, 11, 29, 31, 53, 59, 73, 79, 83, 97, 101, 103, 107, 127, 131, 149, 151, 173, 179, 193, 197, 199, 223, 227, 241, 251],12692490780991144604405700762999880009327321240395152⟩]

theorem wheel_facts (i : Fin 7) :
    let v := wheel i
    let h := v.factors.prod
    0<h ∧ h≤2^180 ∧ (∀ p ∈ v.factors, p.Prime ∧ 2<p ∧ p≤257) ∧
    v.factors.Pairwise Nat.Coprime ∧ 1000*(v.factors.map (·-1)).prod≤649*h ∧
    v.root.Coprime h ∧ (v.root:ZMod h)^2=v.d := by
  fin_cases i <;> decide +kernel

theorem wheel_density (i : Fin 7) :
    1000*(wheel i).factors.prod.totient≤649*(wheel i).factors.prod := by
  obtain ⟨_,_,pr,cop,num,_,_⟩ := wheel_facts i
  rwa [totient_prod _ (fun p hp => (pr p hp).1) cop]

/-- If every prime factor of N is large, all seven wheels are
coprime to N. In particular every input formed from two 1024-bit
primes can use the same list of split primes for a given discriminant. -/
theorem coprime_input (i : Fin 7) {N : ℕ}
    (large : ∀ p : ℕ, p.Prime → p ∣ N → 257<p) : N.Coprime (wheel i).factors.prod := by
  obtain ⟨_,_,pr,_,_,_,_⟩ := wheel_facts i
  apply Nat.coprime_list_prod_right_iff.mpr
  intro p member
  obtain ⟨pp,_,small⟩ := pr p member
  exact (pp.coprime_iff_not_dvd.mpr (fun h => (not_lt_of_ge small) (large p pp h))).symm

private theorem coprime_two (i : Fin 7) : Nat.Coprime 2 (wheel i).factors.prod := by
  apply Nat.coprime_list_prod_right_iff.mpr
  intro p mem
  have info := (wheel_facts i).2.2.1 p mem
  exact (Nat.coprime_primes Nat.prime_two info.1).mpr (by omega)

theorem balanced_multiplier (i : Fin 7) {p q m : ℕ} (pp : p.Prime) (qp : q.Prime)
    (pl : 2^1023≤p) (ql : 2^1023≤q) (mm : m=1 ∨ m=2) :
    (m*(p*q)).Coprime (wheel i).factors.prod := by
  have pair := coprime_input i (N:=p*q) (by
    intro r rp div
    rcases rp.dvd_mul.mp div with l|rr
    · have eq := (Nat.prime_dvd_prime_iff_eq rp pp).mp l
      omega
    · have eq := (Nat.prime_dvd_prime_iff_eq rp qp).mp rr
      omega)
  rcases mm with rfl|rfl
  · simpa
  · exact Nat.coprime_mul_iff_left.mpr ⟨coprime_two i,pair⟩

/-- The fixed CRT root of D supplies a split chart in either orientation,
since the product of its signed coefficients equals D. -/
theorem physical_classes (i : Fin 7) (a b : ℤ) (ab : a*b=(wheel i).d) {M : ℕ}
    (cop : M.Coprime (wheel i).factors.prod) :
    let h := (wheel i).factors.prod
    Nat.card {v : ZMod h × ZMod h //
      (b:ZMod h)*v.2^2-(a:ZMod h)*v.1^2=(M:ZMod h)}=Nat.totient h := by
  let h := (wheel i).factors.prod
  obtain ⟨hp,_,_,_,_,runit,root⟩ := wheel_facts i
  haveI : NeZero h := ⟨hp.ne'⟩
  let r : ZMod h := (wheel i).root
  have ru : IsUnit r := (ZMod.isUnit_iff_coprime _ h).mpr runit
  have mu : IsUnit (M:ZMod h) := (ZMod.isUnit_iff_coprime _ h).mpr cop
  have eq : r^2=(a:ZMod h)*b := by
    rw [←Int.cast_mul,ab]
    exact root
  have units : IsUnit ((a:ZMod h)*b) := eq ▸ ru.pow 2
  have bu := ((Commute.all _ _).isUnit_mul_iff.mp units).2
  let inv : ZMod h := ↑bu.unit⁻¹
  have invu : IsUnit inv := bu.unit⁻¹.isUnit
  have bi : (b:ZMod h)*inv=1 := by simpa only [inv,bu.unit_spec] using bu.unit.mul_inv
  apply ConicTangentReceipt.physical_count (t:=r*inv) (c:=(M:ZMod h)*inv)
    ((ZMod.isUnit_iff_coprime 2 h).mpr (coprime_two i)) bu (ru.mul invu) (mu.mul invu)
  · calc
      _ = r^2*inv*((b:ZMod h)*inv) := by ring
      _ = (a:ZMod h)*(b*inv) := by rw [eq,bi,mul_one,mul_assoc,bi,mul_one]
      _ = _ := by rw [bi,mul_one]
  · rw [mul_left_comm,bi,mul_one]

/-- The cube-root chart dimensions of every 2048-bit signed chart give
ample room for the per-class rounding costs. The comparison is for the
full number of block starts. -/
theorem uniform_rate (i : Fin 7) {N M a b k X W actual : ℕ}
    (nlo : 2^2047≤N) (nhi : N<2^2048) (ma : N≤M) (mb : M≤2*N)
    (ap : 1≤a) (a6 : a≤6) (bp : 1≤b) (b6 : b≤6) (kp : 1≤k)
    (xhi : k*N < 2*a*(X+1)^2) (wlo : (8*a*W^3)^2≤b*M) (whi : b*M<(8*a*(W+1)^3)^2)
    (run : ConicTangentReceipt.Counted X W (wheel i).factors.prod
      (wheel i).factors.prod.totient actual) : 100*actual≤65*((X-1)/W+1) := by
  let h := (wheel i).factors.prod
  have ⟨xp,wl,wh⟩ := geometric_sizes nlo nhi ma mb ap a6 bp b6 kp xhi wlo whi
  obtain ⟨hp,hb,_,_,_,_,_⟩ := wheel_facts i
  change 0<h at hp
  change h≤2^180 at hb
  have small : 10000*h≤W := (Nat.mul_le_mul_left 10000 hb).trans
    ((by decide +kernel : 10000*2^180≤2^330).trans wl)
  have long : 10000*h*W ≤ X := (Nat.mul_le_mul (Nat.mul_le_mul_left 10000 hb) wh).trans
    ((by decide +kernel : 10000*2^180*2^350≤2^1000).trans xp)
  have wc : 0<W := by omega
  have xc : 0<X := by omega
  have compare := rate hp wc xc small long (wheel_density i) rfl rfl
  obtain ⟨start,g,blocks,rfl,positive,gs,last⟩ := run
  have ct := ConicTangentLattice.block_count_bound Finset.univ start
    (fun v => h*g v*(W/g v)) blocks (show 0<h*(W-h+1) by positivity)
    (fun v _ => positive v) (fun v _ => ConicTangentLattice.stride_lower
      (gs v).1 (gs v).2 (by omega)) (fun v _ => last v)
  simp only [Finset.card_univ,Fintype.card_fin] at ct
  exact (Nat.mul_le_mul_left 100 ct).trans compare

end PrimeFactors.ConicTangentUniform
