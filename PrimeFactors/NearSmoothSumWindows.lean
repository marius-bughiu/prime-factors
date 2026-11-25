import PrimeFactors.ApproximateTotient
import PrimeFactors.SiftedDivisorWindow
import PrimeFactors.SmoothCenterSpacing

/-! Inverting both endpoints of a putative interval for an even factor sum.
A sufficiently narrow inverted interval needs just one seven-dimensional
divisor equation, independently of how many sum errors the interval contains. -/

namespace PrimeFactors.NearSmoothSumWindows

open Polynomial

/-- An even sum in [L,U] gives an integer midpoint in [leftHalf n L,U/2]. -/
def leftHalf (n L : ℕ) : ℕ := max ((L+1)/2) (ceilSqrt n)

def lower (n L : ℕ) : ℕ :=
  let a := leftHalf n L
  a+ceilSqrt (a^2-n)

def upper (n U : ℕ) : ℕ :=
  let b := U/2
  b+(b^2-n).sqrt

private theorem coordinates {p q : ℕ} (ord : p≤q) (op : Odd p) (oq : Odd q) :
    ∃ t d : ℕ, p+q=2*t ∧ q=t+d ∧ t^2=p*q+d^2 := by
  obtain ⟨a,rfl⟩ := op
  obtain ⟨v,rfl⟩ := oq
  obtain ⟨w,rfl⟩ := Nat.exists_eq_add_of_le (by omega : a≤v)
  exact ⟨2*a+1+w,w,by omega,by omega,by ring⟩

/-- For a genuine ordered factor pair the directed integer endpoints give
an equivalence. Values between them may still fail to divide the product. -/
theorem exact_interval {n p q L U : ℕ} (prod : p*q=n) (ord : p≤q)
    (op : Odd p) (oq : Odd q) :
    (L≤p+q ∧ p+q≤U) ↔ (lower n L≤q ∧ q≤upper n U) := by
  obtain ⟨t,d,mid,right,sq⟩ := coordinates ord op oq
  rw [prod] at sq
  let A := leftHalf n L
  let B := U/2
  have nd : t^2-n=d^2 := by omega
  have clamp : ceilSqrt n≤t := ceilSqrt_le_iff.mpr (by omega)
  have halves : (L≤p+q ∧ p+q≤U) ↔ (A≤t ∧ t≤B) := by
    dsimp only [A,B,leftHalf]
    rw [max_le_iff]
    omega
  change _ ↔ A+ceilSqrt (A^2-n)≤q ∧ q≤B+(B^2-n).sqrt
  rw [halves,right]
  constructor
  · rintro ⟨lo,hi⟩
    have x := Nat.sub_le_sub_right (Nat.pow_le_pow_left lo 2) n
    have y := Nat.sub_le_sub_right (Nat.pow_le_pow_left hi 2) n
    rw [nd] at x y
    exact ⟨Nat.add_le_add lo (ceilSqrt_le_iff.mpr x),Nat.add_le_add hi (Nat.le_sqrt'.mpr y)⟩
  · rintro ⟨lo,hi⟩
    constructor
    · by_contra! h
      have x := Nat.sub_le_sub_right (Nat.pow_le_pow_left h.le 2) n
      rw [nd] at x
      have z := x.trans (ceilSqrt_le_iff.mp (le_refl (ceilSqrt (A^2-n))))
      have := (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp z
      omega
    · by_contra! h
      have x := Nat.sub_le_sub_right (Nat.pow_le_pow_left h.le 2) n
      rw [nd] at x
      have z := (Nat.sqrt_le' (B^2-n)).trans x
      have := (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp z
      omega

/-- A public lower bound G for the half-gap at the left endpoint bounds the
slope throughout the interval. Directed rounding incurs no extra unit. -/
theorem width {n L U G K : ℕ} (order : leftHalf n L≤U/2)
    (gap : G^2≤(leftHalf n L)^2-n) (scale : U/2≤K*G) :
    upper n U-lower n L ≤ (K+1)*(U/2-leftHalf n L) := by
  let A := leftHalf n L
  let B := U/2
  let l := ceilSqrt (A^2-n)
  let h := (B^2-n).sqrt
  have nA : n≤A^2 := ceilSqrt_le_iff.mp (le_max_right ..)
  have nB : n≤B^2 := nA.trans (Nat.pow_le_pow_left order 2)
  have ll : A^2≤l^2+n := by
    have z : A^2-n≤l^2 := ceilSqrt_le_iff.mp (le_refl l)
    omega
  have hh : h^2+n≤B^2 := by
    have z : h^2≤B^2-n := Nat.sqrt_le' _
    omega
  have gl : G≤l := (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp
      (gap.trans (ceilSqrt_le_iff.mp (le_refl l)))
  have cap : B≤K*l := scale.trans (Nat.mul_le_mul_left _ gl)
  obtain ⟨t,eq⟩ := Nat.exists_eq_add_of_le (show A≤B from order)
  have slope := Nat.mul_le_mul_left (2*t) cap
  rw [eq] at slope hh
  have growth : h≤l+K*t := by
    apply (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp
    nlinarith only [slope,ll,hh,Nat.zero_le (t^2),Nat.zero_le ((K*t)^2)]
  change B+h-(A+l)≤(K+1)*(B-A)
  rw [eq,Nat.add_sub_cancel_left,Nat.add_mul,Nat.one_mul]
  omega

/-- Radius in the index of odd integers and the odd center chosen from public
inverse endpoints. The physical interval can have length 4*radius. -/
def radius : ℕ := 5*2^437

def windowRadius (n L U : ℕ) : ℕ := (upper n U-lower n L+3)/4

def center (n L U : ℕ) : ℕ := 2*(lower n L/2)+1+2*windowRadius n L U

private theorem in_index {n L U q : ℕ} (odd : Odd q) (lo : lower n L≤q)
    (hi : q≤upper n U) :
    ∃ x : ℤ, (q:ℤ)=(center n L U:ℤ)+2*x ∧ |x|≤(windowRadius n L U:ℤ) := by
  have width : upper n U-lower n L≤4*windowRadius n L U := by unfold windowRadius; omega
  obtain ⟨k,hk⟩ := odd
  refine ⟨(k:ℤ)-(lower n L/2:ℕ)-windowRadius n L U,?_,?_⟩
  · dsimp only [center]; push_cast; omega
  · rw [abs_le]
    omega

/-- One public sextic covers all correctly sized cofactor pairs with sums in
[L,U] if the directed interval fits. There are at most six integer roots. -/
theorem one_window {n L U : ℕ} (large : 2^2047≤n) (cop : n.Coprime 45360)
    (odd : Odd n) (fit : upper n U-lower n L≤4*radius) :
    ∃ F : ℤ[X], F≠0 ∧ F.roots.toFinset.card≤6 ∧ ∀ p q : ℕ,
      p*q=n → p≤q → p≤2^1024 → L≤p+q → p+q≤U →
      ∃ x : ℤ, (q:ℤ)=(center n L U:ℤ)+2*x ∧ |x|≤(windowRadius n L U:ℤ) ∧ F.eval x=0 := by
  have co : Odd ((center n L U):ℤ) := by
    refine ⟨((lower n L/2:ℕ):ℤ)+windowRadius n L U,?_⟩
    dsimp only [center]; push_cast; ring
  obtain ⟨F,nz,card,works⟩ := SiftedDivisorWindow.coupled_factorial_window large cop odd _ co
  refine ⟨F,nz,card,?_⟩
  intro p q prod ord cap lo hi
  have odds := Nat.odd_mul.mp (prod ▸ odd)
  obtain ⟨lb,ub⟩ := (exact_interval prod ord odds.1 odds.2).mp ⟨lo,hi⟩
  obtain ⟨x,atQ,near⟩ := in_index odds.2 lb ub
  have floor := CoupledDivisorWindow.lower_le_factor (d:=q) (q:=p)
    (by simpa [Nat.mul_comm] using prod.symm) cap
  have dv : q∣n := prod ▸ dvd_mul_left q p
  refine ⟨x,atQ,near,works x q (by exact_mod_cast dv) atQ (by exact_mod_cast floor) ?_⟩
  have capR : windowRadius n L U≤radius := by unfold windowRadius; omega
  have bound := near.trans (by exact_mod_cast capR : (windowRadius n L U:ℤ)≤radius)
  simpa only [radius,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] using bound

/-- Clip a sum-error band at the bit-width ceiling before inversion. -/
def sumLo (b E : ℕ) : ℕ := SmoothSumSelector.candidate b-E

def sumHi (b E : ℕ) : ℕ := min (SmoothSumSelector.candidate b+E) (2^1025)

export SmoothCenterSpacing (fastCenter fast_correct)

/-- Two necessary product-only tests: the largest half-sum must reach √N;
the smallest sum must be below 2^1024 + N/2^1024. -/
def keep (n E b : ℕ) : Bool :=
  let s := fastCenter b
  decide (n≤(min (s+E) (2^1025)/2)^2 ∧ (s-E)*2^1024<n+(2^1024)^2)

noncomputable def menu (n E : ℕ) : Finset ℕ := (Finset.range 647).filter fun b => keep n E b=true

/-- A surviving band must contain the midpoint and an integer of the required
larger-factor size. These exact endpoint tests may further shrink the menu. -/
noncomputable def active (n E : ℕ) : Finset ℕ := (menu n E).filter fun b =>
  leftHalf n (sumLo b E)≤sumHi b E/2 ∧ lower n (sumLo b E)<2^1024 ∧ 2^1023≤upper n (sumHi b E)

private theorem active_of_sum {n p q b E : ℕ} (prod : p*q=n) (ord : p≤q)
    (op : Odd p) (oq : Odd q) (loQ : 2^1023≤q) (hiQ : q<2^1024) (idx : b<647)
    (lo : sumLo b E≤p+q) (hi : p+q≤sumHi b E) : b∈active n E := by
  obtain ⟨lb,ub⟩ := (exact_interval prod ord op oq).mp ⟨lo,hi⟩
  obtain ⟨t,d,mid,_,square⟩ := coordinates ord op oq
  have clamp : ceilSqrt n≤t := ceilSqrt_le_iff.mpr (by rw [←prod,square]; omega)
  have upperMid : t≤sumHi b E/2 := by omega
  have first := (show n≤t^2 by rw [←prod,square]; omega).trans (Nat.pow_le_pow_left upperMid 2)
  have strict := Nat.mul_pos (Nat.sub_pos_of_lt (ord.trans_lt hiQ)) (Nat.sub_pos_of_lt hiQ)
  have left : (sumLo b E)*2^1024<n+(2^1024)^2 := by
    apply (Nat.mul_le_mul_right _ lo).trans_lt
    rw [←prod]
    zify [show p≤2^1024 from (ord.trans hiQ.le),hiQ.le] at strict ⊢
    nlinarith only [strict]
  have kept : keep n E b=true := by
    simpa only [keep,fast_correct idx,decide_eq_true_eq,sumHi,sumLo] using And.intro first left
  exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr idx,kept⟩,
    max_le (by omega) (clamp.trans upperMid),lb.trans_lt hiQ,loQ.trans ub⟩

/-- Uniform sufficient tests with a public discriminant at the lower midpoint.
At tolerance 2^400 a half-gap floor 2^983 suffices. At tolerance 2^437 a
floor 2^1020 suffices. Exact endpoint checks can admit additional bands. -/
theorem tolerances (n b E : ℕ) (order : leftHalf n (sumLo b E)≤sumHi b E/2)
    (separated : (E≤2^400 ∧ (2^983)^2≤(leftHalf n (sumLo b E))^2-n) ∨
                 (E≤2^435 ∧ (2^1018)^2≤(leftHalf n (sumLo b E))^2-n) ∨
                 (E≤2^437 ∧ (2^1020)^2≤(leftHalf n (sumLo b E))^2-n)) :
    upper n (sumHi b E)-lower n (sumLo b E)≤4*radius := by
  have span : sumHi b E/2-leftHalf n (sumLo b E)≤E := by
    unfold sumHi leftHalf sumLo
    omega
  have size : sumHi b E/2≤2^1024 := by unfold sumHi; omega
  rcases separated with ⟨err,gap⟩|⟨err,gap⟩|⟨err,gap⟩
  · have slope := width order gap (K:=2^41)
      (size.trans (by decide +kernel : (2:ℕ)^1024≤2^41*2^983))
    exact slope.trans ((Nat.mul_le_mul_left _ (span.trans err)).trans (by decide +kernel))
  · have slope := width order gap (K:=64)
      (size.trans (by decide +kernel : (2:ℕ)^1024≤64*2^1018))
    exact slope.trans ((Nat.mul_le_mul_left _ (span.trans err)).trans (by decide +kernel))
  · have slope := width order gap (K:=16)
      (size.trans (by decide +kernel : (2:ℕ)^1024≤16*2^1020))
    exact slope.trans ((Nat.mul_le_mul_left _ (span.trans err)).trans (by decide +kernel))

/-- Every promised larger factor occurs in the same bounded set associated to n,E. -/
def Covers (n E cap : ℕ) : Prop :=
    ∃ factors : Finset ℤ, factors.card≤cap ∧ ∀ p q : ℕ,
      p*q=n → p≤q → 2^1023≤q → q<2^1024 →
      (∃ b<647, SmoothSumSelector.candidate b≤p+q+E ∧ p+q≤SmoothSumSelector.candidate b+E) →
      (q:ℤ)∈factors

set_option maxRecDepth 5000 in
/-- A finite union of public root sets covers every balanced pair satisfying
the near-sum promise. The work charged here is one short-polynomial problem per
active band, with at most six integer roots to test per polynomial. -/
theorem sweep {n E : ℕ} (large : 2^2047≤n) (cop : n.Coprime 45360) (odd : Odd n)
    (fit : ∀ b∈active n E, upper n (sumHi b E)-lower n (sumLo b E)≤4*radius) :
    Covers n E (6*(active n E).card) := by
  classical
  let Band := {b // b∈active n E}
  have per (b : Band) := one_window large cop odd (fit b.val b.prop)
  choose F nz count root using per
  let factors (b : Band) := (F b).roots.toFinset.image fun x => (center n (sumLo b.val E) (sumHi b.val E):ℤ)+2*x
  refine ⟨Finset.univ.biUnion factors,?_,?_⟩
  · apply Finset.card_biUnion_le.trans
    calc
      _ ≤ ∑ _b : Band, 6 := Finset.sum_le_sum (fun b _ => Finset.card_image_le.trans (count b))
      _ = _ := by simp [Band,Nat.mul_comm]
  · intro p q pair order loQ hiQ promise
    obtain ⟨b,idx,lb,ub⟩ := promise
    have lo : sumLo b E≤p+q := by unfold sumLo; omega
    have hi : p+q≤sumHi b E := by unfold sumHi; omega
    have odds := Nat.odd_mul.mp (pair ▸ odd)
    let band : Band := ⟨b,active_of_sum pair order odds.1 odds.2 loQ hiQ idx lo hi⟩
    obtain ⟨x,atQ,_,zero⟩ := root band p q pair order (order.trans hiQ.le) lo hi
    exact Finset.mem_biUnion.mpr ⟨band,Finset.mem_univ _,Finset.mem_image.mpr
      ⟨x,Multiset.mem_toFinset.mpr ((Polynomial.mem_roots (nz band)).mpr zero),atQ.symm⟩⟩

/-- A compact certificate uses no square roots, factor labels or window
selection oracle. Iterate through the 647 candidate exponents and compare integers. -/
def gapCheck (n E G : ℕ) : Bool := (List.range 647).all fun b =>
  !(keep n E b) || decide (n+G^2≤((fastCenter b-E+1)/2)^2)

theorem certified_fit {n b : ℕ} (checked : gapCheck n (2^435) (2^1018)=true)
    (member : b∈active n (2^435)) :
    upper n (sumHi b (2^435))-lower n (sumLo b (2^435))≤4*radius := by
  obtain ⟨m,order,_⟩ := Finset.mem_filter.mp member
  obtain ⟨idx,kept⟩ := Finset.mem_filter.mp m
  apply tolerances _ _ _ order
  right; left
  refine ⟨le_rfl,?_⟩
  have h := List.all_eq_true.mp checked b (List.mem_range.mpr (Finset.mem_range.mp idx))
  simp only [kept,Bool.not_true,Bool.false_or,decide_eq_true_eq,fast_correct (Finset.mem_range.mp idx)] at h
  have up := Nat.pow_le_pow_left (le_max_left ((sumLo b (2^435)+1)/2) (ceilSqrt n)) 2
  change n+(2^1018)^2≤((sumLo b (2^435)+1)/2)^2 at h
  change (2^1018)^2≤(max ((sumLo b (2^435)+1)/2) (ceilSqrt n))^2-n
  omega

/-- Complete 2^435-error coverage from public arithmetic certificates. -/
theorem checked_sweep {n cap : ℕ} (large : 2^2047≤n) (cop : n.Coprime 45360) (odd : Odd n)
    (count : (menu n (2^435)).card≤cap) (checked : gapCheck n (2^435) (2^1018)=true) :
    Covers n (2^435) (6*cap) := by
  obtain ⟨f,h,all⟩ := sweep large cop odd (fun _ hb => certified_fit checked hb)
  have sizes : (active n (2^435)).card≤(menu n (2^435)).card :=
    Finset.card_le_card (Finset.filter_subset ..)
  exact ⟨f,h.trans (Nat.mul_le_mul_left _ (sizes.trans count)),all⟩

set_option maxRecDepth 14000 in
/-- Public-only arithmetic on both 2,048-bit controls. Using `sweep` these
counts allow 42 and 228 roots respectively over the entire near-sum family. -/
theorem controls :
    (menu ChebyshevQuarticScale.fresh (2^435)).card=7 ∧
    gapCheck ChebyshevQuarticScale.fresh (2^435) (2^1018)=true ∧
    (menu ChebyshevQuarticScale.crossed (2^435)).card=38 ∧
    gapCheck ChebyshevQuarticScale.crossed (2^435) (2^1018)=true := by
  decide +kernel

/-- Entire error families on the two published inputs, without any
assumption about where their hidden factors lie. Coverage is conditional only
on the stated near-sum promise. -/
theorem control_roots :
    Covers ChebyshevQuarticScale.fresh (2^435) 42 ∧ Covers ChebyshevQuarticScale.crossed (2^435) 228 :=
  ⟨checked_sweep (by decide +kernel) (by decide +kernel) (Nat.odd_iff.mpr (by decide +kernel))
     controls.1.le controls.2.1,
   checked_sweep (by decide +kernel) (by decide +kernel) (Nat.odd_iff.mpr (by decide +kernel))
     controls.2.2.1.le controls.2.2.2⟩

end PrimeFactors.NearSmoothSumWindows
