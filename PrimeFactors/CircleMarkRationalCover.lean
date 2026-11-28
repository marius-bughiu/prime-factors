import PrimeFactors.RootIntervalSlope
import PrimeFactors.CircleMarkWindows

/-! Sharp rectangular coverage of nonzero roots by signed ratios modulo a prime.
The first coordinate is the numerator and the second is the denominator. -/
namespace PrimeFactors.CircleMarkRationalCover

open Finset

/-- A positive numerator and denominator with their indicated budgets represent
the root up to sign. With denominator budget below the prime, every denominator
is invertible. -/
def Represents {p : ℕ} (r : ZMod p) (H D : ℕ) : Prop :=
  ∃ i ∈ Icc 1 H, ∃ j ∈ Icc 1 D,
    (i:ZMod p) = (j:ZMod p)*r ∨ (i:ZMod p) = -((j:ZMod p)*r)

def SquareHit (p : ℕ) (a : ℤ) (H D : ℕ) : Prop :=
  ∃ i ∈ Icc 1 H, ∃ j ∈ Icc 1 D, (i:ZMod p)^2 = (a:ZMod p)*(j:ZMod p)^2

/-- Evaluating the squared coordinates absorbs the choice between the two
signed representatives. -/
theorem square_iff {p : ℕ} [Fact p.Prime] {a : ℤ} {r : ZMod p}
    (root : r^2=(a:ZMod p)) (H D : ℕ) : SquareHit p a H D ↔ Represents r H D := by
  unfold SquareHit Represents
  simp only [←root,mul_comm (r^2),←mul_pow,sq_eq_sq_iff_eq_or_eq_neg]

/-- The bounded-slope theorem gives a signed numerator of magnitude at most
floor(p/(D+1)). Its congruence is nonzero because the denominator is a unit. -/
theorem cover {p H D : ℕ} [hp : Fact p.Prime] (dp : 0<D) (short : D<p)
    (area : p<(H+1)*(D+1)) (r : ZMod p) (nz : r≠0) : Represents r H D := by
  obtain ⟨j,jp,jd,m,bound⟩ := boundedSlope_exists p D r.val hp.out.pos dp
  let v : ℤ := j*r.val-(p:ℤ)*m
  change |v| * ((D:ℤ)+1)≤p at bound
  have area' : (p:ℤ)<((H:ℤ)+1)*((D:ℤ)+1) := by exact_mod_cast area
  have close := lt_of_mul_lt_mul_right (bound.trans_lt area') (by positivity : 0≤(D:ℤ)+1)
  have mag : v.natAbs≤H := by
    exact_mod_cast (show (v.natAbs:ℤ)≤H by rw [Int.natCast_natAbs]; omega)
  have eqn : (v:ZMod p)=(j:ZMod p)*r := by simp [v]
  have jnz : (j:ZMod p)≠0 := fun h => Nat.not_dvd_of_pos_of_lt jp (jd.trans_lt short)
    ((ZMod.natCast_zmod_eq_zero_iff_dvd ..).mp h)
  have vn : v≠0 := by intro zero; exact mul_ne_zero jnz nz (by simpa [zero] using eqn.symm)
  refine ⟨v.natAbs,mem_Icc.mpr ⟨Int.natAbs_pos.mpr vn,mag⟩,j,mem_Icc.mpr ⟨jp,jd⟩,?_⟩
  rcases le_or_gt 0 v with pos|neg
  · left
    have h : (v.natAbs:ℤ)=v := (Int.natCast_natAbs _).trans (abs_of_nonneg pos)
    rw [←eqn]
    simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z:ZMod p)) h
  · right
    have h : (v.natAbs:ℤ) = -v := (Int.natCast_natAbs _).trans (abs_of_neg neg)
    simpa only [←eqn,Int.cast_neg,Int.cast_natCast] using congrArg (fun z : ℤ => (z:ZMod p)) h

/-- When the grid of endpoints fits inside p residues, the successive positive
multiples of H+1 all lie between H+1 and p-H-1. -/
theorem missed {p H D : ℕ} [NeZero p] (dp : 0<D) (area : (H+1)*(D+1)≤p) :
    ((H+1:ℕ):ZMod p)≠0 ∧ ¬Represents ((H+1:ℕ):ZMod p) H D := by
  have bound : D*(H+1)+H+1≤p := by nlinarith only [area]
  have base : H+1≤D*(H+1) := Nat.le_mul_of_pos_left _ dp
  constructor
  · intro h
    apply Nat.not_dvd_of_pos_of_lt (by omega : 0<H+1) (by omega : H+1<p)
    exact (ZMod.natCast_zmod_eq_zero_iff_dvd ..).mp h
  · rintro ⟨i,hi,j,hj,same|neg⟩
    all_goals
      obtain ⟨ip,ih⟩ := mem_Icc.mp hi
      obtain ⟨jp,jd⟩ := mem_Icc.mp hj
      have jb := Nat.mul_le_mul_right (H+1) jd
      have jl := Nat.le_mul_of_pos_left (H+1) jp
    · rw [←Nat.cast_mul] at same
      have eq := congrArg ZMod.val same
      rw [ZMod.val_natCast_of_lt (by omega),ZMod.val_natCast_of_lt (by omega)] at eq
      omega
    · have zero : ((i+j*(H+1):ℕ):ZMod p)=0 := by push_cast; push_cast at neg; rw [neg]; simp
      exact Nat.not_dvd_of_pos_of_lt (by omega : 0 < i+j*(H+1)) (by omega : i+j*(H+1)<p)
        ((ZMod.natCast_zmod_eq_zero_iff_dvd ..).mp zero)

/-- The strict endpoint inequality is necessary and sufficient. -/
theorem universal_iff {p H D : ℕ} [Fact p.Prime] (dp : 0<D) (short : D<p) :
    (∀ r : ZMod p, r≠0 → Represents r H D) ↔ p<(H+1)*(D+1) := by
  refine ⟨fun all => ?_,fun area => cover dp short area⟩
  by_contra! small
  obtain ⟨nz,absent⟩ := missed dp small
  exact absent (all _ nz)

/-- At a specified denominator budget, the numerator threshold is an integer
quotient. In a square grid it is the integer square root. -/
theorem height_iff {p H D : ℕ} [Fact p.Prime] (dp : 0<D) (short : D<p) :
    (∀ r : ZMod p, r≠0 → Represents r H D) ↔ p/(D+1)≤H := by
  rw [universal_iff dp short,←Nat.div_lt_iff_lt_mul (by omega : 0<D+1)]
  omega

theorem side_iff {p b : ℕ} [Fact p.Prime] (pos : 0<b) (short : b<p) :
    (∀ r : ZMod p, r≠0 → Represents r b b) ↔ p.sqrt≤b := by
  rw [universal_iff pos short,←Nat.sqrt_lt]
  omega

/-- Giving the two lists a total of s entries can achieve the largest area
with lengths floor(s/2) and ceil(s/2). Both lengths are positive and below p
in the stated range. -/
theorem list_budget {p s : ℕ} [Fact p.Prime] (low : 2≤s) (short : (s+1)/2<p) :
    (∃ H D : ℕ, 0<H ∧ 0<D ∧ D<p ∧ H+D≤s ∧
      ∀ r : ZMod p, r≠0 → Represents r H D) ↔ 4*(p+1)≤(s+2)^2 := by
  constructor
  · rintro ⟨H,D,_,dp,ds,total,all⟩
    have area := (universal_iff dp ds).mp all
    have square : 4*((H+1)*(D+1))≤(H+D+2)^2 := by
      exact_mod_cast (show 4*(((H:ℤ)+1)*(D+1))≤(H+D+2)^2 by nlinarith only [sq_nonneg ((H:ℤ)-D)])
    exact (Nat.mul_le_mul_left 4 area).trans (square.trans (Nat.pow_le_pow_left (by omega) 2))
  · intro area
    let H := s/2
    let D := (s+1)/2
    have sum : H+D=s := by dsimp [H,D]; omega
    refine ⟨H,D,by dsimp [H]; omega,by dsimp [D]; omega,short,sum.le,
      (universal_iff (p:=p) (H:=H) (D:=D) (by dsimp [D]; omega) short).mpr ?_⟩
    have parity : D=H ∨ D=H+1 := by dsimp [H,D]; omega
    rcases parity with eq|eq <;> rw [←sum,eq] at area <;> rw [eq] <;> nlinarith only [area]

/-- Even the best aspect ratio spends at least floor(p/2) scalar cells when
it guarantees every root. The one-denominator search attains the bound. -/
theorem scalar_budget {p H D : ℕ} [hp : Fact p.Prime] (hpos : 0<H) (dpos : 0<D)
    (short : D<p) (all : ∀ r : ZMod p, r≠0 → Represents r H D) :
    p/2≤H*D ∧ ∀ r : ZMod p, r≠0 → Represents r (p/2) 1 := by
  have area := (universal_iff dpos short).mp all
  have hH : H=H-1+1 := by omega
  have hD : D=D-1+1 := by omega
  have room : H+D≤H*D+1 := by
    conv_lhs => rw [hH,hD]
    conv_rhs => rw [hH,hD]
    nlinarith only [Nat.zero_le ((H-1)*(D-1))]
  have cap : p<2*(H*D+1) := by nlinarith only [area,room]
  exact ⟨by omega,(height_iff (p:=p) (H:=p/2) (D:=1) (by decide) hp.out.one_lt).mpr (le_refl _)⟩

/-- Every nonzero root at p is realized by a target with Jacobi sign minus one
at the fixed product. This allows the necessity statement to use genuine targets. -/
theorem realize {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (diff : p≠q) (oq : q≠2) {r : ZMod p} (nz : r≠0) :
    ∃ a : ℤ, jacobiSym a (p*q)= -1 ∧ legendreSym p a=1 ∧
      legendreSym q a= -1 ∧ r^2=(a:ZMod p) := by
  obtain ⟨b,ns⟩ := FiniteField.exists_nonsquare (F:=ZMod q) (by rwa [ZMod.ringChar_zmod_n])
  let e := ZMod.chineseRemainder ((Nat.coprime_primes hp.out hq.out).mpr diff)
  let w := e.symm (r^2,b)
  let a : ℤ := w.val
  have back : (a:ZMod (p*q))=w := by simp [a]
  have h := congrArg e back
  rw [map_intCast] at h
  have both : ((a:ZMod p),(a:ZMod q))=(r^2,b) := by simpa only [w,RingEquiv.apply_symm_apply] using h
  have left : (a:ZMod p)=r^2 := congrArg Prod.fst both
  have right : (a:ZMod q)=b := congrArg Prod.snd both
  have lp := (legendreSym.eq_one_iff p (left ▸ pow_ne_zero 2 nz)).mpr
    ((isSquare_iff_exists_sq _).mpr ⟨r,left⟩)
  have lq := (legendreSym.eq_neg_one_iff q).mpr (right ▸ ns)
  refine ⟨a,?_,lp,lq,left.symm⟩
  rw [jacobiSym.mul_right' _ hp.out.ne_zero hq.out.ne_zero,
    ←jacobiSym.legendreSym.to_jacobiSym,←jacobiSym.legendreSym.to_jacobiSym,lp,lq,one_mul]

/-- At fixed square-side prime p the same threshold is exact for the entire
population of negative-Jacobi targets with this orientation. -/
theorem targets_iff {p q H D : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (diff : p≠q) (oq : q≠2) (dp : 0<D) (short : D<p) :
    (∀ a : ℤ, jacobiSym a (p*q)= -1 → legendreSym p a=1 → SquareHit p a H D) ↔
      p<(H+1)*(D+1) := by
  rw [←universal_iff dp short]
  constructor
  · intro all r nz
    obtain ⟨a,neg,square,_,eq⟩ := realize diff oq nz
    exact (square_iff eq H D).mp (all a neg square)
  · intro all a _ square
    have nz : (a:ZMod p)≠0 := by
      intro h
      rw [legendreSym, h,quadraticChar_zero] at square
      contradiction
    obtain ⟨r,eq⟩ := (isSquare_iff_exists_sq _).mp ((legendreSym.eq_one_iff p nz).mp square)
    exact (square_iff eq.symm H D).mpr (all r (fun h => nz (by simp [eq,h])))

/-- At p=11, the 2-by-2 rectangle misses root 3. Adding one denominator
guarantees every nonzero root. The corresponding target 20 is negative at 77. -/
theorem seventy_seven :
    jacobiSym 20 77= -1 ∧ ¬Represents (3:ZMod 11) 2 2 ∧
      (∀ r : ZMod 11, r≠0 → Represents r 2 3) ∧
      ¬SquareHit 11 20 2 2 ∧ SquareHit 11 20 2 3 := by
  letI : Fact (Nat.Prime 11) := ⟨by decide⟩
  have noHit : ¬Represents (3:ZMod 11) 2 2 := (missed (p:=11) (H:=2) (D:=2) (by decide) (by decide)).2
  have all := (universal_iff (p:=11) (H:=2) (D:=3) (by decide) (by decide)).mpr (by decide)
  have eq : (3:ZMod 11)^2=(20:ℤ) := by decide
  exact ⟨by norm_num,noHit,all,fun hit => noHit ((square_iff eq 2 2).mp hit),
    (square_iff eq 2 3).mpr (all 3 (by decide))⟩

end PrimeFactors.CircleMarkRationalCover
