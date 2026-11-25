import PrimeFactors.OffsetFactorProjection
import PrimeFactors.ShiftedOffsetBase

namespace PrimeFactors.OffsetCoordinateMultiplicity

open OffsetFactorProjection

set_option exponentiation.threshold 4096
set_option maxRecDepth 10000

/-- The trial d need not divide N. After moving to the right endpoint c
of a block of width at most sqrt(H)/4, its sharp vector remains strictly
inside squared-norm radius 2c sqrt(H) in the endpoint metric. -/
theorem endpoint_short {T H d c s v : ℤ} (hp : 0<H) (dp : 0<d) (right : d≤c)
    (width : 16*(c-d)^2≤H) (sp : 0≤s) (aspect : s≤2*v)
    (short : 3*(R d T H s v)^2≤4*d^2*H) : (R c T H s v)^2<4*c^2*H := by
  let a := d*s-T*v
  let u := (c-d)*s
  have err : 4*u^2≤H*v^2 := by
    have sc := pow_le_pow_left₀ sp aspect 2
    have sw := mul_le_mul_of_nonneg_left sc (sq_nonneg (c-d))
    have vv := mul_le_mul_of_nonneg_right width (sq_nonneg v)
    dsimp [u]
    nlinarith only [sw,vv]
  have split : c*s-T*v=a+u := by dsimp [a,u]; ring
  have move : 3*R c T H s v≤5*R d T H s v := by
    unfold R
    rw [split]
    change 3*((a+u)^2+H*v^2)≤5*(a^2+H*v^2)
    nlinarith only [sq_nonneg (2*a-3*u),err,mul_nonneg hp.le (sq_nonneg v)]
  have nonneg : 0≤3*R c T H s v := by unfold R; positivity
  have sq := pow_le_pow_left₀ nonneg move 2
  have hi := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ dp.le right 2) hp.le
  nlinarith only [sq,short,hi,mul_pos (sq_pos_of_pos (dp.trans_le right)) hp]

/-- In a reduced binary Gram matrix, the open disk of squared radius
twice the square root of its determinant has only three possible primitive
directions: the two basis vectors and the shorter of their two diagonals. -/
theorem three_directions {A B C i j F : ℤ} (positive : 0<A) (ordered : A≤C)
    (reduced : |2*B|≤A) (prim : IsCoprime i j)
    (norm : F=A*i^2+2*B*i*j+C*j^2) (short : F^2<4*(A*C-B^2)) :
    (|i|=1 ∧ j=0) ∨ (i=0 ∧ |j|=1) ∨ (|j|=1 ∧ i=if B≤0 then j else -j) := by
  have cut : F<A+C := by
    apply lt_of_not_ge
    intro bad
    have sq := pow_le_pow_left₀ (by omega : 0≤A+C) bad 2
    nlinarith only [sq,short,sq_nonneg (A-C),sq_nonneg B]
  have bound : |2*B*i*j|≤A*|i| * |j| := by
    rw [abs_mul,abs_mul]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right reduced (abs_nonneg _)) (abs_nonneg _)
  have cross := (neg_le_neg bound).trans (neg_abs_le (2*B*i*j))
  have major : A*(2*|i|-|j|)^2+(4*C-A)*|j|^2≤4*F := by
    nlinarith only [norm,cross,sq_abs i,sq_abs j,
      congrArg (fun t:ℤ => A*t) (sq_abs i),congrArg (fun t:ℤ => C*t) (sq_abs j)]
  have jb : |j|≤1 := by
    by_contra! bad
    have four := pow_le_pow_left₀ (by decide : (0:ℤ)≤2) (show 2≤|j| by omega) 2
    have lower := mul_le_mul_of_nonneg_left four (show 0≤4*C-A by omega)
    nlinarith only [major,lower,cut,ordered,positive,mul_nonneg positive.le (sq_nonneg (2*|i|-|j|))]
  by_cases zero : j=0
  · left
    rw [zero] at prim
    have unit := isCoprime_zero_right.mp prim
    rcases Int.isUnit_iff.mp unit with e|e <;> simp [e,zero]
  have jo : j=1 ∨ j= -1 := by rw [abs_le] at jb; omega
  have abj : |j|=1 := by rcases jo with e|e <;> simp [e]
  have ib : |i|≤1 := by
    by_contra! bad
    have diff : A*|i|≤A*(|i|^2-1) := by
      apply mul_le_mul_of_nonneg_left _ positive.le
      nlinarith only [sq_nonneg (|i|-2),show 2≤|i| by omega]
    rw [abj,mul_one] at cross
    rw [sq_abs i] at diff
    rcases jo with e|e <;> rw [e] at norm cross <;> nlinarith only [diff,norm,cross,cut]
  by_cases iz : i=0
  · exact Or.inr (Or.inl ⟨iz,abj⟩)
  right;right
  refine ⟨abj,?_⟩
  have io : i=1 ∨ i= -1 := by rw [abs_le] at ib; omega
  rcases io with e|e <;> rcases jo with f|f <;> rw [e,f] at norm ⊢ <;>
    split <;> rename_i sign <;> first | decide | exfalso; nlinarith only [cut,norm,sign]

/-- A basis satisfying the public checks always exists. A shortest vector
and its nearest Bézout complement give the usual Gauss-reduced basis. -/
theorem exists_reduced (T : ℤ) {H c : ℤ} (hp : 0<H) (cp : 0<c) :
    ∃ a b u w : ℤ, a*w-b*u=1 ∧ R c T H a b≤R c T H u w ∧
      |2*((c*a-T*b)*(c*u-T*w)+H*b*w)|≤R c T H a b := by
  let N := T^2+H
  have det : c^2*N-(c*T)^2=c^2*H := by dsimp [N];ring
  have form := gram_form (N:=N) (T:=T) (h:=H) rfl c
  obtain ⟨a,b,apos,best,⟨x,y,bez⟩,_⟩ := ReducedOffsetMinimum.exists_minimum
    (sq_pos_of_pos cp) (mul_pos (sq_pos_of_pos cp) hp) det
  let A := R c T H a b
  let B := (c*a-T*b)*(c*(-y)-T*x)+H*b*x
  have pos : 0<A := by change 0<R c T H a b; rwa [form]
  let k := (A-2*B)/(2*A)
  let u := -y+k*a
  let w := x+k*b
  have basis : a*w-b*u=1 := by dsimp [u,w];linear_combination bez
  have independent : u≠0 ∨ w≠0 := by
    by_cases un : u=0
    · right; intro wn; simp [un,wn] at basis
    · exact Or.inl un
  have bpos := ReducedOffsetMinimum.positive (sq_pos_of_pos cp) (mul_pos (sq_pos_of_pos cp) hp)
    det independent
  have red : |2*(B+k*A)|≤A := by
    have positive : 0<2*A := by omega
    have lo := Int.emod_nonneg (A-2*B) positive.ne'
    have hi := Int.emod_lt_of_pos (A-2*B) positive
    have modEq := Int.emod_add_ediv (A-2*B) (2*A)
    change (A-2*B)%(2*A)+(2*A)*k=A-2*B at modEq
    rw [abs_le]
    constructor <;> nlinarith only [modEq,lo,hi]
  have moved : (c*a-T*b)*(c*u-T*w)+H*b*w=B+k*A := by dsimp [A,B,u,w,R];ring
  exact ⟨a,b,u,w,basis,by rw [form,form]; exact best u w bpos,by rw [moved]; exact red⟩

/-- A reduced basis with oriented determinant one selects a fixed triple
for the whole interval. The columns (a,b),(u,w) need only be computed at
c; the factor d and its candidate (s,v) need not be used in basis choice. -/
theorem block_selector {T H d c s v a b u w : ℤ} (hp : 0<H) (dp : 0<d) (right : d≤c)
    (width : 16*(c-d)^2≤H) (sp : 0≤s) (aspect : s≤2*v) (prim : IsCoprime s v)
    (sharp : 3*(R d T H s v)^2≤4*d^2*H)
    (basis : a*w-b*u=1) (ordered : R c T H a b≤R c T H u w)
    (reduced : |2*((c*a-T*b)*(c*u-T*w)+H*b*w)|≤R c T H a b) :
    let B := (c*a-T*b)*(c*u-T*w)+H*b*w
    ∃ i j : ℤ, s=i*a+j*u ∧ v=i*b+j*w ∧
      ((|i|=1 ∧ j=0) ∨ (i=0 ∧ |j|=1) ∨ (|j|=1 ∧ i=if B≤0 then j else -j)) := by
  intro B
  let i := w*s-u*v
  let j := a*v-b*s
  have si : s=i*a+j*u := by dsimp [i,j]; linear_combination -s*basis
  have vi : v=i*b+j*w := by dsimp [i,j]; linear_combination -v*basis
  have primitive : IsCoprime i j := by
    obtain ⟨y,z,bez⟩ := prim
    refine ⟨y*a+z*b,y*u+z*w,?_⟩
    rw [si,vi] at bez
    linear_combination bez
  let A := R c T H a b
  let C := R c T H u w
  have positive : 0<A := by
    change 0<(c*a-T*b)^2+H*b^2
    by_cases bn : b=0
    · have an : a≠0 := by intro eq; simp [bn,eq] at basis
      simpa [bn] using sq_pos_of_ne_zero (mul_ne_zero (dp.trans_le right).ne' an)
    · exact add_pos_of_nonneg_of_pos (sq_nonneg _) (mul_pos hp (sq_pos_of_ne_zero bn))
  have gram : A*C-B^2=c^2*H := calc
    _ = c^2*H*(a*w-b*u)^2 := by dsimp [A,B,C,R]; ring
    _ = _ := by rw [basis];ring
  have metric : R c T H s v=A*i^2+2*B*i*j+C*j^2 := by
    conv_lhs => rw [si,vi]
    dsimp [A,B,C,R]
    ring
  exact ⟨i,j,si,vi,three_directions positive ordered reduced primitive metric
    (by rw [gram]; simpa only [mul_assoc] using endpoint_short hp dp right width sp aspect sharp)⟩

/-- A real factor with a winning trace obeys the block's sharp cleared
inequality. This algebra uses neither a primality oracle nor rounding. -/
theorem factor_short {p q s v j T H : ℤ} (root : p*q=T^2+H)
    (label : j+2*T*s*v=p*s^2+q*v^2) (sharp : 3*j^2≤4*H) :
    3*(R p T H s v)^2≤4*p^2*H := by
  have repr : R p T H s v=p*j := by
    unfold R
    linear_combination -v^2*root-p*label
  rw [repr]
  nlinarith only [mul_le_mul_of_nonneg_left sharp (sq_nonneg p)]

/-- Every such target allows a block of width 2^510, including shifted
products extremely close to a square. -/
theorem target_block_width {N : ℕ} (large : 2^1023≤N.sqrt) (nonsquare : N.sqrt^2<N) :
    16*((2:ℕ)^510)^2 ≤ N-(N.sqrt-1)^2 := by
  have one : 1≤N.sqrt := (by decide +kernel : 1≤(2:ℕ)^1023).trans large
  obtain ⟨_,lo,_⟩ := ShiftedOffsetBase.parameters one nonsquare
  have eq : 16*((2:ℕ)^510)^2=2*2^1023 := by decide +kernel
  omega

/-- If the block contains the smaller prime, one of its three public
directions gives an actual factor-revealing position of the shifted search. -/
theorem winning_chart {p q : ℕ} (pp : p.Prime) (qp : q.Prime) (ord : p<q)
    (balance : q≤2*p) (large : 17≤p) (c a b u w : ℤ) :
    let N := p*q
    let T := N.sqrt-1
    let H := N-T^2
    let B := (c*a-T*b)*(c*u-T*w)+(H:ℤ)*b*w
    (p:ℤ)≤c → 16*(c-p)^2≤H → a*w-b*u=1 →
    R c T H a b≤R c T H u w → |2*B|≤R c T H a b →
    ∃ j s v : ℕ, CompleteOffsetSearch.InSchedule T H j (s*v) ∧
      (CompleteOffsetSearch.probe N T j (s*v)=some p ∨ CompleteOffsetSearch.probe N T j (s*v)=some q) ∧
      ∃ i l : ℤ, (s:ℤ)=i*a+l*u ∧ (v:ℤ)=i*b+l*w ∧
        ((|i|=1 ∧ l=0) ∨ (i=0 ∧ |l|=1) ∨ (|l|=1 ∧ i=if B≤0 then l else -l)) := by
  intro N T H B right narrow basis ordered reduced
  obtain ⟨j,s,v,vp,_,aspect,prim,label,sharp,schedule,hit⟩ :=
    ShiftedOffsetBase.complete_balanced pp qp ord balance large
  change j+2*T*(s*v)=p*s^2+q*v^2 at label
  change 3*j^2≤4*H at sharp
  have floor : T^2≤N := (Nat.pow_le_pow_left (Nat.sub_le N.sqrt 1) 2).trans (Nat.sqrt_le' N)
  have product : p*q=T^2+H := (Nat.add_sub_of_le floor).symm
  have det : (p:ℤ)*q=(T:ℤ)^2+H := by exact_mod_cast product
  have rep : (j:ℤ)+2*T*s*v=(p:ℤ)*s^2+(q:ℤ)*v^2 := by
    rw [mul_assoc (2*(T:ℤ))]
    exact_mod_cast label
  have Hp : 0<H := by
    have jp := schedule.1
    by_contra! zero
    have one : 1≤j^2 := Nat.one_le_pow _ _ jp
    omega
  have primitive : IsCoprime (s:ℤ) (v:ℤ) := by
    apply Int.isCoprime_iff_gcd_eq_one.mpr
    simpa [Int.gcd] using prim.gcd_eq_one
  exact ⟨j,s,v,schedule,hit,block_selector (by exact_mod_cast Hp) (by exact_mod_cast pp.pos)
    right narrow (Nat.cast_nonneg s) (by exact_mod_cast aspect) primitive
    (factor_short det rep (by exact_mod_cast sharp)) basis ordered reduced⟩

/-- Three directions can actually occur in one block of prime trials for
a same-width semiprime. At d=263 both short directions give integral
offsets, while at d=257 the third is short at a trial prime not dividing N. -/
theorem sharp_example :
    (263:ℕ).Prime ∧ (467:ℕ).Prime ∧ (257:ℕ).Prime ∧ 263*467=(122821:ℕ) ∧
    122821=349^2+(1020:ℕ) ∧ 16*(263-257)^2≤(1020:ℤ) ∧
    3*(R 263 349 1020 1 1)^2≤4*263^2*1020 ∧
    3*(R 263 349 1020 4 3)^2≤4*263^2*1020 ∧
    3*(R 257 349 1020 3 2)^2≤4*257^2*1020 ∧ ¬(257:ℕ)∣122821 := by decide +kernel

/-- A public guide that is sufficiently short makes every rounded-short
primitive direction at this trial coincide with it. Only the guide and
product data are needed to check the strict inequality. -/
def Thin (T H J a b d : ℤ) : Prop := J*R d T H a b<d*H

theorem unique_at_trial {T H J d : ℤ} {x y : ℕ × ℕ} (hp : 0<H) (dp : 0<d)
    (xp : 0<x.1) (primitive : x.1.Coprime x.2) (yp : y.1.Coprime y.2)
    (guide : Thin T H J x.1 x.2 d) (trial : R d T H y.1 y.2≤d*J) : x=y := by
  let N := T^2+H
  have gram := gram_form (N:=N) (T:=T) (h:=H) rfl d
  have det : d^2*N-(d*T)^2=d^2*H := by dsimp [N];ring
  have pos := ReducedOffsetMinimum.positive (sq_pos_of_pos dp) (mul_pos (sq_pos_of_pos dp) hp) det
    (Or.inl (show (x.1:ℤ)≠0 by exact_mod_cast xp.ne') : (x.1:ℤ)≠0 ∨ (x.2:ℤ)≠0)
  apply OffsetShortVectors.unique_of_thin (J:=d*J) det (mul_pos (sq_pos_of_pos dp) hp)
    xp primitive yp pos (by rwa [←gram])
  rw [←gram]
  exact (show R d T H x.1 x.2*(d*J)<d^2*H by
    have scale := mul_lt_mul_of_pos_left guide dp
    unfold Thin at scale
    nlinarith only [scale])

/-- The integral strict test is a closed quadratic inequality after adding
one to the constant term. The return value is the exact inclusive interval;
a negative discriminant produces no interval. -/
def guideWindow (T H J a b : ℤ) : Option (ℤ × ℤ) :=
  let A := J*a^2
  let C := 2*J*a*T*b+H
  let D := C^2-4*A*(J*(T^2+H)*b^2+1)
  if D<0 then none else
    let r : ℤ := D.toNat.sqrt
    some (-((r-C)/(2*A)),(C+r)/(2*A))

theorem guideWindow_iff {T H J a b d : ℤ} (jp : 0<J) (ap : 0<a) :
    Thin T H J a b d ↔ ∃ l r, guideWindow T H J a b=some (l,r) ∧ l≤d ∧ d≤r := by
  let A := J*a^2
  let C := 2*J*a*T*b+H
  let D := C^2-4*A*(J*(T^2+H)*b^2+1)
  have pos : 0<A := mul_pos jp (sq_pos_of_pos ap)
  have eq : (2*A*d-C)^2-D=4*A*(J*R d T H a b-d*H+1) := by dsimp [A,C,D,R];ring
  have cut : Thin T H J a b d ↔ (2*A*d-C)^2≤D := by
    unfold Thin
    constructor
    · intro hit
      have nonpos : J*R d T H a b-d*H+1≤0 := by omega
      linarith only [eq,mul_nonpos_of_nonneg_of_nonpos (by positivity : 0≤4*A) nonpos]
    · intro small
      have nonpos : 4*A*(J*R d T H a b-d*H+1)≤0 := by linarith only [eq,small]
      by_contra! contrary
      have factor : 0<J*R d T H a b-d*H+1 := by omega
      exact not_lt_of_ge nonpos (mul_pos (by positivity) factor)
  unfold guideWindow
  change Thin T H J a b d ↔ ∃ l r, (if D<0 then none else
    some (-(((D.toNat.sqrt:ℤ)-C)/(2*A)),(C+(D.toNat.sqrt:ℤ))/(2*A)))=some (l,r) ∧ l≤d ∧ d≤r
  by_cases neg : D<0
  · simp [neg,cut,not_le_of_gt (neg.trans_le (sq_nonneg (2*A*d-C)))]
  let r : ℤ := D.toNat.sqrt
  have ds : 0≤D := by omega
  have sq : |2*A*d-C|≤r ↔ (2*A*d-C)^2≤D := by
    rw [←Int.natCast_natAbs]
    change ((2*A*d-C).natAbs:ℤ)≤(D.toNat.sqrt:ℤ) ↔ _
    rw [Int.ofNat_le,Nat.le_sqrt',←Int.ofNat_le]
    simp only [Nat.cast_pow,Int.natCast_natAbs,sq_abs,Int.toNat_of_nonneg ds]
  simp only [if_neg neg,Option.some.injEq,Prod.mk.injEq, cut,←sq,abs_le]
  have den : 0<2*A := by omega
  constructor
  · rintro ⟨lo,hi⟩
    refine ⟨-((r-C)/(2*A)),(C+r)/(2*A),⟨rfl,rfl⟩,?_,?_⟩
    · have neglo : -d≤(r-C)/(2*A) := (Int.le_ediv_iff_mul_le den).mpr (by nlinarith only [lo])
      omega
    · apply (Int.le_ediv_iff_mul_le den).mpr; nlinarith only [hi]
  · rintro ⟨_,_,⟨rfl,rfl⟩,lo,hi⟩
    change -((r-C)/(2*A))≤d at lo
    change d≤(C+r)/(2*A) at hi
    have left := (Int.le_ediv_iff_mul_le den).mp (show -d≤(r-C)/(2*A) by omega)
    have right := (Int.le_ediv_iff_mul_le den).mp hi
    constructor <;> nlinarith only [left,right]

/-- Strictly passing endpoints certify the full contiguous interval. -/
theorem thin_between {T H J a b l d r : ℤ} (jp : 0<J) (ap : 0<a)
    (left : Thin T H J a b l) (right : Thin T H J a b r) (low : l≤d) (high : d≤r) :
    Thin T H J a b d := by
  obtain ⟨lo,hi,w,hlo,_⟩ := (guideWindow_iff jp ap).mp left
  obtain ⟨lo',hi',w',_,hhi⟩ := (guideWindow_iff jp ap).mp right
  rw [w] at w'
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj w')
  exact (guideWindow_iff jp ap).mpr ⟨lo,hi,w,hlo.trans low,high.trans hhi⟩

/-- Every same-width target has a terminal one-direction region at the
shifted base. Intersect the given interval with the public factor range. -/
theorem terminal_2048 {N : ℕ} (size : 2^1023≤N.sqrt) (top : N.sqrt≤2^1024)
    (nonsquare : N.sqrt^2<N) {d : ℕ} (low : N.sqrt-2^767≤d) (high : d≤N.sqrt) :
    let T := N.sqrt-1
    let H := N-T^2
    Thin T H (CompleteOffsetWork.height H) 1 1 d := by
  intro T H
  have one : 1≤N.sqrt := (by decide +kernel : 1≤(2:ℕ)^1023).trans size
  obtain ⟨_,hlo,hhi⟩ := ShiftedOffsetBase.parameters one nonsquare
  change 2*T+2≤H at hlo
  change H≤4*T+3 at hhi
  have tr : T+1=N.sqrt := by dsimp [T]; omega
  let J := CompleteOffsetWork.height H
  have hmin : (2:ℕ)^1024≤H := by omega
  have hmax : H≤(2:ℕ)^1027 := by omega
  have dmin : 3*(2:ℕ)^1021≤d := by omega
  have jmin : (2:ℕ)^512≤J := Nat.le_sqrt'.mpr ((Nat.le_div_iff_mul_le (by decide : 0<3)).mpr
    ((by decide +kernel : ((2:ℕ)^512)^2*3≤4*2^1024).trans (Nat.mul_le_mul_left _ hmin)))
  have sharp : J^2*3≤4*H := (Nat.le_div_iff_mul_le (by decide : 0<3)).mp (Nat.sqrt_le' _)
  have linear : 3*2^512*J≤4*H := by
    have p := Nat.mul_le_mul_right J jmin
    change (2:ℕ)^512*J≤J*J at p
    nlinarith only [sharp,p]
  have diff : |(d:ℤ)-T|≤(2:ℤ)^767 := by rw [abs_le]; omega
  have sq := pow_le_pow_left₀ (abs_nonneg _) diff 2
  rw [sq_abs] at sq
  have mass : R d T H 1 1≤((2:ℤ)^767)^2+2^1027 := by
    have up : (H:ℤ)≤2^1027 := by exact_mod_cast hmax
    simpa [R] using add_le_add sq up
  have positive : (0:ℤ)<J := by exact_mod_cast (show 0<J by omega)
  have scale : 4*(((2:ℤ)^767)^2+2^1027)<(3*2^1021)*(3*2^512) := by decide +kernel
  have small := mul_lt_mul_of_pos_right scale positive
  have upper := mul_le_mul_of_nonneg_left mass (show 0≤4*(J:ℤ) by positivity)
  have combine := Nat.mul_le_mul dmin linear
  have lower : ((3*2^1021)*(3*2^512)*(J:ℤ))≤4*d*H := by
    have z : (3*(2:ℤ)^1021)*(3*2^512*J)≤(d:ℤ)*(4*H) := by exact_mod_cast combine
    linarith only [z]
  unfold Thin
  change (J:ℤ)*R d T H 1 1<d*H
  nlinarith only [upper,small,lower]

/-- The last `count` canonical blocks all have the unique diagonal guide.
The first trial of the immediately preceding block fails that strict test.
The final block is clipped at the floor root. -/
def ExactTerminalBlocks (N count : ℕ) : Prop :=
  let r := N.sqrt
  let T := r-1
  let H := N-T^2
  let J := CompleteOffsetWork.height H
  let L := max (2^1023) ((N+(2^1024-1)-1)/(2^1024-1))
  let size := H.sqrt/4+1
  let total := (r-L)/size+1
  let first := total-count
  L≤r ∧ 0<count ∧ count<total ∧ L+first*size≤r ∧
    (∀ d : ℕ, L+first*size≤d → d≤r → Thin T H J 1 1 d) ∧
    ¬Thin T H J 1 1 (L+(first-1)*size : ℕ)

private theorem terminal_receipt {N r j w count : ℕ} (root : r*r≤N ∧ N<(r+1)*(r+1))
    (data : let T := r-1; let H := N-T^2
      let L := max (2^1023) ((N+(2^1024-1)-1)/(2^1024-1))
      let size := w/4+1
      let total := (r-L)/size+1; let first := total-count
      (w*w≤H ∧ H<(w+1)*(w+1)) ∧ (j*j≤4*H/3 ∧ 4*H/3<(j+1)*(j+1)) ∧ 0<j ∧
      L≤r ∧ 0<count ∧ count<total ∧ L+first*size≤r ∧
        Thin T H j 1 1 (L+first*size : ℕ) ∧ Thin T H j 1 1 r ∧
        ¬Thin T H j 1 1 (L+(first-1)*size : ℕ)) : ExactTerminalBlocks N count := by
  obtain ⟨hw,hj,jp,lr,mc,tc,limit,start,finish,prior⟩ := data
  simp only [ExactTerminalBlocks,CompleteOffsetWork.height]
  rw [←Nat.eq_sqrt.mpr root,←Nat.eq_sqrt.mpr hw,←Nat.eq_sqrt.mpr hj]
  exact ⟨lr,mc,tc,limit,fun d lo hi => thin_between (by exact_mod_cast jp) (by decide)
    start finish (by exact_mod_cast lo) (by exact_mod_cast hi),prior⟩

/-- Product-only count of the entire diagonal-guide tail on the fresh control. -/
theorem fresh_terminal_blocks : ExactTerminalBlocks ChebyshevQuarticScale.fresh
    322537533297128465591124228217941482228644817259441712503951193542143179323003 := by
  apply terminal_receipt (r:=158327039176966334715448284019718823474497913662177975160442996009439310669941017429676080400185006424773254142252582891257193029659269227070095120289800339855421063931472090621260003180611046788905349147963313017385074143012442899089952314244753217806428276920663827209779196401916113023989449483782760844629)
    (j:=24350873940639364334886801085192646652213503525186672085206397727635074574986121348349144341028626654802843595248922622201743210614999263828009557158942871)
    (w:=21088475436946170177293322858894233201842577442313811554734593865242840916405710762970825629620750018996513065500828565982529173940327726168417894717339292)
  · decide +kernel
  · simp only [Thin]; decide +kernel

/-- Product-only count of the entire diagonal-guide tail on the crossed control. -/
theorem crossed_terminal_blocks : ExactTerminalBlocks ChebyshevQuarticScale.crossed
    316751388824517120243248164724408243952062625456987099170448113541960011955269 := by
  apply terminal_receipt (r:=135037911685235586269825030135549325391376915966798636179319977077209993450011760943044181307768476527897818717675959823440307553022185653953812606479930673789391793187765141283074720630433120513417190939648203494531748575804685158519937612233285802863014656458801051235008057526662884995918450838938076904614)
    (j:=21534690790390421013056024285375526729526579810281161584549924242069624343778029068870474089933516289576023308315319402177062351872558724660017617861963271)
    (w:=18649589287120896587260585695792769324517708808995476546683078473227218905354059182095063721930719344307773950181905103313937823527775626532266954264611144)
  · decide +kernel
  · simp only [Thin]; decide +kernel

/-- All three directions can survive the rounded, parity-adjusted height
even when each trial must be prime. For N=263*491 the true trial 263
uses two directions; the nondividing trial prime 269 supplies the third. -/
theorem three_rounded_prime_trials :
    (263:ℕ).Prime ∧ (491:ℕ).Prime ∧ (269:ℕ).Prime ∧ 263*491=(129133:ℕ) ∧
    129133=358^2+(969:ℕ) ∧ CompleteOffsetWork.height 969=35 ∧
    16*(269-262)^2≤(969:ℤ) ∧
    R 269 358 969 1 1 ≤ 269*34 ∧ R 263 358 969 3 2 = 263*35 ∧
    R 263 358 969 4 3 = 263*35 ∧ ¬(269:ℕ)∣129133 := by decide +kernel

end PrimeFactors.OffsetCoordinateMultiplicity
