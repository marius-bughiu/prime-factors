import PrimeFactors.AffineExcess
import PrimeFactors.AffineExcessSingle
import PrimeFactors.UniformDivisorCount
import PrimeFactors.ChebyshevPrimeSample
import PrimeFactors.FactorSum
import Mathlib.Data.Finset.Powerset

/-! Finite coverage of product-dependent weights a²N+b with positive intercept. -/
namespace PrimeFactors.AffineExcessPopulation
open Finset AffineExcess
set_option exponentiation.threshold 8192
set_option maxRecDepth 8192

abbrev Row := ℕ×ℕ
def name (t a b i : ℕ) : Row := (slope t a b i, correction t a b i)

noncomputable def menu (t K J : ℕ) : Finset Row :=
  (((Icc 1 K ×ˢ Icc 1 K) ×ˢ range J)).image (fun z => name t z.1.1 z.1.2 z.2)

private theorem menu_card (t K J : ℕ) : (menu t K J).card ≤ K*K*J := by
  apply card_image_le.trans
  simp

theorem in_menu {t a b i K J : ℕ} (ap : 0<a) (bp : 0<b) (ak : a≤K) (bk : b≤K) (ij : i<J) :
    name t a b i ∈ menu t K J := by
  exact mem_image.mpr ⟨((a,b),i),mem_product.mpr ⟨mem_product.mpr
    ⟨mem_Icc.mpr ⟨ap,ak⟩,mem_Icc.mpr ⟨bp,bk⟩⟩,mem_range.mpr ij⟩,rfl⟩

private theorem limits {t K J : ℕ} {r : Row} (h : r∈menu t K J) :
    0<r.2 ∧ r.2<K+24*J ∧ r.1<24*K*J := by
  obtain ⟨⟨⟨a,b⟩,i⟩,hw,rfl⟩ := mem_image.mp h
  obtain ⟨hab,hi⟩ := mem_product.mp hw
  obtain ⟨ha,hb⟩ := mem_product.mp hab
  obtain ⟨ap,ak⟩ := mem_Icc.mp ha
  obtain ⟨bp,bk⟩ := mem_Icc.mp hb
  obtain ⟨pos,cap,_,v⟩ := row_bounds (t:=t) ap bp ak bk (mem_range.mp hi)
  exact ⟨pos,cap,v⟩

def SquareAt (n : ℕ) (x y : Row) : Prop :=
  ∃ z:ℕ, z^2=excess n x.1 x.2*excess n y.1 y.2

def Regular (n : ℕ) (x y : Row) : Prop :=
  0<x.1 ∧ 0<y.1 ∧ 0<constant x.1 y.1 x.2 y.2 ∧ SquareAt n x y

private theorem swap {n : ℕ} {x y : Row} (h : Regular n x y) : Regular n y x := by
  obtain ⟨xp,yp,cp,z,sq⟩ := h
  refine ⟨yp,xp,?_,z,by simpa [mul_comm] using sq⟩
  simpa only [constant, ←Int.natAbs_neg (a:=((x.1:ℤ)*y.2^2-y.1*x.2^2)), neg_sub] using cp

def regularHit (K J n : ℕ) : Prop :=
  ∃ x∈menu (n%24) K J, ∃ y∈menu (n%24) K J, Regular n x y

private noncomputable def residues := (range 24).filter (·.Coprime 24)

private theorem member_residues {n : ℕ} (hn : n.Coprime 24) : n%24∈residues :=
  mem_filter.mpr ⟨mem_range.mpr (Nat.mod_lt _ (by decide)),(Nat.mod_modEq n 24).gcd_eq.trans hn⟩

private theorem coordinate_bound {n V D u v c d : ℕ} (hn : n<2^2048) (hu : u<V) (hv : v<V)
    (hc : c<D) (hd : d<D) :
    coordinate n u v c d ≤ 8*V^2*2^2048+2*V*D^2 := by
  have A := Nat.mul_le_mul (Nat.mul_le_mul hu.le hv.le) hn.le
  have B := Nat.mul_le_mul hu.le (Nat.pow_le_pow_left hd.le 2)
  have C := Nat.mul_le_mul hv.le (Nat.pow_le_pow_left hc.le 2)
  unfold coordinate
  nlinarith only [A,B,C]

private theorem tau_bound {V D T C : ℕ} (cp : 0<C) (cm : C<V*D^2)
    (sized : 2^14882*(V*D^2)^64<(T+1)^336) : (C^2).divisors.card≤T := by
  have lower := UniformDivisorCount.power_bound (pow_pos cp 2)
  rw [←pow_mul] at lower
  have bound := lower.trans (Nat.mul_le_mul_left (2^14882) (Nat.pow_le_pow_left cm.le 64))
  exact Nat.le_of_lt_succ ((Nat.pow_lt_pow_iff_left (by decide : 336≠0)).mp (bound.trans_lt sized))

/-- Unordered distinct choices of normalized rows are counted once in each of
the eight possible residues of N modulo 24. -/
theorem regular_products {K J H T : ℕ}
    (coord : 8*(24*K*J)^2*2^2048+2*(24*K*J)*(K+24*J)^2 < 2^H)
    (divisors : 2^14882*((24*K*J)*(K+24*J)^2)^64<(T+1)^336)
    (S : Finset ℕ) (members : ∀ n∈S, n<2^2048 ∧ n.Coprime 24 ∧ regularHit K J n) :
    S.card ≤ 4*(K*K*J)*(K*K*J-1)*(2*H*T) := by
  classical
  let cells (_t : ℕ) (w : Finset Row) := S.filter fun n =>
    ∃ x∈w, ∃ y∈w, Regular n x y
  let choices (t : ℕ) := (menu t K J).powersetCard 2
  have no_same {x y : Row} {n : ℕ} (h : Regular n x y) : x≠y := by
    intro eq
    subst y
    simpa [constant] using h.2.2.1
  have cover : S ⊆ residues.biUnion fun t => (choices t).biUnion (cells t) := by
    intro n hn
    obtain ⟨_,cop,x,hx,y,hy,hit⟩ := members n hn
    have ne := no_same hit
    have inP : {x,y}∈choices (n%24) := by
      apply mem_powersetCard.mpr
      exact ⟨insert_subset hx (singleton_subset_iff.mpr hy), by simp [ne]⟩
    exact mem_biUnion.mpr ⟨n%24,member_residues cop,mem_biUnion.mpr ⟨{x,y},inP,
      mem_filter.mpr ⟨hn,x,by simp,y,by simp,hit⟩⟩⟩
  have one (t : ℕ) (w : Finset Row) (hw : w∈choices t) : (cells t w).card≤2*H*T := by
    obtain ⟨sub,tw⟩ := mem_powersetCard.mp hw
    obtain ⟨x,y,_ne,rfl⟩ := card_eq_two.mp tw
    have hx : x∈menu t K J := sub (by simp)
    have hy : y∈menu t K J := sub (by simp)
    have get (n : ℕ) (hn : n∈cells t {x,y}) : Regular n x y := by
      obtain ⟨_,a,ha,b,hb,hit⟩ := mem_filter.mp hn
      have ne := no_same hit
      simp only [mem_insert,mem_singleton] at ha hb
      rcases ha with hax|hay <;> rcases hb with hbx|hby
      · exact (ne (hax.trans hbx.symm)).elim
      · rwa [hax,hby] at hit
      · rw [hay,hbx] at hit; exact swap hit
      · exact (ne (hay.trans hby.symm)).elim
    by_cases empty : (cells t {x,y}).Nonempty
    · obtain ⟨n,hn⟩ := empty
      obtain ⟨xp,yp,cp,_⟩ := get n hn
      obtain ⟨_,cx,ux⟩ := limits hx
      obtain ⟨_,cy,uy⟩ := limits hy
      have cb := constant_lt (by omega : 0<K+24*J) ux uy cx cy
      apply (fiber xp yp cp (cells t {x,y}) (fun n' h => (coordinate_bound
        (members n' (mem_filter.mp h).1).1 ux uy cx cy).trans_lt coord)
        (fun n' h => (get n' h).2.2.2)).trans
      exact Nat.mul_le_mul_left _ (tau_bound cp cb divisors)
    · rw [not_nonempty_iff_eq_empty.mp empty,card_empty]; exact Nat.zero_le _
  have pairs (t : ℕ) : ((choices t).biUnion (cells t)).card≤(K*K*J).choose 2*(2*H*T) := by
    apply (card_biUnion_le_card_mul _ _ _ (one t)).trans
    exact Nat.mul_le_mul_right _ ((card_powersetCard ..).le.trans (Nat.choose_le_choose _ (menu_card t K J)))
  have total := (card_le_card cover).trans (card_biUnion_le_card_mul _ _ _ (fun t _ => pairs t))
  have eight : residues.card=8 := by decide +kernel
  rw [eight,Nat.choose_two_right] at total
  have half := Nat.div_mul_le_self ((K*K*J)*(K*K*J-1)) 2
  exact total.trans (by
    have bound := Nat.mul_le_mul_right (4*(2*H*T)) half
    nlinarith only [bound])

/-- Both signs are tested, with z the nonnegative square root. -/
def Proper (n c d z : ℕ) : Prop :=
  (1<(z-c*d).gcd n ∧ (z-c*d).gcd n<n) ∨ (1<(z+c*d).gcd n ∧ (z+c*d).gcd n<n)

def successful (K J n : ℕ) : Prop :=
  ∃ x∈menu (n%24) K J, ∃ y∈menu (n%24) K J, ∃ z:ℕ,
    z^2=excess n x.1 x.2*excess n y.1 y.2 ∧ Proper n x.2 y.2 z

private theorem one_zero {p q c d v z D V : ℕ} (cp : 0<c) (cl : c<D) (dp : 0<d) (dl : d<D)
    (vp : 0<v) (vl : v<V)
    (square : z^2=excess (p*q) 0 c*excess (p*q) v d) (gcds : Proper (p*q) c d z) :
    AffineExcessSingle.SingleHit p q D V := by
  rw [show excess (p*q) 0 c=c^2 by simp [excess]] at square
  obtain ⟨w,rfl,eq⟩ := AffineExcessSingle.remove_square cp square
  refine ⟨c,d,v,w,cp,cl,dp,dl,vp,vl,?_,?_⟩
  · simpa only [excess,mul_assoc] using eq
  · simpa only [Proper,←Nat.mul_sub,←Nat.mul_add] using gcds

private theorem not_proportional {n u v c d z : ℕ} (cop : (2*c*d).Coprime n)
    (square : z^2=excess n u c*excess n v d) (gcds : Proper n c d z) : 0<constant u v c d := by
  by_contra! zero
  have hc := ((Nat.coprime_mul_iff_left.mp (Nat.coprime_mul_iff_left.mp cop).1).2).symm
  have eq := proportional hc (by omega) square
  have compare : c*d≤z := by
    apply (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp
    rw [mul_pow,square]
    exact Nat.mul_le_mul (Nat.le_add_left ..) (Nat.le_add_left ..)
  have minus := Nat.gcd_eq_right ((Nat.modEq_iff_dvd' compare).mp eq.symm)
  have plus := (eq.add_right (c*d)).gcd_eq
  rw [show c*d+c*d=2*c*d by ring,cop.gcd_eq_one] at plus
  rcases gcds with h|h <;> omega

theorem branches {p q X K J : ℕ} (pp : p.Prime) (qp : q.Prime) (px : X≤p) (qx : X≤q)
    (hp : 2<X) (small : K+24*J<X) (hit : successful K J (p*q)) :
    regularHit K J (p*q) ∨ AffineExcessSingle.SingleHit p q (K+24*J) (24*K*J) := by
  obtain ⟨x,hx,y,hy,z,square,gcds⟩ := hit
  obtain ⟨cx,cl,ul⟩ := limits hx
  obtain ⟨dy,dl,vl⟩ := limits hy
  have indiv (a : ℕ) (pos : 0<a) (low : a<X) : a.Coprime (p*q) := by
    apply Nat.coprime_mul_iff_right.mpr
    exact ⟨(pp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt pos (low.trans_le px))).symm,
      (qp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt pos (low.trans_le qx))).symm⟩
  have cop : (2*x.2*y.2).Coprime (p*q) := Nat.coprime_mul_iff_left.mpr
    ⟨Nat.coprime_mul_iff_left.mpr ⟨indiv 2 (by decide) hp,indiv x.2 cx (cl.trans small)⟩,
      indiv y.2 dy (dl.trans small)⟩
  have nz := not_proportional cop square gcds
  by_cases u : x.1=0
  · have vp : 0<y.1 := by
      by_contra! v
      simp [constant,u,show y.1=0 by omega] at nz
    exact Or.inr (one_zero cx cl dy dl vp vl (u ▸ square) gcds)
  by_cases v : y.1=0
  · refine Or.inr (one_zero (z:=z) dy dl cx cl (Nat.pos_of_ne_zero u) ul ?_ ?_)
    · rw [mul_comm,v] at square; exact square
    · simpa only [Proper,mul_comm y.2 x.2] using gcds
  exact Or.inl ⟨x,hx,y,hy,Nat.pos_of_ne_zero u,Nat.pos_of_ne_zero v,nz,z,square⟩

open MixedPrefixSample (X)

attribute [local irreducible] MixedPrefixSample.ordered MixedPrefixSample.primes MixedPrefixSample.X
private theorem sample_data {P : ℕ → Prop} {z : ℕ×ℕ} (hm : z∈MixedPrefixSample.sample P) :
    X≤z.1 ∧ z.1<2*X ∧ z.1.Prime ∧ X≤z.2 ∧ z.2<2*X ∧ z.2.Prime ∧ z.1<z.2 ∧ P (z.1*z.2) := by
  rw [MixedPrefixSample.sample,mem_filter] at hm
  obtain ⟨hp,hq,_,_,he⟩ := (MixedPrefixSample.mem_ordered (z:=z) (E:=P)).mp hm.1
  rw [MixedPrefixSample.primes,mem_filter,mem_Ico] at hp hq
  exact ⟨hp.1.1,hp.1.2,hp.2,hq.1.1,hq.1.2,hq.2,hm.2,he⟩

attribute [local irreducible] MixedPrefixSample.sample

private def W (K J H T : ℕ) := 4*(K*K*J)*(K*K*J-1)*(2*H*T)
private def Z (K J : ℕ) := let D:=K+24*J; let t:=(24*K*J-1).sqrt; X*(4*D*t+t*(t+1))

private theorem by_pairs {K J H T : ℕ}
    (coord : 8*(24*K*J)^2*2^2048+2*(24*K*J)*(K+24*J)^2 < 2^H)
    (divisors : 2^14882*((24*K*J)*(K+24*J)^2)^64<(T+1)^336)
    (S : Finset (ℕ×ℕ)) (members : ∀ a∈S, a.1.Prime ∧ a.2.Prime ∧ a.1<a.2 ∧
      a.1*a.2<2^2048 ∧ (a.1*a.2).Coprime 24 ∧ regularHit K J (a.1*a.2)) :
    S.card≤W K J H T := by
  classical
  let value (z : ℕ×ℕ) := z.1*z.2
  have injective : Set.InjOn value (S : Set (ℕ×ℕ)) := by
    intro a ha b hb eq
    obtain ⟨ap,_,ab,_⟩ := members a ha
    obtain ⟨bp,bq,bb,_⟩ := members b hb
    obtain ⟨e,f⟩ := ordered_semiprime_pair_unique bp bq bb.le ab.le ap.one_lt eq
    exact Prod.ext e f
  have equal : (S.image value).card=S.card := card_image_of_injOn injective
  refine le_trans equal.ge (regular_products coord divisors _ ?_)
  intro n hn
  obtain ⟨a,ha,rfl⟩ := mem_image.mp hn
  exact (members a ha).2.2.2

private theorem positive_count {K J H T : ℕ}
    (coord : 8*(24*K*J)^2*2^2048+2*(24*K*J)*(K+24*J)^2 < 2^H)
    (divisors : 2^14882*((24*K*J)*(K+24*J)^2)^64<(T+1)^336) :
    (MixedPrefixSample.sample (regularHit K J)).card≤W K J H T := by
  apply by_pairs coord divisors
  intro a ha
  obtain ⟨lp,up,pp,lq,uq,qp,pq,hit⟩ := sample_data (z:=a) (P:=regularHit K J) ha
  have big : 24<X := by decide +kernel
  have width : (2*X)*(2*X)=2^2048 := by decide +kernel
  have size := (Nat.mul_lt_mul_of_lt_of_le up uq.le (show 0<2*X by decide +kernel)).trans_eq width
  exact ⟨pp,qp,pq,size,
    Nat.coprime_mul_iff_left.mpr ⟨pp.coprime_iff_not_dvd.mpr
      (Nat.not_dvd_of_pos_of_lt (by decide) (big.trans_le lp)),
      qp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by decide) (big.trans_le lq))⟩,hit⟩

private theorem total_count {K J H T : ℕ} (small : K+24*J<X)
    (coord : 8*(24*K*J)^2*2^2048+2*(24*K*J)*(K+24*J)^2 < 2^H)
    (divisors : 2^14882*((24*K*J)*(K+24*J)^2)^64<(T+1)^336) :
    (MixedPrefixSample.sample (successful K J)).card ≤ W K J H T + Z K J := by
  classical
  let S := MixedPrefixSample.sample (successful K J)
  let A := MixedPrefixSample.sample (regularHit K J)
  let B := S \ A
  have transfer (z : ℕ×ℕ) (hz : z∈S) (pos : regularHit K J (z.1*z.2)) : z∈A := by
    change z∈MixedPrefixSample.sample _ at hz ⊢
    rw [MixedPrefixSample.sample,mem_filter] at hz ⊢
    obtain ⟨hp,hq,ne,lo,_⟩ := (MixedPrefixSample.mem_ordered (z:=z) (E:=successful K J)).mp hz.1
    exact ⟨(MixedPrefixSample.mem_ordered (E:=regularHit K J)).mpr ⟨hp,hq,ne,lo,pos⟩,hz.2⟩
  have singular : B.card ≤ Z K J := by
    apply (AffineExcessSingle.prime_pairs small MixedPrefixSample.primes B (fun p hp => ?_) (fun z hz => ?_)).trans
    · have width : MixedPrefixSample.primes.card≤X := by
        unfold MixedPrefixSample.primes
        apply (card_filter_le _ _).trans
        rw [Nat.card_Ico]
        omega
      exact Nat.mul_le_mul_right _ width
    · rw [MixedPrefixSample.primes,mem_filter,mem_Ico] at hp
      exact ⟨hp.2,hp.1.1⟩
    · obtain ⟨hS,hA⟩ := mem_sdiff.mp hz
      obtain ⟨lp,up,pp,lq,uq,qp,lt,hit⟩ := sample_data hS
      have one := (branches pp qp lp lq (by decide +kernel : 2<X) small hit).resolve_left
        (fun pos => hA (transfer z hS pos))
      exact ⟨by rw [MixedPrefixSample.primes,mem_filter,mem_Ico]; exact ⟨⟨lp,up⟩,pp⟩,qp,lt,uq,one⟩
  have cover : S⊆A∪B := by
    intro z hz; by_cases h : z∈A
    · exact mem_union_left _ h
    · exact mem_union_right _ (mem_sdiff.mpr ⟨hz,h⟩)
  exact (card_le_card cover).trans ((card_union_le _ _).trans (Nat.add_le_add (positive_count coord divisors) singular))

structure Budget where
  k : ℕ
  j : ℕ
  H : ℕ
  T : ℕ
  regularSaving : ℕ
  totalSaving : ℕ

def budgets : List Budget := [
  ⟨64,64,2317,64174450366445192664209971647,1527,861⟩,
  ⟨128,128,2573,30630785694281879143907456713860359640742085,1094,733⟩,
  ⟨256,0,2573,4289488828796505533288666549764352820005579750166977958482,791,610⟩,
  ⟨256,256,3085,6978307373427505719968037956760817704514542210035739877460485341342966075,229,229⟩]

/-- The same exact budgets justify identifying the first affine ceiling and
the first ordinary small-multiplier square on every target product. -/
theorem sizes {b : Budget} (row : b∈budgets) : (2^b.k+24*2^b.j)^2 < 4*X := by
  simp only [budgets, List.mem_cons, List.not_mem_nil, or_false] at row
  rcases row with rfl|rfl|rfl|rfl <;> decide +kernel

theorem ceiling_guard {b : Budget} (row : b∈budgets) {n a intercept : ℕ}
    (large : X≤n) (bound : intercept≤2^b.k) : ((intercept-1)/a)^2<4*n := by
  have below : (intercept-1)/a≤2^b.k+24*2^b.j :=
    (Nat.div_le_self ..).trans ((Nat.sub_le ..).trans (bound.trans (Nat.le_add_right ..)))
  exact (Nat.pow_le_pow_left below 2).trans_lt ((sizes row).trans_le (Nat.mul_le_mul_left _ large))

private def Good (b : Budget) (t : ℕ) : Prop :=
  let K := 2^b.k
  let J := 2^b.j
  K+24*J<X ∧ 8*(24*K*J)^2*2^2048+2*(24*K*J)*(K+24*J)^2 < 2^b.H ∧
  2^14882*((24*K*J)*(K+24*J)^2)^64<(b.T+1)^336 ∧
  21000000*(2^b.regularSaving*W K J b.H b.T) ≤ 2^2046 ∧
  24*K*J-1 < (t+1)^2 ∧
  21000000*(2^b.totalSaving*(W K J b.H b.T + X*(4*(K+24*J)*t+t*(t+1)))) ≤ 2^2046

private noncomputable instance (b : Budget) (t : ℕ) : Decidable (Good b t) := by unfold Good; dsimp only; infer_instance

/-- Both bounds use the genuine uniform finite sample of eligible prime pairs.
The first counts every nonsingular positive-row square, even a trivial gcd.
The second includes any proper gcd from either sign, including constant rows. -/
theorem target_coverage {b : Budget} (row : b∈budgets) :
    2^b.regularSaving*(MixedPrefixSample.sample (regularHit (2^b.k) (2^b.j))).card <
      MixedPrefixSample.eligible.card ∧
    2^b.totalSaving*(MixedPrefixSample.sample (successful (2^b.k) (2^b.j))).card <
      MixedPrefixSample.eligible.card := by
  have good : ∃ t, Good b t := by
    simp only [budgets, List.mem_cons, List.not_mem_nil, or_false] at row
    rcases row with rfl|rfl|rfl|rfl
    · exact ⟨90370220792595849024, by decide +kernel⟩
    · exact ⟨1667036334845641176483977775388818772431, by decide +kernel⟩
    · exact ⟨1667036334845641176483977775388818772431, by decide +kernel⟩
    · exact ⟨567263069764480905071351953054982740965666704933888501678135359357423191985635, by decide +kernel⟩
  obtain ⟨t,small,coord,divisors,reg,tsq,total⟩ := good
  have tcap := Nat.le_of_lt_succ (Nat.sqrt_lt'.mpr tsq)
  have sing : Z (2^b.k) (2^b.j) ≤ _ := Nat.mul_le_mul_left X (Nat.add_le_add
    (Nat.mul_le_mul_left _ tcap) (Nat.mul_le_mul tcap (Nat.add_le_add_right tcap 1)))
  constructor
  · exact Nat.lt_of_mul_lt_mul_left (((Nat.mul_le_mul_left 21000000 (Nat.mul_le_mul_left _
      (positive_count coord divisors))).trans reg).trans_lt ChebyshevPrimeSample.eligible_count)
  · exact Nat.lt_of_mul_lt_mul_left (((Nat.mul_le_mul_left 21000000 (Nat.mul_le_mul_left _
      ((total_count small coord divisors).trans (Nat.add_le_add_left sing _)))).trans total).trans_lt ChebyshevPrimeSample.eligible_count)

end PrimeFactors.AffineExcessPopulation
