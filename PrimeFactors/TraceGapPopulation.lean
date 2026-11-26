import PrimeFactors.TraceProgression
import PrimeFactors.SeparatedPairs

/-! A range of genuine balanced prime gaps for which initial weighted-sum
windows all miss, even if the choice of slopes depends on the entire product. -/

namespace PrimeFactors.TraceGapPopulation

open Finset TraceCoverCertificate

set_option exponentiation.threshold 8192
set_option maxRecDepth 8192

private theorem residual {p q a b K d D : ℕ} (weights : b≤a) (cap : b≤K)
    (gap : p+d≤q) (near : q≤p+D) (size : K*(d+D)≤p) :
    (b:ℤ)*d ≤ |(a:ℤ)*p-b*q| := by
  by_cases ab : a=b
  · subst a
    have h : (d:ℤ)≤(q:ℤ)-p := by
      have h' : (p:ℤ)+d≤q := by exact_mod_cast gap
      omega
    calc
      _ ≤ (b:ℤ)*(q-p) := mul_le_mul_of_nonneg_left h (by positivity)
      _ = -((b:ℤ)*p-b*q) := by ring
      _ ≤ _ := neg_le_abs _
  · have bound : b*d+b*q ≤ a*p := calc
      _ ≤ b*d+b*(p+D) := Nat.add_le_add_left (Nat.mul_le_mul_left _ near) _
      _ = b*(d+D)+b*p := by ring
      _ ≤ p+b*p := Nat.add_le_add_right ((Nat.mul_le_mul_right _ cap).trans size) _
      _ = (b+1)*p := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ (by omega)
    have h : (b:ℤ)*d+b*q ≤ a*p := by exact_mod_cast bound
    exact (show (b:ℤ)*d≤a*p-b*q by omega).trans (le_abs_self _)

/-- On the indicated gap range the residual of every eligible direction is
at least b times the lower gap, including the unweighted direction. -/
theorem large_residual {p q a b : ℕ} (size : 2^1023≤p) (weights : b≤a) (cap : b≤2^32)
    (gap : p+2^975≤q) (near : q≤p+2^990) :
    (b:ℤ)*(2^975:ℕ) ≤ |(a:ℤ)*p-b*q| :=
  residual weights cap gap near ((by decide : 2^32*(2^975+2^990)≤(2:ℕ)^1023).trans size)

/-- If z appears in the covered prefix, the weighted gap has a small square.
This inequality also applies if an implementation chooses the window after seeing N. -/
theorem gap_bound {p q m g : ℕ} {s : Slope} (ap : 0<s.a) (bp : 0<s.b) (pp : 0<p) (qp : 0<q)
    (start : validStart (p*q) s) (hit : s.a*p+s.b*q<cutoff m s g) :
    ((s.a:ℤ)*p-s.b*q)^2 < 2*(s.a*p+s.b*q : ℕ)*(s.step*(1+m*g) : ℕ) := by
  obtain ⟨_,_,_,_,prev⟩ := of_decide_eq_true start
  let l := s.start-s.step
  let z := s.a*p+s.b*q
  let rad := 4*s.a*s.b*(p*q)
  have prevSq : l^2<rad := by
    rcases prev with h|h
    · dsimp [l,rad]; rw [Nat.sub_eq_zero_of_le h.le]; simp [Nat.mul_pos,ap,bp,pp,qp]
    · exact h
  have am : rad ≤ z^2 := by
    dsimp [z,rad]; nlinarith only [sq_nonneg ((s.a*p:ℤ)-s.b*q)]
  have lz : l<z := by
    by_contra! h
    exact (not_le_of_gt (prevSq.trans_le am)) (Nat.pow_le_pow_left h 2)
  have small : z≤l+s.step*(1+m*g) := by
    change z<s.start+s.step*m*g at hit
    dsimp only [l]; rw [mul_add,mul_one,←mul_assoc]; omega
  have eq : ((s.a:ℤ)*p-s.b*q)^2 = (z:ℤ)^2-rad := by dsimp [z,rad]; push_cast; ring
  have le : (z:ℤ)-l≤(s.step*(1+m*g):ℕ) := by
    have hz : (z:ℤ)≤(l:ℤ)+(s.step*(1+m*g):ℕ) := by exact_mod_cast small
    omega
  have sum : (z:ℤ)+l≤2*z := by exact_mod_cast (show z+l≤2*z by omega)
  have diff := mul_le_mul le sum (by positivity) (by positivity)
  have gapz : (l:ℤ)^2 < rad := by exact_mod_cast prevSq
  rw [eq]
  change (z:ℤ)^2-rad<2*z*(s.step*(1+m*g):ℕ)
  nlinarith only [diff,gapz]

/-- A practical-size table of 2^24 starting powers and even 2^894 blocks per
slope cannot include a true weighted trace on these inputs. A group-order
coincidence or a search that starts elsewhere is a separate mechanism. -/
theorem misses {p q m g : ℕ} {s : Slope} (lo : 2^1023≤p) (hi : q<2^1024)
    (gap : p+2^975≤q) (near : q≤p+2^990) (bp : 0<s.b) (ba : s.b≤s.a)
    (ab : s.a≤2*s.b) (bcap : s.b≤2^32) (mem : m≤2^24) (budget : g≤2^894)
    (start : validStart (p*q) s) : cutoff m s g ≤ s.a*p+s.b*q := by
  by_contra! hit
  have sq := gap_bound (bp.trans_le ba) bp (by omega) (by omega) start hit
  let d : ℕ := 2^975
  let U : ℕ := 2^1024
  have res : (s.b:ℤ)*d ≤ |(s.a:ℤ)*p-s.b*q| := large_residual lo ba bcap gap near
  have low := pow_le_pow_left₀ (by positivity : (0:ℤ)≤s.b*d) res 2
  rw [sq_abs] at low
  have st := (of_decide_eq_true start).2.1
  have step : s.step ≤24 := st ▸ Nat.gcd_le_left _ (by decide)
  have hmul := Nat.mul_le_mul mem budget
  have u := Nat.mul_le_mul step (Nat.add_le_add_left hmul 1)
  have z : s.a*p+s.b*q ≤ s.b*(3*U) := by
    have f := Nat.mul_le_mul ab (show p≤U by dsimp [U]; omega)
    have h := Nat.mul_le_mul_left s.b (show q≤U from hi.le)
    nlinarith only [f,h]
  have top := Nat.mul_le_mul (Nat.mul_le_mul_left 2 z) u
  have reorder (b U h : ℕ) : 2*(b*(3*U))*h=b*(2*(3*U)*h) := by ring
  rw [reorder] at top
  have numeric : 2*(3*U)*(24*(1+2^24*2^894))≤d^2 := by decide +kernel
  have upper := top.trans (Nat.mul_le_mul_left s.b numeric)
  have more : s.b*d^2 ≤ (s.b*d)^2 := by
    have b1 : 1≤s.b := bp
    have h := Nat.mul_le_mul_right (s.b*d^2) b1
    nlinarith only [h]
  have final := upper.trans more
  have cast : 2*((s.a*p+s.b*q):ℕ)*(s.step*(1+m*g):ℕ) ≤ ((s.b:ℤ)*d)^2 := by
    exact_mod_cast final
  exact (not_lt_of_ge (cast.trans low)) sq

/-- Oriented pairs in the intermediate gap band, before ordering the two entries. -/
noncomputable def gapPairs (S : Finset ℕ) : Finset (ℕ×ℕ) :=
  (S ×ˢ S).filter fun z =>
    (z.1+2^975≤z.2 ∨ z.2+2^975≤z.1) ∧ z.1≤z.2+2^990 ∧ z.2≤z.1+2^990

private theorem band_count (S : Finset ℕ) (X W B d cap : ℕ) (wpos : 0<W)
    (bounds : ∀ x ∈ S, X≤x ∧ x<X+B*W) (capacity : 2*d+1≤cap) :
    (S.card-B*cap)^2 ≤ B*((S ×ˢ S).filter fun z =>
      (z.1+d≤z.2 ∨ z.2+d≤z.1) ∧ z.1≤z.2+W ∧ z.2≤z.1+W).card := by
  classical
  let index x := (x-X)/W
  let part j := S.filter fun x => index x=j
  let far (x y : ℕ) := x+d≤y ∨ y+d≤x
  let pairs := (S ×ˢ S).filter fun z =>
    far z.1 z.2 ∧ z.1≤z.2+W ∧ z.2≤z.1+W
  let room x := S.filter fun y => (x,y)∈pairs
  have mapped (x : ℕ) (hx : x∈S) : index x∈range B := by
    apply mem_range.mpr
    apply (Nat.div_lt_iff_lt_mul wpos).mpr
    have h := bounds x hx
    omega
  have close (j x y : ℕ) (hx : x∈part j) (hy : y∈part j) :
      x≤y+W ∧ y≤x+W := by
    obtain ⟨sx,ix⟩ := mem_filter.mp hx
    obtain ⟨sy,iy⟩ := mem_filter.mp hy
    have ax := (bounds _ sx).1
    have ay := (bounds _ sy).1
    have xval := Nat.div_add_mod (x-X) W
    have yval := Nat.div_add_mod (y-X) W
    have mx := Nat.mod_lt (x-X) wpos
    have my := Nat.mod_lt (y-X) wpos
    change (x-X)/W=j at ix
    change (y-X)/W=j at iy
    rw [ix] at xval
    rw [iy] at yval
    omega
  have near (j : ℕ) (_ : j∈range B) (x : ℕ) (_ : x∈part j) :
      ((part j).filter fun y => ¬far x y).card ≤ cap := by
    have sub : ((part j).filter fun y => ¬far x y) ⊆ Icc (x-d) (x+d) := by
      intro y hy
      have h := (mem_filter.mp hy).2
      dsimp [far] at h
      exact mem_Icc.mpr ⟨by omega,by omega⟩
    have h := card_le_card sub
    rw [Nat.card_Icc] at h
    omega
  have bound := separated_pairs_lower (range B) part far (fun _ => cap) near
  have cards := card_eq_sum_card_fiberwise (f:=index) (s:=S) (t:=range B) mapped
  change S.card = ∑ j ∈ range B, (part j).card at cards
  rw [←cards] at bound
  simp only [sum_const, smul_eq_mul, card_range] at bound
  have each (j x : ℕ) (hx : x∈part j) :
      ((part j).filter (far x)).card ≤ (room x).card := by
    apply card_le_card
    intro y hy
    obtain ⟨py,hfar⟩ := mem_filter.mp hy
    have sx := (mem_filter.mp hx).1
    have sy := (mem_filter.mp py).1
    have n := close j x y hx py
    exact mem_filter.mpr ⟨sy,mem_filter.mpr ⟨mem_product.mpr ⟨sx,sy⟩,hfar,n⟩⟩
  have rows : ∑ j ∈ range B, ∑ x ∈ part j, ((part j).filter (far x)).card ≤
      ∑ x ∈ S, (room x).card := by
    rw [←sum_fiberwise_of_maps_to mapped (fun x => (room x).card)]
    exact sum_le_sum (fun j _ => sum_le_sum (fun x hx => each j x hx))
  have cardRoom : (∑ x ∈ S, (room x).card) = pairs.card := by
    have h := card_eq_sum_card_fiberwise (s:=pairs) (t:=S) (f:=Prod.fst)
      (fun z hz => (mem_product.mp (mem_filter.mp hz).1).1)
    rw [h]
    apply sum_congr rfl
    intro x sx
    have eq : (room x).image (fun y => (x,y)) = pairs.filter (fun z => z.1=x) := by
      ext z
      constructor
      · intro hz
        obtain ⟨y,hy,rfl⟩ := mem_image.mp hz
        exact mem_filter.mpr ⟨(mem_filter.mp hy).2,rfl⟩
      · intro hz
        obtain ⟨hz,eq⟩ := mem_filter.mp hz
        obtain ⟨p,q⟩ := z
        dsimp at eq
        subst p
        exact mem_image.mpr ⟨q,mem_filter.mpr ⟨(mem_product.mp (mem_filter.mp hz).1).2,hz⟩,rfl⟩
    rw [←eq,card_image_of_injective]
    exact fun _ _ h => congrArg Prod.snd h
  rw [cardRoom] at rows
  exact bound.trans (Nat.mul_le_mul_left B rows)

/-- A separated-pairs argument needs just a lower count in the chosen upper
portion of the prime interval. There are no short-interval prime hypotheses. -/
theorem many_gaps (S : Finset ℕ) (size : (2:ℕ)^1011<S.card)
    (rangeS : ∀ x∈S, 2^1023≤x ∧ x<2^1024) : (2:ℕ)^1987<(gapPairs S).card := by
  have bounds : ∀ x∈S, (2:ℕ)^1023≤x ∧ x<2^1023+2^33*2^990 := by
    rw [show (2:ℕ)^1023+2^33*2^990=2^1024 by decide +kernel]
    exact rangeS
  have h := band_count S (2^1023) (2^990) (2^33) (2^975) (2^977)
    (by decide +kernel) bounds (by decide +kernel)
  change (S.card-2^33*2^977)^2 ≤ 2^33*(gapPairs S).card at h
  rw [show (2:ℕ)^33*2^977=2^1010 by decide +kernel] at h
  have small : (2:ℕ)^1010 < S.card-2^1010 := by
    have twice : (2:ℕ)^1011=2^1010+2^1010 := by decide +kernel
    rw [twice] at size
    omega
  have sq := Nat.pow_lt_pow_left small (show (2:ℕ)≠0 by decide)
  rw [show ((2:ℕ)^1010)^2=2^33*2^1987 by decide +kernel] at sq
  exact Nat.lt_of_mul_lt_mul_left (sq.trans_le h)

/-- On the two explicit prime-population inequalities the fraction of
eligible ordered pairs in the gap band exceeds 2^-43. Each unordered
distinct pair occurs twice when both orientations are counted. -/
theorem target_fraction (S : Finset ℕ) (size : 2^1011<S.card)
    (rangeS : ∀ x∈S, 2^1023≤x ∧ x<2^1024)
    {pop : ℕ} (total : pop≤2^2030) : pop < 2^43*(gapPairs S).card := by
  exact total.trans_lt ((show (2:ℕ)^2030=2^43*2^1987 by decide) ▸
    Nat.mul_lt_mul_of_pos_left (many_gaps S size rangeS) (by decide))

/-- Membership is invariant under reversing the ordered pair. -/
theorem swap_gap {S : Finset ℕ} {p q : ℕ} :
    (p,q)∈gapPairs S ↔ (q,p)∈gapPairs S := by
  simp only [gapPairs, mem_filter, mem_product]
  tauto

/-- When S consists of primes in the upper portion [√2 X, 2X), ordering
either counted pair gives distinct 1024-bit primes and a genuine 2048-bit
product, with both gap inequalities used by `misses`. -/
theorem target_of_gap {S : Finset ℕ} {p q : ℕ}
    (members : ∀ x∈S, x.Prime ∧ 2^1023≤x ∧ x<2^1024 ∧ 2^2047≤x^2)
    (ord : p≤q) (hit : (p,q)∈gapPairs S) :
    p.Prime ∧ q.Prime ∧ 2^1023≤p ∧ q<2^1024 ∧ p+2^975≤q ∧ q≤p+2^990 ∧
    2^2047≤p*q ∧ p*q<2^2048 := by
  obtain ⟨inside,far,_,near⟩ := mem_filter.mp hit
  obtain ⟨ps,qs⟩ := mem_product.mp inside
  obtain ⟨pp,lo,ph,sq⟩ := members p ps
  obtain ⟨pq,_,hi,_⟩ := members q qs
  have lower := sq.trans (show p^2≤p*q by rw [pow_two]; exact Nat.mul_le_mul_left p ord)
  have upper := (Nat.mul_le_mul_right q ph.le).trans_lt
    (Nat.mul_lt_mul_of_pos_left hi (show 0<(2:ℕ)^1024 by decide))
  rw [show (2:ℕ)^1024*2^1024=2^2048 by decide +kernel] at upper
  refine ⟨pp,pq,lo,hi,?_,near,lower,upper⟩
  rcases far with forward | backward
  · exact forward
  · omega

end PrimeFactors.TraceGapPopulation
