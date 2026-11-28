import PrimeFactors.RecognizingQuarticProducts
import PrimeFactors.NormOrbit
import PrimeFactors.FactorSum
import Mathlib.Data.Finset.Option

/-! For Sophie Germain's quartic, a second recognition cell comes from the
fourth root of N/4. Returning the union retains both valid decompositions if
the two cells select different coordinate pairs. -/
namespace PrimeFactors.ComplementaryQuarticProducts

open RecognizingQuarticProducts

theorem quotient_root_iff {n y : ℕ} :
    fourthRoot (n/4) = y ↔ 4*y^4≤n ∧ n<4*(y+1)^4 := by
  rw [fourthRoot_eq_iff,Nat.le_div_iff_mul_le (by decide : 0<4),
    Nat.div_lt_iff_lt_mul (by decide : 0<4),mul_comm (y^4) 4,mul_comm ((y+1)^4) 4]

/-- The second branch evaluates two fourth roots and checks the full residual. -/
def recognizeY (n : ℕ) : Option (ℕ×ℕ) :=
  let y := fourthRoot (n/4)
  let r := n-4*y^4
  let x := fourthRoot r
  if 0<x ∧ 0<y ∧ r=x^4 then some (factors x y) else none

theorem completeY {n x y : ℕ} (xp : 0<x) (yp : 0<y) (repr : n=x^4+4*y^4)
    (upper : n<4*(y+1)^4) : recognizeY n=some (factors x y) := by
  have root : fourthRoot (n/4)=y := quotient_root_iff.mpr ⟨by omega,upper⟩
  unfold recognizeY
  simp only [root]
  simp [repr,fourthRoot_pow,xp,yp]

theorem soundY {n : ℕ} {ab : ℕ×ℕ} (hit : recognizeY n=some ab) :
    ∃ x y : ℕ, 0<x ∧ 0<y ∧ n=x^4+4*y^4 ∧ n<4*(y+1)^4 ∧ ab=factors x y := by
  let y := fourthRoot (n/4)
  let x := fourthRoot (n-4*y^4)
  have bounds : 4*y^4≤n ∧ n<4*(y+1)^4 := quotient_root_iff.mp rfl
  change (if 0<x ∧ 0<y ∧ n-4*y^4=x^4 then some (factors x y) else none) = some ab at hit
  split at hit
  · rename_i h
    exact ⟨x,y,h.1,h.2.1,by omega,bounds.2,(Option.some.inj hit).symm⟩
  · contradiction

/-- Running both branches evaluates four fourth roots, or eight integer square
roots. Each branch returns its optional ordered factor pair. -/
def readings (n : ℕ) : Option (ℕ×ℕ) × Option (ℕ×ℕ) := (recognize n,recognizeY n)

/-- The finite set of distinct ordered factor pairs returned by the two branches. -/
noncomputable def choices (n : ℕ) : Finset (ℕ×ℕ) := (recognize n).toFinset ∪ (recognizeY n).toFinset

theorem mem_choices {n : ℕ} {ab : ℕ×ℕ} : ab∈choices n ↔
    ∃ x y : ℕ, 0<x ∧ 0<y ∧ n=x^4+4*y^4 ∧ (n<(x+1)^4 ∨ n<4*(y+1)^4) ∧ ab=factors x y := by
  change ab ∈ (recognize n).toFinset ∪ (recognizeY n).toFinset ↔ _
  rw [Finset.mem_union,Option.mem_toFinset,Option.mem_toFinset]
  change (recognize n=some ab ∨ recognizeY n=some ab) ↔ _
  constructor
  · rintro (h|h)
    · obtain ⟨x,y,hx,hy,repr,upper,eq⟩ := sound h
      exact ⟨x,y,hx,hy,repr,.inl upper,eq⟩
    · obtain ⟨x,y,hx,hy,repr,upper,eq⟩ := soundY h
      exact ⟨x,y,hx,hy,repr,.inr upper,eq⟩
  · rintro ⟨x,y,hx,hy,repr,upper,rfl⟩
    exact upper.elim (fun h => .inl (complete hx hy repr h)) (fun h => .inr (completeY hx hy repr h))

theorem card_choices (n : ℕ) : (choices n).card≤2 := by
  apply (Finset.card_union_le ..).trans
  rw [Option.card_toFinset,Option.card_toFinset]
  cases recognize n <;> cases recognizeY n <;> simp [Option.elim]

/-- The two ordered factors determine the positive coordinates, even without
a fourth-root bound or a primality hypothesis. -/
theorem coordinates_unique {x y u v : ℕ} (vp : 0<v) (eq : factors x y=factors u v) :
    x=u ∧ y=v := by
  have sum := calc
    2*x^2+4*y^2 = (factors x y).1+(factors x y).2 := (factor_sum _ _).symm
    _ = (factors u v).1+(factors u v).2 := by rw [eq]
    _ = _ := factor_sum u v
  have prod := calc
    x^4+4*y^4 = (factors x y).1*(factors x y).2 := (factor_product _ _).symm
    _ = (factors u v).1*(factors u v).2 := by rw [eq]
    _ = _ := factor_product u v
  have half : x^2+2*y^2=u^2+2*v^2 := by omega
  zify at half prod
  have zero : (((x:ℤ)^2-u^2)*((x:ℤ)^2-2*v^2))=0 := by
    apply (mul_right_inj' (by decide : (2:ℤ)≠0)).mp
    linear_combination prod + ((x:ℤ)^2-2*y^2-u^2-2*v^2)*half
  rcases mul_eq_zero.mp zero with a|b
  · have sx : x^2=u^2 := by exact_mod_cast sub_eq_zero.mp a
    have ex := (Nat.pow_left_inj (by decide : 2≠0)).mp sx
    subst u
    have sy : y^2=v^2 := by omega
    exact ⟨rfl,(Nat.pow_left_inj (by decide : 2≠0)).mp sy⟩
  · have impossible : x^2=2*v^2 := by exact_mod_cast sub_eq_zero.mp b
    exact False.elim (NormOrbit.unequal_squares vp impossible)

private theorem fourth_gap (t : ℕ) (pos : 0<t) : (t+1)^4 ≤ t^4+15*t^3 := by
  have sq := Nat.pow_le_pow_right pos (by decide : 1≤2)
  have cube := Nat.pow_le_pow_right pos (by decide : 2≤3)
  simp only [pow_one] at sq
  nlinarith

/-- The two coordinate cells can overlap for a single representation only at
small inputs. -/
theorem overlap_small {n x y : ℕ} (xp : 0<x) (yp : 0<y) (repr : n=x^4+4*y^4)
    (left : n<(x+1)^4) (right : n<4*(y+1)^4) : x*y<225 ∧ n<2^34 := by
  have a : 4*y^4<15*x^3 := by have := fourth_gap x xp; omega
  have b : x^4<60*y^3 := by have := fourth_gap y yp; omega
  have product : 4*(x*y)^3*(x*y)<4*(x*y)^3*225 := calc
    _ = (4*y^4)*x^4 := by ring
    _ < (15*x^3)*x^4 := Nat.mul_lt_mul_of_pos_right a (pow_pos xp 4)
    _ ≤ (15*x^3)*(60*y^3) := Nat.mul_le_mul_left _ b.le
    _ = _ := by ring
  have small := Nat.lt_of_mul_lt_mul_left product
  have xlow : x≤x*y := by simpa only [mul_one] using Nat.mul_le_mul_left x (show 1≤y from yp)
  have ylow : y≤x*y := by simpa only [one_mul] using Nat.mul_le_mul_right y (show 1≤x from xp)
  have xcap := Nat.pow_le_pow_left (show x≤224 by omega) 4
  have ycap := Nat.pow_le_pow_left (show y≤224 by omega) 4
  exact ⟨small,by omega⟩

theorem product_parity (x y : ℕ) : (x^4+4*y^4)%2=x%2 := by
  have h : x%2=0 ∨ x%2=1 := by omega
  rw [Nat.add_mod,Nat.mul_mod,Nat.pow_mod]
  rcases h with h|h <;> rw [h] <;> norm_num

private theorem odd_table : ∀ (x : Fin 20) (y : Fin 15), x.val%2=1 → 0<y.val →
    x.val^4+4*y.val^4<(x.val+1)^4 → x.val^4+4*y.val^4<4*(y.val+1)^4 →
    (x.val,y.val)=(1,1) ∨ (x.val,y.val)=(3,2) ∨ (x.val,y.val)=(5,3) := by decide +kernel

/-- Among odd products, exactly three positive coordinate pairs fall in both
cells. The statement compares the same representation in the two cells. -/
theorem odd_overlap_iff {x y : ℕ} (xp : 0<x) (yp : 0<y)
    (odd : (x^4+4*y^4)%2=1) :
    (x^4+4*y^4<(x+1)^4 ∧ x^4+4*y^4<4*(y+1)^4) ↔
    (x,y)=(1,1) ∨ (x,y)=(3,2) ∨ (x,y)=(5,3) := by
  constructor
  · rintro ⟨left,right⟩
    have prod := (overlap_small xp yp rfl left right).1
    have a : 4*y^4<15*x^3 := by have := fourth_gap x xp; omega
    have b : x^4<60*y^3 := by have := fourth_gap y yp; omega
    have xc : x<20 := by
      by_contra! big
      have yc : y≤11 := by
        by_contra! many
        have := Nat.mul_le_mul big (show 12≤y by omega)
        omega
      have := Nat.pow_le_pow_left big 4
      have := Nat.pow_le_pow_left yc 3
      omega
    have yc : y<15 := by
      by_contra! big
      have xx : x≤14 := by
        by_contra! many
        have := Nat.mul_le_mul (show 15≤x by omega) big
        omega
      have := Nat.pow_le_pow_left xx 3
      have := Nat.pow_le_pow_left big 4
      omega
    exact odd_table ⟨x,xc⟩ ⟨y,yc⟩ ((product_parity x y).symm.trans odd) yp left right
  · rintro (eq|eq|eq) <;> obtain ⟨rfl,rfl⟩ := Prod.mk.inj eq <;> decide

theorem odd_overlap_products {n x y : ℕ} (xp : 0<x) (yp : 0<y) (repr : n=x^4+4*y^4)
    (odd : n%2=1) (left : n<(x+1)^4) (right : n<4*(y+1)^4) :
    n=5 ∨ n=145 ∨ n=949 := by
  subst n
  rcases (odd_overlap_iff xp yp odd).mp ⟨left,right⟩ with eq|eq|eq <;>
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj eq <;> decide

theorem same_pair_overlap {n : ℕ} {ab : ℕ×ℕ}
    (left : recognize n=some ab) (right : recognizeY n=some ab) : n<2^34 := by
  obtain ⟨x,y,xp,yp,nxy,small,eq⟩ := sound left
  obtain ⟨u,v,_,vp,_,upper,eq'⟩ := soundY right
  obtain ⟨rfl,rfl⟩ := coordinates_unique vp (eq.symm.trans eq')
  exact (overlap_small xp yp nxy small upper).2

private theorem semiprime_overlap {p q : ℕ} {a b : ℕ×ℕ}
    (pp : p.Prime) (qp : q.Prime) (order : p≤q)
    (h : recognize (p*q)=some a) (k : recognizeY (p*q)=some b) :
    ∃ x y : ℕ, 0<x ∧ 0<y ∧ p*q=x^4+4*y^4 ∧ p*q<(x+1)^4 ∧ p*q<4*(y+1)^4 := by
  have unique {ab : ℕ×ℕ} {x y : ℕ} (xp : 0<x) (yp : 0<y)
      (repr : p*q=x^4+4*y^4) (eq : ab=factors x y) : ab=(p,q) := by
    have diff : (x,y)≠(1,1) := by
      intro same
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj same
      norm_num at repr
      exact Nat.not_prime_mul' repr pp.ne_one qp.ne_one (by decide)
    obtain ⟨lower,ord,_⟩ := (proper_iff xp yp).mpr diff
    obtain ⟨a,b⟩ := ordered_semiprime_pair_unique pp qp order ord.le lower
      ((factor_product x y).trans repr.symm)
    exact eq.trans (Prod.ext a b)
  obtain ⟨x,y,xp,yp,repr,lo,eq⟩ := sound h
  obtain ⟨u,v,up,vp,repr',hi,eq'⟩ := soundY k
  have pairs := (eq.symm.trans (unique xp yp repr eq)).trans
    ((unique up vp repr' eq').symm.trans eq')
  obtain ⟨rfl,rfl⟩ := coordinates_unique vp pairs
  exact ⟨x,y,xp,yp,repr,lo,hi⟩

/-- On a sufficiently large semiprime the two recognizers cannot both succeed,
even without assuming their returned pairs agree in advance. -/
theorem disjoint_on_semiprimes {p q : ℕ} (pp : p.Prime) (qp : q.Prime) (order : p≤q)
    (large : 2^34≤p*q) :
    recognize (p*q)=none ∨ recognizeY (p*q)=none := by
  cases h : recognize (p*q) with
  | none => exact .inl rfl
  | some a =>
    cases k : recognizeY (p*q) with
    | none => exact .inr rfl
    | some b =>
      obtain ⟨x,y,xp,yp,repr,lo,hi⟩ := semiprime_overlap pp qp order h k
      exact False.elim ((not_lt_of_ge large) (overlap_small xp yp repr lo hi).2)

/-- For a balanced odd semiprime there are no shared successes at any size.
The composite exceptions 145 and 949 have factor ratios larger than two. -/
theorem disjoint_on_balanced_odd {p q : ℕ} (pp : p.Prime) (qp : q.Prime)
    (order : p≤q) (balanced : q≤2*p) (odd : (p*q)%2=1) :
    recognize (p*q)=none ∨ recognizeY (p*q)=none := by
  cases h : recognize (p*q) with
  | none => exact .inl rfl
  | some a =>
    cases k : recognizeY (p*q) with
    | none => exact .inr rfl
    | some b =>
      obtain ⟨x,y,xp,yp,repr,lo,hi⟩ := semiprime_overlap pp qp order h k
      exfalso
      rcases odd_overlap_products xp yp repr odd lo hi with e|e|e
      · exact Nat.not_prime_mul' e pp.ne_one qp.ne_one (by decide)
      · obtain ⟨a,b⟩ := ordered_semiprime_pair_unique pp qp order
          (by decide : 5≤29) (by decide : 1<5) (by omega : 5*29=p*q)
        omega
      · obtain ⟨a,b⟩ := ordered_semiprime_pair_unique pp qp order
          (by decide : 13≤73) (by decide : 1<13) (by omega : 13*73=p*q)
        omega

/-- A composite with more than two prime factors can return distinct pairs. -/
theorem example_different_pairs :
    readings 7585 = (some (41,185),some (37,205)) := by
  have h := complete (n:=7585) (x:=9) (y:=4) (by decide) (by decide) (by norm_num) (by norm_num)
  have k := completeY (n:=7585) (x:=7) (y:=6) (by decide) (by decide) (by norm_num) (by norm_num)
  rw [readings,h,k]
  norm_num [factors]

theorem example_forward_only :
    recognize 151847041=some (10301,14741) ∧ recognizeY 151847041=none ∧
    Nat.Prime 10301 ∧ Nat.Prime 14741 := by
  obtain ⟨yes,p,q⟩ := example_recognized
  have root : fourthRoot (151847041/4)=78 := quotient_root_iff.mpr ⟨by norm_num,by norm_num⟩
  have res : fourthRoot (151847041-4*78^4)=44 := fourthRoot_eq_iff.mpr ⟨by norm_num,by norm_num⟩
  exact ⟨yes,by rw [recognizeY,root,res]; norm_num,p,q⟩

theorem example_reverse_only :
    recognize 2126389=none ∧ recognizeY 2126389=some (1213,1753) ∧
    Nat.Prime 1213 ∧ Nat.Prime 1753 := by
  have root : fourthRoot 2126389=38 := fourthRoot_eq_iff.mpr ⟨by norm_num,by norm_num⟩
  have res : fourthRoot ((2126389-38^4)/4)=10 := fourthRoot_eq_iff.mpr ⟨by norm_num,by norm_num⟩
  have hit := completeY (n:=2126389) (x:=5) (y:=27) (by decide) (by decide) (by norm_num) (by norm_num)
  exact ⟨by rw [recognize,root,res]; norm_num, hit.trans (by norm_num [factors]),by norm_num,by norm_num⟩

end PrimeFactors.ComplementaryQuarticProducts
