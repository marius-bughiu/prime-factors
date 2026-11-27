import PrimeFactors.WeightedTracePrefix
import PrimeFactors.SharedMultiplierPopulation
import Mathlib.Tactic
import Mathlib.Tactic.IrreducibleDef
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Finset.Card

/-! Count prime pairs recovered by the first square test for some pair of
distinct public multipliers. Crowding is measured between all weighted
primes together, then the same-weight pairs are removed. -/
namespace PrimeFactors.WeightedPrimeCrowding
open Finset
set_option exponentiation.threshold 8192
set_option maxRecDepth 4096
private abbrev U : ℕ := 2^1024
private abbrev H : ℕ := 2^516
private abbrev B : ℕ := 2^515

noncomputable irreducible_def weights : Finset ℕ := Ico 512 576
noncomputable irreducible_def pool : Finset ℕ := (Icc (3*U/4) (7*U/8)).filter Nat.Prime
noncomputable def points := weights ×ˢ pool
def bucket (x : ℕ × ℕ) := (x.1*x.2-384*U)/H
noncomputable def cell (i : ℕ) := points.filter (fun x => bucket x=i)
noncomputable def collisions := (points ×ˢ points).filter (fun z => bucket z.1=bucket z.2)
noncomputable def hits := collisions.filter (fun z => z.1.1≠z.2.1)
noncomputable def products := hits.image (fun z => z.1.2*z.2.2)


private theorem info {x : ℕ × ℕ} (hx : x ∈ points) :
    (512≤x.1 ∧ x.1<576) ∧ (3*U/4≤x.2 ∧ x.2≤7*U/8) ∧ x.2.Prime := by
  simpa [points,weights_def,pool_def, and_assoc] using hx

private theorem size {x : ℕ × ℕ} (hx : x∈points) :
    384*U≤x.1*x.2 ∧ x.1*x.2<512*U := by
  obtain ⟨⟨wl,wu⟩,⟨pl,pu⟩,_⟩ := info hx
  constructor
  · exact le_trans (by decide +kernel) (Nat.mul_le_mul wl pl)
  · exact lt_of_le_of_lt (Nat.mul_le_mul wu.le pu) (by decide +kernel)

private theorem loc {x : ℕ × ℕ} (hx : x∈points) : bucket x∈range B := by
  have h := size hx
  rw [mem_range,bucket,Nat.div_lt_iff_lt_mul (by decide : 0<H)]
  have : B*H=128*U := by decide +kernel
  omega

private theorem near {x y : ℕ × ℕ} (hx : x∈points) (hy : y∈points)
    (eq : bucket x=bucket y) : x.1*x.2 < y.1*y.2+H := by
  have l := (size hx).1
  have r := (size hy).1
  let a := x.1*x.2-384*U
  let b := y.1*y.2-384*U
  have ar := Nat.mod_add_div a H
  have br := Nat.mod_add_div b H
  change a/H=b/H at eq
  rw [eq] at ar
  have am := Nat.mod_lt a (by decide : 0<H)
  dsimp only [a,b] at ar br am
  omega

private theorem points_card : points.card=64*pool.card := by rw [points, card_product, show weights.card=64 by rw [weights_def, Nat.card_Ico]]

private theorem bucket_bound (b : ℕ) (d : ℕ → ℕ) :
    (∑ i∈range b, d i)^2 ≤ b * ∑ i∈range b, (d i)^2 := by
  simpa only [card_range,Nat.cast_id] using (sq_sum_le_card_mul_sum_sq (s:=range b) (f:=d))

private theorem bucket_energy {α : Type*} (s : Finset α) (f : α→ℕ) (b : ℕ)
    (map : Set.MapsTo f s (range b)) :
    s.card^2 ≤ b*((s ×ˢ s).filter (fun z => f z.1=f z.2)).card := by
  let same := (s ×ˢ s).filter (fun z => f z.1=f z.2)
  let members (i : ℕ) := s.filter (fun x => f x=i)
  let tag (z : α×α) := f z.1
  have pairmap : Set.MapsTo tag (same : Set (α×α)) (range b) := by
    intro z hz
    change z∈same at hz
    simp only [same,mem_filter,mem_product] at hz
    exact map hz.1.1
  have fibers (i : ℕ) : same.filter (fun z => tag z=i) = members i ×ˢ members i := by
    ext z
    simp only [same,members,tag,mem_filter,mem_product]
    aesop
  have pairs := card_eq_sum_card_fiberwise pairmap
  simp_rw [fibers,card_product,←sq] at pairs
  change s.card^2 ≤ b*same.card
  rw [card_eq_sum_card_fiberwise map,pairs]
  exact bucket_bound b (fun i => (members i).card)

private theorem energy : points.card^2 ≤ B*collisions.card :=
  bucket_energy points bucket B (fun _ hx => loc hx)

/-- A prime-count upper bound for a short ordinary interval, the only
local distribution input used to remove same-weight pairs. -/
def ShortCount := ∀ n : ℕ, 3*U/4≤n →
    ((Icc n (n+2^507)).filter Nat.Prime).card ≤ 2^500

private theorem same_part (short : ShortCount) (x : ℕ×ℕ) :
    ((cell (bucket x)).filter (fun y => x.1=y.1)).card ≤ 2^500 := by
  classical
  let s := (cell (bucket x)).filter (fun y => x.1=y.1)
  change s.card ≤ _
  by_cases h : s.Nonempty
  · let q := (s.image Prod.snd).min' (h.image _)
    have qmem : q∈s.image Prod.snd := min'_mem _ _
    obtain ⟨z,hz,zq⟩ := mem_image.mp qmem
    have data {y : ℕ×ℕ} (hy : y∈s) : y∈points ∧ bucket y=bucket x ∧ x.1=y.1 := by
      simpa only [s,cell,mem_filter,and_assoc] using hy
    obtain ⟨zp,zb,zw⟩ := data hz
    have qlo : 3*U/4≤q := zq ▸ (info zp).2.1.1
    calc s.card ≤ ((Icc q (q+2^507)).filter Nat.Prime).card := by
          apply card_le_card_of_injOn Prod.snd
          · intro y hy
            obtain ⟨yp,yb,yw⟩ := data hy
            have minq := min'_le _ y.2 (mem_image_of_mem Prod.snd hy)
            have gap := near yp zp (yb.trans zb.symm)
            rw [←yw,←zw,zq] at gap
            have lo := (info yp).1.1
            have ymax : y.2≤q+2^507 := by
              by_contra! bad
              have hb := Nat.mul_le_mul_left x.1 bad.le
              rw [Nat.mul_add] at hb
              have scale := Nat.mul_le_mul_right (2^507) (show 512≤x.1 by omega)
              have : H=512*(2^507) := by decide +kernel
              omega
            exact mem_filter.mpr ⟨mem_Icc.mpr ⟨minq,ymax⟩,(info yp).2.2⟩
          · intro y hy z hz eq
            exact Prod.ext ((data hy).2.2.symm.trans (data hz).2.2) eq
        _ ≤ _ := short q qlo
  · simp [not_nonempty_iff_eq_empty.mp h]

private theorem diagonal_count {α : Type*} (s : Finset α) (f w : α→ℕ) (cap : ℕ)
    (bd : ∀ x, ((s.filter (fun y => f y=f x)).filter (fun y => w x=w y)).card ≤ cap) :
    (((s ×ˢ s).filter (fun z => f z.1=f z.2)).filter (fun z => w z.1=w z.2)).card ≤ s.card*cap := by
  classical
  let pairs := ((s ×ˢ s).filter (fun z => f z.1=f z.2)).filter (fun z => w z.1=w z.2)
  have map : Set.MapsTo (fun z : α×α => z.1) (pairs : Set (α×α)) (s : Set α) := by
    intro z hz
    change z∈pairs at hz
    simp only [pairs,mem_filter,mem_product] at hz
    exact hz.1.1.1
  change pairs.card ≤ _
  rw [card_eq_sum_card_fiberwise map]
  calc _ ≤ ∑ _x∈s, cap := by
         apply sum_le_sum
         intro x _
         apply le_trans _ (bd x)
         apply card_le_card_of_injOn Prod.snd
         · rintro ⟨u,v⟩ hz
           change (u,v)∈pairs.filter (fun z => z.1=x) at hz
           simp only [pairs,mem_filter,mem_product] at hz
           simp only [mem_filter]
           exact ⟨⟨hz.1.1.1.2,hz.1.1.2.symm.trans (congrArg f hz.2)⟩,hz.2 ▸ hz.1.2⟩
         · intro u hu v hv eq
           exact Prod.ext ((mem_filter.mp hu).2.trans (mem_filter.mp hv).2.symm) eq
       _ = _ := by simp

private theorem diagonal (short : ShortCount) :
    (collisions.filter (fun z => z.1.1=z.2.1)).card ≤ points.card*2^500 :=
  diagonal_count points bucket Prod.fst _ (same_part short)

private theorem separate (size total diag good : ℕ) (en : size^2 ≤ B*total)
    (di : diag ≤ size*2^500) (sum : diag+good=total) (num : 2^1017≤size) :
    2^1517 ≤ good := by
  have mult := Nat.mul_le_mul_right size num
  rw [←sq] at mult
  norm_num only [B, Nat.reducePow] at en mult num di ⊢
  omega

theorem many_hits (global : 2^1011 ≤ pool.card) (short : ShortCount) : 2^1517 ≤ hits.card := by
  apply separate points.card collisions.card _ hits.card energy (diagonal short)
  · exact Finset.filter_card_add_filter_neg_card_eq_card (s:=collisions) (fun z => z.1.1=z.2.1)
  · rw [points_card]
    omega


private theorem equal_factors {p q u v : ℕ} (hp : p.Prime) (hu : u.Prime) (hv : v.Prime)
    (same : p*q=u*v) (orientation : decide (p≤q)=decide (u≤v)) : p=u ∧ q=v := by
  have div : p∣u*v := same ▸ dvd_mul_right p q
  rcases hp.dvd_mul.mp div with d|d
  · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp hu).mp d
    exact ⟨rfl, Nat.eq_of_mul_eq_mul_left hp.pos same⟩
  · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp hv).mp d
    rw [Nat.mul_comm u p] at same
    have := Nat.eq_of_mul_eq_mul_left hp.pos same
    subst u
    by_cases h : p≤q <;> by_cases h' : q≤p <;> simp_all <;> omega

private theorem hit_mem {z : (ℕ×ℕ)×(ℕ×ℕ)} (hz : z∈hits) :
    (z.1∈points ∧ z.2∈points) ∧ bucket z.1=bucket z.2 ∧ z.1.1≠z.2.1 := by
  simpa only [hits,collisions,mem_filter,mem_product,and_assoc] using hz

theorem many_products (population : 2^1011 ≤ pool.card) (localCount : ShortCount) :
    2^1504 ≤ products.card := by
  let encode (z : (ℕ×ℕ)×(ℕ×ℕ)) :=
    ((z.1.1,z.2.1),(z.1.2*z.2.2, decide (z.1.2≤z.2.2)))
  have count : hits.card ≤ ((weights ×ˢ weights) ×ˢ (products ×ˢ (univ : Finset Bool))).card := by
    apply card_le_card_of_injOn encode
    · intro z hz
      have ⟨pairs,_,_⟩ := hit_mem hz
      change _ ∈ (_ ×ˢ _)
      apply mem_product.mpr
      refine ⟨mem_product.mpr ⟨?_,?_⟩,mem_product.mpr ⟨mem_image_of_mem _ hz,mem_univ _⟩⟩
      · exact (mem_product.mp (show z.1∈weights ×ˢ pool from pairs.1)).1
      · exact (mem_product.mp (show z.2∈weights ×ˢ pool from pairs.2)).1
    · intro z hz t ht eq
      have hz' := hit_mem hz
      have ht' := hit_mem ht
      change encode z = encode t at eq
      simp only [encode,Prod.mk.injEq] at eq
      have recover := equal_factors (info hz'.1.1).2.2 (info ht'.1.1).2.2
        (info ht'.1.2).2.2 eq.2.1 eq.2.2
      exact Prod.ext (Prod.ext eq.1.1 recover.1) (Prod.ext eq.1.2 recover.2)
  have w : weights.card = 64 := by rw [weights_def,Nat.card_Ico]
  simp only [card_product,w,card_univ,Fintype.card_bool] at count
  have number := many_hits population localCount
  omega

/-- The two scaled factors in a common bucket give the very first possible
integer trace, before sieving or any later square tests. -/
private theorem ceil_test {x y : ℕ} (lo : 384*U≤x) (pos : 0<y)
    (xy : x<y+H) (yx : y<x+H) :
    (4*x*y-1).sqrt+1=x+y := by
  have xpos : 0<x := (by decide : 0<384*U).trans_le lo
  have diff : ((x:ℤ)-y)^2 < (H:ℤ)^2 := by
    have a' : (x:ℤ)<(y:ℤ)+H := by exact_mod_cast xy
    have b' : (y:ℤ)<(x:ℤ)+H := by exact_mod_cast yx
    have a : (x:ℤ)-(y:ℤ)<H := by omega
    have b : -(H:ℤ)<(x:ℤ)-y := by omega
    nlinarith only [mul_pos (sub_pos.mpr a) (show 0<(H:ℤ)+((x:ℤ)-y) by omega)]
  have small : (H:ℤ)^2+1 ≤ 2*(384*(U:ℤ)) := by decide +kernel
  have xlow : (384:ℤ)*U ≤ x := by exact_mod_cast lo
  have ylow : (0:ℤ)<y := by exact_mod_cast pos
  have a : (x+y-1)^2≤4*x*y-1 := by
    have sub : ((x+y-1:ℕ):ℤ)=(x:ℤ)+y-1 := by rw [Nat.cast_sub (by omega),Nat.cast_add,Nat.cast_one]
    have b : (x+y-1)^2+1≤4*x*y := by
      zify
      rw [sub]
      nlinarith only [diff,small,xlow,ylow]
    omega
  have b : 4*x*y-1<(x+y)^2 := by
    have : 4*x*y≤(x+y)^2 := by nlinarith only [sq_nonneg ((x:ℤ)-y)]
    have : 0<4*x*y := by positivity
    omega
  have h := Nat.le_sqrt.mpr (by simpa only [sq] using a)
  have g := Nat.sqrt_lt.mpr (by simpa only [sq] using b)
  omega

theorem recover {z : (ℕ×ℕ)×(ℕ×ℕ)} (hit : z∈hits) :
    let a := z.1.1
    let b := z.2.1
    let p := z.1.2
    let q := z.2.2
    let n := p*q
    let s := (4*(a*b)*n-1).sqrt+1
    s=a*p+b*q ∧ (n.gcd ((s+(s^2-4*(a*b)*n).sqrt)/2)=p ∨
                   n.gcd ((s+(s^2-4*(a*b)*n).sqrt)/2)=q) := by
  rcases z with ⟨⟨a,p⟩,b,q⟩
  dsimp only
  have ⟨⟨hp,hq⟩,eq,_⟩ := hit_mem hit
  have first := ceil_test (size hp).1 (show 0<b*q from (by decide : 0<384*U).trans_le (size hq).1)
    (near hp hq eq) (near hq hp eq.symm)
  dsimp only at first
  rw [show 4*(a*p)*(b*q)=4*(a*b)*(p*q) by ring] at first
  have pa := info hp
  have qb := info hq
  have unit {s w : ℕ} (sprime : s.Prime) (slo : 3*U/4≤s) (wl : 512≤w) (wh : w<576) : w.Coprime s := by
    apply (sprime.coprime_iff_not_dvd.mpr ?_).symm
    have width : 576≤3*U/4 := by decide +kernel
    exact Nat.not_dvd_of_pos_of_lt (by omega) (wh.trans_le (width.trans slo))
  have cop : (a*b).Coprime (p*q) := Nat.coprime_mul_iff_left.mpr
    ⟨Nat.coprime_mul_iff_right.mpr ⟨unit pa.2.2 pa.2.1.1 pa.1.1 pa.1.2,
      unit qb.2.2 qb.2.1.1 pa.1.1 pa.1.2⟩,
     Nat.coprime_mul_iff_right.mpr ⟨unit pa.2.2 pa.2.1.1 qb.1.1 qb.1.2,
      unit qb.2.2 qb.2.1.1 qb.1.1 qb.1.2⟩⟩
  exact ⟨first,WeightedTracePrefix.shared_gcd rfl rfl cop first⟩


/-- Every product counted above has full width and two distinct prime
factors. The weights and the square both lie in the stated search. -/
theorem product_spec {n : ℕ} (member : n∈products) :
    2^2047≤n ∧ n<2^2048 ∧ ∃ a∈weights, ∃ b∈weights, a≠b ∧
      ∃ p∈pool, ∃ q∈pool, p≠q ∧ n=p*q ∧
        let s := (4*(a*b)*n-1).sqrt+1
        s=a*p+b*q ∧ (n.gcd ((s+(s^2-4*(a*b)*n).sqrt)/2)=p ∨
                       n.gcd ((s+(s^2-4*(a*b)*n).sqrt)/2)=q) := by
  obtain ⟨⟨⟨a,p⟩,b,q⟩,hit,rfl⟩ := mem_image.mp member
  have ⟨⟨xp,yp⟩,eq,diff⟩ := hit_mem hit
  have pi := info xp
  have qi := info yp
  have lower := Nat.mul_le_mul pi.2.1.1 qi.2.1.1
  have upper := Nat.mul_le_mul pi.2.1.2 qi.2.1.2
  have xm := mem_product.mp (show (a,p)∈weights ×ˢ pool from xp)
  have ym := mem_product.mp (show (b,q)∈weights ×ˢ pool from yp)
  refine ⟨(by decide +kernel : 2^2047≤(3*U/4)*(3*U/4)).trans lower,
    upper.trans_lt (by decide +kernel : (7*U/8)*(7*U/8)<2^2048),
    a,xm.1,b,ym.1,diff,p,xm.2,q,ym.2,?_,rfl,recover hit⟩
  intro same
  subst q
  have forward := near xp yp eq
  have backward := near yp xp eq.symm
  dsimp only at diff pi forward backward
  have high : H ≤ p := (by decide +kernel : H≤3*U/4).trans pi.2.1.1
  rcases lt_or_gt_of_ne diff with ab|ba
  · have t := Nat.mul_le_mul_right p (show a+1≤b from ab)
    rw [Nat.add_mul,Nat.one_mul] at t
    omega
  · have t := Nat.mul_le_mul_right p (show b+1≤a from ba)
    rw [Nat.add_mul,Nat.one_mul] at t
    omega


/-- This fixed menu is still very unlikely to work on a uniform eligible
pair. Grant every allocation of each multiplier and even the first 2^32
consecutive traces instead of one. -/
theorem success_fraction (pairs : Finset (ℕ×ℕ)) (subset : pairs⊆MixedPrefixSample.eligible)
    (success : ∀ z∈pairs, ∃ a∈weights, ∃ b∈weights,
      SharedMultiplierPopulation.Splits z.1 z.2 (a*b)) :
    2^460*pairs.card < MixedPrefixSample.eligible.card := by
  let menu := (weights ×ˢ weights).image (fun z => z.1*z.2)
  have w : weights.card=64 := by rw [weights_def,Nat.card_Ico]
  have cap : menu.card≤4096 := card_image_le.trans (by rw [card_product,w])
  have bounds {k : ℕ} (hk : k∈menu) : 0<k ∧ k≤2^2048 := by
    obtain ⟨⟨a,b⟩,hm,rfl⟩ := mem_image.mp hk
    simp only [mem_product,weights_def,mem_Ico] at hm
    exact ⟨Nat.mul_pos (by omega) (by omega), (Nat.mul_le_mul hm.1.2.le hm.2.2.le).trans
      (by decide +kernel : 576*576≤2^2048)⟩
  have all := SharedMultiplierPopulation.catalogue (by decide : 0<4096) (fun _ => menu)
    (fun _ _ => cap) (fun _ _ _ hk => bounds hk) pairs subset (by
      intro z hz
      obtain ⟨a,ha,b,hb,split⟩ := success z hz
      exact ⟨a*b,mem_image.mpr ⟨(a,b),mem_product.mpr ⟨ha,hb⟩,rfl⟩,split⟩)
  apply Nat.lt_of_mul_lt_mul_left (a:=4096)
  rwa [←Nat.mul_assoc,show 4096*(2:ℕ)^460=2^472 by decide +kernel]

end PrimeFactors.WeightedPrimeCrowding
