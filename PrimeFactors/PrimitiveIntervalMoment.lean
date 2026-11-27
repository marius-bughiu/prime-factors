import PrimeFactors.PrimitiveCharacterParityMoment
import Mathlib.Data.Int.Sqrt

/-! A signed primitive-character kernel summed over an interval of public
length. The result determines the factor sum. Direct evaluation uses B²
ordered kernel entries. Grouping by diagonals uses 2B−1 public gcds for B≥1. -/
namespace PrimeFactors.PrimitiveIntervalMoment

open Finset PrimitiveCharacterParityMoment

/-- Length of the interval, computed from the product. -/
def cutoff (n : ℕ) : ℕ := (n/2).sqrt

/-- The upper layer may occur at 2B+1, where it contributes zero entries. -/
theorem cutoff_bounds {p q : ℕ} (pos : 0<p) (balanced : q<2*p) :
    cutoff (p*q)<p ∧ q≤2*cutoff (p*q)+1 := by
  have lower : cutoff (p*q)<p := Nat.sqrt_lt'.mpr ((Nat.div_lt_iff_lt_mul (by decide : 0<2)).mpr
    ((Nat.mul_lt_mul_of_pos_left balanced pos).trans_eq (by ring)))
  have twice : 2*(q/2)≤q := Nat.mul_div_le q 2
  have square : (q/2)^2*2 ≤ p*q := calc
    _ = (q/2)*(2*(q/2)) := by ring
    _ ≤ _ := Nat.mul_le_mul (by omega) twice
  have half : q/2≤cutoff (p*q) := Nat.le_sqrt'.mpr ((Nat.le_div_iff_mul_le (by decide : 0<2)).mpr square)
  exact ⟨lower,by omega⟩

noncomputable def box (B : ℕ) : Finset (ℕ×ℕ) := (Icc 1 B) ×ˢ Icc 1 B

noncomputable def layer (B k : ℕ) : Finset (ℕ×ℕ) := (box B).filter fun w => w.1+w.2=k

/-- Beyond B the first coordinate ranges from k−B through B. -/
theorem layer_count {B k : ℕ} (large : B<k) : (layer B k).card=2*B+1-k := by
  let f (m : ℕ) := (m,k-m)
  have eq : layer B k = (Icc (k-B) B).image f := by
    ext w
    constructor
    · intro h
      obtain ⟨hbox,sum⟩ := mem_filter.mp h
      obtain ⟨a,b⟩ := mem_product.mp hbox
      rw [mem_Icc] at a b
      exact mem_image.mpr ⟨w.1,mem_Icc.mpr ⟨by omega,a.2⟩,Prod.ext rfl (by dsimp [f]; omega)⟩
    · rintro h
      obtain ⟨m,hm,rfl⟩ := mem_image.mp h
      rw [mem_Icc] at hm
      apply mem_filter.mpr
      exact ⟨mem_product.mpr ⟨mem_Icc.mpr ⟨by dsimp [f]; omega,hm.2⟩,
        mem_Icc.mpr ⟨by dsimp [f]; omega,by dsimp [f]; omega⟩⟩,by dsimp [f]; omega⟩
  rw [eq,card_image_of_injective _ (fun _ _ h => congrArg Prod.fst h),Nat.card_Icc]
  omega

private theorem layer_weight {B k : ℕ} (large : B<k) (v : ℂ) :
    ∑ w ∈ box B, (if w.1+w.2=k then v else 0) = ((2*B+1-k:ℕ):ℂ)*v := by
  rw [←sum_filter]
  change (∑ _w ∈ layer B k, v) = _
  rw [sum_const, nsmul_eq_mul,layer_count large]

noncomputable def aggregate (p q B : ℕ) : ℂ :=
  ∑ w ∈ box B, kernel p q true w.1 w.2

theorem kernel_layers {p q B : ℕ} [Fact p.Prime] [Fact q.Prime] (ord : p<q) (below : B<p)
    (w : ℕ×ℕ) (inside : w∈box B) : kernel p q true w.1 w.2 =
    1-(if w.1+w.2=p then ((p-1:ℕ):ℂ) else 0)-(if w.1+w.2=q then ((q-1:ℕ):ℂ) else 0) := by
  obtain ⟨a,b⟩ := mem_product.mp inside
  rw [mem_Icc] at a b
  have away {r x : ℕ} (hi : B<r) (lo : 1≤x) (cap : x≤B) : ¬r∣x :=
    Nat.not_dvd_of_pos_of_lt lo (cap.trans_lt hi)
  have multiple {r : ℕ} (hi : B<r) : r∣w.1+w.2 ↔ w.1+w.2=r :=
    ⟨fun h => Nat.eq_of_dvd_of_lt_two_mul (by omega) h (by omega),fun h => h ▸ dvd_rfl⟩
  rw [signed_kernel (away below a.1 a.2) (away below b.1 b.2)
    (away (below.trans ord) a.1 a.2) (away (below.trans ord) b.1 b.2)]
  simp only [multiple below,multiple (below.trans ord)]
  split_ifs <;> first | omega | ring

/-- Each prime layer replaces the default contribution 1 by 1−(r−1).
There are no intersecting layers when the two primes are distinct. -/
theorem aggregate_layers {p q B : ℕ} [Fact p.Prime] [Fact q.Prime]
    (ord : p<q) (below : B<p) :
    aggregate p q B = (B:ℂ)^2 - ((2*B+1-p:ℕ):ℂ)*((p-1:ℕ):ℂ)
      - ((2*B+1-q:ℕ):ℂ)*((q-1:ℕ):ℂ) := by
  rw [aggregate,sum_congr rfl (kernel_layers ord below),sum_sub_distrib,sum_sub_distrib,layer_weight below,
    layer_weight (below.trans ord)]
  simp [box,Finset.card_product,pow_two]

/-- Integer form of the exact unnormalized aggregate. -/
def value (n b s : ℤ) : ℤ := b^2+s^2-2*n-(2*b+2)*s+4*b+2

theorem aggregate_value {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (ord : p<q) (balanced : q<2*p) :
    aggregate p q (cutoff (p*q)) =
      ((value (p*q) (cutoff (p*q)) (p+q):ℤ):ℂ) := by
  let B := cutoff (p*q)
  obtain ⟨lo,hi⟩ := cutoff_bounds (Fact.out : p.Prime).pos balanced
  change B<p at lo
  change q≤2*B+1 at hi
  change aggregate p q B = _
  rw [aggregate_layers ord lo]
  change _ = ((value (p*q) B (p+q):ℤ):ℂ)
  unfold value
  push_cast [Nat.cast_sub hi,Nat.cast_sub (ord.le.trans hi),
    Nat.cast_sub (Fact.out : p.Prime).one_le,Nat.cast_sub (Fact.out : q.Prime).one_le]
  ring

/-- Public expression for the sum given the exact integer reading v. -/
def recover (n b v : ℤ) : ℤ := b+1+Int.sqrt (v+2*n-2*b-1)

theorem recover_value {n b s : ℤ} (side : b+1≤s) : recover n b (value n b s) = s := by
  have square : value n b s+2*n-2*b-1 = (s-(b+1))*(s-(b+1)) := by unfold value; ring
  rw [recover,square,Int.sqrt_eq,Int.natAbs_of_nonneg (sub_nonneg.mpr side)]
  ring

/-- A single exact aggregate at the public length determines the true sum.
The aggregate itself is defined using the two local character families. -/
theorem recover_from_aggregate {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (ord : p<q) (balanced : q<2*p) {v : ℤ}
    (reading : aggregate p q (cutoff (p*q))=(v:ℂ)) :
    recover (p*q) (cutoff (p*q)) v=p+q := by
  have eq : (value (p*q) (cutoff (p*q)) (p+q):ℤ) = v := by
    exact_mod_cast (aggregate_value ord balanced).symm.trans reading
  rw [←eq]
  apply recover_value
  have lo := (cutoff_bounds (Fact.out : p.Prime).pos balanced).1
  omega

/-- At 15, the larger-prime layer lies just beyond the last populated diagonal. -/
theorem control_15 : cutoff 15=2 ∧ (layer 2 3).card=2 ∧ (layer 2 5).card=0 ∧
    aggregate 3 5 2=0 ∧ recover 15 2 0=8 := by
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  letI : Fact (Nat.Prime 5) := ⟨by decide⟩
  refine ⟨by decide +kernel,by rw [layer_count (by decide)],by rw [layer_count (by decide)],?_,by decide +kernel⟩
  rw [aggregate_layers (by decide) (by decide)]
  norm_num

/-- The full triangular multiplicity, including the rising part of the square. -/
theorem triangular {B t : ℕ} (lo : 2≤t) :
    (layer B t).card = min (t-1) (2*B+1-t) := by
  by_cases upper : B<t
  · rw [layer_count upper,min_eq_right (by omega)]
  rw [min_eq_left (by omega)]
  let f (m : ℕ) := (m,t-m)
  have eq : layer B t = (Icc 1 (t-1)).image f := by
    ext w
    constructor
    · intro hw
      obtain ⟨hi,sum⟩ := mem_filter.mp hw
      obtain ⟨a,b⟩ := mem_product.mp hi
      rw [mem_Icc] at a b
      exact mem_image.mpr ⟨w.1,mem_Icc.mpr ⟨a.1,by omega⟩,Prod.ext rfl (by dsimp [f]; omega)⟩
    · intro hw
      obtain ⟨m,hm,rfl⟩ := mem_image.mp hw
      rw [mem_Icc] at hm
      apply mem_filter.mpr
      exact ⟨mem_product.mpr ⟨mem_Icc.mpr ⟨hm.1,by dsimp [f]; omega⟩,
        mem_Icc.mpr ⟨by dsimp [f]; omega,by dsimp [f]; omega⟩⟩,by dsimp [f]; omega⟩
  rw [eq,card_image_of_injective _ (fun _ _ h => congrArg Prod.fst h),Nat.card_Icc]
  omega

/-- Before 2p, a nontrivial gcd is precisely the prime diagonal itself. -/
theorem gcd_diagonal {p q t : ℕ} [Fact p.Prime] [Fact q.Prime] (ord : p<q)
    (pos : 0<t) (hi : t<2*p) :
    (p*q).gcd t = if t=p then p else if t=q then q else 1 := by
  by_cases ep : t=p
  · rw [if_pos ep,ep]
    exact Nat.gcd_eq_right (dvd_mul_right ..)
  by_cases eq : t=q
  · rw [if_neg ep,if_pos eq,eq]
    exact Nat.gcd_eq_right (dvd_mul_left ..)
  rw [if_neg ep,if_neg eq]
  have np : ¬p∣t := fun h => ep (Nat.eq_of_dvd_of_lt_two_mul pos.ne' h hi)
  have nq : ¬q∣t := fun h => eq (Nat.eq_of_dvd_of_lt_two_mul pos.ne' h (by omega))
  exact (((Fact.out : p.Prime).coprime_iff_not_dvd.mpr np).mul
    ((Fact.out : q.Prime).coprime_iff_not_dvd.mpr nq)).gcd_eq_one

/-- The signed kernel is the public integer 2−gcd(N,m+n) throughout the box. -/
theorem kernel_gcd {p q B : ℕ} [Fact p.Prime] [Fact q.Prime] (ord : p<q) (below : B<p)
    (w : ℕ×ℕ) (inside : w∈box B) : kernel p q true w.1 w.2 = 2-((p*q).gcd (w.1+w.2):ℂ) := by
  obtain ⟨a,b⟩ := mem_product.mp inside
  rw [mem_Icc] at a b
  rw [kernel_layers ord below w inside,gcd_diagonal ord (by omega) (by omega)]
  simp only [Nat.cast_sub (Fact.out : p.Prime).one_le, Nat.cast_sub (Fact.out : q.Prime).one_le, Nat.cast_one]
  split_ifs <;> first | omega | ring

/-- One gcd for each possible diagonal reproduces the full character aggregate.
The formula applies at the public cutoff by cutoff_bounds. -/
theorem gcd_aggregate {p q B : ℕ} [Fact p.Prime] [Fact q.Prime] (ord : p<q) (below : B<p) :
    aggregate p q B = ∑ t ∈ Icc 2 (2*B),
      ((min (t-1) (2*B+1-t):ℕ):ℂ)*(2-((p*q).gcd t:ℂ)) := by
  let f (w : ℕ×ℕ) := w.1+w.2
  have maps : Set.MapsTo f (box B) (Icc 2 (2*B)) := by
    intro w hw
    obtain ⟨a,b⟩ := mem_product.mp hw
    rw [mem_Icc] at a b
    exact mem_Icc.mpr ⟨by dsimp [f]; omega,by dsimp [f]; omega⟩
  rw [aggregate,sum_congr rfl (kernel_gcd ord below)]
  rw [←sum_fiberwise_of_maps_to' maps (fun t => 2-((p*q).gcd t:ℂ))]
  apply sum_congr rfl
  intro t ht
  change (∑ _w ∈ layer B t, (2-((p*q).gcd t:ℂ))) = _
  rw [sum_const,nsmul_eq_mul,triangular (mem_Icc.mp ht).1]

theorem diagonal_count (B : ℕ) : (Icc 2 (2*B)).card=2*B-1 := by rw [Nat.card_Icc]; omega

set_option exponentiation.threshold 4096 in
theorem full_width_cutoff {n : ℕ} (full : 2^2047≤n) : 2^1023≤cutoff n := by
  apply Nat.le_sqrt'.mpr
  exact (Nat.le_div_iff_mul_le (by decide : 0<2)).mpr
    ((show (2^1023)^2*2=2^2047 by decide +kernel).le.trans full)

/-- Both exceptional diagonals occur at 143. -/
theorem control_143 : cutoff 143=8 ∧ (layer 8 11).card=6 ∧ (layer 8 13).card=4 ∧
    aggregate 11 13 8=(-44:ℂ) ∧ recover 143 8 (-44)=24 := by
  letI : Fact (Nat.Prime 11) := ⟨by decide⟩
  letI : Fact (Nat.Prime 13) := ⟨by decide⟩
  refine ⟨by decide +kernel,by rw [layer_count (by decide)],by rw [layer_count (by decide)],?_,by decide +kernel⟩
  rw [aggregate_layers (by decide) (by decide)]
  norm_num

end PrimeFactors.PrimitiveIntervalMoment
