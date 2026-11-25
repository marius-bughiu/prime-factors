import PrimeFactors.OffsetProjectiveSlopes
import PrimeFactors.OffsetDyadicSlopes
import PrimeFactors.OffsetPrimePowerSlopes

namespace PrimeFactors.OffsetAdaptiveFloor
open Finset OffsetProjectiveSlopes
set_option maxRecDepth 4000
set_option exponentiation.threshold 2048

private abbrev corePrimes := primes131.toFinset
private def ratio (p : ℕ) : ℚ := (p:ℚ) / ((p-1:ℕ):ℚ)

private theorem prime_mem {p : ℕ} (hp : p.Prime) (odd : p≠2) (bound : p≤743) : p∈corePrimes := by
  rcases primes131_complete p (List.mem_range.mpr (by omega)) with m|two|non
  · exact List.mem_toFinset.mpr m
  · contradiction
  · contradiction

private theorem ratio_ge_one {p : ℕ} (hp : 2≤p) : 1≤ratio p := by
  unfold ratio
  rw [Nat.cast_sub (by omega : 1≤p), Nat.cast_one]
  have h : (2:ℚ)≤p := by exact_mod_cast hp
  apply (le_div_iff₀ (by linarith : 0<(p:ℚ)-1)).mpr
  linarith

set_option maxRecDepth 4000 in
private theorem prefix_upper : (primes131.map ratio).prod * (744/743:ℚ)^130 ≤ 8 := by
  decide +kernel

/-- The cost of losing the singular slopes at every odd prime is bounded at
target width, uniformly over the identities of at most 130 distinct primes. -/
theorem totient_loss (S : Finset ℕ) (ok : ∀ p∈S, p.Prime ∧ p≠2) (few : S.card≤130) :
    (∏ p∈S,p) ≤ 8 * ∏ p∈S,(p-1) := by
  let A := S ∩ corePrimes
  let B := S \ corePrimes
  have inside : ∏ p∈A,ratio p ≤ ∏ p∈corePrimes,ratio p := by
    let sub : A ⊆ corePrimes := Finset.inter_subset_right
    have unit (p : ℕ) (hp : p∈corePrimes) := ratio_ge_one
      (primes131_checked.2.2 p (List.mem_toFinset.mp hp)).1.two_le
    have excess : (1:ℚ) ≤ ∏ p∈corePrimes \ A, ratio p := by
      simpa using (Finset.prod_le_prod (s:=corePrimes \ A) (f:=fun _ => (1:ℚ))
        (fun _ _ => by norm_num) (fun p hp => unit p (Finset.mem_sdiff.mp hp).1))
    have pos : 0 ≤ ∏ p∈A,ratio p := Finset.prod_nonneg fun p hp =>
      le_trans (by norm_num : (0:ℚ)≤1) (unit p (sub hp))
    rw [←Finset.prod_sdiff (f:=ratio) sub]
    simpa using mul_le_mul_of_nonneg_right excess pos
  have outside : ∏ p∈B,ratio p ≤ (744/743:ℚ)^130 := by
    calc
      _ ≤ ∏ _p∈B, (744/743:ℚ) := by
        apply Finset.prod_le_prod
        · intro p hp
          exact (ratio_ge_one (ok p (Finset.mem_sdiff.mp hp).1).1.two_le).trans' (by norm_num)
        · intro p hp
          obtain ⟨ps,pr⟩ := Finset.mem_sdiff.mp hp
          have over : 743<p := Nat.lt_of_not_ge fun h => pr (prime_mem (ok p ps).1 (ok p ps).2 h)
          have big : (744:ℚ)≤p := by exact_mod_cast over
          unfold ratio
          rw [Nat.cast_sub (by omega : 1≤p),Nat.cast_one]
          apply (div_le_iff₀ (by linarith : 0<(p:ℚ)-1)).mpr
          linarith
      _ = (744/743:ℚ)^B.card := Finset.prod_const _
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) ((Finset.card_le_card Finset.sdiff_subset).trans few)
  have split : B ∪ A = S := Finset.sdiff_union_inter _ _
  have dis : Disjoint B A := Finset.disjoint_left.mpr (fun _ hb ha =>
    (Finset.mem_sdiff.mp hb).2 (Finset.mem_inter.mp ha).2)
  have sig : ∏ p∈S,ratio p ≤ 8 := calc
    _ = (∏ p∈B,ratio p)*(∏ p∈A,ratio p) := by conv_lhs => rw [←split,Finset.prod_union dis]
    _ ≤ (744/743:ℚ)^130*(∏ p∈corePrimes,ratio p) := by
      apply mul_le_mul outside inside
      · apply Finset.prod_nonneg
        intro p hp
        exact le_trans (by norm_num : (0:ℚ)≤1) (ratio_ge_one (ok p (Finset.mem_inter.mp hp).1).1.two_le)
      · positivity
    _ ≤ 8 := by rw [mul_comm,List.prod_toFinset _ primes131_checked.2.1]; exact prefix_upper
  have den : 0 < ∏ p∈S, ((p-1:ℕ):ℚ) := by
    apply Finset.prod_pos
    intro p hp
    have := (ok p hp).1.two_le
    exact_mod_cast (show 0<p-1 by omega)
  simp only [ratio,Finset.prod_div_distrib] at sig
  have z := (div_le_iff₀ den).mp sig
  have num : (∏ p∈S,(p:ℚ))=((∏ p∈S,p : ℕ):ℚ) := by push_cast; rfl
  rw [num,←Nat.cast_prod] at z
  exact_mod_cast z

def regular (p : ℕ) := (p-1)/2

set_option maxRecDepth 4000 in
private theorem prefix_lower : 2^893 < (primes131.map regular).prod := by decide +kernel

private theorem many_regular (S : Finset ℕ) (ok : ∀ p∈S, p.Prime ∧ p≠2) (many : 131≤S.card) :
    2^893<∏ p∈S,regular p := by
  have count : corePrimes.card=131 := (List.toFinset_card_of_nodup primes131_checked.2.1).trans primes131_checked.1
  have cheap := cheapest_prefix corePrimes S regular 371 (by rwa [count])
    (fun x hx => by
      have := (primes131_checked.2.2 x (List.mem_toFinset.mp (Finset.mem_sdiff.mp hx).1)).2.2
      dsimp [regular]; omega)
    (fun x hx => by
      obtain ⟨xs,out⟩ := Finset.mem_sdiff.mp hx
      have large : 743<x := by
        by_contra! small
        exact out (prime_mem (ok x xs).1 (ok x xs).2 small)
      dsimp [regular]; omega)
  have price := Nat.le_mul_of_pos_left (∏ p∈corePrimes,regular p)
    (show 0<371^(S.card-corePrimes.card) by positivity)
  have checked : 2^893 < ∏ p∈corePrimes,regular p := by
    rw [List.prod_toFinset _ primes131_checked.2.1]
    exact prefix_lower
  exact checked.trans_le (price.trans cheap)

/-- Extra prime-power digits multiply both the local subtree size and its
modulus by the same factor m. Grant the first binary digit for free. -/
theorem scaled_floor (S : Finset ℕ) {m : ℕ} (positive : 0<m)
    (ok : ∀ p∈S, p.Prime ∧ p≠2) (large : 2^1023 < 2*m*(∏ p∈S,p)) :
    2^889 < m*(∏ p∈S,regular p) := by
  by_cases many : 131≤S.card
  · exact (show (2:ℕ)^889≤2^893 by decide +kernel).trans_lt ((many_regular S ok many).trans_le
      (Nat.le_mul_of_pos_left _ positive))
  · have few : S.card≤130 := by omega
    have cost := totient_loss S ok few
    have eq : (∏ p∈S,(p-1)) = 2^S.card*(∏ p∈S,regular p) := by
      calc _ = ∏ p∈S,2*regular p := by
             apply Finset.prod_congr rfl
             intro p hp
             obtain ⟨b,pb⟩ := (ok p hp).1.odd_of_ne_two (ok p hp).2
             dsimp [regular]; omega
           _ = _ := by rw [Finset.prod_mul_distrib,Finset.prod_const]
    rw [eq] at cost
    have scale := Nat.pow_le_pow_right (by decide : 0<2) few
    have bound := Nat.mul_le_mul_left (2*m)
      (cost.trans (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ scale)))
    have numeric : (2:ℕ)^1023 = 2^134 * 2^889 := by decide +kernel
    have scalar : 2*8*(2:ℕ)^130=2^134 := by decide +kernel
    apply (Nat.mul_lt_mul_left (by positivity : 0<(2:ℕ)^134)).mp
    rw [←numeric,←scalar]
    exact (large.trans_le bound).trans_eq (by ring)

/-- Price of the binary coordinate, allowing an odd modulus with a = 0. -/
noncomputable def binaryPrice (a N T : ℕ) : ℕ := match a with
  | 0 => 1
  | k+1 => (OffsetDyadicSlopes.labels k N T).card

/-- A fixed collection of odd prime powers and an optional binary power
has the same obstruction, using the actual finite mask sizes for either
possible quadratic character at each eligible odd prime. -/
theorem fixed_masks_lower (a N T : ℕ) (S : Finset ℕ) (e : ℕ → ℕ) (square : ℕ → Bool)
    (ok : ∀ p∈S, p.Prime ∧ p≠2) (high : 2^1023<2^a*(∏ p∈S,p^(e p+1))) :
    2^889 < binaryPrice a N T * ∏ p∈S,OffsetPrimePowerSlopes.maskCount p (e p) (square p) := by
  let extra := ∏ p∈S,p^e p
  have extraPos : 0<extra := Finset.prod_pos (fun p hp => pow_pos (ok p hp).1.pos _)
  have two : 2^a ≤ 2*2^(a-1) := by cases a <;> simp [pow_succ,mul_comm]
  have binary : 2^(a-1) ≤ binaryPrice a N T := by
    cases a with
    | zero => simp [binaryPrice]
    | succ k => simpa only [Nat.add_sub_cancel,binaryPrice] using OffsetDyadicSlopes.labels_ge_half k N T
  have eq : (∏ p∈S,p^(e p+1))=extra*(∏ p∈S,p) := by simp only [extra,pow_succ,Finset.prod_mul_distrib]
  rw [eq] at high
  have needed : 2^1023<2*(2^(a-1)*extra)*(∏ p∈S,p) := by
    calc _ < _ := high
         _ ≤ (2*2^(a-1))*(extra*(∏ p∈S,p)) := Nat.mul_le_mul_right _ two
         _ = _ := by ring
  have floor := scaled_floor S (m:=2^(a-1)*extra) (Nat.mul_pos (by positivity) extraPos) ok needed
  have per (p : ℕ) (hp : p∈S) : p^e p*regular p ≤ OffsetPrimePowerSlopes.maskCount p (e p) (square p) := by
    letI : Fact p.Prime := ⟨(ok p hp).1⟩
    have lim := OffsetPrimePowerSlopes.modulus_floor (ok p hp).2 (e p) (square p)
    have pos := (ok p hp).1.pos
    have twoPrice : 2*regular p = p-1 := by
      obtain ⟨b,pb⟩ := (ok p hp).1.odd_of_ne_two (ok p hp).2
      dsimp [regular]; omega
    rw [←twoPrice,pow_succ] at lim
    apply (Nat.le_of_mul_le_mul_left (c:=2*p) _ (by positivity))
    convert lim using 1
    ring
  have product := Finset.prod_le_prod' per
  rw [Finset.prod_mul_distrib] at product
  exact floor.trans_le ((show 2^(a-1)*extra*(∏ p∈S,regular p) =
    2^(a-1)*(extra*(∏ p∈S,regular p)) by ring).trans_le (Nat.mul_le_mul binary product))

/-- A decision tree restricted to regular local branches. A new odd prime
has at least (p−1)/2 permanent labels. After the first digit, refining a
regular class by a factor q contributes q children. Each child can choose a
different next operation. The stopping condition grants a free factor of 2
in the modulus and relaxes the reconstruction threshold to 2^1023. -/
inductive Schedule : Finset ℕ → ℕ → Type where
  | stop {S m} (room : 2^1023 < 2*m*(∏ p∈S,p)) : Schedule S m
  | choose {S m} (p : ℕ) (prime : p.Prime) (odd : p≠2) (fresh : p∉S)
      (child : Fin ((p-1)/2) → Schedule (insert p S) m) : Schedule S m
  | refine {S m} (n : ℕ) (child : Fin (n+1) → Schedule S (m*(n+1))) : Schedule S m

noncomputable def Schedule.leaves {S m} : Schedule S m → ℕ
  | .stop _ => 1
  | .choose _ _ _ _ child => ∑ i, (child i).leaves
  | .refine _ child => ∑ i, (child i).leaves

private theorem count_children {d bound price : ℕ} (pos : 0<d) (counts : Fin d → ℕ)
    (h : ∀ i, bound < (price*d)*counts i) : bound < price*(∑ i,counts i) := by
  letI : NeZero d := ⟨pos.ne'⟩
  have sum := Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty (α:=Fin d)) (fun i _ => h i)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id,←Finset.mul_sum] at sum
  apply (Nat.mul_lt_mul_left pos).mp
  simpa only [mul_assoc,mul_left_comm,mul_comm] using sum

theorem Schedule.leaf_bound {S m} (t : Schedule S m) (positive : 0<m)
    (ok : ∀ p∈S,p.Prime ∧ p≠2) :
    2^889 < (m*(∏ p∈S,regular p))*t.leaves := by
  induction t with
  | stop room =>
    simpa [leaves] using scaled_floor _ positive ok room
  | @choose S m p prime odd fresh child ih =>
    have low := prime.two_le
    have pos : 0<(p-1)/2 := by omega
    apply count_children pos (fun i => (child i).leaves)
    intro i
    have valid (q : ℕ) (hq : q∈insert p S) : q.Prime ∧ q≠2 := by
      rcases Finset.mem_insert.mp hq with rfl|old
      · exact ⟨prime,odd⟩
      · exact ok q old
    have one := ih i positive valid
    rw [Finset.prod_insert fresh] at one
    simpa only [regular,mul_assoc,mul_left_comm,mul_comm] using one
  | @refine S m n child ih =>
    apply count_children (Nat.succ_pos n) (fun i => (child i).leaves)
    intro i
    simpa only [mul_assoc,mul_left_comm,mul_comm] using ih i (Nat.mul_pos positive (Nat.succ_pos _)) ok

/-- Uniform leaf count for every adaptive ordering and depth of the regular
local tests. A nonlocal rejection or a lattice search inside a partial class
can end the search earlier and is outside this tree model. -/
theorem adaptive_lower (t : Schedule ∅ 1) : 2^889<t.leaves := by
  simpa using t.leaf_bound (by decide) (by simp)

/-- The tree stopping condition follows from the rectangle threshold at
the target width. -/
theorem threshold_for_target {N M : ℕ} (width : 2^2047≤N) (off : N.sqrt^2<N)
    (room : let T:=N.sqrt; let h:=N-T^2; let J:=CompleteOffsetWork.height h;
      2*J*(T*J/h+1)<M) : 2^1023<M := by
  have floor : 2^1023≤N.sqrt := Nat.le_sqrt'.mpr
    ((show ((2:ℕ)^1023)^2≤2^2047 by decide +kernel).trans width)
  exact floor.trans_lt ((CompleteOffsetWork.rectangle_threshold (T:=N.sqrt) (Nat.sub_pos_of_lt off)).trans room)

end PrimeFactors.OffsetAdaptiveFloor
