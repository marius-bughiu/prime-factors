import PrimeFactors.FactorEndingDecoder
import PrimeFactors.TwoPowerGuessShare
import PrimeFactors.DyadicFactorClueGain

/-! How much of the uniform ordered residue-pair population can a guessed
sum cover if receiving that sum also settles both low factor endings? -/
namespace PrimeFactors.DecidableSumGuessMass

open Finset PrimeSquareSumWeights ObservableSeparationDepth FactorEndingDecoder
open private PrimeFactors.CombinedSumWeights.weight_first from PrimeFactors.CombinedSumWeights
open private PrimeFactors.DyadicFactorClueGain.one_class from PrimeFactors.DyadicFactorClueGain

/-- Each first coordinate is counted once: its partner is s−x. -/
noncomputable def roots (N s e : ℕ) : Finset ℕ := (range (2^e)).filter
  fun x => (x : ZMod (2^e))*(s-x)=(N : ZMod (2^e))

theorem weight_eq (N s e : ℕ) : weight N (s:ZMod (2^e))=(roots N s e).card := by
  classical
  rw [PrimeFactors.CombinedSumWeights.weight_first,Nat.card_eq_fintype_card,Fintype.card_subtype]
  apply card_nbij' ZMod.val (fun x : ℕ => (x:ZMod (2^e)))
  · intro x hx
    simpa only [roots,mem_filter,mem_range,ZMod.val_lt,true_and,ZMod.natCast_zmod_val]
      using (mem_filter.mp hx).2
  · intro x hx
    exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hx).2⟩
  · intro x _
    exact ZMod.natCast_zmod_val _
  · intro x hx
    exact (ZMod.val_natCast ..).trans (Nat.mod_eq_of_lt (mem_range.mp (mem_filter.mp hx).1))

theorem ready_congr {N N' s : ℤ} {k e : ℕ} (prod : N ≡ N' [ZMOD (2:ℤ)^e]) :
    ready N s k e = ready N' s k e := by
  have discr : s^2-4*N ≡ s^2-4*N' [ZMOD (2:ℤ)^(e+2)] := by
    obtain ⟨w,eq⟩ := Int.modEq_iff_dvd.mp prod
    exact Int.modEq_iff_dvd.mpr ⟨-w,by rw [pow_add]; linear_combination -4*eq⟩
  have eq : reading N s e=reading N' s e := discr
  simp only [ready,eq]

theorem endings_congr {N N' s : ℤ} {k e : ℕ} (prod : N ≡ N' [ZMOD (2:ℤ)^e]) :
    endings N s k e = endings N' s k e := by
  have same := (Int.ModEq.refl ((s/2)^2)).sub prod
  simp only [endings, same.eq]

private theorem prod_odd {a b : ℤ} {N e : ℕ} (he : 1≤e) (odd : Odd N)
    (con : a*b ≡ (N:ℤ) [ZMOD (2:ℤ)^e]) : Odd a ∧ Odd b := by
  have low := con.of_dvd (show (2:ℤ)∣2^e from dvd_pow_self 2 (by omega))
  have no : Odd (N:ℤ) := by exact_mod_cast odd
  have eq : (a*b)%2=(N:ℤ)%2 := low
  exact Int.odd_mul.mp (Int.odd_iff.mpr (eq.trans (Int.odd_iff.mp no)))

/-- Every first coordinate contributing to a ready sum has one of the two
endings actually returned by the decoder. This uses only the product remainder. -/
theorem root_ending {N s k e x : ℕ} (hk : 3≤k) (enough : k≤e) (odd : Odd N)
    (accept : ready N s k e=true) (hx : x∈roots N s e) :
    x%2^k=(endings N s k e).1.toNat ∨ x%2^k=(endings N s k e).2.toNat := by
  let M : ℤ := 2^e
  let y : ℤ := ((s:ℤ)-x)%M+M
  have yp : y ≡ (s:ℤ)-x [ZMOD M] := by
    change (((s:ℤ)-x)%M+M)%M=_
    simp
  have eq : (x:ℤ)*((s:ℤ)-x) ≡ (N:ℤ) [ZMOD (2:ℤ)^e] := by
    rw [show (2:ℤ)^e=((2^e:ℕ):ℤ) by norm_num]
    apply (ZMod.intCast_eq_intCast_iff _ _ (2^e)).mp
    simpa only [Int.cast_mul,Int.cast_sub,Int.cast_natCast] using (mem_filter.mp hx).2
  have prod := (yp.mul_left (x:ℤ)).trans eq
  have sum : (s:ℤ) ≡ (x:ℤ)+y [ZMOD M] := by simpa only [add_sub_cancel] using (yp.add_left (x:ℤ)).symm
  have xo := prod_odd (by omega : 1≤e) odd prod
  have distinct : (x:ℤ)≠y := by
    have lt : (x:ℤ)<M := by dsimp only [M]; exact_mod_cast mem_range.mp (mem_filter.mp hx).1
    have nonneg := Int.emod_nonneg ((s:ℤ)-x) (by dsimp [M]; positivity : M≠0)
    dsimp only [y]
    omega
  have gate : ready ((x:ℤ)*y) s k e=true := (ready_congr prod).trans accept
  have det := (ready_iff hk (by omega) xo.1 xo.2 distinct sum).mp gate
  have output := endings_correct xo.1 xo.2 (by omega : 1≤e) enough sum det
  rw [endings_congr prod] at output
  have low : (((x:ℤ)%(2:ℤ)^k).toNat)=x%2^k := by
    have eq : (x:ℤ)%(2:ℤ)^k = ((x%2^k:ℕ):ℤ) := by push_cast; rfl
    rw [eq,Int.toNat_natCast]
  rcases output with h|h
  · exact Or.inl (low.symm.trans (congrArg (fun p : ℤ×ℤ => p.1.toNat) h).symm)
  · exact Or.inr (low.symm.trans (congrArg (fun p : ℤ×ℤ => p.2.toNat) h).symm)

private noncomputable def lane (k e r : ℕ) := (range (2^e)).filter fun x => x ≡ r [MOD 2^k]

private theorem lane_card {k e : ℕ} (le : k≤e) (r : ℕ) : (lane k e r).card=2^(e-k) :=
  PrimeFactors.DyadicFactorClueGain.one_class le r

/-- One sum can cover at most as many ordered pairs as the one or two
k-bit endings that it certifies. A coincident pair has only one such class. -/
theorem weight_bound {N s k e : ℕ} (hk : 3≤k) (enough : k≤e) (odd : Odd N)
    (accept : ready N s k e=true) :
    weight N (s : ZMod (2^e)) ≤
      (if (endings N s k e).1=(endings N s k e).2 then 1 else 2)*2^(e-k) := by
  let a := (endings N s k e).1.toNat
  let b := (endings N s k e).2.toNat
  have in_lane (x r : ℕ) (hx : x∈roots N s e) (hr : x%2^k=r) : x∈lane k e r := by
    apply mem_filter.mpr
    refine ⟨(mem_filter.mp hx).1,?_⟩
    change x%2^k=r%2^k
    rw [←hr,Nat.mod_mod]
  have cover : roots N s e ⊆ lane k e a ∪ lane k e b := by
    intro x hx
    exact mem_union.mpr ((root_ending hk enough odd accept hx).imp (in_lane x a hx) (in_lane x b hx))
  rw [weight_eq]
  split_ifs with same
  · have equal : a=b := congrArg Int.toNat same
    rw [equal,union_self] at cover
    simpa only [one_mul,lane_card enough] using card_le_card cover
  · calc
      _ ≤ _ := card_le_card cover
      _ ≤ _ := card_union_le ..
      _ = _ := by rw [lane_card enough,lane_card enough,two_mul]

/-- Each odd first coordinate has exactly one partner for the fixed product. -/
theorem population {N e : ℕ} (odd : Odd N) (ep : 0<e) : Nat.card (Pairs N (2^e))=2^(e-1) := by
  rw [total ((ZMod.isUnit_iff_coprime N _).mpr (odd.coprime_two_right.pow_right e)),
    Nat.totient_prime_pow Nat.prime_two ep]
  simp

/-- Probability bound on a uniform ordered pair of odd residues with a
fixed product (there are 2^(e−1) pairs). -/
theorem probability_bound {N s k e : ℕ} (hk : 3≤k) (enough : k≤e) (odd : Odd N)
    (accept : ready N s k e=true) :
    (weight N (s:ZMod (2^e)):ℚ)/(2:ℚ)^(e-1) ≤ 1/(2:ℚ)^(k-2) := by
  have raw := weight_bound hk enough odd accept
  have top : weight N (s:ZMod (2^e))≤2*2^(e-k) := by split at raw <;> omega
  rw [div_le_div_iff₀ (by positivity) (by positivity),one_mul]
  calc
    _ ≤ ((2:ℚ)*2^(e-k))*2^(k-2) := mul_le_mul_of_nonneg_right (by exact_mod_cast top) (by positivity)
    _ = _ := by
      rw [mul_assoc,←pow_add,mul_comm,←pow_succ]
      congr 1
      omega


/-- If a ready guess returns two equal endings, the uniform bound halves. -/
theorem singleton_probability {N s k e : ℕ} (hk : 3≤k) (enough : k≤e) (odd : Odd N)
    (accept : ready N s k e=true) (same : (endings N s k e).1=(endings N s k e).2) :
    (weight N (s:ZMod (2^e)):ℚ)/(2:ℚ)^(e-1) ≤ 1/(2:ℚ)^(k-1) := by
  have top := weight_bound hk enough odd accept
  rw [if_pos same,one_mul] at top
  rw [div_le_div_iff₀ (by positivity) (by positivity),one_mul]
  calc
    _ ≤ (2:ℚ)^(e-k)*2^(k-1) := mul_le_mul_of_nonneg_right (by exact_mod_cast top) (by positivity)
    _ = _ := by rw [←pow_add]; congr 1; omega

private theorem actual_root {p q x e : ℕ} :
    x∈roots (p*q) (p+q) e ↔ x<2^e ∧ (2:ℤ)^e ∣ ((x:ℤ)-p)*(x-q) := by
  simp only [roots,mem_filter,mem_range]
  apply and_congr_right
  intro _
  have ringEq : (x:ZMod (2^e))*((↑(p+q:ℕ):ZMod (2^e))-x)=↑(p*q:ℕ) ↔
      ((x:ZMod (2^e))-p)*(x-q)=0 := by
    push_cast
    constructor <;> intro h <;> linear_combination -h
  rw [ringEq]
  have cast := ZMod.intCast_zmod_eq_zero_iff_dvd (((x:ℤ)-p)*(x-q)) (2^e)
  simpa only [Int.cast_mul,Int.cast_sub,Int.cast_natCast,Nat.cast_pow,Nat.cast_ofNat] using cast

private theorem congr_dvd (x p k : ℕ) :
    x ≡ p [MOD 2^k] ↔ (2:ℤ)^k ∣ (x:ℤ)-p := by
  have cast : x ≡ p [MOD 2^k] ↔ (x:ℤ) ≡ p [ZMOD (2:ℤ)^k] := by
    exact_mod_cast Int.natCast_modEq_iff.symm
  rw [cast,Int.modEq_comm,Int.modEq_iff_dvd]

/-- If the other ending is known modulo 2^d, an entire k-bit class stays
in the same sum fiber through precision k+d. -/
private theorem extend_lane {x p q : ℤ} {k d e : ℕ} (short : e≤k+d) (le : d≤k)
    (agree : (2:ℤ)^d ∣ q-p) (near : (2:ℤ)^k ∣ x-p) :
    (2:ℤ)^e ∣ (x-p)*(x-q) := by
  have other : (2:ℤ)^d ∣ x-q := by
    rw [show x-q=(x-p)-(q-p) by ring]
    exact dvd_sub ((pow_dvd_pow (2:ℤ) le).trans near) agree
  exact (pow_dvd_pow (2:ℤ) short).trans (by rw [pow_add]; exact mul_dvd_mul near other)

/-- At the first sufficient precision, the sum has every lift of both
compatible endings. This includes the exceptional gap order k−1. -/
theorem at_first_depth {p q k t : ℕ} {g : ℤ} (hk : 3≤k)
    (gap : (q:ℤ)-p=(2:ℤ)^t*g) (odd : Odd g) :
    let e := FactorPairSeparationDepth.depth k t
    weight (p*q) ((p+q:ℕ):ZMod (2^e)) =
      (if p ≡ q [MOD 2^k] then 1 else 2)*2^(e-k) := by
  let e := FactorPairSeparationDepth.depth k t
  change weight _ (_:ZMod (2^e))=_
  have short : e≤k+min k t := by dsimp [e,FactorPairSeparationDepth.depth]; split_ifs <;> omega
  have enough : k≤e := by dsimp [e,FactorPairSeparationDepth.depth]; split_ifs <;> omega
  have agree : (2:ℤ)^(min k t) ∣ (q:ℤ)-p := (pow_dvd_pow _ (min_le_right ..)).trans ⟨g,gap⟩
  have sets : roots (p*q) (p+q) e=lane k e p ∪ lane k e q := by
    ext x
    rw [actual_root]
    simp only [lane,mem_union,mem_filter,mem_range,congr_dvd]
    constructor
    · rintro ⟨width,ok⟩
      exact ((FactorPairSeparationDepth.at_depth hk gap odd) x ok).imp (And.intro width) (And.intro width)
    · rintro (⟨width,a⟩|⟨width,b⟩)
      · exact ⟨width,extend_lane short (min_le_left ..) agree a⟩
      · have rev : (2:ℤ)^min k t ∣ (p:ℤ)-q := by rw [←neg_sub]; exact dvd_neg.mpr agree
        exact ⟨width,by rw [mul_comm]; exact extend_lane short (min_le_left ..) rev b⟩
  rw [weight_eq,sets]
  split_ifs with same
  · have lanes : lane k e p=lane k e q := by
      apply filter_congr
      exact fun _ _ => ⟨fun h => h.trans same,fun h => h.trans same.symm⟩
    rw [lanes,union_self,lane_card enough,one_mul]
  · have dis : Disjoint (lane k e p) (lane k e q) := disjoint_left.mpr (fun _ hp hq =>
      same ((Nat.ModEq.symm (mem_filter.mp hp).2).trans (mem_filter.mp hq).2))
    rw [card_union_of_disjoint dis,lane_card enough,lane_card enough,two_mul]

/-- Maximum probability is realized at the first sufficient precision on
each genuine pair with distinct k-bit endings. The matching singleton
probability is exactly half as large. -/
theorem first_probability {p q k t : ℕ} {g : ℤ} (hk : 3≤k)
    (gap : (q:ℤ)-p=(2:ℤ)^t*g) (odd : Odd g) (oddProduct : Odd (p*q)) :
    let e := FactorPairSeparationDepth.depth k t
    (weight (p*q) ((p+q:ℕ):ZMod (2^e)):ℚ)/Nat.card (Pairs (p*q) (2^e)) =
      if p ≡ q [MOD 2^k] then 1/(2:ℚ)^(k-1) else 1/(2:ℚ)^(k-2) := by
  let e := FactorPairSeparationDepth.depth k t
  change (weight _ (_:ZMod (2^e)):ℚ)/Nat.card (Pairs (p*q) (2^e))=_
  have enough : k≤e := by dsimp [e,FactorPairSeparationDepth.depth]; split_ifs <;> omega
  rw [population oddProduct (by omega : 0<e),Nat.cast_pow,Nat.cast_ofNat,at_first_depth hk gap odd]
  change (((if _ then 1 else 2)*2^(e-k):ℕ):ℚ)/2^(e-1)=_
  split_ifs
  · simp only [one_mul,Nat.cast_pow,Nat.cast_ofNat]
    rw [div_eq_div_iff (by positivity) (by positivity),one_mul,←pow_add]
    congr 1; omega
  · push_cast
    rw [div_eq_div_iff (by positivity) (by positivity),one_mul,mul_assoc,←pow_add,mul_comm,←pow_succ]
    congr 1; omega

/-- Histogram of all attained sum labels in the bounded comparison. -/
def controlWeight (s : ℕ) : ℕ :=
  if s=46 ∨ s=82 then 16 else if s=2 ∨ s=62 ∨ s=66 ∨ s=126 then 8 else 0

/-- All 64 ordered pairs for product one modulo 128 occupy six sum
labels. The two most frequent labels each cover 16 pairs. -/
theorem control_table (s : Fin 128) : weight 1 (s.val:ZMod 128)=controlWeight s.val := by
  have all : ∀ s : Fin 128, (roots 1 s.val 7).card=controlWeight s.val := by decide +kernel
  exact (weight_eq 1 s.val 7).trans (all s)

/-- Among these six supported labels, only 62 and 66 determine both
five-bit factor endings. Each covers eight of the 64 pairs. -/
theorem control_ready :
    ready 1 46 5 7=false ∧ ready 1 82 5 7=false ∧
    ready 1 62 5 7=true ∧ ready 1 66 5 7=true ∧
    ready 1 2 5 7=false ∧ ready 1 126 5 7=false := by
  norm_num [ready,reading,zeroBits,FactorPairSeparationDepth.depth,Nat.log2_eq_log_two]

end PrimeFactors.DecidableSumGuessMass
