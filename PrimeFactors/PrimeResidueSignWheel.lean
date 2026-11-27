import PrimeFactors.PrimeResidueRealization
import PrimeFactors.RootableSignSpan
import PrimeFactors.CharacterDivisorColumn

/-! Every abstract sign row on the six fixed generators occurs at a unit
modulo 9240. Pairing complementary units preserves a prescribed product
residue, and the two prime intervals realize those rows at actual factors. -/
namespace PrimeFactors.PrimeResidueSignWheel

open RootableSignSpan PrimeResidueRealization Finset
set_option maxRecDepth 4096
set_option exponentiation.threshold 4096
attribute [local irreducible] products lane through

def generators : Fin 6 → ℤ := ![-1,2,3,5,7,11]
private def representative : Fin 6 → ℕ := ![479,421,401,697,1081,1009]

private theorem period (i : Fin 6) : 4*(generators i).natAbs ∣ M := by
  fin_cases i <;> decide

private theorem unit_odd {n : ℕ} (u : n.Coprime M) : Odd n := by
  exact Nat.coprime_two_right.mp (u.of_dvd_right (by decide : 2 ∣ M))

theorem periodic {a b : ℕ} (ua : a.Coprime M) (ub : b.Coprime M) (same : Nat.ModEq M a b) :
    publicRow a generators = publicRow b generators := by
  unfold publicRow
  congr 1
  funext i
  exact congrArg bit (CharacterDivisorColumn.periodic (unit_odd ua) (unit_odd ub) _
    (same.of_dvd (period i)))

private theorem sign_mul {a b : ℕ} (ua : a.Coprime M) (ub : b.Coprime M) :
    publicRow (a*b) generators = publicRow a generators + publicRow b generators := by
  have sign {n : ℕ} (u : n.Coprime M) (i : Fin 6) :
      jacobiSym (generators i) n = 1 ∨ jacobiSym (generators i) n = -1 := by
    apply jacobiSym.eq_one_or_neg_one
    rw [Int.gcd_eq_natAbs,Int.natAbs_natCast]
    exact (u.of_dvd_right ((dvd_mul_left _ 4).trans (period i))).symm
  apply LinearMap.ext
  intro v
  simp only [publicRow, row_apply, LinearMap.add_apply, ← sum_add_distrib]
  apply sum_congr rfl
  intro i _
  rw [jacobiSym.mul_right' _ (unit_odd ua).pos.ne' (unit_odd ub).pos.ne',
    bit_mul (sign ua i) (sign ub i),add_mul]

private theorem representative_unit (i : Fin 6) : (representative i).Coprime M := by
  fin_cases i <;> decide

private theorem entry (i j : Fin 6) :
    bit (jacobiSym (generators i) (representative j)) = (if i=j then 1 else 0) := by
  fin_cases i <;> fin_cases j <;> norm_num [generators, representative, bit, Matrix.cons_val]

private theorem single_row (i : Fin 6) : publicRow (representative i) generators = LinearMap.proj i := by
  apply LinearMap.ext
  intro v
  simp [publicRow,row_apply,entry]

private theorem sum_rows (s : Finset (Fin 6)) :
    publicRow (∏ i ∈ s, representative i) generators = ∑ i ∈ s, LinearMap.proj i := by
  induction s using Finset.induction_on with
  | empty =>
    apply LinearMap.ext
    intro v
    simp [publicRow,row_apply,bit]
  | @insert j s outside ih =>
    rw [prod_insert outside,sum_insert outside,sign_mul (representative_unit j)
      (Nat.Coprime.prod_left (fun i _ => representative_unit i)),single_row,ih]

private theorem express (x : Row 6) :
    x = ∑ i ∈ univ.filter (fun i : Fin 6 => x (Pi.single i 1) = 1), LinearMap.proj i := by
  apply LinearMap.ext
  intro v
  rw [LinearMap.sum_apply, Finset.sum_filter]
  conv_lhs => rw [← Finset.univ_sum_single v, map_sum]
  apply sum_congr rfl
  intro i _
  have either (b : Bit) : b=0 ∨ b=1 := (by decide : ∀ b : Bit, b=0 ∨ b=1) b
  rcases either (v i) with zero|one
  · simp [zero]
  · rw [one]
    rcases either (x (Pi.single i 1)) with h|h <;> simp [h,one]

/-- All 64 dual vectors on the fixed six signs occur in the integer wheel. -/
theorem surjective (x : Row 6) :
    ∃ a < M, a.Coprime M ∧ publicRow a generators = x := by
  let s := univ.filter (fun i : Fin 6 => x (Pi.single i 1) = 1)
  let z := ∏ i ∈ s, representative i
  have uz : z.Coprime M := Nat.Coprime.prod_left fun i _ => representative_unit i
  have ua : (z%M).Coprime M := by
    rw [Nat.Coprime,←Nat.gcd_rec,Nat.gcd_comm]
    exact uz
  refine ⟨z%M, Nat.mod_lt _ (by decide), ua, ?_⟩
  exact (periodic ua uz (Nat.mod_modEq z M)).trans ((sum_rows s).trans (express x).symm)

private theorem paired_residue {C a : ℕ} (hc : C < M) (uc : C.Coprime M) (ua : a.Coprime M) :
    ∃ b < M, b.Coprime M ∧ (a*b)%M = C := by
  let c := ZMod.unitOfCoprime C uc
  let u := ZMod.unitOfCoprime a ua
  let v := u⁻¹*c
  let b := (v : ZMod M).val
  have h : ((a*b : ℕ) : ZMod M) = (C : ZMod M) := by
    rw [Nat.cast_mul, ← ZMod.coe_unitOfCoprime a ua, ← ZMod.coe_unitOfCoprime C uc]
    change (u : ZMod M) * ((v : ZMod M).val : ZMod M) = c
    rw [ZMod.natCast_zmod_val]
    simp [v]
  have same := (ZMod.natCast_eq_natCast_iff _ _ _).mp h
  exact ⟨b,(v : ZMod M).val_lt,ZMod.val_coe_unit_coprime v,
    (show (a*b)%M = C%M from same).trans (Nat.mod_eq_of_lt hc)⟩

private theorem generator_nonzero {p : ℕ} (large : 11 < p) (i : Fin 6) :
    (generators i : ZMod p) ≠ 0 := by
  intro zero
  have dvd := Int.natAbs_dvd_natAbs.mpr ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp zero)
  have dv : p ∣ (generators i).natAbs := by simpa only [Int.natAbs_natCast] using dvd
  have facts : 0 < (generators i).natAbs ∧ (generators i).natAbs ≤ 11 := by fin_cases i <;> decide
  exact (Nat.not_dvd_of_pos_of_lt facts.1 (facts.2.trans_lt large)) dv

private theorem local_public {p : ℕ} [Fact p.Prime] : localRow p generators = publicRow p generators := by
  simp only [localRow,publicRow,jacobiSym.legendreSym.to_jacobiSym]

/-- Occurrence on a balanced product with a fixed residue C and prescribed
positive masks. The roots in this predicate may differ between products. -/
def OccursAt (C : ℕ) (L : Submodule Bit (Mask 6)) (P : Set (Row 6)) (n : ℕ) : Prop :=
  ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p < q ∧ 2^1023 ≤ p ∧ q < 2^1024 ∧
    n = p*q ∧ 2^2047 ≤ n ∧ n < 2^2048 ∧ n%M = C ∧
    P = {publicRow p generators, publicRow q generators} ∧
    ∀ v ∈ L, IsSquare (word generators v : ZMod n)

/-- Each compatible pair of sign rows occurs for more than 2^2000 distinct
semiprimes of the required size and product residue. Every prescribed mask
has a square root on each corresponding product. -/
theorem realize (bm : BMOR) {C : ℕ} (hc : C < M) (uc : C.Coprime M)
    {L : Submodule Bit (Mask 6)} {P : Set (Row 6)}
    (compatible : Compatible (publicRow C generators) L P) :
    ∃ S : Finset ℕ, 2^2000 < S.card ∧ ∀ n ∈ S, OccursAt C L P n := by
  obtain ⟨x,y,rfl,sum,known⟩ := compatible
  obtain ⟨a,ha,ua,ax⟩ := surjective x
  obtain ⟨b,hb,ub,ab⟩ := paired_residue hc uc ua
  refine ⟨products a b, product_population bm ha ua hb ub, ?_⟩
  intro n hn
  obtain ⟨p,q,hp,hq,pq,pl,qh,pa,qb,rfl,prodC,width,top⟩ := product_properties (a:=a) (b:=b) (n:=n) hn
  have up : p.Coprime M := by
    rw [Nat.Coprime,Nat.gcd_comm,Nat.gcd_rec M p,pa]
    exact ua
  have uq : q.Coprime M := by
    rw [Nat.Coprime,Nat.gcd_comm,Nat.gcd_rec M q,qb]
    exact ub
  have fixed := prodC.trans ab
  have px : publicRow p generators = x :=
    (periodic up ua (pa.trans (Nat.mod_eq_of_lt ha).symm)).trans ax
  have total := periodic (Nat.coprime_mul_iff_left.mpr ⟨up,uq⟩) uc (fixed.trans (Nat.mod_eq_of_lt hc).symm)
  rw [sign_mul up uq, px, ← sum] at total
  have qy := add_left_cancel total
  refine ⟨p,q,hp,hq,pq,pl,qh,rfl,width,top,fixed,by rw [px,qy],?_⟩
  intro v hv
  letI : Fact p.Prime := ⟨hp⟩
  letI : Fact q.Prime := ⟨hq⟩
  have large : 11 < p := lt_of_lt_of_le (by decide) pl
  apply (rootable_iff ((Nat.coprime_primes hp hq).mpr pq.ne) generators
    (generator_nonzero large) (generator_nonzero (large.trans pq)) v).mpr
  rw [local_public (p:=p),local_public (p:=q),px,qy]
  exact known hv

/-- Abstract compatibility captures precisely the information shared across
actual products with a fixed residue and the stated existence of roots. -/
theorem occurs_iff (bm : BMOR) {C : ℕ} (hc : C < M) (uc : C.Coprime M)
    (L : Submodule Bit (Mask 6)) (P : Set (Row 6)) :
    (∃ n, OccursAt C L P n) ↔ Compatible (publicRow C generators) L P := by
  constructor
  · rintro ⟨n,p,q,pp,qp,pq,pl,_,rfl,_,_,res,rfl,roots⟩
    have cop : (p*q).Coprime M := by
      rw [Nat.Coprime,Nat.gcd_comm,Nat.gcd_rec M (p*q),res]
      exact uc
    obtain ⟨up,uq⟩ := Nat.coprime_mul_iff_left.mp cop
    refine ⟨publicRow p generators, publicRow q generators, rfl, ?_, ?_⟩
    · exact (sign_mul up uq).symm.trans (periodic cop uc (res.trans (Nat.mod_eq_of_lt hc).symm))
    · intro v hv
      letI : Fact p.Prime := ⟨pp⟩
      letI : Fact q.Prime := ⟨qp⟩
      have large : 11 < p := lt_of_lt_of_le (by decide) pl
      rw [←local_public (p:=p), ←local_public (p:=q)]
      exact (rootable_iff ((Nat.coprime_primes pp qp).mpr pq.ne) generators
        (generator_nonzero large) (generator_nonzero (large.trans pq)) v).mp (roots v hv)
  · intro ok
    obtain ⟨S,size,all⟩ := realize bm hc uc ok
    obtain ⟨n,hn⟩ := card_pos.mp ((by decide : 0 < 2^2000).trans size)
    exact ⟨n,all n hn⟩

/-- Exact ambiguity among possible unordered pairs of factor sign vectors
for genuine 2048-bit products, when the public sign row is nonzero. -/
theorem ambiguity_count (bm : BMOR) {C : ℕ} (hc : C < M) (uc : C.Coprime M)
    (L : Submodule Bit (Mask 6)) (positive : L ≤ LinearMap.ker (publicRow C generators))
    (v : Mask 6) (nonzero : publicRow C generators v = 1) :
    Nat.card {P : Set (Row 6) // ∃ n, OccursAt C L P n} =
      2^(6 - Module.finrank Bit L - 1) := by
  exact (Nat.card_congr (Equiv.subtypeEquivRight (occurs_iff bm hc uc L))).trans
    (compatible_count _ L positive v nonzero)

end PrimeFactors.PrimeResidueSignWheel
