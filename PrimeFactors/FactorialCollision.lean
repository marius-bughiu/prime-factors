import PrimeFactors.BinomialDivisorWindow
import Mathlib.Data.Sym.Card

/-! A finite signed-simplex pigeonhole bound for short integer relations.
The refinement step implements the usual volume argument using only finite sets. -/

namespace PrimeFactors.FactorialCollision

open Finset

/-- A mesh fine enough that losing one grid unit per coordinate preserves the
strict volume inequality. All parameters and the resulting mesh are integers. -/
private theorem mesh {A M r : ℕ} (hr : 0<r) (hm : 0<M) (gap : A<M^r) :
    ∃ t S : ℕ, 0<t ∧ S+r<t*M ∧ A*t^r<(S+1)^r := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr.ne'
  let t := (r+1)^2*M^r + r+2
  have ht : 0<t := by dsimp [t]; omega
  have large : r+2≤t*M := (by dsimp [t]; omega : r+2≤t).trans (Nat.le_mul_of_pos_right _ hm)
  let S := t*M-(r+2)
  have eq : t*M=(S+1)+(r+1) := by dsimp [S]; omega
  refine ⟨t,S,ht,by omega,?_⟩
  have grow := abs_pow_sub_pow_le ((t*M:ℕ):ℤ) ((S+1:ℕ):ℤ) (r+1)
  have bound : S+1≤t*M := by omega
  have eb : ((t*M:ℕ):ℤ)-((S+1:ℕ):ℤ)=(r+1:ℕ) := by omega
  have zb : ((S+1:ℕ):ℤ)≤((t*M:ℕ):ℤ) := by exact_mod_cast bound
  have zp := pow_le_pow_left₀ (by positivity : 0≤((S+1:ℕ):ℤ)) zb (r+1)
  rw [abs_of_nonneg (sub_nonneg.mpr zp), eb,abs_of_nonneg (Int.natCast_nonneg _),
    abs_of_nonneg (Int.natCast_nonneg _),abs_of_nonneg (Int.natCast_nonneg _),max_eq_left zb] at grow
  have pert : (t*M)^(r+1) ≤ (S+1)^(r+1)+(r+1)^2*(t*M)^r := by
    have z : ((t*M:ℕ):ℤ)^(r+1) ≤ ((S+1:ℕ):ℤ)^(r+1)+((r+1:ℕ):ℤ)^2*((t*M:ℕ):ℤ)^r := by
      simpa only [Nat.add_sub_cancel, sq, add_comm] using (sub_le_iff_le_add.mp grow)
    exact_mod_cast z
  have small : (r+1)^2*M^r<t := by dsimp [t]; omega
  have loss : (r+1)^2*(t*M)^r<t^(r+1) := by
    rw [Nat.mul_pow, pow_succ t r]
    have pos := Nat.pow_pos ht (n:=r)
    nlinarith only [Nat.mul_lt_mul_of_pos_left small pos]
  have gap' := Nat.mul_le_mul_right (t^(r+1)) (show A+1≤M^(r+1) from gap)
  rw [Nat.mul_pow] at pert
  change A*t^(r+1)<(S+1)^(r+1)
  rw [add_mul,one_mul,mul_comm (M^(r+1))] at gap'
  omega

private abbrev Points (r S : ℕ) := (Fin r → Bool) × Sym (Fin (r+1)) S

/-- Split the half-lines at 0: equal absolute counts on different signs encode
distinct integers even when the count vanishes. The final count is slack. -/
private noncomputable def coord {r S : ℕ} (p : Points r S) (i : Fin r) : ℤ :=
  let c : ℤ := p.2.val.count i.castSucc
  if p.1 i then c else -c-1

private theorem counts {r S : ℕ} (p : Points r S) :
    (∑ i : Fin r, p.2.val.count i.castSucc) + p.2.val.count (Fin.last r)=S := by
  rw [← Fin.sum_univ_castSucc (fun i => p.2.val.count i), Multiset.sum_count_eq_card (by simp)]
  exact p.2.prop

private theorem coord_injective {r S : ℕ} : Function.Injective (@coord r S) := by
  intro p q eq
  have each (i : Fin r) :
      p.1 i=q.1 i ∧ p.2.val.count i.castSucc=q.2.val.count i.castSucc := by
    have h := congrFun eq i
    cases a : p.1 i <;> cases b : q.1 i <;> simp [coord,a,b] at h ⊢ <;> omega
  apply Prod.ext (funext (fun i => (each i).1))
  apply Subtype.ext
  apply Multiset.ext'
  intro i
  refine Fin.lastCases ?_ (fun j => (each j).2) i
  have hp := counts p
  have hq := counts q
  rw [sum_congr rfl (fun j _ => (each j).2)] at hp
  omega

private theorem coord_norm {r S : ℕ} (p : Points r S) : (∑ i, |coord p i|) ≤ ((S+r:ℕ):ℤ) := by
  have term (i : Fin r) : |coord p i| ≤ (p.2.val.count i.castSucc:ℤ)+1 := by
    cases a : p.1 i <;> simp only [coord,a,Bool.false_eq_true,if_false,if_true]
    all_goals apply abs_le.mpr; constructor <;> omega
  have all := sum_le_sum (s:=univ) (fun i _ => term i)
  rw [sum_add_distrib] at all
  have sumCap : (∑ i : Fin r, p.2.val.count i.castSucc) ≤ S := by have := counts p; omega
  have castCap : (∑ i : Fin r, (p.2.val.count i.castSucc:ℤ)) ≤ (S:ℤ) := by exact_mod_cast sumCap
  simpa using all.trans (add_le_add_right castCap _)


/-- Two points in the same class have weighted distance strictly below M when
the size of the label set times the factorial determinant bound is below M^r.
No additivity or periodicity of the labelling is needed. -/
theorem finite_collision {L : Type*} [Fintype L] {r M : ℕ} (hr : 0<r) (hm : 0<M)
    (w : Fin r → ℕ) (hw : ∀ i, 0<w i)
    (room : Fintype.card L * (r.factorial * ∏ i, w i) < M^r)
    (label : (Fin r → ℤ) → L) :
    ∃ u v : Fin r → ℤ, u≠v ∧ label u=label v ∧ ∑ i, |u i-v i| *(w i:ℤ) < (M:ℤ) := by
  classical
  obtain ⟨t,S,ht,rad,more⟩ := mesh hr hm room
  let Q := 2*t
  let step (i : Fin r) := Q*w i
  have hQ : 0<Q := by dsimp [Q]; omega
  have hs (i : Fin r) : 0<step i := Nat.mul_pos hQ (hw i)
  letI (i : Fin r) : NeZero (step i) := ⟨(hs i).ne'⟩
  let coarse (p : Points r S) := fun i => coord p i / (step i:ℤ)
  let residues (p : Points r S) := fun i : Fin r => (coord p i : ZMod (step i))
  let tag (p : Points r S) := (label (coarse p), residues p)
  have count : (S+1)^r≤r.factorial*(S+r).choose r := by
    rw [← Nat.ascFactorial_eq_factorial_mul_choose]
    exact Nat.pow_succ_le_ascFactorial ..
  have many : Fintype.card (L × ((i : Fin r) → ZMod (step i))) < Fintype.card (Points r S) := by
    rw [Fintype.card_prod,Fintype.card_pi]
    simp only [ZMod.card,step,prod_mul_distrib,prod_const,card_univ,Fintype.card_fin,Q,mul_pow]
    rw [show Fintype.card (Points r S) = 2^r*(S+r).choose r by
      simp only [Points,Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,Fintype.card_bool,
        Sym.card_sym_eq_choose]
      rw [show r+1+S-1=S+r by omega, Nat.choose_symm_add]]
    apply Nat.lt_of_mul_lt_mul_left (a:=r.factorial)
    calc
      _ = 2^r * ((Fintype.card L*(r.factorial*∏ i,w i))*t^r) := by ring
      _ < 2^r * ((S+1)^r) := Nat.mul_lt_mul_of_pos_left more (by positivity)
      _ ≤ _ := by simpa only [mul_left_comm] using Nat.mul_le_mul_left (2^r) count
  obtain ⟨a,b,ne,eq⟩ := Fintype.exists_ne_map_eq_of_card_lt tag many
  have rems := congrArg Prod.snd eq
  have split (i : Fin r) : (step i:ℤ)*(coarse a i-coarse b i) = coord a i-coord b i := by
    have e := (ZMod.intCast_eq_intCast_iff _ _ _).mp (congrFun rems i)
    change coord a i % (step i:ℤ)=coord b i % (step i:ℤ) at e
    have ha := Int.ediv_add_emod (coord a i) (step i)
    have hb := Int.ediv_add_emod (coord b i) (step i)
    dsimp only [coarse]
    rw [mul_sub]
    omega
  refine ⟨coarse a,coarse b,?_,congrArg Prod.fst eq,?_⟩
  · intro same
    apply ne
    apply coord_injective
    funext i
    have e := split i
    rw [congrFun same i, sub_self, mul_zero] at e
    omega
  · have scale (i : Fin r) : (Q:ℤ)*(|coarse a i-coarse b i| *(w i:ℤ)) =
        |coord a i-coord b i| := by
      rw [← split,abs_mul,abs_of_nonneg (Int.natCast_nonneg _)]
      dsimp only [step]
      push_cast
      ring
    have dist := sum_le_sum (s:=univ) (fun i _ => abs_sub (coord a i) (coord b i))
    rw [sum_add_distrib] at dist
    have diameter : (∑ i, |coord a i-coord b i|) ≤ 2*((S+r:ℕ):ℤ) := by
      linarith only [dist,coord_norm a,coord_norm b]
    have small : 2*((S+r:ℕ):ℤ)<(Q:ℤ)*(M:ℤ) := by
      exact_mod_cast (by simpa only [Q,mul_assoc] using Nat.mul_lt_mul_of_pos_left rad (by decide : 0<2) : 2*(S+r)<Q*M)
    apply lt_of_mul_lt_mul_left (a:=(Q:ℤ)) _ (Int.natCast_nonneg _)
    simpa only [mul_sum,scale] using diameter.trans_lt small

/-- Equality in the volume test does not suffice for strict shortness. In
dimension one the parity labels give two colors and minimum separation two. -/
theorem equality_counterexample {a b : ℤ} (different : a≠b) (same : (a : ZMod 2)=(b : ZMod 2)) :
    2≤|a-b| := by
  have zero : ((a-b:ℤ):ZMod 2)=0 := by push_cast; rw [same,sub_self]
  have dvd : (2:ℤ)∣a-b := (ZMod.intCast_zmod_eq_zero_iff_dvd ..).mp zero
  by_contra! small
  exact different (sub_eq_zero.mp (Int.eq_zero_of_abs_lt_dvd dvd small))

open BinomialDivisorWindow HigherDivisorWindow Polynomial in
/-- The same Taylor congruences for the cleared binomial basis, with the
factorial volume criterion at every public anchor. -/
theorem short_row {k m n H D : ℕ} (hn : 0<n) (hkH : k≤H) (hd : 0<D)
    (room : n^(m+m.choose 2)*((k+1).factorial*∏ i : Fin (k+1), H.choose i.val) < (D^m)^(k+1))
    (t : ℤ) :
    ∃ v : Fin (k+1) → ℤ, v≠0 ∧ Jets m n t (cleared k v) ∧
      (∑ i, |v i| *(H.choose i.val:ℤ)) < (D:ℤ)^m := by
  classical
  letI (i : Fin m) : NeZero (n^(m-i.val)) := ⟨(pow_pos hn _).ne'⟩
  let label := labels k m n t
  have size : Fintype.card ((i : Fin m) → ZMod (n^(m-i.val))) *
      ((k+1).factorial*∏ i : Fin (k+1), H.choose i.val) < (D^m)^(k+1) := by
    simpa only [Fintype.card_pi,ZMod.card,prod_pow_eq_pow_sum,tag_sum] using room
  obtain ⟨u,v,ne,eq,short⟩ := FactorialCollision.finite_collision (by omega) (pow_pos hd m)
    _ (fun i => Nat.choose_pos (by omega : i.val≤H)) size label
  refine ⟨u-v,sub_ne_zero.mpr ne,?_,by simpa using short⟩
  have z : label (u-v)=0 := by rw [map_sub,eq,sub_self]
  intro i
  have loc := congrFun z i
  change ((taylor t (cleared k (u-v))).coeff i.val : ZMod (n^(m-i.val)))=0 at loc
  simpa only [← Nat.cast_pow] using (ZMod.intCast_zmod_eq_zero_iff_dvd ..).mp loc

end PrimeFactors.FactorialCollision
