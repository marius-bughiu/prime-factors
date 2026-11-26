import PrimeFactors.PersistentLocalSurvivors

/-! Sum residues of an odd product at powers of two. The underlying counts are
classical (Bower, Evans, Luo and Miller, Theorem 3.3). The explicit normal forms
below support a direct test without enumerating residue-class factors. -/

namespace PrimeFactors.PrimePowerSumFilter
open LocalMidpointLanes

noncomputable section

private theorem root_at {e k : ℕ} {D : ℤ} (le : k ≤ e) (ok : hasRoot e D) :
    IsSquare (D : ZMod (2^k)) := by
  obtain ⟨z,hz⟩ := ok
  have h := (ZMod.intCast_zmod_eq_zero_iff_dvd (D-z^2) (2^k)).mpr
    (by simpa using (pow_dvd_pow (2:ℤ) le).trans hz)
  push_cast at h
  exact ⟨z,by simpa [pow_two] using sub_eq_zero.mp h⟩

private theorem four_cancel (e : ℕ) (d : ℤ) :
    hasRoot (e+2) (4*d) ↔ hasRoot e d := by
  constructor
  · rintro ⟨z,k,hz⟩
    rw [pow_add] at hz
    have hz2 : (2:ℤ)∣z^2 := ⟨2*d-2*2^e*k,by linear_combination -hz⟩
    obtain ⟨w,rfl⟩ := Int.prime_two.dvd_of_dvd_pow hz2
    exact ⟨w,k,by linarith only [show 4*(d-w^2)=4*(2^e*k) by linear_combination hz]⟩
  · rintro ⟨z,k,hz⟩
    exact ⟨2*z,k,by rw [pow_add]; linear_combination 4*hz⟩

/-- Testing the discriminant of an even sum needs two extra bits when
the desired factorization is taken modulo a power of two. -/
theorem full_discriminant (e : ℕ) (N h : ℤ) :
    AdmissibleSum (N : ZMod (2^e)) (2*h) ↔ hasRoot (e+2) ((2*h)^2-4*N) := by
  rw [midpoint_iff_integer,show (2*h)^2-4*N=4*(h^2-N) by ring,four_cancel]

private theorem three_digits : ∀ n h : ZMod 8, 2*n=6 →
    (∀ d : ZMod 8, h^2-n=d*d → 2*h=n+1) ∧ (2*h=n+1 → h^2-n=1) := by decide +kernel

private theorem five_digits : ∀ n h : ZMod 32, 4*n=20 →
    (∀ d : ZMod 32, h^2-n=d*d → 2*h=n+1 ∨ 2*h=-(n+1)) ∧
    ((2*h=n+1 ∨ 2*h=-(n+1)) → h^2-n=4) := by decide +kernel

private theorem from_mod {m : ℕ} {a b : ℤ} (h : (a : ZMod m)=b) : (m:ℤ)∣a-b := by
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ m).mp
  push_cast
  exact sub_eq_zero.mpr h

/-- At and beyond eight, one complete sum class survives if N is 3 modulo 4. -/
theorem three_mod_four {N h : ℤ} (n : N%4=3) {e : ℕ} (depth : 3≤e) :
    AdmissibleSum (N : ZMod (2^e)) (2*h) ↔ 2*(h : ZMod 8)=N+1 := by
  rw [midpoint_iff_integer]
  have bits : 2*(N : ZMod 8)=6 := by
    have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd (2*N-6) 8).mpr
      (show (8:ℤ) ∣ 2*N-6 from ⟨N/4,by omega⟩)
    push_cast at hz
    exact sub_eq_zero.mp hz
  obtain ⟨nec,suff⟩ := three_digits (N : ZMod 8) h bits
  constructor
  · intro ok
    obtain ⟨d,hd⟩ := root_at depth ok
    exact nec d (by simpa using hd)
  · intro ok
    have hv : (8:ℤ) ∣ (h^2-N)-1 := from_mod (m:=8) (by simpa using suff ok)
    exact square_unit _ ((pow_dvd_pow (2:ℤ) (min_le_right e 3)).trans hv)

/-- At and beyond 32, just the two signed classes of N+1 survive if N is 5 modulo 8. -/
theorem five_mod_eight {N h : ℤ} (n : N%8=5) {e : ℕ} (depth : 5≤e) :
    AdmissibleSum (N : ZMod (2^e)) (2*h) ↔
      2*(h : ZMod 32)=N+1 ∨ 2*(h : ZMod 32)=-(N+1) := by
  rw [midpoint_iff_integer]
  have bits : 4*(N : ZMod 32)=20 := by
    have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd (4*N-20) 32).mpr
      (show (32:ℤ) ∣ 4*N-20 from ⟨N/8,by omega⟩)
    push_cast at hz
    exact sub_eq_zero.mp hz
  obtain ⟨nec,suff⟩ := five_digits (N : ZMod 32) h bits
  constructor
  · intro ok
    obtain ⟨d,hd⟩ := root_at depth ok
    exact nec d (by simpa using hd)
  · intro ok
    have hv : (32:ℤ) ∣ (h^2-N)-4 := from_mod (m:=32) (by simpa using suff ok)
    obtain ⟨z,hz⟩ := hv
    have eq : h^2-N=4*(1+8*z) := by linarith
    rw [eq,show e=(e-2)+2 by omega,four_cancel]
    exact square_unit _ ((pow_dvd_pow (2:ℤ) (min_le_right _ 3)).trans ⟨z,by ring⟩)

/-- One extra bit is insufficient for the discriminant at precision five. -/
theorem one_extra_fails :
    hasRoot 6 ((2:ℤ)^2-4*77) ∧ ¬AdmissibleSum (77 : ZMod 32) 2 := by
  refine ⟨⟨4,-5,by decide⟩,?_⟩
  have h := five_mod_eight (N:=77) (h:=1) (e:=5) (by decide) (by decide)
  simpa using h.not.mpr (by decide)

/-- The nonlinear coordinate for either sign of a unit-product sum. -/
noncomputable def digit {m : ℕ} (y : ZMod m) := y+4*y^2

private theorem odd_unit (k : ℕ) (v : ZMod (2^k)) : IsUnit (1+4*v) := by
  have odd : ¬2∣1+4*v.val := by omega
  have cop := (Nat.prime_two.coprime_iff_not_dvd.mpr odd).symm.pow_right k
  simpa using (ZMod.isUnit_iff_coprime _ _).mpr cop

theorem digit_bijective (k : ℕ) : Function.Bijective (digit (m:=2^k)) := by
  have inj : Function.Injective (digit (m:=2^k)) := by
    intro a b eq
    have hz : (a-b)*(1+4*(a+b))=0 := by
      unfold digit at eq
      linear_combination eq
    exact sub_eq_zero.mp ((odd_unit k (a+b)).mul_right_cancel (by simpa using hz))
  exact ⟨inj, Finite.surjective_of_injective inj⟩

private theorem root_square (k : ℕ) (D : ℤ) :
    hasRoot k D ↔ IsSquare (D : ZMod (2^k)) := by
  refine ⟨root_at le_rfl, ?_⟩
  rintro ⟨d,hd⟩
  obtain ⟨x,rfl⟩ := ZMod.intCast_surjective d
  exact ⟨x,by simpa using from_mod (m:=2^k) (a:=D) (b:=x^2) (by simpa [pow_two] using hd)⟩

private theorem neg_sum {m : ℕ} (s : ZMod m) :
    AdmissibleSum 1 (-s) ↔ AdmissibleSum 1 s := by
  have flip (u : ZMod m) : AdmissibleSum 1 u → AdmissibleSum 1 (-u) := by
    rintro ⟨x,y,h,rfl⟩
    exact ⟨-x,-y,by simpa using h,by ring⟩
  exact ⟨by simpa using flip (-s),flip s⟩

theorem singular_branch (k : ℕ) (y : ℤ) :
    AdmissibleSum (1 : ZMod (2^(k+4))) ((2+16*y : ℤ) : ZMod _) ↔
      IsSquare (digit (y : ZMod (2^k))) := by
  have eq : (2+16*y : ℤ) = 2*(1+8*y) := by ring
  rw [eq]
  push_cast
  have h := midpoint_iff_integer (k+4) (1 : ℤ) (1+8*y)
  push_cast at h
  rw [h,show (1+8*y)^2-1=4*(4*(y+4*y^2)) by ring,
    show k+4=(k+2)+2 by omega,four_cancel,four_cancel,root_square]
  simp [digit]

/-- Normalized unit-product sums have two disjoint signs modulo 16.
In each sign the remaining digits are indexed by the square values of a
permutation modulo the smaller power of two. -/
theorem unit_normal_form (k : ℕ) (s : ℤ) :
    AdmissibleSum (1 : ZMod (2^(k+4))) s ↔ ∃ y : ℤ,
      (s=2+16*y ∨ s=-(2+16*y)) ∧ IsSquare (digit (y : ZMod (2^k))) := by
  have small (a : AdmissibleSum (1 : ZMod (2^(k+4))) s) :
      (s : ZMod 16)=2 ∨ (s : ZMod 16) = -2 := by
    obtain ⟨x,y,prod,sum⟩ := a
    let f := ZMod.castHom (show 16∣2^(k+4) by rw [pow_add]; exact dvd_mul_left _ _) (ZMod 16)
    have xy : f x*f y=1 := by simpa only [map_mul,map_one] using congrArg f prod
    have plus : f x+f y=(s : ZMod 16) := by simpa only [map_add,map_intCast] using congrArg f sum
    rw [←plus]
    exact (show ∀ x y : ZMod 16, x*y=1 → x+y=2 ∨ x+y= -2 by decide +kernel) _ _ xy
  constructor
  · intro ok
    rcases small ok with pos | neg
    · obtain ⟨y,hy⟩ := from_mod (m:=16) (a:=s) (b:=2) (by simpa using pos)
      have rep : s=2+16*y := by omega
      exact ⟨y,Or.inl rep,(singular_branch _ _).mp (rep ▸ ok)⟩
    · obtain ⟨y,hy⟩ := from_mod (m:=16) (a:=s) (b:=-2) (by simpa using neg)
      have rep : s= -(2+16*(-y)) := by omega
      have ok' := (neg_sum (m:=2^(k+4)) ((2+16*(-y) : ℤ) : ZMod _)).mp
        (by simpa only [rep,Int.cast_neg] using ok)
      exact ⟨-y,Or.inr rep,(singular_branch _ _).mp ok'⟩
  · rintro ⟨y,rfl|rfl,ok⟩
    · exact (singular_branch _ _).mpr ok
    · simpa only [Int.cast_neg] using (neg_sum _).mpr ((singular_branch _ _).mpr ok)

/-- Multiplication by a square root of the public product transports the
unit-product normal form to that product. -/
theorem normalize {m : ℕ} (r : (ZMod m)ˣ) (s : ZMod m) :
    AdmissibleSum ((r : ZMod m)*(r : ZMod m)) ((r : ZMod m)*s) ↔ AdmissibleSum 1 s := by
  constructor
  · rintro ⟨x,y,prod,sum⟩
    refine ⟨(↑r⁻¹ : ZMod m)*x,(↑r⁻¹ : ZMod m)*y,?_,?_⟩
    · rw [mul_mul_mul_comm,prod,mul_mul_mul_comm]
      simp
    · rw [←mul_add,sum,←mul_assoc]; simp
  · rintro ⟨x,y,prod,rfl⟩
    exact ⟨(r : ZMod m)*x,(r : ZMod m)*y,by rw [mul_mul_mul_comm,prod,mul_one],(mul_add ..).symm⟩

/-- A product 1 modulo 8 supplies the normalizing unit at every depth. -/
theorem normalizing_unit {N : ℕ} (n : N%8=1) (e : ℕ) :
    ∃ r : (ZMod (2^e))ˣ, (r : ZMod (2^e))*(r : ZMod (2^e))=N := by
  have mod8 : (8:ℤ) ∣ (N:ℤ)-1 := ⟨(N/8 : ℕ),by omega⟩
  obtain ⟨r,hr⟩ := (root_square e (N : ℤ)).mp (square_unit _
    ((pow_dvd_pow (2:ℤ) (min_le_right e 3)).trans mod8))
  push_cast at hr
  have unit : IsUnit (N : ZMod (2^e)) := (ZMod.isUnit_iff_coprime _ _).mpr
    ((Nat.prime_two.coprime_iff_not_dvd.mpr (by omega)).symm.pow_right _)
  have ur : IsUnit r := isUnit_mul_self_iff.mp (by rw [←hr]; exact unit)
  exact ⟨ur.unit,by simpa only [IsUnit.unit_spec] using hr.symm⟩

private theorem plus_eq (k : ℕ) (x y : ℤ) :
    ((2+16*x : ℤ) : ZMod (2^(k+4))) = ((2+16*y : ℤ) : ZMod _) ↔
      (x : ZMod (2^k)) = (y : ZMod _) := by
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub,ZMod.intCast_eq_intCast_iff_dvd_sub]
  push_cast
  rw [pow_add]
  constructor
  · rintro ⟨z,hz⟩
    exact ⟨z,by linarith only [show 16*(y-x)=16*(2^k*z) by linear_combination hz]⟩
  · rintro ⟨z,hz⟩
    exact ⟨z,by linear_combination 16*hz⟩

private noncomputable def positive (k : ℕ) (y : ZMod (2^k)) : ZMod (2^(k+4)) :=
  ((2+16*(y.val:ℤ) : ℤ) : ZMod _)

private theorem positive_cast (k : ℕ) (z : ℤ) :
    positive k (z : ZMod _) = ((2+16*z : ℤ) : ZMod _) := by
  apply (plus_eq ..).mpr
  simp

private theorem positive_inj (k : ℕ) : Function.Injective (positive k) := by
  intro a b h
  simpa using (plus_eq k (a.val : ℤ) b.val).mp h

private theorem positive_ne_neg (k : ℕ) (a b : ZMod (2^k)) :
    positive k a ≠ -(positive k b) := by
  intro h
  have low : 16 ∣ 2^(k+4) := by rw [pow_add]; exact dvd_mul_left _ _
  let f := ZMod.castHom low (ZMod 16)
  have val (z : ZMod (2^k)) : f (positive k z) = 2 := by
    unfold positive
    rw [map_intCast]
    push_cast
    rw [show (16 : ZMod 16)=0 by decide,zero_mul,add_zero]
  have eq := congrArg f h
  rw [map_neg,val,val] at eq
  exact (by decide : (2:ZMod 16)≠ -2) eq

private noncomputable def signed (k : ℕ) (b : Bool) (y : ZMod (2^k)) : ZMod (2^(k+4)) :=
  if b then -(positive k y) else positive k y

private theorem signed_ok (k : ℕ) (b : Bool) (y : ZMod (2^k)) (ok : IsSquare (digit y)) :
    AdmissibleSum 1 (signed k b y) := by
  have pos := (singular_branch k y.val).mpr (by simpa using ok)
  cases b
  · exact pos
  · exact (neg_sum _).mpr pos

private abbrev Good (k : ℕ) := {z : ZMod (2^k) // IsSquare (digit z)}
private abbrev Traces (k : ℕ) := {s : ZMod (2^(k+4)) // AdmissibleSum 1 s}

private noncomputable def pack (k : ℕ) (x : Bool × Good k) : Traces k :=
  ⟨signed k x.1 x.2.val,signed_ok _ _ _ x.2.property⟩

private theorem pack_bijective (k : ℕ) : Function.Bijective (pack k) := by
  constructor
  · rintro ⟨b,⟨x,hx⟩⟩ ⟨c,⟨y,hy⟩⟩ eq
    have h := congrArg Subtype.val eq
    change signed k b x = signed k c y at h
    cases b <;> cases c <;> simp only [signed,Bool.false_eq_true,if_false,if_true,neg_inj] at h
    · cases positive_inj k h; rfl
    · exact False.elim (positive_ne_neg k _ _ h)
    · exact False.elim (positive_ne_neg k _ _ h.symm)
    · cases positive_inj k h; rfl
  · rintro ⟨s,hs⟩
    obtain ⟨z,rfl⟩ := ZMod.intCast_surjective s
    obtain ⟨y,h|h,ok⟩ := (unit_normal_form k z).mp hs
    · exact ⟨⟨false,⟨y,ok⟩⟩,Subtype.ext (by simpa only [h] using positive_cast k y)⟩
    · refine ⟨⟨true,⟨y,ok⟩⟩,Subtype.ext ?_⟩
      change -positive k (y : ZMod _) = (z : ZMod _)
      rw [h,Int.cast_neg,positive_cast]

/-- The exact reduced sum count is twice the square count four bits below
when the product is 1 modulo 8. This counts sums, including singular ones,
without counting square roots with their multiplicities. -/
theorem square_product_count {N : ℕ} (n : N%8=1) (k : ℕ) :
    Nat.card {s : ZMod (2^(k+4)) // AdmissibleSum (N : ZMod _) s} =
      2 * Nat.card {v : ZMod (2^k) // IsSquare v} := by
  obtain ⟨r,hr⟩ := normalizing_unit n (k+4)
  let e := r.mulLeft
  let scale : Traces k ≃ {s : ZMod (2^(k+4)) // AdmissibleSum (N : ZMod _) s} :=
    e.subtypeEquiv (p:=AdmissibleSum 1) (q:=AdmissibleSum (N : ZMod _))
      (fun s => by simpa only [←hr] using (normalize r s).symm)
  let perm := (Equiv.ofBijective _ (digit_bijective k)).subtypeEquiv
    (p:=fun y => IsSquare (digit y)) (q:=IsSquare) (fun _ => Iff.rfl)
  rw [←Nat.card_congr scale,←Nat.card_congr (Equiv.ofBijective _ (pack_bijective k)),
    Nat.card_prod,Nat.card_congr perm]
  simp

end
end PrimeFactors.PrimePowerSumFilter
