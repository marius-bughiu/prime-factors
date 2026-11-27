import PrimeFactors.FactorSumSpacing

/-! Nine is the least positive spacing which every product admits as a
difference of factor sums at every three-adic precision. -/
namespace PrimeFactors.ThreeAdicUniversalSpacing

open FactorSumSpacing

private theorem twoUnit (k : ℕ) : IsUnit (2 : ZMod (3^(k+1))) :=
  (ZMod.isUnit_iff_coprime 2 _).mpr ((by decide : (2:ℕ).Coprime 3).pow_right _)

/-- A concrete family of traces for the product one at any precision. -/
private theorem oneTrace (k : ℕ) (z : ZMod (3^(k+1))) :
    AdmissibleSum 1 (2+9*z^2) := by
  obtain ⟨a,rfl⟩ := ZMod.intCast_surjective z
  have one : ((4+9*a^2 : ℤ) : ZMod 3)=1 := by
    push_cast
    rw [show (9 : ZMod 3)=0 by decide,zero_mul,add_zero]
    decide
  have sq := (isSquare_primePow_iff_of_unit (by decide : 3≠2) (4+9*a^2)
    (by rw [one]; decide) k).mpr (by rw [one]; exact ⟨1,by simp⟩)
  obtain ⟨b,hb⟩ := sq
  push_cast at hb
  apply (admissibleSum_iff_isSquare_of_two_unit (twoUnit k) _ _).mpr
  refine ⟨3*(a:ZMod (3^(k+1)))*b,?_⟩
  linear_combination (9*(a:ZMod (3^(k+1)))^2)*hb

private theorem oneGap (k : ℕ) (h : ZMod (3^(k+1))) : Gap (3^(k+1)) 1 (9*h) := by
  obtain ⟨u,hu⟩ := twoUnit k
  let z := (↑(u⁻¹):ZMod (3^(k+1)))
  have half : 2*z=1 := by rw [←hu]; exact u.mul_inv
  let a := (h-1)*z
  let b := (h+1)*z
  have diff : b^2-a^2=h := calc
    _ = h*(2*z)^2 := by dsimp [a,b]; ring
    _ = h := by rw [half]; simp
  exact ⟨2+9*a^2,oneTrace k a,by
    rw [show (2+9*a^2)+9*h=2+9*b^2 by linear_combination -9*diff]
    exact oneTrace k b⟩

private theorem unitLift (n : ℤ) (k : ℕ) (nz : (n:ZMod 3)≠0) :
    IsUnit (n:ZMod (3^(k+1))) := by
  let v := (n:ZMod (3^(k+1))).val
  let red := ZMod.castHom (dvd_pow_self 3 (Nat.succ_ne_zero k)) (ZMod 3)
  have rem : (v:ZMod 3)=(n:ZMod 3) := calc
    _ = red (v:ZMod (3^(k+1))) := (map_natCast red v).symm
    _ = _ := by simp only [v,ZMod.natCast_zmod_val,map_intCast]
  have c := (ZMod.isUnit_iff_coprime v 3).mp (rem ▸ nz.isUnit)
  have u := (ZMod.isUnit_iff_coprime v (3^(k+1))).mpr (c.pow_right _)
  simpa only [v,ZMod.natCast_zmod_val] using u

private theorem scaleSum {m : ℕ} (c : ZMod m) {s : ZMod m} (h : AdmissibleSum 1 s) :
    AdmissibleSum (c*c) (s*c) := by
  obtain ⟨x,y,hxy,rfl⟩ := h
  refine ⟨x*c,y*c,?_,by ring⟩
  calc _ = (x*y)*(c*c) := by ring
       _ = c*c := by rw [hxy,one_mul]

private theorem squareCase (n h : ℤ) (one : (n : ZMod 3)=1) (k : ℕ) :
    Gap (3^(k+1)) n (9*(h:ZMod (3^(k+1)))) := by
  have nz : (n:ZMod 3)≠0 := one ▸ one_ne_zero
  obtain ⟨r,hr⟩ := (isSquare_primePow_iff_of_unit (by decide : 3≠2) n nz k).mpr
    (by rw [one]; exact ⟨1,by simp⟩)
  have ru : IsUnit r := isUnit_of_mul_isUnit_left (hr ▸ unitLift n k nz)
  obtain ⟨v,rfl⟩ := ru
  obtain ⟨s,first,last⟩ := oneGap k ((h:ZMod (3^(k+1)))*↑(v⁻¹))
  rw [hr]
  refine ⟨s*v,scaleSum _ first,?_⟩
  have clean : (s+9*((h:ZMod (3^(k+1)))*↑(v⁻¹)))*v = s*v+9*h := calc
    _ = s*v+9*(h:ZMod (3^(k+1)))*(↑(v⁻¹)*v) := by ring
    _ = _ := by simp
  exact clean ▸ scaleSum (v:ZMod (3^(k+1))) last

private theorem nonsquareCase (n h : ℤ) (two : (n : ZMod 3)=2) (k : ℕ) :
    Gap (3^(k+1)) n (9*(h:ZMod (3^(k+1)))) := by
  have any (s : ℤ) (zero : (s:ZMod 3)=0) :
      AdmissibleSum (n:ZMod (3^(k+1))) (s:ZMod (3^(k+1))) := by
    have reg : ((s^2-4*n:ℤ):ZMod 3)≠0 := by push_cast; rw [two,zero]; decide
    apply (admissibleSum_primePow_iff_of_regular (by decide : 3≠2) n s reg k).mpr
    rw [zero,two]
    exact ⟨1,2,by decide,by decide⟩
  exact ⟨0,by simpa only [Int.cast_zero] using any 0 (by simp),by
    simpa only [zero_add,Int.cast_mul,Int.cast_ofNat] using
      any (9*h) (by push_cast; rw [show (9:ZMod 3)=0 by decide,zero_mul])⟩

/-- The chosen displacement applies to every integer product, including
products divisible by three. Its two admissible traces can use different pairs. -/
theorem multiple_nine (n h : ℤ) (k : ℕ) : Gap (3^(k+1)) n ((9*h:ℤ):ZMod (3^(k+1))) := by
  by_cases zero : (n:ZMod 3)=0
  · exact prime_power_of_zero (by decide) n (9*h) zero k
  have split : ∀ a : ZMod 3, a≠0 → a=1 ∨ a=2 := by decide
  rcases split _ zero with one|two
  · simpa only [Int.cast_mul,Int.cast_ofNat] using squareCase n h one k
  · simpa only [Int.cast_mul,Int.cast_ofNat] using nonsquareCase n h two k

/-- The two unit products 1 and 2 suffice to check sharpness modulo nine. -/
theorem nine_table (t : ZMod 9) :
    (Gap 9 1 t ↔ t=0 ∨ t=4 ∨ t=5) ∧ (Gap 9 2 t ↔ t=0 ∨ t=3 ∨ t=6) := by
  revert t
  unfold Gap AdmissibleSum
  decide +kernel

/-- Across all products and positive powers of three, precisely the
multiples of nine are guaranteed to be differences. -/
theorem universal_iff (t : ℤ) : (∀ (n : ℤ) (k : ℕ), Gap (3^(k+1)) n t) ↔ 9∣t := by
  constructor
  · intro h
    obtain ⟨first,second⟩ := nine_table (t:ZMod 9)
    have a := first.mp (by simpa only [Int.cast_one] using h 1 1)
    have b := second.mp (by simpa only [Int.cast_ofNat] using h 2 1)
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd t 9).mp
    rcases a with a|a|a
    · exact a
    · rw [a] at b
      exact False.elim ((by decide : ¬((4:ZMod 9)=0 ∨ (4:ZMod 9)=3 ∨ (4:ZMod 9)=6)) b)
    · rw [a] at b
      exact False.elim ((by decide : ¬((5:ZMod 9)=0 ∨ (5:ZMod 9)=3 ∨ (5:ZMod 9)=6)) b)
  · rintro ⟨h,rfl⟩ n k
    exact multiple_nine n h k

end PrimeFactors.ThreeAdicUniversalSpacing
