import PrimeFactors.SingularDyadicClueSuffixes

/-! Every odd factor suffix contains a refinement for which the fixed
sum congruence alone works at arbitrarily high binary precision. -/
namespace PrimeFactors.DyadicCluePersistentClass

open DyadicClueFullSumClass

/-- The squares of the two possible one-bit extensions differ at bit k+1.
Thus at least one extension is outside the square-root branch. -/
theorem regular_extension {k N a : ℕ} (hk : 2≤k) (ao : Odd a) (room : a<2^k) :
    ∃ b : ℕ, b<2^(k+1) ∧ Odd b ∧ b ≡ a [MOD 2^k] ∧
      b∉SingularDyadicClueSuffixes.menu (k+1) N := by
  have even : Even ((2:ℕ)^k) := (by decide : Even (2:ℕ)).pow_of_ne_zero (by omega)
  have base : a<2^(k+1) := room.trans (Nat.pow_lt_pow_right (by decide) (by omega))
  by_cases first : a∈SingularDyadicClueSuffixes.menu (k+1) N
  · refine ⟨a+2^k,by rw [pow_succ]; omega,ao.add_even even,?_,?_⟩
    · simp [Nat.ModEq]
    intro second
    have eq := (SingularDyadicClueSuffixes.mem_menu.mp second).2.trans
      (SingularDyadicClueSuffixes.mem_menu.mp first).2.symm
    have power : 2^k=2*2^(k-1) := by
      conv_lhs => rw [show k=(k-1)+1 by omega,pow_succ,mul_comm]
    have diff : (a+2^k)^2=a^2+2^(k+1)*(a+2^(k-1)) := by
      rw [pow_succ 2 k,power]
      ring
    rw [diff] at eq
    have zero := Nat.ModEq.add_left_cancel' (a^2) (by simpa only [Nat.add_zero] using eq :
      a^2+2^(k+1)*(a+2^(k-1)) ≡ a^2+0 [MOD 2^(k+1+1)])
    have even' : 2∣a+2^(k-1) := (Nat.mul_dvd_mul_iff_left (by positivity : 0<2^(k+1))).mp
      (by simpa only [pow_succ 2 (k+1)] using Nat.modEq_zero_iff_dvd.mp zero)
    exact (Nat.not_even_iff_odd.mpr
      (ao.add_even ((by decide : Even (2:ℕ)).pow_of_ne_zero (by omega : k-1≠0))))
      (even_iff_two_dvd.mpr even')
  · exact ⟨a,base,ao,Nat.ModEq.refl _,first⟩

/-- A whole sum class out of every 2^(2k+3) consecutive integers is
admissible at every higher precision with the original suffix. -/
theorem exists_class {k N a : ℕ} (hk : 3≤k) (_odd : Odd N) (ao : Odd a) (room : a<2^k) :
    ∃ b : ℕ, ∀ s : ℕ, s ≡ b [MOD 2^(2*k+3)] → Possible k N a s := by
  obtain ⟨c,small,co,same,miss⟩ := regular_extension (N:=N) (by omega : 2≤k) ao room
  obtain ⟨t,ht,classes⟩ := SingularDyadicClueSuffixes.regular_branch (by omega : 0<k+1) co small miss
  let M := 2^(2*k+3)
  let u := ZMod.unitOfCoprime c (co.coprime_two_right.pow_right (2*k+3))
  let z : ZMod M := (↑u⁻¹ : ZMod M)*((c:ZMod M)^2+N)
  have eq : (c:ZMod M)*(z.val:ZMod M)=(c:ZMod M)^2+N := by
    rw [ZMod.natCast_zmod_val]
    change (c:ZMod M)*((↑u⁻¹ : ZMod M)*_)=_
    rw [←mul_assoc]
    have inv : (c:ZMod M)*(↑u⁻¹:ZMod M)=1 := (ZMod.coe_unitOfCoprime c _ ▸ Units.mul_inv u)
    rw [inv,one_mul]
  have modEq : c*z.val ≡ c^2+N [MOD M] := (ZMod.natCast_eq_natCast_iff _ _ _).mp (by
    push_cast
    exact eq)
  refine ⟨z.val,?_⟩
  intro s sm
  have low : ((if t=k+1 then k+1+1 else k+1)+t)≤2*k+3 := by split <;> omega
  have fix := ((sm.mul_left c).trans modEq).of_dvd (pow_dvd_pow 2 low)
  have work := (classes (s:ℤ)).mpr (by exact_mod_cast Int.natCast_modEq_iff.mpr fix)
  intro e
  obtain ⟨x,source,prod⟩ := work e
  have original : (c:ℤ) ≡ a [ZMOD (2:ℤ)^k] := by exact_mod_cast Int.natCast_modEq_iff.mpr same
  exact ⟨x,(source.of_dvd (pow_dvd_pow (2:ℤ) (Nat.le_succ k))).trans original,prod⟩

end PrimeFactors.DyadicCluePersistentClass
