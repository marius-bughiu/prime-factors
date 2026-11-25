import PrimeFactors.CanonicalNorm
import Mathlib.NumberTheory.LSeries.PrimesInAP

namespace PrimeFactors.NormWheelImage

open PrimeFactors.CanonicalNorm

private theorem relocate {H M : ℤ} (pos : 0<M) (width : 16*M≤H) (k z : ℤ) :
    ∃ x : ℤ, k*H≤32*x ∧ 32*x≤(k+2)*H ∧ x ≡ z [ZMOD M] := by
  let first := (k*H+31)/32
  let x := first + (z-first)%M
  have lo := Int.emod_nonneg (z-first) pos.ne'
  have hi := Int.emod_lt_of_pos (z-first) pos
  refine ⟨x, ?_, ?_, ?_⟩
  · dsimp [x,first] at *
    omega
  · dsimp [x,first] at *
    rw [add_mul]
    omega
  · simpa [x] using (Int.mod_modEq (z-first) M).add_left first

private theorem square_bounds {x H k j : ℤ} (lo : k*H≤32*x) (hi : 32*x≤j*H)
    (pos : 0≤k*H) : k^2*H^2≤1024*x^2 ∧ 1024*x^2≤j^2*H^2 := by
  constructor
  · nlinarith only [pow_le_pow_left₀ pos lo 2]
  · nlinarith only [pow_le_pow_left₀ (pos.trans lo) hi 2]

private theorem in_band {N H V : ℤ} (side : 256≤H) (under : H^4≤N) (over : N<(H+1)^4)
    (lo : 734*H^2≤1024*V) (hi : V≤H^2) : 0<V ∧ V^2≤N ∧ N≤2*V^2 := by
  have vp : 0<V := by nlinarith [sq_pos_of_pos (by omega : 0<H)]
  have top : 1024*(H+1)^2 ≤ 1033*H^2 := by
    nlinarith [mul_nonneg (by omega : 0≤H-256) (by omega : 0≤H)]
  have a := pow_le_pow_left₀ (by positivity : 0≤1024*(H+1)^2) top 2
  have b := pow_le_pow_left₀ (by positivity : 0≤734*H^2) lo 2
  refine ⟨vp, ?_, ?_⟩
  · nlinarith only [pow_le_pow_left₀ vp.le hi 2,under]
  · nlinarith only [a,b,over,pow_nonneg (sq_nonneg H) 2]

/-- A reduced wheel class admitting any odd-prime representative occurs among
the actual canonical norms in the balanced factor band. M is an even multiple
of the wheel W, allowing the parity branches to survive coordinate relocation. -/
theorem prime_class {N H W M : ℤ} (side : 256≤H) (under : H^4≤N) (over : N<(H+1)^4)
    (mp : 0<M) (width : 16*M≤H) (evenM : 2∣M) (wheel : W∣M) {p : ℕ} [Fact p.Prime]
    (odd : p≠2) : ∃ V d t a : ℤ, IsCanonical V d t a ∧
      t≤H ∧ a≤H ∧ 0<V ∧ V^2≤N ∧ N≤2*V^2 ∧ V ≡ p [ZMOD W] := by
  obtain ⟨d,u,b,_,_,uo,forms⟩ := exists_canonical odd
  have move (k z : ℤ) := relocate mp width k z
  rcases forms with ⟨_,bo,e⟩ | ⟨_,bo,e⟩ | ⟨_,bo,_,e⟩
  · obtain ⟨t,tl,th,tc⟩ := move 20 u
    obtain ⟨a,al,ah,ac⟩ := move 20 b
    have ts := square_bounds tl th (by omega)
    have asq := square_bounds al ah (by omega)
    let V := t^2+a^2
    have band := in_band side under over (V := V) (by dsimp [V]; nlinarith [sq_nonneg H])
      (by dsimp [V]; nlinarith [sq_nonneg H])
    refine ⟨V,-1,t,a,⟨by omega,by omega,(tc.of_dvd evenM).eq.trans uo,
      Or.inl ⟨rfl,(ac.of_dvd evenM).eq.trans bo,rfl⟩⟩,by omega,by omega,
      band.1,band.2.1,band.2.2,?_⟩
    rw [e]
    exact ((tc.of_dvd wheel).pow 2).add ((ac.of_dvd wheel).pow 2)
  · obtain ⟨t,tl,th,tc⟩ := move 16 u
    obtain ⟨a,al,ah,ac⟩ := move 16 b
    have ts := square_bounds tl th (by omega)
    have asq := square_bounds al ah (by omega)
    let V := t^2+2*a^2
    have band := in_band side under over (V := V) (by dsimp [V]; nlinarith [sq_nonneg H])
      (by dsimp [V]; nlinarith [sq_nonneg H])
    refine ⟨V,-2,t,a,⟨by omega,by omega,(tc.of_dvd evenM).eq.trans uo,
      Or.inr (Or.inl ⟨rfl,(ac.of_dvd evenM).eq.trans bo,rfl⟩)⟩,by omega,by omega,
      band.1,band.2.1,band.2.2,?_⟩
    rw [e]
    exact ((tc.of_dvd wheel).pow 2).add (((ac.of_dvd wheel).pow 2).mul_left 2)
  · obtain ⟨t,tl,th,tc⟩ := move 16 u
    obtain ⟨a,al,ah,ac⟩ := move 23 b
    have ts := square_bounds tl th (by omega)
    have asq := square_bounds al ah (by omega)
    let V := 2*a^2-t^2
    have band := in_band side under over (V := V) (by dsimp [V]; nlinarith)
      (by dsimp [V]; nlinarith [sq_nonneg H])
    refine ⟨V,2,t,a,⟨by omega,by omega,(tc.of_dvd evenM).eq.trans uo,
      Or.inr (Or.inr ⟨rfl,(ac.of_dvd evenM).eq.trans bo,by omega,rfl⟩)⟩,by omega,by omega,
      band.1,band.2.1,band.2.2,?_⟩
    rw [e]
    exact (((ac.of_dvd wheel).pow 2).mul_left 2).sub ((tc.of_dvd wheel).pow 2)

/-- No wheel-unit value class can be discarded by the canonical norm band
when the parity-preserving period occupies at most one sixteenth of the side. -/
theorem all_units {N H : ℤ} {W : ℕ} [NeZero W] (r : ZMod W) (unit : IsUnit r)
    (side : 256≤H) (under : H^4≤N) (over : N<(H+1)^4)
    (width : 16*(Nat.lcm 2 W : ℕ) ≤ H) :
    ∃ V d t a : ℤ, IsCanonical V d t a ∧ t≤H ∧ a≤H ∧
      0<V ∧ V^2≤N ∧ N≤2*V^2 ∧ (V : ZMod W)=r := by
  obtain ⟨p,large,prime,pr⟩ := Nat.forall_exists_prime_gt_and_eq_mod unit 2
  letI : Fact p.Prime := ⟨prime⟩
  have pos : 0 < Nat.lcm 2 W := Nat.lcm_pos (by decide) (NeZero.pos W)
  obtain ⟨V,d,t,a,h,ht,ha,pv,vn,nv,cong⟩ := prime_class (W := (W : ℤ)) side under over
    (by exact_mod_cast pos) width (by exact_mod_cast Nat.dvd_lcm_left 2 W)
    (by exact_mod_cast Nat.dvd_lcm_right 2 W) (p:=p) (by omega)
  refine ⟨V,d,t,a,h,ht,ha,pv,vn,nv,?_⟩
  have eq := (ZMod.intCast_eq_intCast_iff V p W).mpr cong
  simpa [pr] using eq

end PrimeFactors.NormWheelImage
