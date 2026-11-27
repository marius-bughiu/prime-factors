import PrimeFactors.TwelveSeedBirthday

namespace PrimeFactors.TwelveSmallSeeds
open TwelveResidueCollision TwelveImageSize TwelveSeedBirthday

set_option maxHeartbeats 900000
set_option exponentiation.threshold 2050

private theorem cast_ne {p : ℕ} {z : ℤ} (pos : 0<z) (small : z<p) : (z : ZMod p)≠0 := by
  rw [Ne,ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact fun d => (not_lt_of_ge (Int.le_of_dvd pos d)) small

private def maskFactors (x : ℤ) : List ℤ :=
  [x,x+1,x-1,x+3,x-3,x^2+3,x^2-3,x^2+6*x-3,x^2-6*x-3]

/-- Each individual mask factor is strictly between zero and p. -/
theorem regular {p : ℕ} [Fact p.Prime] {x M : ℤ} (start : 16≤x) (stop : x≤M)
    (cap : M^2+6*M+3 < (p:ℤ)) : mask (x : ZMod p)≠0 := by
  have lo := mul_nonneg (show 0≤x by omega) (show 0≤x-16 by omega)
  have hi := mul_nonneg (show 0≤M-x by omega) (show 0≤M+x by omega)
  have hit (z : ℤ) (hz : z∈maskFactors x) : (z : ZMod p) ≠ 0 := by
    simp only [maskFactors,List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with h|h|h|h|h|h|h|h|h <;> subst z <;> apply cast_ne <;> nlinarith
  have all : ((maskFactors x).map (Int.castRingHom (ZMod p))).prod ≠ 0 := by
    apply List.prod_ne_zero
    intro h
    obtain ⟨z,hz,eq⟩ := List.mem_map.mp h
    exact hit z hz eq
  simpa [maskFactors,mask,mul_assoc] using all

/-- Dividing these inequalities by the positive denominator puts each
nonidentity branch strictly between -4 and 4. -/
theorem numerator_bounds {x a b : ℤ} (lx : 16≤x) (bmin : x-3≤b)
    (amin : -(3*x+3)≤a) (amax : a≤3*x+3) : -4*b<a ∧ a<4*b := by omega

private theorem pair_ne {p : ℕ} [Fact p.Prime] {x y M a b : ℤ}
    (lx : 16≤x) (ux : x≤M) (ly : 16≤y) (uy : y≤M) (cap : M^2+6*M+3 < (p:ℤ))
    (bmin : x-3 ≤ b) (bmax : b≤x+3) (amin : -(3*x+3) ≤ a) (amax : a≤3*x+3) :
    pair (a : ZMod p) (b : ZMod p) (y : ZMod p) ≠ 0 := by
  have bot : b*4 ≤ b*y := mul_le_mul_of_nonneg_left (by omega) (by omega)
  obtain ⟨left,right⟩ := numerator_bounds lx bmin amin amax
  have top : b*y ≤ (M+3)*M := mul_le_mul (by omega) uy (by omega) (by omega)
  have pos₁ := cast_ne (p:=p) (z:=b*y-a) (by nlinarith) (by nlinarith)
  have pos₂ := cast_ne (p:=p) (z:=b*y+a) (by nlinarith) (by nlinarith)
  simpa [pair] using mul_ne_zero pos₁ pos₂

private theorem cross_ne_ordered {p : ℕ} [Fact p.Prime] {x y M : ℤ}
    (lx : 16≤x) (ux : x≤M) (ly : 16≤y) (uy : y≤M) (ord : x<y)
    (cap : M^2+6*M+3 < (p:ℤ)) :
    num (x:ZMod p)*den (y:ZMod p)-num (y:ZMod p)*den (x:ZMod p) ≠ 0 := by
  have base : (108 : ZMod p) ≠ 0 := by
    exact_mod_cast (cast_ne (p:=p) (z:=108) (by decide) (by nlinarith [sq_nonneg (M-10)]))
  have first : pair (x:ZMod p) 1 (y:ZMod p) ≠ 0 := by
    have h := mul_ne_zero
      (cast_ne (p:=p) (z:=y-x) (by omega) (by nlinarith [sq_nonneg M]))
      (cast_ne (p:=p) (z:=y+x) (by omega) (by nlinarith [sq_nonneg M]))
    simpa [pair] using h
  have r := @pair_ne p _ x y M
  have h₂ := r (a:=3*x-3) (b:=x+3) lx ux ly uy cap (by omega) (by omega) (by omega) (by omega)
  have h₃ := r (a:=x-3) (b:=x+1) lx ux ly uy cap (by omega) (by omega) (by omega) (by omega)
  have h₄ := r (a:=-3) (b:=x) lx ux ly uy cap (by omega) (by omega) (by omega) (by omega)
  have h₅ := r (a:=-x-3) (b:=x-1) lx ux ly uy cap (by omega) (by omega) (by omega) (by omega)
  have h₆ := r (a:=-3*x-3) (b:=x-3) lx ux ly uy cap (by omega) (by omega) (by omega) (by omega)
  push_cast at h₂ h₃ h₄ h₅ h₆
  rw [difference]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
    (mul_ne_zero (neg_ne_zero.mpr base) first) h₂) h₃) h₄) h₅) h₆

/-- Distinct seeds in the public interval have unequal rational keys over the
prime field, even before the denominators are inverted. -/
theorem cross_ne {p : ℕ} [Fact p.Prime] {x y M : ℤ}
    (lx : 16≤x) (ux : x≤M) (ly : 16≤y) (uy : y≤M) (apart : x≠y)
    (cap : M^2+6*M+3 < (p:ℤ)) :
    num (x:ZMod p)*den (y:ZMod p) ≠ num (y:ZMod p)*den (x:ZMod p) := by
  rcases lt_or_gt_of_ne apart with ord|ord
  · exact sub_ne_zero.mp (cross_ne_ordered lx ux ly uy ord cap)
  · exact Ne.symm (sub_ne_zero.mp (cross_ne_ordered ly uy lx ux ord cap))

/-- None of the twelve bilinear branch tests can vanish between distinct seeds. -/
theorem all_directions_miss {p : ℕ} [Fact p.Prime] {x y M : ℤ}
    (lx : 16≤x) (ux : x≤M) (ly : 16≤y) (uy : y≤M) (apart : x≠y)
    (cap : M^2+6*M+3 < (p:ℤ)) (i : Fin 12) :
    imageDen (x:ZMod p) i * (y:ZMod p) ≠ imageNum (x:ZMod p) i := by
  intro eq
  apply sub_ne_zero.mpr (cross_ne lx ux ly uy apart cap)
  rw [product_identity]
  exact mul_eq_zero_of_right _ (Finset.prod_eq_zero
    (f:=fun j : Fin 12 => imageDen (x:ZMod p) j * (y:ZMod p)-imageNum (x:ZMod p) j)
    (Finset.mem_univ i) (sub_eq_zero.mpr eq))

/-- The interval starting at sixteen already contains the entire random
birthday budget, with room below every 1024-bit prime. -/
def lastSeed : ℤ := 2^511+15

theorem full_size_cap {p : ℕ} (low : 2^1023≤p) : lastSeed^2+6*lastSeed+3 < (p:ℤ) := by
  have h : lastSeed^2+6*lastSeed+3 < (2:ℤ)^1023 := by norm_num [lastSeed]
  exact h.trans_le (by exact_mod_cast low)

theorem length_of_interval : lastSeed-16+1=2^511 := by unfold lastSeed; ring

private theorem char108 {p : ℕ} (hp : 2^1023≤p) : (108:ZMod p)≠0 := by
  exact_mod_cast (cast_ne (p:=p) (z:=108) (by decide)
    (by exact_mod_cast (by norm_num : 108 < 2^1023).trans_le hp))

/-- The publicly normalized labels are pairwise distinct at each hidden
prime throughout the entire interval of consecutive seeds. -/
theorem keys_injective {p : ℕ} [Fact p.Prime] (hp : 2^1023≤p)
    {x y : ℤ} (lx : 16≤x) (ux : x≤lastSeed) (ly : 16≤y) (uy : y≤lastSeed)
    (apart : x≠y) : value (x:ZMod p) ≠ value (y:ZMod p) := by
  have small := full_size_cap hp
  have hx := ((regular_iff (char108 hp) _).mp (regular lx ux small)).1
  have hy := ((regular_iff (char108 hp) _).mp (regular ly uy small)).1
  exact fun eq => cross_ne lx ux ly uy apart small ((div_eq_div_iff hx hy).mp eq)

private theorem gcd_unit {n : ℕ} [NeZero n] (z : ZMod n) (h : IsUnit z) : n.gcd z.val=1 := by
  have u : IsUnit (z.val:ZMod n) := by rwa [ZMod.natCast_zmod_val]
  exact ((ZMod.isUnit_iff_coprime _ _).mp u).symm.gcd_eq_one

private theorem unit_of_pair {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (cop : p.Coprime q)
    {z : ZMod (p*q)} {u : ZMod p} {v : ZMod q} (hu : u≠0) (hv : v≠0)
    (red : ZMod.chineseRemainder cop z=(u,v)) : IsUnit z := by
  have h : IsUnit (u,v) := Prod.isUnit_iff.mpr ⟨isUnit_iff_ne_zero.mpr hu,isUnit_iff_ne_zero.mpr hv⟩
  rw [←red] at h
  simpa using h.map (ZMod.chineseRemainder cop).symm.toRingHom

theorem mask_unit {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (cop : p.Coprime q)
    (hp : 2^1023≤p) (hq : 2^1023≤q) {x : ℤ} (lx : 16≤x) (ux : x≤lastSeed) :
    IsUnit (mask (x:ZMod (p*q))) := by
  apply unit_of_pair cop (regular lx ux (full_size_cap hp)) (regular lx ux (full_size_cap hq))
  simp [mask,map_ofNat]
  rfl

/-- The setup gcd always equals one on this block. -/
theorem setup_gcd {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (cop : p.Coprime q)
    (hp : 2^1023≤p) (hq : 2^1023≤q) {x : ℤ} (lx : 16≤x) (ux : x≤lastSeed) :
    (p*q).gcd (mask (x:ZMod (p*q))).val=1 := gcd_unit _ (mask_unit cop hp hq lx ux)

noncomputable def input {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (cop : p.Coprime q)
    (hp : 2^1023≤p) (hq : 2^1023≤q) {x : ℤ} (lx : 16≤x) (ux : x≤lastSeed) :
    Input (p*q) := ⟨(x:ZMod (p*q)), Finset.mem_filter.mpr
      ⟨Finset.mem_univ _,mask_unit cop hp hq lx ux⟩⟩

private theorem key_coords {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (cop : p.Coprime q)
    (hp : 2^1023≤p) (hq : 2^1023≤q) {x : ℤ} (lx : 16≤x) (ux : x≤lastSeed) :
    ZMod.chineseRemainder cop (publicKey (input cop hp hq lx ux)) =
      (value (x:ZMod p), value (x:ZMod q)) := by
  have pl := (by norm_num : 864<2^1023).trans_le hp
  have ql := (by norm_num : 864<2^1023).trans_le hq
  refine (coordinates pl ql cop _).trans ?_
  let e := ZMod.chineseRemainder cop
  change (value (e (x:ZMod (p*q))).1, value (e (x:ZMod (p*q))).2) = _
  rw [map_intCast]
  rfl

/-- Checking every pair of the 2^511 consecutive inputs still gives gcd one
for every difference of the actual normalized public keys. -/
theorem public_key_gcd {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (cop : p.Coprime q)
    (hp : 2^1023≤p) (hq : 2^1023≤q) {x y : ℤ}
    (lx : 16≤x) (ux : x≤lastSeed) (ly : 16≤y) (uy : y≤lastSeed) (apart : x≠y) :
    (p*q).gcd (publicKey (input cop hp hq lx ux) - publicKey (input cop hp hq ly uy)).val=1 := by
  apply gcd_unit
  apply unit_of_pair cop (sub_ne_zero.mpr (keys_injective hp lx ux ly uy apart))
    (sub_ne_zero.mpr (keys_injective hq lx ux ly uy apart))
  rw [map_sub,key_coords,key_coords]
  rfl

/-- The denominator-free comparison has gcd one as well. -/
theorem cross_gcd {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (cop : p.Coprime q)
    (hp : 2^1023≤p) (hq : 2^1023≤q) {x y : ℤ}
    (lx : 16≤x) (ux : x≤lastSeed) (ly : 16≤y) (uy : y≤lastSeed) (apart : x≠y) :
    (p*q).gcd (num (x:ZMod (p*q))*den (y:ZMod (p*q))-
      num (y:ZMod (p*q))*den (x:ZMod (p*q))).val=1 := by
  apply gcd_unit
  apply unit_of_pair cop (sub_ne_zero.mpr (cross_ne lx ux ly uy apart (full_size_cap hp)))
    (sub_ne_zero.mpr (cross_ne lx ux ly uy apart (full_size_cap hq)))
  simp [num,den,sextic,map_ofNat]
  rfl

/-- Individual orientation comparisons also give only gcd one. This includes
the identity direction, which compares the original residues. -/
theorem direction_gcd {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (cop : p.Coprime q)
    (hp : 2^1023≤p) (hq : 2^1023≤q) {x y : ℤ}
    (lx : 16≤x) (ux : x≤lastSeed) (ly : 16≤y) (uy : y≤lastSeed) (apart : x≠y) (i : Fin 12) :
    (p*q).gcd (imageDen (x:ZMod (p*q)) i*(y:ZMod (p*q))-imageNum (x:ZMod (p*q)) i).val=1 := by
  apply gcd_unit
  apply unit_of_pair cop (sub_ne_zero.mpr (all_directions_miss lx ux ly uy apart (full_size_cap hp) i))
    (sub_ne_zero.mpr (all_directions_miss lx ux ly uy apart (full_size_cap hq) i))
  simp [imageDen,imageNum]
  rfl

end PrimeFactors.TwelveSmallSeeds
