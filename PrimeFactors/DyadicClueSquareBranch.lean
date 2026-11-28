import PrimeFactors.DyadicClueFullSumClass
import PrimeFactors.LocalMidpointLanes
import PrimeFactors.SingularDyadicClueSuffixes
import PrimeFactors.DyadicSquareValueCount

/-! On a factor suffix containing a square root of the product, normalize
the sum around twice that root. Additional admissibility at every precision
is then governed by ordinary square residues. -/
namespace PrimeFactors.DyadicClueSquareBranch

/-- One local factor pair at the specified output precision, with the first
factor in the prescribed input suffix. -/
def AtLevel (k e : ℕ) (N a s : ℤ) : Prop :=
  ∃ x : ℤ, x ≡ a [ZMOD (2:ℤ)^k] ∧ x*(s-x) ≡ N [ZMOD (2:ℤ)^e]

private theorem unit_of_odd {r : ℤ} (odd : Odd r) (j : ℕ) : IsUnit (r : ZMod (2^j)) := by
  obtain ⟨c,hc⟩ := odd
  have cop : IsCoprime (2:ℤ) r := ⟨-c,1,by linarith⟩
  obtain ⟨u,v,eq⟩ := (cop.pow_left : IsCoprime ((2:ℤ)^j) r)
  have cast := congrArg (Int.castRingHom (ZMod (2^j))) eq
  simp only [map_add,map_mul,map_one,map_pow,Int.coe_castRingHom] at cast
  have zero : (2:ZMod (2^j))^j=0 := by
    simpa only [Nat.cast_pow,Nat.cast_ofNat] using ZMod.natCast_self (2^j)
  apply isUnit_of_mul_eq_one_right _ _
  simpa only [Int.cast_ofNat,zero,mul_zero,zero_add] using cast

private theorem square_unit (j : ℕ) (v : ZMod (2^j)) :
    ∃ u : (ZMod (2^j))ˣ, 1+8*v=(u : ZMod _)^2 := by
  obtain ⟨i,rfl⟩ := ZMod.intCast_surjective v
  obtain ⟨x,odd,div⟩ := LocalMidpointLanes.lift_eight (D:=1+8*i)
    (by simp) j
  obtain ⟨u,hu⟩ := unit_of_odd odd j
  refine ⟨u,?_⟩
  rw [hu]
  have dv := (pow_dvd_pow (2:ℤ) (by omega : j≤j+3)).trans div
  have eq := (ZMod.intCast_zmod_eq_zero_iff_dvd _ (2^j)).mpr (by simpa using dv)
  push_cast at eq
  exact sub_eq_zero.mp eq

private theorem times_square_unit {j : ℕ} {s : ZMod (2^j)} (u : (ZMod (2^j))ˣ) :
    IsSquare (s*(u : ZMod _)^2) ↔ IsSquare s := by
  constructor
  · rintro ⟨v,hv⟩
    refine ⟨v*(↑u⁻¹ : ZMod _),?_⟩
    calc
      s = (s*(u : ZMod _)^2)*(↑u⁻¹ : ZMod _)^2 := by rw [mul_assoc,←mul_pow,Units.mul_inv,one_pow,mul_one]
      _ = _ := by rw [hv]; ring
  · rintro ⟨v,hv⟩
    exact ⟨v*u,by rw [hv]; ring⟩

private theorem normalized_square {k j : ℕ} (hk : 3≤k) (r h : ℤ) (odd : Odd r) :
    IsSquare (((r*h+(2^(k-1)*h)^2 : ℤ)) : ZMod (2^j)) ↔
      IsSquare ((r*h:ℤ):ZMod (2^j)) := by
  obtain ⟨u,hu⟩ := unit_of_odd odd j
  have eight : (8:ℤ)∣(2^(k-1):ℤ)^2 := by
    rw [←pow_mul]
    exact pow_dvd_pow 2 (by omega : 3≤(k-1)*2)
  obtain ⟨b,hb⟩ := eight
  have scale := congrArg (Int.castRingHom (ZMod (2^j))) hb
  change ((((2:ℤ)^(k-1))^2 : ℤ) : ZMod (2^j))=((8*b : ℤ) : ZMod (2^j)) at scale
  push_cast at scale
  obtain ⟨v,hv⟩ := square_unit j ((b:ZMod (2^j))*(h:ZMod (2^j))*(↑u⁻¹:ZMod (2^j)))
  push_cast
  have eq : (r:ZMod (2^j))*(h:ZMod (2^j))+(2^(k-1)*(h:ZMod (2^j)))^2 =
      ((r:ZMod (2^j))*(h:ZMod (2^j)))*(v:ZMod (2^j))^2 := by
    rw [←hv,mul_pow,scale,←hu]
    linear_combination -(8*(b:ZMod (2^j))*(h:ZMod (2^j))^2) * (Units.mul_inv u)
  rw [eq,times_square_unit]

/-- At precision 2k+j, a root of N at that precision in the supplied suffix
provides the center. Each lift of the sum 2r modulo 2^(2k) corresponds
exactly to a square test at the remaining j bits. -/
theorem square_branch {k j : ℕ} (hk : 3≤k) {N a r : ℤ} (odd : Odd r)
    (same : r ≡ a [ZMOD (2:ℤ)^k]) (root : r^2 ≡ N [ZMOD (2:ℤ)^(2*k+j)]) (h : ℤ) :
    AtLevel k (2*k+j) N a (2*r+2^(2*k)*h) ↔ IsSquare ((r*h : ℤ) : ZMod (2^j)) := by
  rw [←normalized_square hk r h odd]
  let T := r*h+(2^(k-1)*h)^2
  have sq_iff : IsSquare (T : ZMod (2^j)) ↔ ∃ z : ℤ, z^2 ≡ T [ZMOD (2:ℤ)^j] := by
    rw [←show ((2^j:ℕ):ℤ)=(2:ℤ)^j by push_cast; rfl]
    constructor
    · rintro ⟨v,hv⟩
      obtain ⟨z,rfl⟩ := ZMod.intCast_surjective v
      exact ⟨z,(ZMod.intCast_eq_intCast_iff _ _ _).mp (by push_cast; simpa [pow_two] using hv.symm)⟩
    · rintro ⟨z,hz⟩
      have eq := (ZMod.intCast_eq_intCast_iff _ _ _).mpr hz
      exact ⟨z,by push_cast at eq; simpa [pow_two] using eq.symm⟩
  change _ ↔ IsSquare (T : ZMod (2^j))
  rw [sq_iff]
  have pow2 : (2:ℤ)^(2*k)=(2^k)^2 := by rw [←pow_mul,mul_comm 2 k]
  have half : (2:ℤ)^k=2*2^(k-1) := by
    conv_lhs => rw [show k=(k-1)+1 by omega,pow_succ,mul_comm]
  have factor (u : ℤ) :
      r^2-(r+2^k*u)*((2*r+2^(2*k)*h)-(r+2^k*u)) =
      2^(2*k)*((u-2^(k-1)*h)^2-T) := by
    simp only [T,pow2]
    linear_combination -((2:ℤ)^k)^2*u*h*half
  have relates (u : ℤ) :
      (r+2^k*u)*((2*r+2^(2*k)*h)-(r+2^k*u)) ≡ N [ZMOD (2:ℤ)^(2*k+j)] ↔
      (u-2^(k-1)*h)^2 ≡ T [ZMOD (2:ℤ)^j] := by
    refine (Iff.intro (fun l => l.trans root.symm) (fun l => l.trans root)).trans ?_
    rw [Int.modEq_iff_dvd,Int.modEq_iff_dvd,factor,pow_add,
      Int.mul_dvd_mul_iff_left (by positivity : (2:ℤ)^(2*k)≠0),
      show (u-2^(k-1)*h)^2-T= -(T-(u-2^(k-1)*h)^2) by ring,Int.dvd_neg]
  constructor
  · rintro ⟨x,suffix,hit⟩
    obtain ⟨u,hu⟩ := Int.modEq_iff_dvd.mp (suffix.trans same.symm).symm
    have eq : x=r+2^k*u := by linarith
    exact ⟨_,(relates u).mp (eq ▸ hit)⟩
  · rintro ⟨z,hz⟩
    let u := z+2^(k-1)*h
    refine ⟨r+2^k*u, ?_, (relates u).mpr (by simpa [u] using hz)⟩
    apply Int.ModEq.trans _ same
    apply Int.modEq_iff_dvd.mpr
    rw [show r-(r+2^k*u)=2^k*(-u) by ring]
    exact dvd_mul_right _ _

/-- Every permissible sum first agrees with twice the chosen root modulo
2^(2k). This also covers sums not initially presented as lifts of the center. -/
theorem center_necessary {k j : ℕ} (hk : 0<k) {N a r s : ℤ} (odd : Odd r)
    (same : r ≡ a [ZMOD (2:ℤ)^k]) (root : r^2 ≡ N [ZMOD (2:ℤ)^(2*k+j)])
    (hit : AtLevel k (2*k+j) N a s) : s ≡ 2*r [ZMOD (2:ℤ)^(2*k)] := by
  obtain ⟨x,suffix,prod⟩ := hit
  obtain ⟨u,hu⟩ := Int.modEq_iff_dvd.mp (suffix.trans same.symm).symm
  have eq : x=r+2^k*u := by linarith
  have xo : Odd x := eq ▸ odd.add_even (((by decide : Even (2:ℤ)).pow_of_ne_zero hk.ne').mul_right u)
  obtain ⟨b,hb⟩ := xo
  have cop : IsCoprime (2:ℤ) x := ⟨-b,1,by linarith⟩
  have mid := Int.modEq_iff_dvd.mp ((prod.trans root.symm).of_dvd
    (pow_dvd_pow (2:ℤ) (by omega : 2*k≤2*k+j)))
  have square : (2:ℤ)^(2*k)∣(x-r)^2 := by
    rw [hu,mul_pow,←pow_mul,mul_comm k 2]
    exact dvd_mul_right _ _
  apply Int.modEq_iff_dvd.mpr
  apply cop.pow_left.dvd_of_dvd_mul_left
  convert dvd_sub mid square using 1
  ring

/-- Count distinct lifts of the sum, with one additional index h for each
residue modulo 2^j. Several different factors may realize the same sum. -/
theorem lift_count {k j : ℕ} (hk : 3≤k) {N a r : ℤ} (odd : Odd r)
    (same : r ≡ a [ZMOD (2:ℤ)^k]) (root : r^2 ≡ N [ZMOD (2:ℤ)^(2*k+j)]) :
    Nat.card {h : ZMod (2^j) // AtLevel k (2*k+j) N a (2*r+2^(2*k)*(h.val:ℤ))} =
      Nat.card {h : ZMod (2^j) // IsSquare h} := by
  obtain ⟨u,hu⟩ := unit_of_odd odd j
  let f := u.mulLeft
  apply Nat.card_congr (f.subtypeEquiv (p:=fun h : ZMod (2^j) =>
    AtLevel k (2*k+j) N a (2*r+2^(2*k)*(h.val:ℤ))) (q:=IsSquare) ?_)
  intro h
  change AtLevel k (2*k+j) N a (2*r+2^(2*k)*(h.val:ℤ)) ↔ IsSquare (f h)
  rw [square_branch hk odd same root]
  change IsSquare (((r*(h.val:ℤ):ℤ):ZMod (2^j))) ↔ IsSquare ((u:ZMod _)*h)
  push_cast
  rw [ZMod.natCast_zmod_val,hu]

/-- Every suffix selected by the public square-root condition admits a
center at the requested precision. The formula counts all distinct lifts
of its base sum class that actually have compatible factor witnesses. -/
theorem singular_count {k j N a : ℕ} (hk : 3≤k) (pos : 1≤j) (odd : Odd N)
    (hit : a∈SingularDyadicClueSuffixes.menu k N) :
    ∃ r : ℤ, Odd r ∧ r ≡ a [ZMOD (2:ℤ)^k] ∧ r^2 ≡ N [ZMOD (2:ℤ)^(2*k+j)] ∧
      (∀ s : ℤ, AtLevel k (2*k+j) N a s → s ≡ 2*r [ZMOD (2:ℤ)^(2*k)]) ∧
      Nat.card {h : ZMod (2^j) // AtLevel k (2*k+j) N a (2*r+2^(2*k)*(h.val:ℤ))} =
        (2^j + (if j%2=0 then 8 else 10))/6 := by
  obtain ⟨r,ro,same,root⟩ := SingularDyadicClueSuffixes.lift hk odd hit (2*k+j)
  exact ⟨r,ro,same,root,fun _ h => center_necessary (by omega) ro same root h,
    (lift_count hk ro same root).trans (DyadicSquareValueCount.closed pos)⟩

end PrimeFactors.DyadicClueSquareBranch
