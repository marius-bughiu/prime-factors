import PrimeFactors.QuarticStripDenominators

/-! Coordinate sizes for primitive and unreduced points in the fourth-root
recognition intervals, including denominators through 2^512. -/
namespace PrimeFactors.QuarticStripCoordinateBounds

set_option exponentiation.threshold 8192

private theorem box {m x y L S : ℕ} (form : m=x^4+4*y^4) (height : m<L^4)
    (room : 16*L^3≤S^4) :
    (m<(x+1)^4 → x<L ∧ y<S) ∧ (m<4*(y+1)^4 → y<L ∧ x<S) := by
  have xlow : x<L := (Nat.pow_lt_pow_iff_left (by decide : 4≠0)).mp (by omega)
  have ylow : y<L := (Nat.pow_lt_pow_iff_left (by decide : 4≠0)).mp (by omega)
  constructor
  · intro h
    have gap : y^4<(x+1)^3 := by
      rw [form] at h
      nlinarith only [h,Nat.zero_le x,Nat.zero_le (x^2)]
    have cap := Nat.pow_le_pow_left (show x+1≤L by omega) 3
    exact ⟨xlow,(Nat.pow_lt_pow_iff_left (by decide : 4≠0)).mp (by omega)⟩
  · intro h
    have gap : x^4<16*(y+1)^3 := by
      rw [form] at h
      nlinarith only [h,Nat.zero_le y,Nat.zero_le (y^2)]
    have cap := Nat.mul_le_mul_left 16 (Nat.pow_le_pow_left (show y+1≤L by omega) 3)
    exact ⟨ylow,(Nat.pow_lt_pow_iff_left (by decide : 4≠0)).mp (by omega)⟩

private theorem scaled {n d : ℕ} (hn : n<2^2048) (pos : 0<d) :
    d^4*n<(d*2^512)^4 := by
  rw [mul_pow,show ((2:ℕ)^512)^4=2^2048 by decide +kernel]
  exact Nat.mul_lt_mul_of_pos_left hn (pow_pos pos _)

theorem small {n d x y : ℕ} (hn : n<2^2048) (hd : d≤2^200)
    (form : d^4*n=x^4+4*y^4) :
    (d^4*n<(x+1)^4 → x<2^712 ∧ y<2^535) ∧
    (d^4*n<4*(y+1)^4 → y<2^712 ∧ x<2^535) := by
  apply box form _ (by decide +kernel)
  have h := (Nat.mul_le_mul_right n (Nat.pow_le_pow_left hd 4)).trans_lt
    (Nat.mul_lt_mul_of_pos_left hn (by decide +kernel : 0<((2:ℕ)^200)^4))
  exact h.trans_eq (by decide +kernel)

theorem large {n d x y : ℕ} (hn : n<2^2048) (lo : 2^200<d) (hi : d≤2^512)
    (form : d^4*n=x^4+4*y^4) :
    (d^4*n<(x+1)^4 → x<d^4 ∧ y<2^769) ∧
    (d^4*n<4*(y+1)^4 → y<d^4 ∧ x<2^769) := by
  have pos : 0<d := by omega
  have cap := scaled hn pos
  have side := (Nat.mul_le_mul_right (2^512) hi).trans_eq (show (2:ℕ)^512*2^512=2^1024 by decide +kernel)
  have room := (Nat.mul_le_mul_left 16 (Nat.pow_le_pow_left side 3)).trans
    (by decide +kernel : 16*((2:ℕ)^1024)^3≤(2^769)^4)
  have cube : 2^512≤d^3 := (by decide +kernel : (2:ℕ)^512≤(2^200)^3).trans (Nat.pow_le_pow_left lo.le 3)
  have lift : d*2^512≤d^4 := (Nat.mul_le_mul_left d cube).trans_eq (by ring)
  obtain ⟨left,right⟩ := box form cap room
  exact ⟨fun gap => ⟨(left gap).1.trans_le lift,(left gap).2⟩,
    fun gap => ⟨(right gap).1.trans_le lift,(right gap).2⟩⟩

end PrimeFactors.QuarticStripCoordinateBounds
