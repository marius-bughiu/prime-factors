import PrimeFactors.Multiplier

/-! Exclude every divisor of an odd product in an interval below its
square root by checking the discriminants of all parity-compatible sums. -/
namespace PrimeFactors.SumIntervalExclusion

/-- Each supplied h certifies the gap between h² and (h+1)². A negative
discriminant is rejected directly. Every subsequent row advances by four. -/
def check (n first : ℕ) : List ℕ → Bool
  | [] => true
  | h::hs => decide (first^2<4*n ∨
      (4*n+h^2<first^2 ∧ first^2<4*n+(h+1)^2)) && check n (first+4) hs

theorem check_sound {n first : ℕ} {hs : List ℕ} (cert : check n first hs=true) {i : ℕ}
    (inside : i<hs.length) (g : ℕ) : (first+4*i)^2≠4*n+g^2 := by
  induction hs generalizing i first with
  | nil => simp at inside
  | cons h hs ih =>
    simp only [check,Bool.and_eq_true,decide_eq_true_eq] at cert
    obtain ⟨miss,more⟩ := cert
    cases i with
    | zero =>
      simp only [Nat.mul_zero,Nat.add_zero]
      intro square
      rcases miss with negative|⟨lo,hi⟩
      · omega
      · rcases le_or_gt g h with small|big
        · have := Nat.pow_le_pow_left small 2
          omega
        · have : (h+1)^2≤g^2 := Nat.pow_le_pow_left (Nat.succ_le_of_lt big) 2
          omega
    | succ j =>
      rw [show first+4*(j+1)=first+4+4*j by omega]
      exact ih more (by simpa using inside)

theorem sum_congruence {p q : ℕ} (odd : (p*q)%2=1) : (p+q)%4=(p*q+1)%4 := by
  obtain ⟨⟨a,ha⟩,⟨b,hb⟩⟩ := Nat.odd_mul.mp (Nat.odd_iff.mpr odd)
  have eq : p*q+1=p+q+4*(a*b) := by rw [ha,hb]; ring
  rw [eq,Nat.add_mul_mod_self_left]

/-- A divisor pair would place its sum in the arithmetic progression
first, first+4, ..., first+4*(hs.length−1). The certificate inequalities
on the endpoints are cleared of divisions. No primality or balance is
required, only that the interval end lies below the square root. -/
theorem excludes {n a b first : ℕ} {hs : List ℕ} (odd : n%2=1)
    (ap : 0<a) (ab : a≤b) (below : b*b≤n) (cong : first%4=(n+1)%4)
    (low : b*first < b*b+n+4*b) (hi : a*a+n < a*(first+4*hs.length))
    (cert : check n first hs=true) (p : ℕ) (pl : a≤p) (pu : p≤b) : ¬p∣n := by
  rintro ⟨q,rfl⟩
  have bp := ap.trans_le ab
  have qb : b≤q := by
    by_contra! small
    exact (not_lt_of_ge below) <| (Nat.mul_le_mul_right q pu).trans_lt
      (Nat.mul_lt_mul_of_pos_left small bp)
  have left_bound : b*b+p*q≤b*(p+q) := by
    zify at pu qb ⊢
    nlinarith only [mul_nonneg (sub_nonneg.mpr pu) (sub_nonneg.mpr qb)]
  have right_bound : a*(p+q)≤a*a+p*q := by
    zify at pl ab qb ⊢
    nlinarith only [mul_nonneg (sub_nonneg.mpr pl) (sub_nonneg.mpr (ab.trans qb))]
  have bottom : first < p+q+4 := Nat.lt_of_mul_lt_mul_left (a:=b) (by
    rw [Nat.mul_add,Nat.mul_comm b 4]
    omega)
  have top : p+q<first+4*hs.length := Nat.lt_of_mul_lt_mul_left (right_bound.trans_lt hi)
  have residue := (sum_congruence odd).trans cong.symm
  let i := (p+q-first)/4
  have loc : i<hs.length ∧ p+q=first+4*i := by dsimp [i]; omega
  have sq := multiplier_sum_square p q 1 1
  simp only [one_mul,mul_one] at sq
  rw [loc.2] at sq
  exact check_sound cert loc.1 _ sq

end PrimeFactors.SumIntervalExclusion
