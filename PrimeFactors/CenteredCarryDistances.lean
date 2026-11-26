import PrimeFactors.LowBitsCarryMenu

/-! Distances to the nearest radix multiples after any successful carry probe. -/

namespace PrimeFactors.CenteredCarryDistances

open PredictedTraceCarries

/-- Nearest rounding minimizes the magnitude of the residual among all
integer anchors, including a tie. -/
theorem nearest_min {n D : ℤ} (dp : 0<D) (b : ℤ) :
    |n-nearest n D*D| ≤ |n-b*D| := by
  let a := nearest n D
  change |n-a*D| ≤ |n-b*D|
  by_cases eq : a=b
  · rw [eq]
  have one : 1≤|b-a| := by have := abs_pos.mpr (sub_ne_zero.mpr (Ne.symm eq)); omega
  have apart : D≤|(n-a*D)-(n-b*D)| := calc
    D ≤ |b-a| * D := by simpa only [one_mul] using mul_le_mul_of_nonneg_right one dp.le
    _ = _ := by rw [show (n-a*D)-(n-b*D)=(b-a)*D by ring,abs_mul,abs_of_pos dp]
  have triangle := abs_sub (n-a*D) (n-b*D)
  have bound : 2*|n-a*D|≤D := by simpa only [a,mul_comm D] using nearest_error (n:=n) dp
  linarith only [apart,triangle,bound]

def anchor (n D : ℕ) : ℕ := (nearest n D).toNat

theorem anchor_cast (n : ℕ) {D : ℕ} (dp : 0<D) : ((anchor n D : ℕ):ℤ)=nearest n D := by
  apply Int.toNat_of_nonneg
  unfold nearest
  exact Int.ediv_nonneg (by positivity) (by positivity)

/-- Every actual split (including an incidental square) bounds the product
of the two nearest distances. Twice the area costs at most (2K+1)D. -/
theorem centered_of_probe {p q D f K : ℕ} {h k : ℤ} (pp : p.Prime) (qp : q.Prime) (ne : p≠q)
    (dp : 0<D) (small : |k|≤(K:ℤ)) (hit : probe (p*q) D h k=some f) :
    2*|(p:ℤ)-(anchor p D:ℕ)*D|≤D ∧ 2*|(q:ℤ)-(anchor q D:ℕ)*D|≤D ∧
    2*(|(p:ℤ)-(anchor p D:ℕ)*D| * |(q:ℤ)-(anchor q D:ℕ)*D|)≤(2*(K:ℤ)+1)*D := by
  have di : (0:ℤ)<D := by exact_mod_cast dp
  rw [anchor_cast _ dp,anchor_cast _ dp]
  have side (x : ℤ) : 2*|x-nearest x D*D|≤D := by
    simpa only [mul_comm (D:ℤ)] using nearest_error (n:=x) di
  refine ⟨side _,side _,?_⟩
  obtain ⟨A,B,prod⟩ := LowBitsCarryMenu.lift_of_probe pp qp ne hit
  have smaller := mul_le_mul (nearest_min (n:=(p:ℤ)) di A) (nearest_min (n:=(q:ℤ)) di B)
    (abs_nonneg _) (abs_nonneg _)
  conv at smaller => rhs; rw [←abs_mul,←prod]
  let n : ℤ := (p*q:ℕ)
  have triangle := abs_add_le (n-D*nearest n D) ((D:ℤ)*k)
  have lower := nearest_error (n:=n) di
  have budget := mul_le_mul_of_nonneg_left small di.le
  rw [abs_mul,abs_of_pos di] at triangle
  change _ ≤ |n-D*nearest n D+D*k| at smaller
  nlinarith only [smaller,triangle,lower,budget]

/-- Natural anchor form for counting both coordinate distances in a rectangle. -/
theorem of_probe {p q D f K : ℕ} {h k : ℤ} (pp : p.Prime) (qp : q.Prime) (ne : p≠q)
    (dp : 0<D) (small : |k|≤(K:ℤ)) (hit : probe (p*q) D h k=some f) :
    ∃ a b : ℕ, |(p:ℤ)-a*D|≤D ∧ |(q:ℤ)-b*D|≤D ∧
      |(p:ℤ)-a*D| * |(q:ℤ)-b*D|≤((K:ℤ)+1)*D := by
  obtain ⟨x,y,area⟩ := centered_of_probe pp qp ne dp small hit
  refine ⟨anchor p D,anchor q D,by omega,by omega,?_⟩
  have pos : (0:ℤ)≤D := by positivity
  nlinarith only [area,pos]

end PrimeFactors.CenteredCarryDistances
