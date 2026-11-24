import PrimeFactors.TraceDirection

namespace PrimeFactors.QuarticSlopeBit

open PrimeFactors.QuarticTrace PrimeFactors.TraceDirection

private theorem square_residues (x : ℤ) :
    x^2 % 8 = if x % 2 = 1 then 1 else if x % 4 = 0 then 0 else 4 := by
  rw [pow_two, Int.mul_emod]
  have bounds := Int.emod_lt_of_pos x (by decide : (0 : ℤ) < 8)
  have lower := Int.emod_nonneg x (by decide : (8 : ℤ) ≠ 0)
  interval_cases h : x % 8 <;> split_ifs <;> omega

private theorem odd_mul_even {h v : ℤ} (ho : Odd h) (ve : v%2=0) :
    (h*v)%4=v%4 := by
  obtain ⟨k, hk⟩ := ho
  have div : v=2*(v/2) := by omega
  have step : h*v = 4*(k*(v/2))+v := by rw [hk]; linear_combination 2*k*div
  omega

/-- The low two bits of a slope chosen for an odd/even norm direction. -/
theorem slope_mod_four {u v s : ℤ} (uo : Odd u) (ve : v%2=0)
    (slope : (u*s)%4=v%4) :
    (s%4=0 ∧ (u^2+v^2)%8=1) ∨ (s%4=2 ∧ (u^2+v^2)%8=5) := by
  have se : s%2=0 := by
    obtain ⟨k, hk⟩ := uo
    have eq : u*s = 2*(k*s)+s := by rw [hk]; ring
    omega
  rw [odd_mul_even uo se] at slope
  have u1 := Int.odd_iff.mp uo
  rw [Int.add_emod, square_residues u, square_residues v]
  split_ifs <;> omega

/-- One unnormalized complete trace detects residue class five for the prime
at which the selector is a nonsquare. -/
theorem trace_mod_sixteen {p q : ℕ} [Fact p.Prime] [Fact q.Prime] [NeZero (p*q)]
    (cop : p.Coprime q) (pc : p%4=1) (qc : q%4=1) (d : ℤ)
    (left : quadraticChar (ZMod p) (d : ZMod p) = -1)
    (right : quadraticChar (ZMod q) (d : ZMod q) = 1) :
    complete (p*q) d % 16 = 8 ↔ p%8=5 := by
  obtain ⟨h,u,v,ho,uo,_,norm,_,trace⟩ := direction_of_traces p q cop pc qc d left right
  have u1 := Int.odd_iff.mp uo
  have residue := congrArg (fun z : ℤ => z%8) norm
  dsimp at residue
  rw [Int.add_emod, square_residues u, square_residues v, if_pos u1] at residue
  have p4 : (p : ℤ)%4=1 := by exact_mod_cast pc
  have ve : v%2=0 := by split_ifs at residue <;> omega
  have m := odd_mul_even ho ve
  rw [trace, mul_assoc]
  have reduce : (4*(h*v))%16=4*((h*v)%4) := by omega
  rw [reduce,m]
  have cast8 : ((p%8 : ℕ) : ℤ)=(p : ℤ)%8 := by push_cast; rfl
  split_ifs at residue <;> omega

private theorem square_crt {p q : ℕ} (cop : p.Coprime q) (a : ℤ) :
    IsSquare (a : ZMod (p*q)) ↔ IsSquare (a : ZMod p) ∧ IsSquare (a : ZMod q) := by
  let e := ZMod.chineseRemainder cop
  constructor
  · rintro ⟨x,hx⟩
    have eq := congrArg e hx
    rw [map_intCast,map_mul] at eq
    exact ⟨⟨(e x).1, congrArg Prod.fst eq⟩, ⟨(e x).2, congrArg Prod.snd eq⟩⟩
  · rintro ⟨⟨x,hx⟩,⟨y,hy⟩⟩
    refine ⟨e.symm (x,y), e.injective ?_⟩
    rw [map_intCast,map_mul,e.apply_symm_apply]
    exact Prod.ext hx hy

/-- At a product of a 1 mod 8 and a 5 mod 8 prime, deciding if a Jacobi-positive
input is square is equivalent to reading one bit of its doubled-parameter trace. -/
theorem residuosity_iff_trace {p q : ℕ} [pp : Fact p.Prime] [pq : Fact q.Prime] [NeZero (p*q)]
    (cop : p.Coprime q) (pc : p%8=1) (qc : q%8=5) (a : ℤ)
    (sign : jacobiSym a (p*q)=1) :
    IsSquare (a : ZMod (p*q)) ↔ complete (p*q) (2*a)%16=8 := by
  rw [square_crt cop]
  rw [jacobiSym.mul_right' _ pp.out.ne_zero pq.out.ne_zero,
    ← jacobiSym.legendreSym.to_jacobiSym p, ← jacobiSym.legendreSym.to_jacobiSym q] at sign
  change quadraticChar (ZMod p) (a : ZMod p)*quadraticChar (ZMod q) (a : ZMod q)=1 at sign
  have pn : (a : ZMod p) ≠ 0 := fun h => by simp [h] at sign
  have qn : (a : ZMod q) ≠ 0 := fun h => by simp [h] at sign
  rw [← quadraticChar_one_iff_isSquare pn, ← quadraticChar_one_iff_isSquare qn]
  have p2 : quadraticChar (ZMod p) 2=1 := by
    rw [quadraticChar_two (by rw [ZMod.ringChar_zmod_n]; omega), ZMod.card, ZMod.χ₈_nat_eq_if_mod_eight]
    split_ifs <;> omega
  have q2 : quadraticChar (ZMod q) 2 = -1 := by
    rw [quadraticChar_two (by rw [ZMod.ringChar_zmod_n]; omega), ZMod.card, ZMod.χ₈_nat_eq_if_mod_eight]
    split_ifs <;> omega
  have pd : quadraticChar (ZMod p) ((2*a : ℤ) : ZMod p)=quadraticChar (ZMod p) (a : ZMod p) := by
    rw [Int.cast_mul, Int.cast_ofNat, map_mul, p2, one_mul]
  have qd : quadraticChar (ZMod q) ((2*a : ℤ) : ZMod q) = -quadraticChar (ZMod q) (a : ZMod q) := by
    rw [Int.cast_mul, Int.cast_ofNat, map_mul, q2, neg_one_mul]
  rcases quadraticChar_dichotomy pn with pos | neg
  · rw [pos,one_mul] at sign
    letI : NeZero (q*p) := ⟨Nat.mul_ne_zero pq.out.ne_zero pp.out.ne_zero⟩
    have bit := (trace_mod_sixteen cop.symm (by omega) (by omega) (2*a)
      (by rw [qd,sign]) (by rw [pd,pos])).mpr qc
    simp only [Nat.mul_comm q p] at bit
    simp [pos, sign, bit]
  · rw [neg,neg_one_mul] at sign
    have qneg : quadraticChar (ZMod q) (a : ZMod q) = -1 := by omega
    have bit := trace_mod_sixteen cop (by omega) (by omega) (2*a)
      (by rw [pd,neg]) (by rw [qd,qneg]; decide)
    simp [neg,bit,pc]

/-- Arithmetic cross-check for the two pairs in the discovery note.
The four character sums are measured there by direct enumeration. -/
theorem congruence_examples :
    (33017 : ℕ)%1536=42233%1536 ∧
    (20*(660/4) : ℤ)%32=(-240/4)%32 ∧ (14*(-572/4) : ℤ)%32=(440/4)%32 ∧
    (20 : ℕ)%4 ≠ 14%4 ∧ (66389 : ℕ)%4096=99157%4096 ∧
    (18*(-36/4) : ℤ)%32=(504/4)%32 ∧ (30*(1020/4) : ℤ)%32=(136/4)%32 ∧
    (18 : ℕ)%8 ≠ 30%8 := by decide

end PrimeFactors.QuarticSlopeBit
