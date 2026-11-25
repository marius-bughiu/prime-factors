import PrimeFactors.GroupedOffsetRowExamples
import PrimeFactors.CompleteOffsetSearch

namespace PrimeFactors.OffsetDivisorSieve

/-- A signed square yields an integral root even when its square root is
smaller than the offset and the residual T*j-h*k is negative. -/
theorem signed_root {T h k j d : ℤ}
    (square : d^2=GroupedOffsetRows.form T h j k) :
    ∃ m : ℤ, d=2*m+j ∧ m*(m+j)+h*k^2=k*T*j := by
  unfold GroupedOffsetRows.form at square
  have par : d^2%2=j^2%2 := by
    rw [square,show 4*k*(T*j-h*k)=2*(2*k*(T*j-h*k)) by ring,Int.add_mul_emod_self_left]
  rw [pow_two,pow_two,Int.mul_emod d d,Int.mul_emod j j] at par
  have same : d%2=j%2 := by
    rcases (show d%2=0 ∨ d%2=1 by omega) with a|a <;>
      rcases (show j%2=0 ∨ j%2=1 by omega) with b|b <;> rw [a,b] at par ⊢ <;> norm_num at par ⊢
  let m := (d-j)/2
  have split : d=2*m+j := by dsimp [m]; omega
  refine ⟨m,split,?_⟩
  rw [split] at square
  nlinarith only [square]

/-- Every divisor of the entire offset, including every dyadic divisor, must
permit a square root of -h. Only the signed square and primitivity are used. -/
theorem offset_divisor {T h k j d w : ℤ} (unit : IsCoprime k j)
    (square : d^2=GroupedOffsetRows.form T h j k) (wj : w ∣ j) :
    ∃ b : ℤ, b^2 ≡ -h [ZMOD w] := by
  obtain ⟨m,_,rel⟩ := signed_root square
  obtain ⟨a,b,inverse⟩ := unit
  have inv : a*k ≡ 1 [ZMOD j] := Int.modEq_iff_dvd.mpr ⟨b,by linear_combination -inverse⟩
  have rd : m^2 ≡ -h*k^2 [ZMOD j] := Int.modEq_iff_dvd.mpr ⟨m-k*T,by linear_combination -rel⟩
  refine ⟨a*m,Int.ModEq.of_dvd wj ?_⟩
  calc (a*m)^2 = a^2*m^2 := by ring
       _ ≡ a^2*(-h*k^2) [ZMOD j] := rd.mul_left _
       _ = -h*(a*k)^2 := by ring
       _ ≡ -h*1^2 [ZMOD j] := (inv.pow 2).mul_left _
       _ = -h := by ring

/-- A square root modulo a positive offset always has a centered lift.
Its centered size alone imposes no extra restriction on the offset. -/
theorem centered {h j x : ℤ} (pos : 0<j) (root : x^2 ≡ -h [ZMOD j]) :
    ∃ b : ℤ, 2*|b|≤j ∧ b^2 ≡ -h [ZMOD j] := by
  let r := x%j
  have low : 0≤r := Int.emod_nonneg _ pos.ne'
  have high : r<j := Int.emod_lt_of_pos _ pos
  have rx : r ≡ x [ZMOD j] := Int.mod_modEq _ _
  by_cases small : 2*r≤j
  · exact ⟨r,by rwa [abs_of_nonneg low],(rx.pow 2).trans root⟩
  · refine ⟨r-j,by rw [abs_of_nonpos (by omega : r-j≤0)];omega,?_⟩
    have center : r-j ≡ r [ZMOD j] := Int.modEq_iff_dvd.mpr ⟨1,by ring⟩
    exact ((center.trans rx).pow 2).trans root

/-- With only the remainder h prescribed, every admissible offset occurs on
nonsquare inputs with arbitrarily large floor square roots, already at k=1. -/
theorem realizable_at_large_center {h j x : ℤ} (hp : 0<h) (jp : 0<j)
    (root : x^2 ≡ -h [ZMOD j]) (bound : ℤ) :
    ∃ T d : ℤ, bound≤T ∧ 0≤T ∧ T^2<T^2+h ∧ T^2+h<(T+1)^2 ∧
      d^2=GroupedOffsetRows.form T h j 1 := by
  let r := x%j
  let b := r+j*(|bound|+h+1)
  have rp : 0≤r := Int.emod_nonneg _ jp.ne'
  have scaled := mul_le_mul_of_nonneg_right (show 1≤j by omega)
    (show 0≤|bound|+h+1 by linarith [abs_nonneg bound])
  have hb : h≤b := by dsimp [b];linarith [abs_nonneg bound]
  have mb : bound≤b := by dsimp [b];linarith [le_abs_self bound]
  have lift : b ≡ r [ZMOD j] := Int.modEq_iff_dvd.mpr ⟨-(|bound|+h+1),by dsimp [b];ring⟩
  have bx : b ≡ x [ZMOD j] := lift.trans (Int.mod_modEq _ _)
  obtain ⟨c,eq⟩ := Int.modEq_iff_dvd.mp ((bx.pow 2).trans root)
  have neg : c≤0 := by
    by_contra! pos
    nlinarith only [eq,mul_pos jp pos,sq_nonneg b,hp]
  refine ⟨b-c,2*b+j,by omega,by omega,by omega,by nlinarith only [hb,neg,hp],?_⟩
  unfold GroupedOffsetRows.form
  linear_combination -4*eq

/-- The actual executable success guard gives a signed square. Casting the
guarded natural subtraction to the integers preserves the gap exactly. -/
theorem probe_square {N T j k f : ℕ} (hit : CompleteOffsetSearch.probe N T j k=some f) :
    ∃ d : ℤ, d^2=GroupedOffsetRows.form T ((N:ℤ)-(T:ℤ)^2) j k := by
  let S := j+2*T*k
  let target := 4*k^2*N
  let d := (S^2-target).sqrt
  unfold CompleteOffsetSearch.probe at hit
  dsimp only at hit
  split at hit
  next pass =>
    have ok : target≤S^2 := pass.1
    have square : d^2=S^2-target := pass.2.1
    have eq : d^2+target=S^2 := square ▸ Nat.sub_add_cancel ok
    refine ⟨(d:ℤ),?_⟩
    unfold GroupedOffsetRows.form
    dsimp only [target,S] at eq
    zify at eq
    linear_combination eq
  next => contradiction

/-- The complete 1,024-bit prime-pair theorem still finds one of the actual
prime factors after requiring a centered root for the entire offset. This
same root passes every divisor test, including powers of two. -/
theorem complete_filtered_1024 {N p q : ℕ} (pair : p*q=N) (pp : p.Prime) (qp : q.Prime)
    (distinct : p≠q) (pbits : 2^1023≤p ∧ p<2^1024) (qbits : 2^1023≤q ∧ q<2^1024) :
    let T := N.sqrt
    let h := N-T^2
    ∃ j k : ℕ, 3*j^2≤4*h ∧ CompleteOffsetSearch.InSchedule T h j k ∧
      (∃ b : ℤ, 2*|b|≤(j:ℤ) ∧ ∀ w : ℤ, w ∣ (j:ℤ) → b^2 ≡ -(h:ℤ) [ZMOD w]) ∧
      (CompleteOffsetSearch.probe N T j k=some p ∨ CompleteOffsetSearch.probe N T j k=some q) := by
  obtain ⟨j,k,small,domain,hit⟩ := CompleteOffsetSearch.complete_1024_bit_factors pair pp qp
    distinct pbits qbits
  dsimp only
  refine ⟨j,k,small,domain,?_,hit⟩
  have yes : ∃ f, CompleteOffsetSearch.probe N N.sqrt j k=some f :=
    hit.elim (fun hp => ⟨p,hp⟩) (fun hq => ⟨q,hq⟩)
  obtain ⟨f,good⟩ := yes
  obtain ⟨d,square⟩ := probe_square good
  have unit := domain.2.2.2.2.symm.isCoprime
  have cast : ((N-N.sqrt^2:ℕ):ℤ)=(N:ℤ)-(N.sqrt:ℤ)^2 := by
    rw [Nat.cast_sub (Nat.sqrt_le' N),Nat.cast_pow]
  rw [← cast] at square
  obtain ⟨x,root⟩ := offset_divisor unit square (dvd_refl (j:ℤ))
  obtain ⟨b,size,cong⟩ := centered (by exact_mod_cast domain.1) root
  exact ⟨b,size,fun _ div => cong.of_dvd div⟩

private def obstructionTable (n : ℕ) (moduli : List ℕ) : Bool :=
  let h := (n:ℤ)-(n.sqrt:ℤ)^2
  moduli.all fun q => decide (0<q) && (List.range q).all fun b =>
    decide ((b:ℤ)^2%(q:ℤ) ≠ (-h)%(q:ℤ))

private theorem table_excludes {n : ℕ} {moduli : List ℕ} (table : obstructionTable n moduli)
    {q : ℕ} (mem : q ∈ moduli) {j k : ℤ} (div : (q:ℤ) ∣ j) (unit : IsCoprime k j) :
    ¬∃ d : ℤ, d^2=GroupedOffsetRows.form n.sqrt ((n:ℤ)-(n.sqrt:ℤ)^2) j k := by
  intro hit
  obtain ⟨d,square⟩ := hit
  obtain ⟨b,sq⟩ := offset_divisor unit square div
  unfold obstructionTable at table
  obtain ⟨pos,checks⟩ := Bool.and_eq_true_iff.mp (List.all_eq_true.mp table q mem)
  have qp : 0<(q:ℤ) := by exact_mod_cast of_decide_eq_true pos
  let r := b%(q:ℤ)
  have lo : 0≤r := Int.emod_nonneg _ qp.ne'
  have hi : r<(q:ℤ) := Int.emod_lt_of_pos _ qp
  have valid : r.toNat ∈ List.range q := List.mem_range.mpr (by omega)
  have rejects := of_decide_eq_true (List.all_eq_true.mp checks r.toNat valid)
  rw [Int.toNat_of_nonneg lo] at rejects
  exact rejects (((Int.mod_modEq b (q:ℤ)).pow 2).trans sq)

open ChebyshevQuarticScale in
/-- Explicit prime-power obstructions through base prime 47 on the fresh
2,048-bit input. Every multiple fails for every primitive signed multiplier. -/
theorem fresh_obstructions {q : ℕ} (mem : q ∈ [4,5,11,13,17,19,23,31,37,81])
    {j k : ℤ} (div : (q:ℤ) ∣ j) (unit : IsCoprime k j) :
    ¬∃ d : ℤ, d^2=GroupedOffsetRows.form fresh.sqrt ((fresh:ℤ)-(fresh.sqrt:ℤ)^2) j k :=
  table_excludes (n:=fresh) (by
    unfold obstructionTable
    rw [show fresh.sqrt=GroupedOffsetRowExamples.fresh.T from GroupedOffsetRowExamples.fresh_row.1]
    decide +kernel) mem div unit

open ChebyshevQuarticScale in
/-- Same signed all-multiplier exclusion on the crossed 2,048-bit input. -/
theorem crossed_obstructions {q : ℕ} (mem : q ∈ [4,5,7,9,11,17,19,23,37,47])
    {j k : ℤ} (div : (q:ℤ) ∣ j) (unit : IsCoprime k j) :
    ¬∃ d : ℤ, d^2=GroupedOffsetRows.form crossed.sqrt ((crossed:ℤ)-(crossed.sqrt:ℤ)^2) j k :=
  table_excludes (n:=crossed) (by
    unfold obstructionTable
    rw [show crossed.sqrt=GroupedOffsetRowExamples.crossed.T from GroupedOffsetRowExamples.crossed_row.1]
    decide +kernel) mem div unit

end PrimeFactors.OffsetDivisorSieve
