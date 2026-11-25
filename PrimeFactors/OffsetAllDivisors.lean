import PrimeFactors.OffsetDivisorSieve

namespace PrimeFactors.OffsetAllDivisors
open Finset

/-- Primitive multipliers through K for one offset. -/
noncomputable def multipliers (j K : ℕ) : Finset ℕ :=
  (Icc 1 K).filter fun k => j.Coprime k

private def encode (p : ℕ) (x : ℕ × ℕ) := x.2+1+x.1*p
private def decode (p k : ℕ) := (k/p,k%p-1)

private theorem decode_encode {p i r : ℕ} (small : r+1<p) :
    decode p (encode p (i,r))=(i,r) := by
  simp [decode,encode,Nat.add_mul_div_right _ _ (by omega : 0<p),
    Nat.div_eq_of_lt small,Nat.mod_eq_of_lt small]

/-- Each full block of p consecutive multipliers contributes p−1 coprime
choices at offset p^e. The injection uses no enumeration of the range. -/
theorem prime_power_count {p : ℕ} (prime : p.Prime) (e K : ℕ) :
    K/p*(p-1) ≤ (multipliers (p^e) K).card := by
  let domain := range (K/p) ×ˢ range (p-1)
  have count : domain.card ≤ (multipliers (p^e) K).card := by
    apply card_le_card_of_injOn (encode p)
    · rintro ⟨i,r⟩ hx
      obtain ⟨hi,hr⟩ := mem_product.mp hx
      have lim := (Nat.le_div_iff_mul_le prime.pos).mp (show i+1≤K/p from mem_range.mp hi)
      have small : r+1<p := by have := mem_range.mp hr; omega
      have undiv : ¬p ∣ r+1 := Nat.not_dvd_of_pos_of_lt (by omega) small
      have cop := (Nat.coprime_add_mul_right_right p (r+1) i).mpr (prime.coprime_iff_not_dvd.mpr undiv)
      apply mem_filter.mpr
      exact ⟨mem_Icc.mpr ⟨by change 1≤r+1+i*p; omega, by change r+1+i*p≤K; nlinarith only [lim,small]⟩,
        cop.pow_left e⟩
    · rintro ⟨i,r⟩ hx ⟨i',r'⟩ hy same
      have ls := mem_range.mp (mem_product.mp hx).2
      have rs := mem_range.mp (mem_product.mp hy).2
      exact (decode_encode (i:=i) (p:=p) (by omega : r+1<p)).symm.trans
        ((congrArg (decode p) same).trans (decode_encode (by omega : r'+1<p)))
  simpa [domain,card_product] using count

/-- A centered square root simultaneously passes all offset divisor tests.
The counted multipliers also have nonnegative residual and strictly positive
signed discriminant. They are candidates before testing for a perfect square. -/
def SurvivingRow (N j : ℕ) : Prop :=
  let T := N.sqrt
  let h := N-T^2
  let row := multipliers j (T*j/h)
  (∃ b : ℤ, 2*|b|≤(j:ℤ) ∧ ∀ w : ℤ, w∣(j:ℤ) → b^2 ≡ -(h:ℤ) [ZMOD w]) ∧
  2^511 < row.card ∧ ∀ k ∈ row, 3*j^2≤4*h ∧ CompleteOffsetSearch.InSchedule T h j k ∧
    h*k≤T*j ∧ 0<GroupedOffsetRows.form T h j k

private theorem certify {N T p e : ℕ} {b : ℤ} (sq : N.sqrt=T) (prime : p.Prime)
    (hp : 0<N-T^2) (sharp : 3*(p^e)^2≤4*(N-T^2)) (center : 2*|b|≤((p^e:ℕ):ℤ))
    (root : b^2 ≡ -((N-T^2:ℕ):ℤ) [ZMOD ((p^e:ℕ):ℤ)])
    (many : 2^511<(T*(p^e)/(N-T^2))/p*(p-1)) : SurvivingRow N (p^e) := by
  unfold SurvivingRow
  rw [sq]
  dsimp only
  refine ⟨⟨b,center,fun _ div => root.of_dvd div⟩,many.trans_le (prime_power_count prime _ _),?_⟩
  intro k hk
  obtain ⟨mem,cop⟩ := mem_filter.mp hk
  obtain ⟨kp,cap⟩ := mem_Icc.mp mem
  have jp : 0<p^e := pow_pos prime.pos _
  have js : p^e≤(4*(N-T^2)).sqrt := Nat.le_sqrt'.mpr (by omega)
  have residual : (N-T^2)*k≤T*(p^e) := by simpa [Nat.mul_comm k] using (Nat.le_div_iff_mul_le hp).mp cap
  refine ⟨sharp,⟨jp,js,kp,cap.trans (Nat.le_succ _),cop⟩,residual,?_⟩
  have rr : 0≤(T:ℤ)*((p^e:ℕ):ℤ)-((N-T^2:ℕ):ℤ)*k := sub_nonneg.mpr (by exact_mod_cast residual)
  unfold GroupedOffsetRows.form
  have pj : 0<((p^e:ℕ):ℤ) := by exact_mod_cast jp
  positivity

private def freshRoot : ℤ := -1388569081821981928629018559746679698391443240038490844448109720992268310446829137894054161109471559975864626203484764615489399682500130767319601616627628
private def crossedRoot : ℤ := -2560590762260835885792580049121805660583532114171820857061519820348363357724957201064074878489564721868691593359643532482834065867296404520716100868321216

open ChebyshevQuarticScale in
/-- More than 2^511 primitive, positive-discriminant candidates survive all
offset divisors at the single fresh offset 7^182. -/
theorem fresh_row : SurvivingRow fresh (7^182) := by
  apply certify (T:=GroupedOffsetRowExamples.fresh.T) (b:=freshRoot) GroupedOffsetRowExamples.fresh_row.1
  all_goals decide +kernel

open ChebyshevQuarticScale in
/-- The same finite lower bound at the single crossed offset 13^138. -/
theorem crossed_row : SurvivingRow crossed (13^138) := by
  apply certify (T:=GroupedOffsetRowExamples.crossed.T) (b:=crossedRoot) GroupedOffsetRowExamples.crossed_row.1
  all_goals decide +kernel

end PrimeFactors.OffsetAllDivisors
