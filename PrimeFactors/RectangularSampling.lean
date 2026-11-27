import PrimeFactors.RectangularDistinctProducts
import PrimeFactors.RectangularRowNormalization

/-! Count uniform trials in the exact positive multiplier set. A trial is
credited with a hit whenever its complete unsieved interval contains a square. -/
namespace PrimeFactors.RectangularSampling
open Finset RectangularFullWidth RectangularRowNormalization RectangularSearchFloor
set_option exponentiation.threshold 4096

theorem counts {p q : ℕ} (pp : p.Prime) (qp : q.Prime) (lt : p<q)
    (pl : 2^1023≤p) (qu : q<2^1024) (lo : 2^2047≤p*q) (hi : p*q<2^2048) :
    let N := p*q
    let all := emitted (K N) 1024 (excess N)
    let good := all ∩ hits N (B N) (H N) (K N) false
    2^157*good.card≤all.card ∧ (10^12)*(2^117)*good.card≤all.card := by
  dsimp only
  let N := p*q
  let b := B N
  let h := H N
  let k := K N
  let all := emitted k 1024 (excess N)
  let good := all ∩ hits N b h k false
  obtain ⟨_,_,_,bu,hu,_,_⟩ := dimensions lo hi
  have np : 0<N := Nat.mul_pos pp.pos qp.pos
  have upper : b+h<N := by dsimp [b,h,N]; omega
  have mul : h*b<N := by
    have price : h*(b+1)≤N := Nat.div_mul_le_self ..
    by_cases zero : h=0
    · simpa [zero] using np
    · rw [Nat.mul_add,Nat.mul_one] at price; omega
  have pc := primitive_cap (B:=b) (H:=h) (K:=k) pp qp lt (by omega) upper mul
  have each := count (B:=b) (H:=h) (K:=k) pp qp lt (by dsimp [h,N]; omega) (by omega)
  have raw : good.card≤2*2^343 :=
    (card_le_card inter_subset_right).trans (each.trans (Nat.mul_le_mul pc (full_sqrt lo hi)))
  have denom : 2^501≤all.card := RectangularDistinctProducts.full_width lt qu lo hi
  change 2^157*good.card≤all.card ∧ (10^12)*(2^117)*good.card≤all.card
  omega

end PrimeFactors.RectangularSampling
