import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.GroupTheory.OrderOfElement

namespace PrimeFactors.WeightedBaseOrder

/-- Project each known powered base to one pairwise-coprime component of its
order. One combined base then realizes the product of the component orders.
The same integer recipe can be used independently in both local unit groups. -/
theorem combine {G ι : Type*} [CommGroup G] (S : Finset ι) (stride : ℕ)
    (base : ι → G) (order component : ι → ℕ)
    (known : ∀ i ∈ S, orderOf ((base i)^stride) = order i)
    (nz : ∀ i ∈ S, order i ≠ 0) (dvd : ∀ i ∈ S, component i ∣ order i)
    (cop : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → (component i).Coprime (component j)) :
    orderOf ((∏ i ∈ S, (base i)^(order i / component i))^stride) = ∏ i ∈ S, component i := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i T hi ih =>
    have small {j : ι} (hj : j ∈ T) : j ∈ insert i T := Finset.mem_insert_of_mem hj
    have rest := ih (fun j h => known j (small h)) (fun j h => nz j (small h))
      (fun j h => dvd j (small h)) (fun j h k h' => cop j (small h) k (small h'))
    have here := Finset.mem_insert_self i T
    have selected : orderOf (((base i)^(order i/component i))^stride)=component i := by
      rw [pow_right_comm, ← known i here]
      exact orderOf_pow_orderOf_div (by rw [known i here]; exact nz i here)
        (by rw [known i here]; exact dvd i here)
    rw [Finset.prod_insert hi, Finset.prod_insert hi, mul_pow,
      (Commute.all _ _).orderOf_mul_eq_mul_orderOf_of_coprime, selected, rest]
    rw [selected,rest,Nat.coprime_prod_right_iff]
    exact fun j hj => cop i here j (small hj) (fun eq => hi (eq ▸ hj))

end PrimeFactors.WeightedBaseOrder
