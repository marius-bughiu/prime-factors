import Mathlib.Data.Nat.ChineseRemainder

namespace PrimeFactors.WeightedSparseCoverage

/-- Two phases separated by k cover every residue when the common omitted
template is 0 through k-1 and 2k ≤ ell. -/
theorem two_phases (u k ell : ℕ) (short : 2*k≤ell) :
    k≤u%ell ∨ k≤(u+k)%ell := by
  by_cases small : u%ell<k
  · right
    rw [← Nat.mod_add_mod u ell k, Nat.mod_eq_of_lt (by omega : u%ell+k<ell)]
    omega
  · exact Or.inl (by omega)

/-- Local covers by arbitrary phase choices yield a legal common sparse baby
index in some global phase. The CRT representative lies in the first period.
Here u is the trace index relative to the original left endpoint. -/
theorem translated_cover {ι : Type*} [Fintype ι] (ell : ι → ℕ)
    (pos : ∀ i, 0<ell i) (cop : Pairwise (fun i j => (ell i).Coprime (ell j)))
    (choices : ι → Finset ℕ) (keep : ι → ℕ → Prop) (u span : ℕ)
    (sp : 0<span) (period : ∀ i, ell i ∣ span)
    (covers : ∀ i, ∃ r ∈ choices i, keep i ((u+r)%(ell i))) :
    ∃ j block baby : ℕ, j < ∏ i, ell i ∧
      (∀ i, ∃ r ∈ choices i, j ≡ r [MOD ell i]) ∧
      u+j=span*block+baby ∧ baby<span ∧ ∀ i, keep i (baby%(ell i)) := by
  classical
  choose r membership allowed using covers
  have nz : ∀ i ∈ (Finset.univ : Finset ι), ell i ≠ 0 := fun i _ => (pos i).ne'
  have cp : Set.Pairwise (↑(Finset.univ : Finset ι)) (fun i j => (ell i).Coprime (ell j)) :=
    fun _ _ _ _ h => cop h
  let crt := Nat.chineseRemainderOfFinset r ell Finset.univ nz cp
  let j := crt.val
  have eq (i : ι) : j ≡ r i [MOD ell i] := crt.property i (Finset.mem_univ i)
  refine ⟨j,(u+j)/span,(u+j)%span,?_,fun i => ⟨r i,membership i,eq i⟩,
    (Nat.div_add_mod (u+j) span).symm,Nat.mod_lt _ sp,?_⟩
  · exact Nat.chineseRemainderOfFinset_lt_prod r ell nz cp
  · intro i
    rw [Nat.mod_mod_of_dvd _ (period i)]
    rw [show (u+j)%(ell i)=(u+r i)%(ell i) from (eq i).add_left u]
    exact allowed i

end PrimeFactors.WeightedSparseCoverage
