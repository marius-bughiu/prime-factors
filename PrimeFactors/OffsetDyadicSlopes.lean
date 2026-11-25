import PrimeFactors.OffsetSquareSplit
import PrimeFactors.PersistentLocalSurvivors
import PrimeFactors.FactorSum
import Mathlib.Data.ZMod.Units

/-!
For an odd target the forward chart is the modular hyperbola sumset translated
by −2T. Bower, Evans, Luo and Miller, Theorem 3.3, give its exact cardinality
at every dyadic precision: https://arxiv.org/abs/1212.2930. This file proves
the connection to true weighted discriminants and checks the concrete masks.
-/
namespace PrimeFactors.OffsetDyadicSlopes

/-- Forward-chart labels for an invertible denominator. The two actual
integer roots are used before reduction, so no division by two in ZMod is
needed. -/
noncomputable def forward (m : ℕ) [NeZero m] (N T : ZMod m) : Finset (ZMod m) :=
  ((Finset.univ : Finset (ZMod m)).filter (fun x => x.val.Coprime m)).image
    (fun x => x+N*x⁻¹-2*T)

theorem forward_iff {m : ℕ} [NeZero m] {N T r : ZMod m} (unit : IsUnit N) :
    r∈forward m N T ↔ AdmissibleSum N (r+2*T) := by
  have valid (x : ZMod m) : x.val.Coprime m ↔ IsUnit x := by
    rw [←ZMod.isUnit_iff_coprime,ZMod.natCast_zmod_val]
  constructor
  · rintro label
    obtain ⟨x,mem,rfl⟩ := Finset.mem_image.mp label
    have xu := (valid x).mp (Finset.mem_filter.mp mem).2
    refine ⟨x,N*x⁻¹,?_,by ring⟩
    rw [mul_left_comm, ZMod.mul_inv_of_unit x xu,mul_one]
  · rintro ⟨x,y,prod,sum⟩
    have xu := ((Commute.all x y).isUnit_mul_iff.mp (prod ▸ unit)).1
    refine Finset.mem_image.mpr ⟨x,Finset.mem_filter.mpr ⟨Finset.mem_univ _,(valid x).mpr xu⟩,?_⟩
    have yp : N*x⁻¹=y := by rw [←prod,mul_right_comm,ZMod.mul_inv_of_unit x xu,one_mul]
    rw [yp,sum]; ring

/-- A genuine weighted square in every odd-k row belongs to the forward
mask at every dyadic precision. The labels depend only on N and T. -/
theorem forward_of_square {N T j k d : ℕ} (nodd : Odd N) (kodd : Odd k)
    (square : (j+2*T*k)^2=4*k^2*N+d^2) (e : ℕ) :
    ((j:ZMod (2^e))*(k:ZMod (2^e))⁻¹)∈forward (2^e) N T := by
  let m := 2^e
  let A := (j+2*T*k+d)/2
  let B := (j+2*T*k-d)/2
  obtain ⟨sum,prod⟩ := OffsetSquareSplit.root_identities square
  change A+B=j+2*T*k at sum
  change A*B=N*k^2 at prod
  have nu := (ZMod.isUnit_iff_coprime N m).mpr (nodd.coprime_two_right.pow_right e)
  have ku := (ZMod.isUnit_iff_coprime k m).mpr (kodd.coprime_two_right.pow_right e)
  have kinv := ZMod.mul_inv_of_unit (k:ZMod m) ku
  have s : (A:ZMod m)+B=j+2*T*k := by simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using congrArg (fun z:ℕ => (z:ZMod m)) sum
  have p : (A:ZMod m)*B=N*k^2 := by simpa only [Nat.cast_mul,Nat.cast_pow] using congrArg (fun z:ℕ => (z:ZMod m)) prod
  apply (forward_iff nu).mpr
  refine ⟨(A:ZMod m)*(k:ZMod m)⁻¹,(B:ZMod m)*(k:ZMod m)⁻¹,?_,?_⟩
  · calc
      _ = ((A:ZMod m)*B)*((k:ZMod m)⁻¹)^2 := by ring
      _ = N*((k:ZMod m)*(k:ZMod m)⁻¹)^2 := by rw [p]; ring
      _ = _ := by rw [kinv]; simp
  · calc
      _ = ((A:ZMod m)+B)*(k:ZMod m)⁻¹ := by ring
      _ = (j:ZMod m)*(k:ZMod m)⁻¹+(2*T)*((k:ZMod m)*(k:ZMod m)⁻¹) := by rw [s]; ring
      _ = _ := by rw [kinv,mul_one]

/-- Every forward label is the reduction of a square-admitting label at any
higher precision. Surjectivity on units lifts the parameter x, after which
its partner is N/x. -/
theorem forward_lifts {m M : ℕ} [NeZero M] [NeZero m] (div : m∣M) (N T : ℕ) {r : ZMod m}
    (mem : r∈forward m N T) :
    ∃ R∈forward M N T, ZMod.castHom div (ZMod m) R=r ∧ IsSquare ((R+2*T)^2-4*N) := by
  obtain ⟨x,xm,rfl⟩ := Finset.mem_image.mp mem
  have xu : IsUnit x := by
    simpa only [ZMod.natCast_zmod_val] using
      (ZMod.isUnit_iff_coprime x.val m).mpr (Finset.mem_filter.mp xm).2
  obtain ⟨u,rfl⟩ := xu
  obtain ⟨v,hv⟩ := ZMod.unitsMap_surjective div u
  let z : ZMod M := v
  let y : ZMod M := (N:ZMod M)*↑(v⁻¹)
  have mult : z*y=N := by
    dsimp [z,y]; rw [mul_left_comm,Units.mul_inv,mul_one]
  refine ⟨z+y-2*T,?_,?_,?_⟩
  · exact Finset.mem_image.mpr ⟨z,Finset.mem_filter.mpr
      ⟨Finset.mem_univ _,ZMod.val_coe_unit_coprime v⟩,by simp [z,y,ZMod.inv_coe_unit]⟩
  · let f := ZMod.castHom div (ZMod m)
    have red : f (v : ZMod M)=(u:ZMod m) := congrArg Units.val hv
    have ired : f (↑(v⁻¹) : ZMod M)=(↑(u⁻¹):ZMod m) :=
      congrArg Units.val ((map_inv (ZMod.unitsMap div) v).trans (congrArg Inv.inv hv))
    change f (z+y-2*T) = _
    simp only [z,y,map_sub,map_add,map_mul,map_natCast,map_ofNat,red,ired,ZMod.inv_coe_unit]
  · refine ⟨z-y,?_⟩
    linear_combination -4*mult.symm

/-- The reverse chart normalizes j to 1 and k to an even coordinate 2b.
Every such coordinate survives square tests to arbitrary dyadic precision. -/
theorem reverse_all (N T b : ℤ) (e : ℕ) :
    IsSquare ((((1+2*T*(2*b))^2-4*N*(2*b)^2:ℤ):ZMod (2^e))) := by
  have shape : (1+2*T*(2*b))^2-4*N*(2*b)^2 =
      1+8*(T*b+2*T^2*b^2-2*N*b^2) := by ring
  rw [shape]
  exact PersistentLocalSurvivors.dyadic_unit_square _ _

/-- For modulus 2^(e+1) the disjoint reverse chart alone has 2^e labels.
This lower bound is independent of the product. -/
theorem reverse_count (e : ℕ) :
    ((Finset.range (2^e)).image (fun x : ℕ => 2*x)).card=2^e := by
  rw [Finset.card_image_of_injective _ (fun x y h => by omega),Finset.card_range]

/-- The full projective alphabet at modulus 2^(e+1). A disjoint sum keeps
even reverse coordinates distinct from every finite forward label. -/
noncomputable def labels (e N T : ℕ) :=
  (forward (2^(e+1)) N T).disjSum ((Finset.range (2^e)).image (fun b : ℕ => 2*b))

theorem labels_card (e N T : ℕ) :
    (labels e N T).card=(forward (2^(e+1)) N T).card+2^e := by
  rw [labels, Finset.card_disjSum,reverse_count]

theorem labels_ge_half (e N T : ℕ) : 2^e≤(labels e N T).card := by rw [labels_card];omega

/-- Two Newton iterations starting at x give an inverse of any odd x through
nine bits. Finite examples check the multiplicative identity before use. -/
private def inverse9 {m : ℕ} (x : ZMod m) : ZMod m :=
  let y := x*(2-x*x)
  y*(2-x*y)

private noncomputable def table (m : ℕ) [NeZero m] (N T : ZMod m) : Finset (ZMod m) :=
  ((Finset.univ : Finset (ZMod m)).filter (fun x => x.val.Coprime m)).image
    (fun x => x+N*inverse9 x-2*T)

private theorem table_exact {m : ℕ} [NeZero m] (N T : ZMod m)
    (check : ∀ x : ZMod m, x.val.Coprime m → x*inverse9 x=1) : forward m N T=table m N T := by
  apply Finset.image_congr
  intro x mem
  have cop := (Finset.mem_filter.mp mem).2
  have xu : IsUnit x := by
    simpa only [ZMod.natCast_zmod_val] using (ZMod.isUnit_iff_coprime x.val m).mpr cop
  have eq : x⁻¹=inverse9 x := left_inv_eq_right_inv (ZMod.inv_mul_of_unit x xu) (check x cop)
  dsimp only
  rw [eq]

set_option maxRecDepth 4000 in
/-- The two selected full-size fixtures' forward masks, expressed using
only the required low digits of N and its integer square root. -/
theorem example_masks : forward 8 7 5 = {6} ∧
    forward 512 1 166 =
      {6,98,114,134,178,182,226,246,262,354,390,434,438,482} := by
  rw [table_exact (7:ZMod 8) 5 (by decide +kernel),
      table_exact (1:ZMod 512) 166 (by decide +kernel)]
  decide +kernel

end PrimeFactors.OffsetDyadicSlopes
