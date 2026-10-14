import Hindman168.NilpotentAdjoint
import Hindman168.UnitriangularLieAlgebra

/-! The actual adjoint on strictly upper-triangular matrices raises support
at every iterate. This gives a uniform finite Hadamard formula, with no
supplied nilpotency bound or BCH assumption. -/

namespace Hindman168
open Matrix Module

variable {n : ℕ} {R : Type*} [CommRing R] [Algebra ℚ R]
local instance adjointCutoffMatrixLieRing : LieRing (Matrix (Fin n) (Fin n) R) :=
  LieRing.ofAssociativeRing

 def unitriangularAdjointQ (X : StrictUpperTriangular n R) : End ℚ (StrictUpperTriangular n R) where
  toFun Y := ⟨commutatorEndQ X.val Y.val,
    (X.property.lie Y.property).antitone (by omega)⟩
  map_add' Y Z := Subtype.ext ((commutatorEndQ X.val).map_add Y.val Z.val)
  map_smul' c Y := Subtype.ext ((commutatorEndQ X.val).map_smul c Y.val)

 theorem unitriangularAdjointQ_apply_value (X Y : StrictUpperTriangular n R) :
    (unitriangularAdjointQ X Y).val = X.val * Y.val - Y.val * X.val := rfl

 theorem unitriangularAdjointQ_pow_value (X Y : StrictUpperTriangular n R) (m : ℕ) :
    ((unitriangularAdjointQ X ^ m) Y).val = (commutatorEndQ X.val ^ m) Y.val := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [pow_succ', pow_succ']
    change commutatorEndQ X.val (((unitriangularAdjointQ X ^ m) Y).val) =
      commutatorEndQ X.val ((commutatorEndQ X.val ^ m) Y.val)
    rw [ih]

 theorem unitriangularAdjointQ_pow_depth (X Y : StrictUpperTriangular n R)
    {k : ℕ} (hY : MatrixDepth k Y.val) (m : ℕ) :
    MatrixDepth (k + m) ((unitriangularAdjointQ X ^ m) Y).val := by
  induction m with
  | zero => simpa only [pow_zero, Module.End.one_apply, Nat.add_zero] using hY
  | succ m ih =>
    rw [pow_succ']
    have hd := X.property.lie ih
    change MatrixDepth (1 + (k + m))
      (X.val * ((unitriangularAdjointQ X ^ m) Y).val -
        ((unitriangularAdjointQ X ^ m) Y).val * X.val) at hd
    change MatrixDepth (k + (m + 1))
      (X.val * ((unitriangularAdjointQ X ^ m) Y).val -
        ((unitriangularAdjointQ X ^ m) Y).val * X.val)
    convert hd using 1; omega

 theorem unitriangularAdjointQ_pow_eq_zero (X : StrictUpperTriangular n R) :
    unitriangularAdjointQ X ^ (n - 1) = 0 := by
  apply LinearMap.ext
  intro Y
  apply Subtype.ext
  exact (unitriangularAdjointQ_pow_depth X Y Y.property (n - 1)).eq_zero (by omega)

 theorem unitriangularAdjointQ_nilpotent (X : StrictUpperTriangular n R) :
    IsNilpotent (unitriangularAdjointQ X) := ⟨n - 1, unitriangularAdjointQ_pow_eq_zero X⟩

 theorem unitriangularAdjointQ_exp_value (X Y : StrictUpperTriangular n R) :
    (IsNilpotent.exp (unitriangularAdjointQ X) Y).val =
      IsNilpotent.exp X.val * Y.val * IsNilpotent.exp (-X.val) := by
  have hN := commutatorEndQ_nilpotent X.property.nilpotent
  obtain ⟨m, hm⟩ := hN
  have hA : unitriangularAdjointQ X ^ m = 0 := by
    apply LinearMap.ext
    intro Z
    apply Subtype.ext
    rw [unitriangularAdjointQ_pow_value, hm]
    rfl
  rw [IsNilpotent.exp_eq_sum hA, ← exp_commutatorEndQ_apply X.property.nilpotent,
    IsNilpotent.exp_eq_sum hm]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply]
  rw [Submodule.coe_sum]
  apply Finset.sum_congr rfl
  intro i _
  change (i.factorial : ℚ)⁻¹ • ((unitriangularAdjointQ X ^ i) Y).val = _
  rw [unitriangularAdjointQ_pow_value]

 theorem unitriangular_finite_hadamard (X Y : StrictUpperTriangular n R) :
    IsNilpotent.exp X.val * Y.val * IsNilpotent.exp (-X.val) =
      ∑ i ∈ Finset.range (n - 1), (i.factorial : ℚ)⁻¹ • ((commutatorEndQ X.val ^ i) Y.val) := by
  rw [← unitriangularAdjointQ_exp_value, IsNilpotent.exp_eq_sum
    (unitriangularAdjointQ_pow_eq_zero X)]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply]
  rw [Submodule.coe_sum]
  apply Finset.sum_congr rfl
  intro i _
  change (i.factorial : ℚ)⁻¹ • ((unitriangularAdjointQ X ^ i) Y).val = _
  rw [unitriangularAdjointQ_pow_value]

end Hindman168
