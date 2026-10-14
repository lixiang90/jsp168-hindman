import Mathlib.Algebra.Lie.Subalgebra

/-! Pointwise Lie structures on actual arrays. These are explicit local
structures, so they cannot change any existing native Lie instance. -/
namespace Hindman168

@[reducible]
def pointwiseLieRing (V L : Type*) [LieRing L] : LieRing (V → L) where
  bracket x y v := ⁅x v,y v⁆
  add_lie x y z := by funext v; exact add_lie (x v) (y v) (z v)
  lie_add x y z := by funext v; exact lie_add (x v) (y v) (z v)
  lie_self x := by funext v; exact lie_self (x v)
  leibniz_lie x y z := by funext v; exact leibniz_lie (x v) (y v) (z v)

attribute [local instance] pointwiseLieRing

@[reducible]
def pointwiseLieAlgebra (R V L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L] :
    LieAlgebra R (V → L) where
  toModule := inferInstance
  lie_smul r x y := by funext v; exact lie_smul r (x v) (y v)

attribute [local instance] pointwiseLieAlgebra

noncomputable def pointwiseLieEvaluation (R V L : Type*) [CommRing R]
    [LieRing L] [LieAlgebra R L] (v : V) : (V → L) →ₗ⁅R⁆ L where
  toFun x := x v
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_lie' := rfl

end Hindman168
