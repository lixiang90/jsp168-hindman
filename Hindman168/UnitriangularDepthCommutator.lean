import Hindman168.UnitriangularMatrixDepth
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Tactic.NoncommRing

/-! The actual group commutator of depth k and depth l lies at depth k+l.
The proof uses the exact noncommutative matrix difference identity and actual
matrix unit inverses. No normality or filtration law is assumed. -/

namespace Hindman168
open Matrix
open scoped commutatorElement

variable {n : ℕ} {R : Type*} [CommRing R]

 theorem unitriangular_commutator_delta (u v : Unitriangular n R) :
    unitriangularDelta ⁅u, v⁆ =
      (unitriangularDelta u * unitriangularDelta v -
        unitriangularDelta v * unitriangularDelta u) *
      (↑u.val⁻¹ : Matrix (Fin n) (Fin n) R) *
      (↑v.val⁻¹ : Matrix (Fin n) (Fin n) R) := by
  let A : Matrix (Fin n) (Fin n) R := u.val
  let B : Matrix (Fin n) (Fin n) R := v.val
  let A' : Matrix (Fin n) (Fin n) R := ↑u.val⁻¹
  let B' : Matrix (Fin n) (Fin n) R := ↑v.val⁻¹
  have hA : A * A' = 1 := u.val.val_inv
  have hB : B * B' = 1 := v.val.val_inv
  change A * B * A' * B' - 1 = ((A - 1) * (B - 1) - (B - 1) * (A - 1)) * A' * B'
  calc
    A * B * A' * B' - 1 = (A * B - B * A) * A' * B' := by
      rw [sub_mul, sub_mul]
      simp only [mul_assoc, hA, mul_one, hB]
    _ = _ := by
      apply congrArg (fun M : Matrix (Fin n) (Fin n) R => M * A' * B')
      noncomm_ring

 theorem UnitriangularDepth.commutator {k l : ℕ} {u v : Unitriangular n R}
    (hu : UnitriangularDepth k u) (hv : UnitriangularDepth l v) :
    UnitriangularDepth (k + l) ⁅u, v⁆ := by
  apply (unitriangularDepth_iff_delta (k + l) _).mpr
  rw [unitriangular_commutator_delta]
  have hA := (unitriangularDepth_iff_delta k u).mp hu
  have hB := (unitriangularDepth_iff_delta l v).mp hv
  have hd : MatrixDepth (k + l)
      (unitriangularDelta u * unitriangularDelta v -
        unitriangularDelta v * unitriangularDelta u) := by
    apply (hA.mul hB).sub
    simpa only [Nat.add_comm l k] using hB.mul hA
  have hAi : MatrixDepth 0 (↑u.val⁻¹ : Matrix (Fin n) (Fin n) R) :=
    unitriangular_matrixDepth_zero u⁻¹
  have hBi : MatrixDepth 0 (↑v.val⁻¹ : Matrix (Fin n) (Fin n) R) :=
    unitriangular_matrixDepth_zero v⁻¹
  simpa only [Nat.add_zero] using (hd.mul hAi).mul hBi

 theorem unitriangularDepth_commutator_le (k l : ℕ) :
    ⁅unitriangularDepthSubgroup n k R, unitriangularDepthSubgroup n l R⁆ ≤
      unitriangularDepthSubgroup n (k + l) R := by
  exact Subgroup.commutator_le.mpr fun u hu v hv => UnitriangularDepth.commutator hu hv

 theorem unitriangularDepth_zero_eq_top : unitriangularDepthSubgroup n 0 R = ⊤ := by
  apply eq_top_iff.mpr
  intro u _ i j hij hgap
  omega

 theorem unitriangularDepth_one_eq_top : unitriangularDepthSubgroup n 1 R = ⊤ := by
  apply eq_top_iff.mpr
  intro u _ i j hij hgap
  omega

 theorem unitriangularDepth_normal (k : ℕ) : (unitriangularDepthSubgroup n k R).Normal := by
  refine ⟨?_⟩
  intro u hu v
  have hv : v ∈ unitriangularDepthSubgroup n 0 R := by rw [unitriangularDepth_zero_eq_top]; trivial
  have hc : ⁅v, u⁆ ∈ unitriangularDepthSubgroup n k R := by
    change UnitriangularDepth k ⁅v, u⁆
    simpa only [Nat.zero_add] using UnitriangularDepth.commutator hv hu
  have hm := (unitriangularDepthSubgroup n k R).mul_mem hc hu
  simpa [commutatorElement_def, mul_assoc] using hm

end Hindman168
