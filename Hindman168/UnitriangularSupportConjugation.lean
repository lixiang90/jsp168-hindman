import Hindman168.UnitriangularRationalSupportSlices

/-! Actual conjugation preserves each admissible support slice. The
conjugation difference is proved to have one greater depth by expanding
(g-1)Yg⁻¹ + Y(g⁻¹-1). No normality of the original integer lattice or
independent coordinate periodicity is assumed. -/

noncomputable section
namespace Hindman168
open Matrix Set

variable {n : ℕ} {R : Type*} [CommRing R]
local instance supportConjugationMatrixLieRing : LieRing (Matrix (Fin n) (Fin n) R) :=
  LieRing.ofAssociativeRing

 theorem unitriangularDelta_depth_one (g : Unitriangular n R) :
    MatrixDepth 1 (unitriangularDelta g) := by
  apply (unitriangularDepth_iff_delta 1 g).mp
  intro i j hij hgap
  omega

 theorem MatrixDepth.unitriangular_conjugate_difference
    {k : ℕ} {Y : Matrix (Fin n) (Fin n) R} (hY : MatrixDepth k Y)
    (g : Unitriangular n R) :
    MatrixDepth (k + 1) (unitriangularConjugationRingHom g Y - Y) := by
  have hg := unitriangularDelta_depth_one g
  have hgi := unitriangularDelta_depth_one g⁻¹
  have h0 : MatrixDepth 0 (↑g.val⁻¹ : Matrix (Fin n) (Fin n) R) :=
    unitriangular_matrixDepth_zero g⁻¹
  have hleft : MatrixDepth (k + 1)
      (unitriangularDelta g * Y * (↑g.val⁻¹ : Matrix (Fin n) (Fin n) R)) := by
    simpa only [Nat.add_comm 1 k, Nat.add_zero] using (hg.mul hY).mul h0
  have hright := hY.mul hgi
  have heq : unitriangularConjugationRingHom g Y - Y =
      unitriangularDelta g * Y * (↑g.val⁻¹ : Matrix (Fin n) (Fin n) R) +
        Y * unitriangularDelta g⁻¹ := by
    change (g.val : Matrix (Fin n) (Fin n) R) * Y *
        (↑g.val⁻¹ : Matrix (Fin n) (Fin n) R) - Y =
      ((g.val : Matrix (Fin n) (Fin n) R) - 1) * Y *
        (↑g.val⁻¹ : Matrix (Fin n) (Fin n) R) +
      Y * ((↑g.val⁻¹ : Matrix (Fin n) (Fin n) R) - 1)
    noncomm_ring
  rw [heq]
  exact hleft.add hright

 theorem matrixSupportSlice_conjugation_mem (k : ℕ) (hk : 1 ≤ k)
    (p : Fin n → Fin n → Prop) (hp : ∀ i j, p i j → j.val < i.val + k + 1)
    (g : Unitriangular n R) {Y : Matrix (Fin n) (Fin n) R}
    (hY : Y ∈ matrixSupportSliceLieSubalgebra n k R hk p hp) :
    unitriangularConjugationRingHom g Y ∈ matrixSupportSliceLieSubalgebra n k R hk p hp := by
  have hd := MatrixDepth.unitriangular_conjugate_difference hY.1 g
  refine ⟨MatrixDepth.unitriangular_conjugate hY.1 g, ?_⟩
  intro i j hij
  have he := hd i j (hp i j hij)
  change unitriangularConjugationRingHom g Y i j - Y i j = 0 at he
  rw [hY.2 i j hij, sub_zero] at he
  exact he

 theorem matrixSupportSlice_conjugation_iff (k : ℕ) (hk : 1 ≤ k)
    (p : Fin n → Fin n → Prop) (hp : ∀ i j, p i j → j.val < i.val + k + 1)
    (g : Unitriangular n R) (Y : Matrix (Fin n) (Fin n) R) :
    unitriangularConjugationRingHom g Y ∈ matrixSupportSliceLieSubalgebra n k R hk p hp ↔
      Y ∈ matrixSupportSliceLieSubalgebra n k R hk p hp := by
  constructor
  · intro hY
    have hi := matrixSupportSlice_conjugation_mem k hk p hp g⁻¹ hY
    rw [unitriangularConjugationRingHom_inv_cancel] at hi
    exact hi
  · exact matrixSupportSlice_conjugation_mem k hk p hp g

 variable [Algebra ℚ R]

 theorem unitriangularSupportSliceSubgroup_normal (k : ℕ) (hk : 1 ≤ k)
    (p : Fin n → Fin n → Prop) (hp : ∀ i j, p i j → j.val < i.val + k + 1) :
    (unitriangularLieSubgroup (matrixSupportSliceLieSubalgebra n k R hk p hp)
      (matrixSupportSlice_le_strict k hk p hp)).Normal := by
  refine ⟨?_⟩
  intro u hu g
  change (unitriangularLogarithm (g * u * g⁻¹)).val ∈
    matrixSupportSliceLieSubalgebra n k R hk p hp
  rw [unitriangularLogarithm_conjugation]
  exact matrixSupportSlice_conjugation_mem k hk p hp g hu

 theorem unitriangularLieSubgroup_inf_supportSlice
    (V : LieSubalgebra R (Matrix (Fin n) (Fin n) R))
    (hV : V ≤ strictUpperTriangularLieSubalgebra n R) (k : ℕ) (hk : 1 ≤ k)
    (p : Fin n → Fin n → Prop) (hp : ∀ i j, p i j → j.val < i.val + k + 1) :
    unitriangularLieSubgroup (V ⊓ matrixSupportSliceLieSubalgebra n k R hk p hp)
      (inf_le_left.trans hV) =
    unitriangularLieSubgroup V hV ⊓
      unitriangularLieSubgroup (matrixSupportSliceLieSubalgebra n k R hk p hp)
        (matrixSupportSlice_le_strict k hk p hp) := by
  ext g
  rfl

 theorem unitriangularSupportSlice_inf_conjugation_mem
    (V : LieSubalgebra R (Matrix (Fin n) (Fin n) R))
    (hV : V ≤ strictUpperTriangularLieSubalgebra n R) (k : ℕ) (hk : 1 ≤ k)
    (p : Fin n → Fin n → Prop) (hp : ∀ i j, p i j → j.val < i.val + k + 1)
    {g u : Unitriangular n R} (hg : g ∈ unitriangularLieSubgroup V hV)
    (hu : u ∈ unitriangularLieSubgroup (V ⊓ matrixSupportSliceLieSubalgebra n k R hk p hp)
      (inf_le_left.trans hV)) :
    g * u * g⁻¹ ∈ unitriangularLieSubgroup
      (V ⊓ matrixSupportSliceLieSubalgebra n k R hk p hp) (inf_le_left.trans hV) := by
  rw [unitriangularLieSubgroup_inf_supportSlice V hV k hk p hp] at hu ⊢
  refine ⟨(unitriangularLieSubgroup V hV).mul_mem
    ((unitriangularLieSubgroup V hV).mul_mem hg hu.1)
    ((unitriangularLieSubgroup V hV).inv_mem hg), ?_⟩
  have hn := unitriangularSupportSliceSubgroup_normal k hk p hp (R := R)
  exact hn.conj_mem u hu.2 g

end Hindman168
