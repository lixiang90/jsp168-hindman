import Hindman168.NativeNilmanifoldData
import Hindman168.NativeProductGlobalLogarithm
import Hindman168.NativeLieCenterExponential

/-! ACTUAL original diagonal-center vector subspace in the ORIGINAL
product model; its centrality and closedness are proved, not assumptions. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeDiagonalCenterInclusion {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    nativeLieCenterModel (I := D.I) (G := D.G) →ₗ[ℝ] (D.E × D.E) :=
  (nativeLieCenterModel (I := D.I) (G := D.G)).subtype.prod
    (nativeLieCenterModel (I := D.I) (G := D.G)).subtype

noncomputable def nativeDiagonalCenterModel {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    Submodule ℝ (D.E × D.E) := LinearMap.range (nativeDiagonalCenterInclusion D)

theorem native_diagonal_center_model_mem {s : ℕ} (D : NativeNilmanifoldData.{u} s) (v : D.E × D.E) :
    v ∈ nativeDiagonalCenterModel D ↔ ∃ w : nativeLieCenterModel (I := D.I) (G := D.G), v = (w.val,w.val) := by
  constructor
  · rintro ⟨w,hw⟩
    exact ⟨w,hw.symm⟩
  · rintro ⟨w,rfl⟩
    exact ⟨w,rfl⟩

theorem native_diagonal_center_model_closed {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    IsClosed ((nativeDiagonalCenterModel D) : Set (D.E × D.E)) :=
  (nativeDiagonalCenterModel D).closed_of_finiteDimensional

theorem native_diagonal_center_model_le {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    nativeDiagonalCenterModel D ≤ nativeLieCenterModel (I := D.I.prod D.I) (G := D.G × D.G) := by
  letI := nativeProductGroup_simplyConnected (I := D.I) (J := D.I) (G := D.G) (K := D.G)
  intro v hv
  obtain ⟨w,rfl⟩ := (native_diagonal_center_model_mem D v).mp hv
  apply (nativeLieExponential_mem_center_iff_mem_centerModel (I := D.I.prod D.I) (G := D.G × D.G) _).mp
  rw [nativeProductExponential_eq (I := D.I) (J := D.I) (G := D.G) (K := D.G)]
  have hz : nativeLieExponential (E := D.E) (I := D.I) (G := D.G) w.val ∈ Subgroup.center D.G :=
    (nativeLieExponential_mem_center_iff_mem_centerModel (I := D.I) (G := D.G) w.val).mpr w.property
  apply Subgroup.mem_center_iff.mpr
  intro g
  exact Prod.ext (Subgroup.mem_center_iff.mp hz g.1) (Subgroup.mem_center_iff.mp hz g.2)

end Hindman168
