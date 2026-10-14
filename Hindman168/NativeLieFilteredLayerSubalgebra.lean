import Hindman168.NativeNilmanifoldData
import Hindman168.NativeLieAdjointInfinitesimal

/-! Actual Lie model filtration layers with proved bracket weights are
native Lie subalgebras. An exact Log membership proof identifies their
exponential subgroups with the actual original group layers. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeLieFilteredLayerSubalgebra {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : ℕ → Submodule ℝ D.E) (hF : Antitone F)
    (hB : ∀ i j v w, v ∈ F i → w ∈ F j →
      nativeLieAdjointDifferential (I := D.I) (G := D.G) v w ∈ F (i+j)) (i : ℕ) :
    LieSubalgebra ℝ (GroupLieAlgebra D.I D.G) where
  toSubmodule := F i
  lie_mem' := by
    intro v w hv hw
    have hm := hF (Nat.le_add_right i i) (hB i i v w hv hw)
    have he : nativeLieAdjointDifferential (I := D.I) (G := D.G) v w =
        (⁅v,w⁆ : GroupLieAlgebra D.I D.G) := by
      rw [← nativeLieAdjointGenerator_eq_differential]
      exact nativeLieAdjointGenerator_eq_native_bracket (I := D.I) (G := D.G) v w
    exact he ▸ hm

theorem native_lie_filtered_layer_subalgebra_model {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : ℕ → Submodule ℝ D.E) (hF : Antitone F)
    (hB : ∀ i j v w, v ∈ F i → w ∈ F j →
      nativeLieAdjointDifferential (I := D.I) (G := D.G) v w ∈ F (i+j)) (i : ℕ) :
    nativeLieSubalgebraModel (nativeLieFilteredLayerSubalgebra D F hF hB i) = F i := rfl

theorem native_lie_filtered_layer_subgroup_eq {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : ℕ → Submodule ℝ D.E) (hF : Antitone F)
    (hB : ∀ i j v w, v ∈ F i → w ∈ F j →
      nativeLieAdjointDifferential (I := D.I) (G := D.G) v w ∈ F (i+j))
    (L : ℕ → Subgroup D.G)
    (hLog : ∀ i g, g ∈ L i ↔ nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) g ∈ F i)
    (i : ℕ) : nativeLieSubalgebraSubgroup (nativeLieFilteredLayerSubalgebra D F hF hB i) = L i := by
  ext g
  rw [nativeLieSubalgebraSubgroup_mem_globalLogarithm_iff,native_lie_filtered_layer_subalgebra_model]
  exact (hLog i g).symm

end Hindman168
