import Hindman168.RoughStretchedFiltrationIndices
import Hindman168.NativeLieLowerCentralModel
import Hindman168.AlignmentLieLowerCentralBrackets

namespace Hindman168
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G]

attribute [local instance] lieGroup_smooth_min_three

noncomputable def roughNativeStretchedLieFiltration (D i : ℕ) : Submodule ℝ E :=
  nativeLieLowerCentralModel (I := I) (G := G) ((i ⌈/⌉ D)-1)

omit [BoundarylessManifold I G] [T2Space G] in
theorem rough_native_stretched_lie_antitone (D : ℕ) (hD : 0 < D) :
    Antitone (roughNativeStretchedLieFiltration (I := I) (G := G) D) := by
  intro i j hij
  exact nativeLieLowerCentralModel_antitone
    (Nat.sub_le_sub_right (rough_ceiling_index_monotone D hD hij) 1)

omit [BoundarylessManifold I G] [T2Space G] in
theorem rough_native_stretched_lie_initial (D : ℕ) (hD : 0 < D)
    (i : ℕ) (hi : i ≤ D) : roughNativeStretchedLieFiltration (I := I) (G := G) D i = ⊤ := by
  have h := rough_ceiling_index_initial D hD i hi
  have he : (i ⌈/⌉ D)-1 = 0 := by omega
  rw [roughNativeStretchedLieFiltration, he, nativeLieLowerCentralModel_zero]

theorem rough_native_stretched_lie_bracket (D : ℕ) (hD : 0 < D) {i j : ℕ} {v w : E}
    (hv : v ∈ roughNativeStretchedLieFiltration (I := I) (G := G) D i)
    (hw : w ∈ roughNativeStretchedLieFiltration (I := I) (G := G) D j) :
    nativeLieAdjointDifferential (I := I) (G := G) v w ∈
      roughNativeStretchedLieFiltration (I := I) (G := G) D (i+j) := by
  let x : GroupLieAlgebra I G := v
  let y : GroupLieAlgebra I G := w
  have hb := alignmentLie_weighted_lowerCentral_bracket
    (R := ℝ) (L := GroupLieAlgebra I G) (x := x) (y := y) hv hw
  have hle := Nat.sub_le_sub_right (rough_ceiling_index_add D hD i j) 1
  have hmem := LieModule.antitone_lowerCentralSeries ℝ
    (GroupLieAlgebra I G) (GroupLieAlgebra I G) hle hb
  rw [← nativeLieAdjointGenerator_eq_differential]
  exact (nativeLieAdjointGenerator_eq_native_bracket (I := I) (G := G) x y).symm ▸ hmem

end Hindman168
