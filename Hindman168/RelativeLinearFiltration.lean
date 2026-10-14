import Hindman168.RelativeLieSubalgebra
import Mathlib.Analysis.Normed.Operator.Bilinear

/-! ACTUAL relative Lie-model layers: both coordinates in Fi and their
difference in Fi+1. Original filtered bilinearity gives the genuine
cross-layer bracket condition, including the extra difference layer. -/

namespace Hindman168
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def relativeLinearFiltration (F : ℕ → Submodule ℝ E) (i : ℕ) : Submodule ℝ (E × E) :=
  relativeLinearModel (F i) (F (i+1))

theorem relative_linear_filtration_antitone (F : ℕ → Submodule ℝ E) (hF : Antitone F) :
    Antitone (relativeLinearFiltration F) := by
  intro i j hij v hv
  obtain ⟨h1,h2,hd⟩ := (relative_linear_model_mem_iff _ _ v).mp hv
  exact (relative_linear_model_mem_iff _ _ v).mpr
    ⟨hF hij h1,hF hij h2,hF (Nat.add_le_add_right hij 1) hd⟩

theorem relative_linear_filtration_zero (F : ℕ → Submodule ℝ E)
    (h0 : F 0 = ⊤) (h1 : F 1 = ⊤) : relativeLinearFiltration F 0 = ⊤ := by
  ext v
  change v ∈ relativeLinearModel (F 0) (F 1) ↔ v ∈ (⊤ : Submodule ℝ (E × E))
  rw [relative_linear_model_mem_iff,h0,h1]
  simp only [Submodule.mem_top,and_self]

theorem relative_linear_filtration_bilinear (F : ℕ → Submodule ℝ E)
    (B : E →L[ℝ] (E →L[ℝ] E))
    (hB : ∀ i j v w, v ∈ F i → w ∈ F j → B v w ∈ F (i+j))
    {i j : ℕ} {v w : E × E}
    (hv : v ∈ relativeLinearFiltration F i) (hw : w ∈ relativeLinearFiltration F j) :
    (B v.1 w.1,B v.2 w.2) ∈ relativeLinearFiltration F (i+j) := by
  obtain ⟨hv1,hv2,hvd⟩ := (relative_linear_model_mem_iff _ _ v).mp hv
  obtain ⟨hw1,hw2,hwd⟩ := (relative_linear_model_mem_iff _ _ w).mp hw
  apply (relative_linear_model_mem_iff _ _ _).mpr
  refine ⟨hB i j _ _ hv1 hw1,hB i j _ _ hv2 hw2,?_⟩
  have he : B v.1 w.1-B v.2 w.2 = B (v.1-v.2) w.1+B v.2 (w.1-w.2) := by
    simp only [map_sub,sub_apply]
    abel
  rw [he]
  exact (F (i+j+1)).add_mem
    (by simpa only [Nat.add_assoc,Nat.add_comm 1 j] using hB (i+1) j _ _ hvd hw1)
    (by simpa only [Nat.add_assoc] using hB i (j+1) _ _ hv2 hwd)

end Hindman168
