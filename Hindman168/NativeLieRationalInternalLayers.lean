import Hindman168.NativeLieRationalAlgebra

/-! Internal rational lower-central layers of an actual bracket-closed
Q-subspace of the original native Lie algebra. They are the images of
its own Lie lower-central series, rather than intersections with real
ambient layers. Actual inclusion preserves brackets and proves
termination at the original group's nilpotency class. -/

namespace Hindman168
open Function Set
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G]

attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeLieRationalInternalLayer (V : Submodule ℚ E)
    (hbr : nativeLieRationalBracketClosed (I := I) (G := G) V) (j : ℕ) : Submodule ℚ E :=
  let A := nativeLieRationalSubalgebra (I := I) (G := G) V hbr
  (LieModule.lowerCentralSeries ℚ A A j).toSubmodule.map A.incl.toLinearMap

omit [BoundarylessManifold I G] [T2Space G] in
 theorem nativeLieRationalInternalLayer_mem_iff
    (V : Submodule ℚ E) (hbr : nativeLieRationalBracketClosed (I := I) (G := G) V)
    (j : ℕ) (w : E) :
    w ∈ nativeLieRationalInternalLayer (I := I) (G := G) V hbr j ↔
      ∃ x : nativeLieRationalSubalgebra (I := I) (G := G) V hbr,
        x ∈ LieModule.lowerCentralSeries ℚ
          (nativeLieRationalSubalgebra (I := I) (G := G) V hbr)
          (nativeLieRationalSubalgebra (I := I) (G := G) V hbr) j ∧ x.val = w := by
  exact Submodule.mem_map

omit [BoundarylessManifold I G] [T2Space G] in
 theorem nativeLieRationalInternalLayer_zero
    (V : Submodule ℚ E) (hbr : nativeLieRationalBracketClosed (I := I) (G := G) V) :
    nativeLieRationalInternalLayer (I := I) (G := G) V hbr 0 = V := by
  ext w
  rw [nativeLieRationalInternalLayer_mem_iff]
  constructor
  · rintro ⟨x, _, rfl⟩
    exact x.property
  · intro hw
    exact ⟨⟨w, hw⟩, LieSubmodule.mem_top _, rfl⟩

omit [BoundarylessManifold I G] [T2Space G] in
 theorem nativeLieRationalInternalLayer_antitone
    (V : Submodule ℚ E) (hbr : nativeLieRationalBracketClosed (I := I) (G := G) V) :
    Antitone (nativeLieRationalInternalLayer (I := I) (G := G) V hbr) := by
  intro j k hjk
  exact Submodule.map_mono
    (LieModule.antitone_lowerCentralSeries ℚ
      (nativeLieRationalSubalgebra (I := I) (G := G) V hbr)
      (nativeLieRationalSubalgebra (I := I) (G := G) V hbr) hjk)

omit [BoundarylessManifold I G] [T2Space G] in
 theorem nativeLieRationalInternalLayer_le
    (V : Submodule ℚ E) (hbr : nativeLieRationalBracketClosed (I := I) (G := G) V) (j : ℕ) :
    nativeLieRationalInternalLayer (I := I) (G := G) V hbr j ≤ V := by
  intro w hw
  obtain ⟨x, _, rfl⟩ := (nativeLieRationalInternalLayer_mem_iff V hbr j w).mp hw
  exact x.property

 theorem nativeLieRationalInternalLayer_differential_next
    (V : Submodule ℚ E) (hbr : nativeLieRationalBracketClosed (I := I) (G := G) V)
    (j : ℕ) {v w : E} (hv : v ∈ V)
    (hw : w ∈ nativeLieRationalInternalLayer (I := I) (G := G) V hbr j) :
    nativeLieAdjointDifferential (I := I) (G := G) v w ∈
      nativeLieRationalInternalLayer (I := I) (G := G) V hbr (j + 1) := by
  let A := nativeLieRationalSubalgebra (I := I) (G := G) V hbr
  obtain ⟨x, hx, rfl⟩ := (nativeLieRationalInternalLayer_mem_iff V hbr j w).mp hw
  let y : A := ⟨v, hv⟩
  have hl : ⁅y, x⁆ ∈ LieModule.lowerCentralSeries ℚ A A (j + 1) := by
    rw [LieModule.lowerCentralSeries_succ]
    exact LieSubmodule.lie_mem_lie (LieSubmodule.mem_top y) hx
  have he : nativeLieAdjointDifferential (I := I) (G := G) v x.val =
      (⁅y, x⁆ : A).val := by
    rw [← nativeLieAdjointGenerator_eq_differential]
    exact nativeLieAdjointGenerator_eq_native_bracket (I := I) (G := G) (y : GroupLieAlgebra I G) x
  rw [he]
  exact (nativeLieRationalInternalLayer_mem_iff V hbr (j + 1) _).mpr ⟨⁅y, x⁆, hl, rfl⟩

omit [BoundarylessManifold I G] [T2Space G] in
 theorem nativeLieRationalInternalLayer_le_ambient
    (V : Submodule ℚ E) (hbr : nativeLieRationalBracketClosed (I := I) (G := G) V) (j : ℕ) :
    nativeLieRationalInternalLayer (I := I) (G := G) V hbr j ≤
      (LieModule.lowerCentralSeries ℚ (GroupLieAlgebra I G) (GroupLieAlgebra I G) j).toSubmodule := by
  let A := nativeLieRationalSubalgebra (I := I) (G := G) V hbr
  exact lieModule_lcs_map_le (f := A.incl) (g := A.incl.toLinearMap) (fun _ _ => rfl) j

 theorem nativeLieRationalInternalLayer_nilpotencyClass_bot [Group.IsNilpotent G]
    (V : Submodule ℚ E) (hbr : nativeLieRationalBracketClosed (I := I) (G := G) V) :
    nativeLieRationalInternalLayer (I := I) (G := G) V hbr (Group.nilpotencyClass G) = ⊥ := by
  apply le_antisymm _ bot_le
  have h := nativeLieRationalInternalLayer_le_ambient (I := I) (G := G) V hbr (Group.nilpotencyClass G)
  rw [nativeLieRationalLowerCentral_nilpotencyClass_bot] at h
  exact h

end Hindman168
