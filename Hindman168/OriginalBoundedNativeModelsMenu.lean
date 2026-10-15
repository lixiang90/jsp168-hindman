import Hindman168.OriginalBoundedNativeModelsFiltered
import Hindman168.OriginalBoundedNativeModelsMetric

/-! A finite menu of genuine geometric models fixed before the niltest.
Every menu entry is an actual rational filtered model, its canonical grid
cover, and its real native nilmanifold with the original quotient metric.
The finiteness proof is explicit bounded-coordinate enumeration; matching
codes are connected to the models by proved geometric transport. -/

namespace Hindman168.OriginalBoundedNativeModels

open Module OAI.Erdos3
open scoped TensorProduct NNReal

/-- Universe-zero geometric data, as used by the original inverse endpoint. -/
structure RationalGeometry (s : ℕ) where
  L : Type
  [lieRing : LieRing L]
  [lieAlgebra : LieAlgebra ℚ L]
  dim : ℕ
  model : RationalFilteredNilmanifold L s dim
  [realTopology : TopologicalSpace (ℝ ⊗[ℚ] L)]
  [realTopologicalAdd : IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [realContinuousSMul : ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]
  [realT2 : T2Space (ℝ ⊗[ℚ] L)]

attribute [instance] RationalGeometry.lieRing RationalGeometry.lieAlgebra
  RationalGeometry.realTopology RationalGeometry.realTopologicalAdd
  RationalGeometry.realContinuousSMul RationalGeometry.realT2

noncomputable def representedCodes (s : ℕ) (p : ℝ) : Finset (RationalModelCode s) := by
  classical
  exact (boundedRationalModelCodes s ⌈p⌉₊ ⌈Real.exp p⌉₊ ⌈Real.exp p⌉₊).filter
    (fun c => ∃ A : RationalGeometry s, filteredGeometryCode A.model = c)

abbrev MenuIndex (s : ℕ) (p : ℝ) := {c // c ∈ representedCodes s p}

noncomputable def representative (s : ℕ) (p : ℝ) (i : MenuIndex s p) :
    RationalGeometry s := by
  classical
  exact Classical.choose (Finset.mem_filter.mp i.property).2

theorem representative_code (s : ℕ) (p : ℝ) (i : MenuIndex s p) :
    filteredGeometryCode (representative s p i).model = i.val := by
  classical
  exact Classical.choose_spec (Finset.mem_filter.mp i.property).2

/-- The menu's lattice is the constructed cover lattice, so every original
lattice with its code receives an actual quotient map from this model. -/
noncomputable def menuModel (s : ℕ) (p : ℝ) (i : MenuIndex s p) :
    RationalFilteredNilmanifold (representative s p i).L s (representative s p i).dim :=
  gridCover (representative s p i).model

noncomputable def menuNativeModel (s : ℕ) (p : ℝ) (i : MenuIndex s p) :
    NativeNilmanifoldData.{0} s := nativeModel (menuModel s p i)

noncomputable def menuLipschitzBound (s : ℕ) (p : ℝ) (i : MenuIndex s p) : ℝ≥0 :=
  Real.toNNReal (Real.exp p) *
    coordinateLipschitzBound (representative s p i).dim (representative s p i).dim 1

section Coverage

variable {L M : Type} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
  {s d e : ℕ} (D : RationalFilteredNilmanifold L s d)
  (E : RationalFilteredNilmanifold M s e) {σ : Type*} {w : σ → ℕ}

theorem exists_transport_of_code_eq
    (h : filteredGeometryCode D = filteredGeometryCode E) (T : D.Niltest w) :
    ∃ U : (gridCover E).Niltest w,
      U.normBound = T.normBound ∧
      U.lipBound = T.lipBound * coordinateLipschitzBound e e 1 ∧
      ∀ x : σ → ℤ, U.eval x = T.eval x := by
  have hdim : d = e := congrArg Sigma.fst h
  subst e
  have hpair : (D.grid, D.rationalModelCoordinates) = (E.grid, E.rationalModelCoordinates) :=
    eq_of_heq (Sigma.mk.inj_iff.mp h).2
  have hgrid := congrArg Prod.fst hpair
  have hcoords := congrArg Prod.snd hpair
  exact ⟨transportNiltest D E hcoords hgrid T, rfl, rfl,
    transportNiltest_eval D E hcoords hgrid T⟩

omit [LieRing M] [LieAlgebra ℚ M]
  [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)] in
theorem code_mem_representedCodes {p : ℝ} (hp : 0 ≤ p) (hD : D.GeometryComplexityLE p) :
    filteredGeometryCode D ∈ representedCodes s p := by
  classical
  apply Finset.mem_filter.mpr
  exact ⟨filteredGeometryCode_mem D hp hD,
    ⟨{ L := L, dim := d, model := D }, rfl⟩⟩

omit [LieRing M] [LieAlgebra ℚ M]
  [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)] in
theorem menuIndex_nonempty_of_model {p : ℝ} (hp : 0 ≤ p) (hD : D.GeometryComplexityLE p) :
    Nonempty (MenuIndex s p) :=
  ⟨⟨filteredGeometryCode D, code_mem_representedCodes D hp hD⟩⟩

omit [LieRing M] [LieAlgebra ℚ M]
  [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)] in
/-- Uniform finite-model normalization of the actual upstream niltest.
The index type, genuine native spaces, and all Lipschitz bounds depend only
on `s,p`; polynomial coefficients, interval length and the test input occur
only after these have been fixed. -/
theorem exists_menu_niltest {p : ℝ} (hp : 0 ≤ p) (T : D.Niltest w)
    (hT : T.ComplexityLE p) :
    ∃ i : MenuIndex s p, ∃ U : (menuModel s p i).Niltest w,
      U.normBound = T.normBound ∧ U.lipBound ≤ menuLipschitzBound s p i ∧
      ∀ x : σ → ℤ, U.eval x = T.eval x := by
  let i : MenuIndex s p :=
    ⟨filteredGeometryCode D, code_mem_representedCodes D hp hT.1⟩
  have hcode : filteredGeometryCode D =
      filteredGeometryCode (representative s p i).model := (representative_code s p i).symm
  obtain ⟨U, hn, hl, heval⟩ := exists_transport_of_code_eq D
    (representative s p i).model hcode T
  refine ⟨i, U, hn, ?_, heval⟩
  rw [hl]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply NNReal.coe_le_coe.mp
  rw [Real.coe_toNNReal _ (Real.exp_pos p).le]
  have hbudget := RationalFilteredNilmanifold.Niltest.observable_budget hT
  have hn0 := T.normBound.coe_nonneg
  linarith


omit [LieRing M] [LieAlgebra ℚ M]
  [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)] in
/-- The finite rational-model result on the actual native quotient, with
its chosen compatible metric and a continuous Lipschitz observable. -/
theorem exists_menu_native_observable {p : ℝ} (hp : 0 ≤ p) (T : D.Niltest w)
    (hT : T.ComplexityLE p) :
    ∃ i : MenuIndex s p, ∃ U : (menuModel s p i).Niltest w,
      letI := (menuNativeModel s p i).metric
      ∃ obs : C((menuNativeModel s p i).G ⧸ (menuNativeModel s p i).Γ, ℂ),
        (∀ z, ‖obs z‖ ≤ T.normBound) ∧ LipschitzWith (menuLipschitzBound s p i) obs ∧
        ∀ x : σ → ℤ, obs (QuotientGroup.mk
          ((menuModel s p i).filtration.realification.polynomialOrbitEval w x U.orbit)) =
            T.eval x := by
  obtain ⟨i, U, hn, hl, heval⟩ := exists_menu_niltest D hp T hT
  refine ⟨i, U, ?_⟩
  letI := (menuModel s p i).metricSpace
  let obs : C((menuModel s p i).Space, ℂ) := ⟨U.observable, U.lipschitz.continuous⟩
  refine ⟨obs, ?_, U.lipschitz.weaken hl, heval⟩
  intro z
  exact (U.norm_le z).trans_eq (congrArg ((↑) : ℝ≥0 → ℝ) hn)

end Coverage

end Hindman168.OriginalBoundedNativeModels
