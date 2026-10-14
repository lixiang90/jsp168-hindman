import Hindman168.NativeSubgroupRationalGroupLayers
import Hindman168.NativeLieRationalLayerDescent

/-! Equality of the INTERNAL rational Lie layers of W_Gamma with the
actual Q log spans of the specified original group's lower-central
subgroups. Genuine commutator leading terms give an inclusion modulo
the next layer. Actual relative normalization and terminating Lie-layer
descent remove that remainder; Gamma need not be ambient normal. -/

namespace Hindman168
open scoped Manifold ContDiff commutatorElement

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

 theorem nativeSubgroupLowerCentralSeries_pair_bracket_mod_next
    (Γ : Subgroup G) (j : ℕ) {g h : G}
    (hg : g ∈ Γ) (hh : h ∈ Γ.lowerCentralSeries j) :
    nativeLieAdjointDifferential (I := I) (G := G)
      (nativeLieGlobalLogarithm (E := E) (I := I) (G := G) g)
      (nativeLieGlobalLogarithm (E := E) (I := I) (G := G) h) ∈
      nativeSubgroupRationalLogSpan (E := E) (I := I) (Γ.lowerCentralSeries (j + 1)) ⊔
        nativeSubgroupRationalInternalLayer (E := E) (I := I) Γ (j + 2) := by
  let V := nativeSubgroupRationalLogSpan (E := E) (I := I) Γ
  let hbr := nativeSubgroupRationalLogSpan_bracket_closed (E := E) (I := I) Γ
  have hv := nativeSubgroup_logarithm_mem_span (E := E) (I := I) Γ hg
  have hw := nativeSubgroupLowerCentralSeries_log_mem_internal (E := E) (I := I) Γ j hh
  have he := nativeLieGlobalLogarithm_commutator_leading_internal V hbr hv j hw
  rw [nativeLieExponential_globalLogarithm, nativeLieExponential_globalLogarithm] at he
  have hc : ⁅g, h⁆ ∈ Γ.lowerCentralSeries (j + 1) := by
    rw [Subgroup.lowerCentralSeries_succ, Subgroup.commutator_comm]
    exact Subgroup.commutator_mem_commutator hg hh
  have hm := (nativeSubgroupRationalLogSpan (E := E) (I := I) (Γ.lowerCentralSeries (j + 1)) ⊔
    nativeSubgroupRationalInternalLayer (E := E) (I := I) Γ (j + 2)).sub_mem
    (Submodule.mem_sup_left (nativeSubgroup_logarithm_mem_span (E := E) (I := I) _ hc))
    (Submodule.mem_sup_right he)
  convert hm using 1
  abel

 theorem nativeSubgroupLowerCentralSeries_differential_spans_mod_next
    (Γ : Subgroup G) (j : ℕ) {v w : E}
    (hv : v ∈ nativeSubgroupRationalLogSpan (E := E) (I := I) Γ)
    (hw : w ∈ nativeSubgroupRationalLogSpan (E := E) (I := I) (Γ.lowerCentralSeries j)) :
    nativeLieAdjointDifferential (I := I) (G := G) v w ∈
      nativeSubgroupRationalLogSpan (E := E) (I := I) (Γ.lowerCentralSeries (j + 1)) ⊔
        nativeSubgroupRationalInternalLayer (E := E) (I := I) Γ (j + 2) := by
  let V := nativeSubgroupRationalLogSpan (E := E) (I := I) Γ
  let F := nativeSubgroupRationalLogSpan (E := E) (I := I) (Γ.lowerCentralSeries j)
  let N := nativeSubgroupRationalLogSpan (E := E) (I := I) (Γ.lowerCentralSeries (j + 1)) ⊔
    nativeSubgroupRationalInternalLayer (E := E) (I := I) Γ (j + 2)
  let B := nativeLieAdjointDifferential (I := I) (G := G)
  have hsecond : ∀ g ∈ Γ, ∀ y ∈ F,
      B (nativeLieGlobalLogarithm (E := E) (I := I) (G := G) g) y ∈ N := by
    intro g hg y hy
    let A : E →ₗ[ℚ] E := (B (nativeLieGlobalLogarithm (E := E) (I := I) (G := G) g)).toLinearMap.restrictScalars ℚ
    have hf : F ≤ N.comap A := by
      apply Submodule.span_le.mpr
      rintro z ⟨h, hh, rfl⟩
      exact nativeSubgroupLowerCentralSeries_pair_bracket_mod_next (E := E) (I := I) Γ j hg hh
    exact hf hy
  let A : E →ₗ[ℚ] E := (B.flip w).toLinearMap.restrictScalars ℚ
  have hvn : V ≤ N.comap A := by
    apply Submodule.span_le.mpr
    rintro z ⟨g, hg, rfl⟩
    exact hsecond g hg w hw
  exact hvn hv

 theorem nativeSubgroupLowerCentralSeries_rationalSpan_eq_internal
    (Γ : Subgroup G) (j : ℕ) :
    nativeSubgroupRationalLogSpan (E := E) (I := I) (Γ.lowerCentralSeries j) =
      nativeSubgroupRationalInternalLayer (E := E) (I := I) Γ j := by
  let V := nativeSubgroupRationalLogSpan (E := E) (I := I) Γ
  let hbr := nativeSubgroupRationalLogSpan_bracket_closed (E := E) (I := I) Γ
  induction j with
  | zero =>
    rw [Subgroup.lowerCentralSeries_zero, nativeSubgroupRationalInternalLayer_zero]
  | succ j ih =>
    apply le_antisymm (nativeSubgroupLowerCentralSeries_rationalSpan_le_internal Γ (j + 1))
    let N := nativeSubgroupRationalLogSpan (E := E) (I := I) (Γ.lowerCentralSeries (j + 1))
    have hconj : ∀ g ∈ Γ, ∀ h ∈ Γ.lowerCentralSeries (j + 1), g * h * g⁻¹ ∈ Γ.lowerCentralSeries (j + 1) := by
      intro g hg h hh
      exact ((Subgroup.mem_normalizer_iff.mp
        (Γ.self_le_normalizer_lowerCentralSeries (j + 1) hg)) h).mp hh
    apply nativeLieRationalInternalLayer_absorb_next V hbr N
      (fun _ hv _ hn => nativeSubgroupRationalLogSpan_differential_mem_of_normalized
        (E := E) (I := I) (G := G) Γ (Γ.lowerCentralSeries (j + 1)) hconj hv hn) (j + 1)
    apply (nativeLieRationalInternalLayer_succ_le_iff V hbr j _).mpr
    intro v hv w hw
    have hwF : w ∈ nativeSubgroupRationalLogSpan (E := E) (I := I) (Γ.lowerCentralSeries j) := by
      rw [ih]
      exact hw
    exact nativeSubgroupLowerCentralSeries_differential_spans_mod_next Γ j hv hwF

end Hindman168
