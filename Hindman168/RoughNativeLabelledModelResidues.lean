import Hindman168.RoughNativeModelFiniteResidue

namespace Hindman168
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G]
attribute [local instance] lieGroup_smooth_min_three

theorem rough_native_labelled_model_residues {κ : Type*} [Fintype κ]
    (Γ : Subgroup G) (V : E) (K N : ℕ) (hK : 0 < K) (hN : 0 < N)
    (hperiod : nativeLieExponential (I := I) (G := G) ((K : ℝ) • V) ∈ Γ)
    (support : Finset (κ →₀ ℕ)) {w H q z : ℕ} {Z A : ℝ}
    (theta : (κ →₀ ℕ) → Polynomial ℝ) (M0 : Polynomial ℚ)
    (M : (κ →₀ ℕ) → Polynomial ℚ)
    (hmodels : ∀ J ∈ support, RoughCoefficientModel w H q (∑ j, J j) Z A (theta J) (M J))
    (h0 : ∃ n : ℤ, M0.eval (z : ℚ) = (n : ℚ)) (hz : z < H) (l r : κ → ℤ) :
    ∃ j : ((κ → Fin N) × (κ → Fin K)) → Fin K, ∀ x : κ → ℤ,
      (QuotientGroup.mk (nativeLieExponential (I := I) (G := G)
        (MvPolynomial.eval (Option.elim · (z : ℝ) (fun k => (x k : ℝ)))
          (MvPolynomial.map (Rat.castHom ℝ) (roughSpatialJointPolynomial support M0 M)) • V)) : G ⧸ Γ) =
        QuotientGroup.mk (nativeLieExponential (I := I) (G := G)
          (((j (roughBoxLabel l r N K hN hK x)).val : ℝ) • V)) := by
  classical
  have hh : ∀ p : (κ → Fin N) × (κ → Fin K), ∃ j : Fin K, ∀ x : κ → ℤ,
      (∀ k, Int.ModEq (K : ℤ) (x k) (p.2 k).val) →
      (QuotientGroup.mk (nativeLieExponential (I := I) (G := G)
        (MvPolynomial.eval (Option.elim · (z : ℝ) (fun k => (x k : ℝ)))
          (MvPolynomial.map (Rat.castHom ℝ) (roughSpatialJointPolynomial support M0 M)) • V)) : G ⧸ Γ) =
        QuotientGroup.mk (nativeLieExponential (I := I) (G := G) ((j.val : ℝ) • V)) :=
    fun p => rough_native_joint_model_finite_residue Γ V K hK hperiod support theta M0 M
      hmodels h0 hz (fun k => (p.2 k).val)
  choose j hj using hh
  refine ⟨j, ?_⟩
  intro x
  apply hj (roughBoxLabel l r N K hN hK x) x
  intro k
  exact (rough_residue_label_iff K hK (x k) (roughResidueLabel K hK (x k))).mp rfl

end Hindman168
