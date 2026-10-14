import Hindman168.RoughNativePartitionFreezing
import Hindman168.RoughNativeResidueProductApproximation
import Hindman168.RoughNativeLabelledModelResidues
import Hindman168.RoughNativeKernelMap

namespace Hindman168
open MvPolynomial
open scoped Manifold ContDiff Classical
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem rough_native_labelled_piece_tests {κ : Type*} [Fintype κ] {step : ℕ}
    (D : NativeNilmanifoldData.{u} step) (S : LieSubalgebra ℝ (GroupLieAlgebra D.I D.G))
    (hS : nativeLatticeRationalSubspace (E := D.E) (I := D.I) D.Γ (nativeLieSubalgebraModel S))
    (χ : D.E →ₗ[ℝ] ℝ)
    (hχ : ∀ x ∈ nativeLieSubalgebraModel S, ∀ y ∈ nativeLieSubalgebraModel S,
      χ (nativeLieAdjointDifferential (I := D.I) (G := D.G) x y) = 0)
    (hQ : ∀ x ∈ nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ,
      ∃ r : ℚ, χ x = (r : ℝ))
    (V : D.E) (hVr : V ∈ nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ)
    (hVS : V ∈ nativeLieSubalgebraModel S) (hχV : χ V = 1)
    (K : ℕ) (hK : 0 < K)
    (hperiod : nativeLieExponential (I := D.I) (G := D.G) ((K : ℝ) • V) ∈ D.Γ)
    (support : Finset (κ →₀ ℕ)) (d : ℕ) (hd : ∀ J ∈ support, (∑ j, J j) ≤ d)
    (A C B : ℝ) (hA : 0 ≤ A) (hC : 1 ≤ C) (hB : 0 ≤ B) (Lip : NNReal)
    {εfreeze εapprox : ℝ} (hεf : 0 < εfreeze) (hεa : 0 < εapprox) :
    let family := fun j : Fin K => roughNativeKernelNilmanifold D S hS χ hχ hQ V hVr (j.val : ℤ)
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    letI : ∀ j, MetricSpace ((family j).G ⧸ (family j).Γ) := fun j => (family j).metric
    letI : ∀ j, TopologicalSpace ((family j).G ⧸ (family j).Γ) := fun j =>
      (family j).metric.toUniformSpace.toTopologicalSpace
    ∃ N : ℕ, ∃ L : NNReal, ∃ hN : 0 < N, ∀ (w H q z : ℕ) (Z : ℝ)
      (P0 : Polynomial ℝ) (theta : (κ →₀ ℕ) → Polynomial ℝ)
      (M0 : Polynomial ℚ) (M : (κ →₀ ℕ) → Polynomial ℚ),
      (∀ J ∈ support, RoughCoefficientModel w H q (∑ j, J j) Z A (theta J) (M J)) →
      z < H → 0 < Z → (∃ n : ℤ, M0.eval (z : ℚ) = (n : ℚ)) →
      (0 ≤ P0.eval (z : ℝ)-((M0.eval (z : ℚ) : ℚ) : ℝ) ∧
        P0.eval (z : ℝ)-((M0.eval (z : ℚ) : ℚ) : ℝ) < 1) →
      ∀ (l r : κ → ℤ), (∀ j, 2*(N : ℤ) ≤ r j-l j) →
      (∀ j, (r j : ℝ)-l j ≤ C*Z) →
      (∀ j, |(l j : ℝ)| ≤ C*Z) → (∀ j, |(r j : ℝ)| ≤ C*Z) →
      ∀ F : (D.G ⧸ D.Γ) → ℝ, LipschitzWith Lip F → (∀ v, |F v| ≤ B) →
      let m := map (Rat.castHom ℝ) (roughSpatialJointPolynomial support M0 M)
      let a := roughSpatialJointPolynomial support P0 theta-m
      ∀ (P : (Option κ → ℝ) → D.G)
        (hP : ∀ x, P x ∈ nativeLieSubalgebraSubgroup (E := D.E) S)
        (hchar : ∀ x, nativeLieLogarithmCharacter (I := D.I) (G := D.G) χ (P x) = eval x a+eval x m),
      let Q := fun j : Fin K => roughNativeKernelMap D S hS χ hχ hQ V hVr
        (j.val : ℤ) hVS hχV a m P hP hchar
      ∃ indices : ((κ → Fin N) × (κ → Fin K)) → Fin K,
      ∃ tests : ∀ p : (κ → Fin N) × (κ → Fin K),
        (family (indices p)).G ⧸ (family (indices p)).Γ → ℝ,
        (∀ p, LipschitzWith L (tests p)) ∧ (∀ p v, |tests p v| ≤ B) ∧
        ∀ x ∈ Fintype.piFinset (fun j => Finset.Ico (l j) (r j)),
          let p := roughBoxLabel l r N K hN hK x
          let xp : Option κ → ℝ := (Option.elim · (z : ℝ) (fun j => (x j : ℝ)))
          |F (QuotientGroup.mk (P xp))-tests p (QuotientGroup.mk (Q (indices p) xp))| ≤ εfreeze+εapprox := by
  intro family
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI : ∀ j, MetricSpace ((family j).G ⧸ (family j).Γ) := fun j => (family j).metric
  letI : ∀ j, TopologicalSpace ((family j).G ⧸ (family j).Γ) := fun j =>
    (family j).metric.toUniformSpace.toTopologicalSpace
  obtain ⟨N, hN, hfreeze⟩ := rough_native_balanced_piece_freezing D V support d hd A C hA hC Lip hεf
  let R : ℝ := 1+(support.card : ℝ)*A*C ^ d
  obtain ⟨L, happ⟩ := rough_native_residue_product_approximation D S hS χ hχ hQ V hVr
    (fun j : Fin K => (j.val : ℤ)) R B hB Lip hεa
  refine ⟨N, L, hN, ?_⟩
  intro w H q z Z P0 theta M0 M hmodels hz hZ h0 hconst l r hlen hside hl hr F hF hbound m a P hP hchar Q
  have hab : ∀ j, l j ≤ r j := by
    intro j
    have hh := hlen j
    have hn0 : (0 : ℤ) ≤ 2*N := by positivity
    omega
  obtain ⟨indices, hres⟩ := rough_native_labelled_model_residues D.Γ V K N hK hN hperiod
    support theta M0 M hmodels h0 hz l r
  let anchor (p : (κ → Fin N) × (κ → Fin K)) : κ → ℤ := roughBoxLower l r N p.1
  let b (p : (κ → Fin N) × (κ → Fin K)) : ℝ :=
    eval (Option.elim · (z : ℝ) (fun j => (anchor p j : ℝ))) a
  have hb : ∀ p, |b p| ≤ R := by
    intro p
    have hc := rough_balanced_box_contained l r N hN hab p.1
    have ha : ∀ j, |(anchor p j : ℝ)| ≤ C*Z := by
      intro j
      have hlo : (l j : ℝ) ≤ (anchor p j : ℝ) := by exact_mod_cast hc.1 j
      have hhi : (anchor p j : ℝ) ≤ r j := by
        exact_mod_cast (hc.2.1 j).trans (hc.2.2 j)
      have hla := abs_le.mp (hl j)
      have hra := abs_le.mp (hr j)
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    exact rough_joint_horizontal_error_box support d hd P0 theta M0 M hmodels hz hA hC hZ hconst
      (fun j => (anchor p j : ℝ)) ha
  have htests : ∀ p : (κ → Fin N) × (κ → Fin K),
      ∃ f : (family (indices p)).G ⧸ (family (indices p)).Γ → ℝ,
        LipschitzWith L f ∧ (∀ v, |f v| ≤ B) ∧
        ∀ (h : (family (indices p)).G) (right : D.G),
          (QuotientGroup.mk right : D.G ⧸ D.Γ) = QuotientGroup.mk
            (nativeLieExponential (I := D.I) (G := D.G) (((indices p).val : ℝ) • V)) →
          |F (QuotientGroup.mk (nativeLieExponential (I := D.I) (G := D.G) (b p • V)*h.val*right))-
            f (QuotientGroup.mk h)| ≤ εapprox := by
    intro p
    exact happ (indices p) (b p) (hb p) F hF hbound
  choose tests hlip hsup herr using htests
  refine ⟨indices, tests, hlip, hsup, ?_⟩
  intro x hx
  let p := roughBoxLabel l r N K hN hK x
  let xp : Option κ → ℝ := (Option.elim · (z : ℝ) (fun j => (x j : ℝ)))
  have hxpiece : x ∈ Fintype.piFinset (fun j =>
      Finset.Ico (roughBoxLower l r N p.1 j) (roughBoxUpper l r N p.1 j)) := by
    apply Fintype.mem_piFinset.mpr
    intro j
    apply Finset.mem_Ico.mpr
    exact (rough_interval_label_iff (l j) (r j) N hN (hab j) (x j)
      (Finset.mem_Ico.mp (Fintype.mem_piFinset.mp hx j)) (p.1 j)).mp rfl
  have hf := hfreeze w H q z Z P0 theta M0 M hmodels hz hZ hconst l r hlen hside hl hr F hF P p.1 x hxpiece
  have he := herr p (Q (indices p) xp)
    (nativeLieExponential (I := D.I) (G := D.G) (eval xp m • V)) (hres x)
  exact (abs_sub_le _ _ _).trans (add_le_add hf.le he)

end Hindman168
