import Hindman168.RoughNativeModelFreezing
import Hindman168.RoughNativeFrozenFactorization
import Hindman168.RoughBalancedBoxGeometry

namespace Hindman168
open MvPolynomial
open scoped Manifold ContDiff Classical
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem rough_native_balanced_piece_freezing {κ : Type*} [Fintype κ] {step : ℕ}
    (D : NativeNilmanifoldData.{u} step) (V : D.E)
    (support : Finset (κ →₀ ℕ)) (d : ℕ) (hd : ∀ J ∈ support, (∑ j, J j) ≤ d)
    (A C : ℝ) (hA : 0 ≤ A) (hC : 1 ≤ C) (Lip : NNReal) {ε : ℝ} (hε : 0 < ε) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∃ N : ℕ, 0 < N ∧ ∀ (w H q z : ℕ) (Z : ℝ)
      (P0 : Polynomial ℝ) (theta : (κ →₀ ℕ) → Polynomial ℝ)
      (M0 : Polynomial ℚ) (M : (κ →₀ ℕ) → Polynomial ℚ),
      (∀ J ∈ support, RoughCoefficientModel w H q (∑ j, J j) Z A (theta J) (M J)) →
      z < H → 0 < Z →
      (0 ≤ P0.eval (z : ℝ)-((M0.eval (z : ℚ) : ℚ) : ℝ) ∧
        P0.eval (z : ℝ)-((M0.eval (z : ℚ) : ℚ) : ℝ) < 1) →
      ∀ (l r : κ → ℤ), (∀ j, 2*(N : ℤ) ≤ r j-l j) →
      (∀ j, (r j : ℝ)-l j ≤ C*Z) →
      (∀ j, |(l j : ℝ)| ≤ C*Z) → (∀ j, |(r j : ℝ)| ≤ C*Z) →
      ∀ F : (D.G ⧸ D.Γ) → ℝ, LipschitzWith Lip F →
      ∀ (P : (Option κ → ℝ) → D.G) (i : κ → Fin N) (x : κ → ℤ),
      x ∈ Fintype.piFinset (fun j =>
        Finset.Ico (roughBoxLower l r N i j) (roughBoxUpper l r N i j)) →
      let a := roughSpatialJointPolynomial support P0 theta -
        map (Rat.castHom ℝ) (roughSpatialJointPolynomial support M0 M)
      let m := map (Rat.castHom ℝ) (roughSpatialJointPolynomial support M0 M)
      let xp : Option κ → ℝ := (Option.elim · (z : ℝ) (fun j => (x j : ℝ)))
      let b := eval (Option.elim · (z : ℝ) (fun j => (roughBoxLower l r N i j : ℝ))) a
      |F (QuotientGroup.mk (P xp))-F (QuotientGroup.mk
        (nativeLieExponential (I := D.I) (G := D.G) (b • V) *
          roughNativeKernelFactor (I := D.I) V (eval xp a) (eval xp m) (P xp) *
            nativeLieExponential (I := D.I) (G := D.G) (eval xp m • V)))| < ε := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  obtain ⟨δ, hδ, hfreeze⟩ := rough_native_model_subbox_freezing D V support d hd A C hA hC Lip hε
  obtain ⟨n, hn⟩ := exists_nat_gt (2*C/δ)
  let N := n+1
  have hN : 0 < N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hsize : 2*C/(N : ℝ) ≤ δ := by
    apply (div_le_iff₀ hNr).mpr
    have hh := (div_lt_iff₀ hδ).mp hn
    dsimp only [N]
    push_cast
    nlinarith
  refine ⟨N, hN, ?_⟩
  intro w H q z Z P0 theta M0 M hmodels hz hZ h0 l r hlen hside hl hr F hF P i x hx
  let anchor : κ → ℤ := roughBoxLower l r N i
  have hab : ∀ j, l j ≤ r j := by
    intro j
    have hh := hlen j
    have hn0 : (0 : ℤ) ≤ 2*N := by positivity
    omega
  have hcontain := rough_balanced_box_contained l r N hN hab i
  have hxsub : ∀ j, (roughBoxLower l r N i j : ℝ) ≤ (x j : ℝ) ∧
      (x j : ℝ) ≤ roughBoxUpper l r N i j := by
    intro j
    have hh := Finset.mem_Ico.mp (Fintype.mem_piFinset.mp hx j)
    exact_mod_cast (show roughBoxLower l r N i j ≤ x j ∧ x j ≤ roughBoxUpper l r N i j from
      ⟨hh.1, hh.2.le⟩)
  have hanchor : ∀ j, (roughBoxLower l r N i j : ℝ) ≤ (anchor j : ℝ) ∧
      (anchor j : ℝ) ≤ roughBoxUpper l r N i j := by
    intro j
    exact ⟨le_rfl, by exact_mod_cast hcontain.2.1 j⟩
  have hxpos : ∀ j, |(x j : ℝ)| ≤ C*Z := by
    intro j
    have hlo : (l j : ℝ) ≤ roughBoxLower l r N i j := by exact_mod_cast hcontain.1 j
    have hhi : (roughBoxUpper l r N i j : ℝ) ≤ r j := by exact_mod_cast hcontain.2.2 j
    have ha := abs_le.mp (hl j)
    have hb := abs_le.mp (hr j)
    exact abs_le.mpr ⟨by linarith [hxsub j], by linarith [hxsub j]⟩
  have hapos : ∀ j, |(anchor j : ℝ)| ≤ C*Z := by
    intro j
    have hlo : (l j : ℝ) ≤ roughBoxLower l r N i j := by exact_mod_cast hcontain.1 j
    have hhi : (roughBoxUpper l r N i j : ℝ) ≤ r j := by exact_mod_cast hcontain.2.2 j
    have ha := abs_le.mp (hl j)
    have hb := abs_le.mp (hr j)
    exact abs_le.mpr ⟨by linarith [hanchor j], by linarith [hanchor j]⟩
  have hclose : ∀ j, |(x j : ℝ)-(anchor j : ℝ)| ≤ δ*Z := by
    intro j
    have hh := rough_balanced_box_close l r N hN hlen C Z hside i
      (fun j => (x j : ℝ)) (fun j => (anchor j : ℝ)) hxsub hanchor j
    have hmul := mul_le_mul_of_nonneg_right hsize hZ.le
    have he : (2*C/(N : ℝ))*Z = 2*C*Z/N := by ring
    rw [he] at hmul
    exact hh.trans hmul
  let a := roughSpatialJointPolynomial support P0 theta -
    map (Rat.castHom ℝ) (roughSpatialJointPolynomial support M0 M)
  let m := map (Rat.castHom ℝ) (roughSpatialJointPolynomial support M0 M)
  let xp : Option κ → ℝ := (Option.elim · (z : ℝ) (fun j => (x j : ℝ)))
  let Q := roughNativeKernelFactor (I := D.I) V (eval xp a) (eval xp m) (P xp)
  let R := nativeLieExponential (I := D.I) (G := D.G) (eval xp m • V)
  have hf := hfreeze w H q z Z P0 theta M0 M hmodels hz hZ h0 F hF
    (fun j => (x j : ℝ)) (fun j => (anchor j : ℝ)) (QuotientGroup.mk (Q*R)) hxpos hapos hclose
  have he : nativeLieExponential (I := D.I) (G := D.G) (eval xp a • V)*(Q*R) = P xp :=
    (mul_assoc _ _ _).symm.trans (rough_native_kernel_factorization V (eval xp a) (eval xp m) (P xp)).symm
  change |F (QuotientGroup.mk (nativeLieExponential (I := D.I) (G := D.G)
    (eval xp a • V)*(Q*R)))-F (QuotientGroup.mk
      (nativeLieExponential (I := D.I) (G := D.G)
        (eval (Option.elim · (z : ℝ) (fun j => (anchor j : ℝ))) a • V)*(Q*R)))| < ε at hf
  rw [he] at hf
  simpa only [mul_assoc] using hf

end Hindman168
