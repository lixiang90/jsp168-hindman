import Hindman168.NativeOriginalCommonBadCharacter
import Hindman168.RoughNativeBadFamily
import Hindman168.RoughInterpolationPaperGrowth

/-! The TRUE original bad-progression family now yields ONE common original
character and ALL affine rows on a true reparametrized bad family.
The paper's actual real-power growth hypotheses supply the original thresholds. -/
namespace Hindman168
open MeasureTheory MvPolynomial Filter
open scoped Manifold ContDiff BigOperators Classical
universe u

theorem native_original_common_bad_family {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (n d : ℕ) (c C B η : ℝ) (L : NNReal)
    (hc : 0 < c) (hC : 0 ≤ C) (hB : 0 ≤ B) (hη : 0 < η)
    (Scale Z : ℕ → ℝ) (hScale : Tendsto Scale atTop atTop)
    (hr : ∀ a : ℝ, 0 < a → Tendsto (fun w => Z w/(Scale w)^a) atTop atTop) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∃ S : Finset (D.E →ₗ[ℝ] ℝ),
      (∀ χ ∈ S, RoughNativeHorizontalFunctional (I := D.I) D.Γ χ) ∧
      ∃ A : ℝ, 0 < A ∧ ∀ H : ℕ, 0 < H → ∃ N : ℕ, 0 < N ∧ ∀ᶠ w in atTop,
      RoughNativeBadFamily (κ := Fin n) D N w (Scale w) (Z w) d c C L B η →
      ∃ χ ∈ S, ∃ (Q : (Option (Fin n) → ℝ) → D.G)
        (p : RoughVectorMvPolynomial (Option (Fin n)) D.E) (t diff : ℕ),
        RoughVectorMvDegreeLE p d ∧
        (∀ x, roughVectorMvEval p x = nativeLieGlobalLogarithm (E := D.E) (I := D.I) (Q x)) ∧
        0 < diff ∧ (∀ prime : ℕ, prime.Prime → prime ∣ diff → prime ≤ w) ∧
        ∀ z : ℕ, z < H →
          Scale w ≤ (t+diff*z : ℕ) ∧ (t+diff*z : ℕ) < 2*Scale w ∧
          (primorial w).Coprime (t+diff*z) ∧ RoughNativeBadIndex D Q z (t+diff*z) (Z w) c C L B η ∧
          ∃ pOb : ℕ, ∃ bOb : Fin n → ℕ,
            (pOb=1 ∨ pOb=t+diff*z) ∧ (∀ j, bOb j ≤ pOb) ∧
            ∀ I : Fin n → ℕ, 0 < (∑ j, I j) →
              ‖((coeff (Finsupp.equivFunOnFinite.symm I)
                (roughMvAffineSubstitution (fun j => (bOb j : ℝ)) (fun _ => (pOb : ℝ))
                  (roughScalarSpatialProjection χ p (z : ℝ))) : ℝ) : UnitAddCircle)‖ ≤
                    A*((pOb : ℝ)/(Z w))^(∑ j, I j) := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  have hn : ∀ k : ℕ, 0 < k → Tendsto (fun w => Z w/Scale w^k) atTop atTop := by
    intro k hk
    simpa only [Real.rpow_natCast] using hr k (by exact_mod_cast hk)
  obtain ⟨hg,hScaleOne,hZ⟩ := rough_interpolation_growth_from_ratios hScale hn
  obtain ⟨S,hS,A,hA,hCommon⟩ := native_original_common_bad_character D n d c C B η L
    hc hC hB hη Scale Z hg hScaleOne (hZ.mono (fun _ h => h.le))
  refine ⟨S,hS,A,hA,?_⟩
  intro H hH
  obtain ⟨N,hN,hStage⟩ := hCommon H hH
  refine ⟨N,hN,?_⟩
  filter_upwards [hStage] with w hw
  rintro ⟨Q,p,t,diff,hDegree,hLog,hDiff,hSmooth,hBad⟩
  have hLogAll (x : Option (Fin n) → ℝ) :
      nativeLieGlobalLogarithm (E := D.E) (I := D.I) (Q x)=roughVectorMvEval p x := by
    have he : (fun i : Option (Fin n) => i.elim (x none) (fun j => x (some j)))=x := by funext i; cases i <;> rfl
    simpa only [he] using (hLog (x none) (fun j => x (some j))).symm
  obtain ⟨a,b,χ,hχ,_hb,_hbN,hDegreeNew,hLogNew,hDiffNew,hSmoothNew,hRows⟩ :=
    hw Q p hDegree hLogAll t diff hDiff hSmooth
      (fun z hz => ⟨(hBad z hz).1,(hBad z hz).2.1⟩)
      (fun z hz => (hBad z hz).2.2.1) (fun z hz => (hBad z hz).2.2.2)
  refine ⟨χ,hχ,_,_,t+diff*a,b*diff,hDegreeNew,fun x => (hLogNew x).symm,hDiffNew,hSmoothNew,?_⟩
  intro z hz
  exact (hRows z hz).2

end Hindman168
