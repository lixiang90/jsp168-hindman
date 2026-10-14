import Hindman168.NativeOriginalAsymptoticBadPairCharacters
import Hindman168.RoughParameterAffineProjection
import Hindman168.RoughFiniteLabelThinning

/-! TRUE bad input on a smooth parameter progression yields ONE common
original character, LITERAL reparametrized raw source and EVERY positive
affine row. Constants/length thresholds precede all raw sources and scales. -/
namespace Hindman168
open MeasureTheory MvPolynomial Filter
open scoped Manifold ContDiff BigOperators Classical
universe u

theorem native_original_common_bad_character {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (n d : ℕ) (c C B η : ℝ) (L : NNReal)
    (hc : 0 < c) (hC : 0 ≤ C) (hB : 0 ≤ B) (hη : 0 < η)
    (Scale Z : ℕ → ℝ) (hg : PowerDominates atTop Z Scale)
    (hScale : ∀ᶠ w in atTop, 1 ≤ Scale w) (hZ : ∀ᶠ w in atTop, 0 ≤ Z w) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∃ S : Finset (D.E →ₗ[ℝ] ℝ),
      (∀ χ ∈ S, RoughNativeHorizontalFunctional (I := D.I) D.Γ χ) ∧
      ∃ A : ℝ, 0 < A ∧ ∀ H : ℕ, 0 < H → ∃ N : ℕ, 0 < N ∧ ∀ᶠ w in atTop,
      ∀ (Q : (Option (Fin n) → ℝ) → D.G) (p : RoughVectorMvPolynomial (Option (Fin n)) D.E),
        RoughVectorMvDegreeLE p d →
        (∀ x, nativeLieGlobalLogarithm (E := D.E) (I := D.I) (Q x) = roughVectorMvEval p x) →
      ∀ t diff : ℕ, 0 < diff → (∀ prime : ℕ, prime.Prime → prime ∣ diff → prime ≤ w) →
        (∀ z : ℕ, z < N → Scale w ≤ (t+diff*z : ℕ) ∧ (t+diff*z : ℕ) < 2*Scale w) →
        (∀ z : ℕ, z < N → (primorial w).Coprime (t+diff*z)) →
        (∀ z : ℕ, z < N → RoughNativeBadIndex D Q z (t+diff*z) (Z w) c C L B η) →
      ∃ a b : ℕ, ∃ χ ∈ S, 0 < b ∧ b ≤ N ∧
        let Qnew := fun x : Option (Fin n) → ℝ => Q (fun i => i.elim ((a : ℝ)+(b : ℝ)*x none) (fun j => x (some j)))
        let pnew := roughParameterAffineSource (a : ℝ) (b : ℝ) p
        RoughVectorMvDegreeLE pnew d ∧
        (∀ x, nativeLieGlobalLogarithm (E := D.E) (I := D.I) (Qnew x) = roughVectorMvEval pnew x) ∧
        0 < b*diff ∧ (∀ prime : ℕ, prime.Prime → prime ∣ b*diff → prime ≤ w) ∧
        ∀ z : ℕ, z < H → a+b*z < N ∧
          Scale w ≤ ((t+diff*a)+(b*diff)*z : ℕ) ∧ ((t+diff*a)+(b*diff)*z : ℕ) < 2*Scale w ∧
          (primorial w).Coprime ((t+diff*a)+(b*diff)*z) ∧
          RoughNativeBadIndex D Qnew z ((t+diff*a)+(b*diff)*z) (Z w) c C L B η ∧
          ∃ pOb : ℕ, ∃ bOb : Fin n → ℕ,
            (pOb=1 ∨ pOb=(t+diff*a)+(b*diff)*z) ∧ (∀ j, bOb j ≤ pOb) ∧
            ∀ J : Fin n → ℕ, 0 < (∑ j, J j) →
              ‖((coeff (Finsupp.equivFunOnFinite.symm J)
                (roughMvAffineSubstitution (fun j => (bOb j : ℝ)) (fun _ => (pOb : ℝ))
                  (roughScalarSpatialProjection χ pnew (z : ℝ))) : ℝ) : UnitAddCircle)‖ ≤
                    A*((pOb : ℝ)/(Z w))^(∑ j, J j) := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  obtain ⟨S,hS,A,hA,hProduce⟩ := native_original_asymptotic_bad_pair_characters
    D n d c C B η L hc hC hB hη Scale Z hg hScale hZ
  refine ⟨S,hS,A,hA,?_⟩
  intro H hH
  obtain ⟨N,hN,hThin⟩ := rough_finite_label_thinning H hH ↥S
  refine ⟨N,hN,?_⟩
  filter_upwards [hProduce,eventually_ge_atTop N] with w hw hNw
  intro Q p hp hQ t diff hDiff hSmooth hSize hRough hBad
  let P (z : ℕ) (χ : ↥S) := ∃ pOb : ℕ, ∃ bOb : Fin n → ℕ,
    (pOb=1 ∨ pOb=t+diff*z) ∧ (∀ j, bOb j ≤ pOb) ∧
    ∀ J : Fin n → ℕ, 0 < (∑ j, J j) →
      ‖((coeff (Finsupp.equivFunOnFinite.symm J)
        (roughMvAffineSubstitution (fun j => (bOb j : ℝ)) (fun _ => (pOb : ℝ))
          (roughScalarSpatialProjection χ.val p (z : ℝ))) : ℝ) : UnitAddCircle)‖ ≤
            A*((pOb : ℝ)/(Z w))^(∑ j, J j)
  have hAll (z : ℕ) (hz : z < N) : ∃ χ : ↥S, P z χ := by
    obtain ⟨χ,hχ,hPacket⟩ := hw (t+diff*z) (hSize z hz).1 (hSize z hz).2 Q p hp hQ z (hBad z hz)
    exact ⟨⟨χ,hχ⟩,hPacket⟩
  obtain ⟨a,b,χ,hb,hbN,hRows⟩ := hThin P hAll
  obtain ⟨hBDiff,hSmoothNew,hValues⟩ := rough_smooth_progression_reparametrization
    w N H t diff a b (Scale w) hDiff hb hbN hNw hSmooth (fun z hz => (hRows z hz).1) hSize hRough
  let Qnew := fun x : Option (Fin n) → ℝ => Q (fun i => i.elim ((a : ℝ)+(b : ℝ)*x none) (fun j => x (some j)))
  let pnew := roughParameterAffineSource (a : ℝ) (b : ℝ) p
  have hLog (x : Option (Fin n) → ℝ) :
      nativeLieGlobalLogarithm (E := D.E) (I := D.I) (Qnew x)=roughVectorMvEval pnew x := by
    have he : (fun i : Option (Fin n) => i.elim (x none) (fun j => x (some j)))=x := by funext i; cases i <;> rfl
    rw [← he,rough_parameter_affine_eval]
    exact hQ _
  refine ⟨a,b,χ.val,χ.property,hb,hbN,rough_parameter_affine_degree _ _ hp,hLog,hBDiff,hSmoothNew,?_⟩
  intro z hz
  obtain ⟨hEq,hLow,hHigh,hCop⟩ := hValues z hz
  have hIndex := (hRows z hz).1
  have hBadNew := rough_native_bad_index_reparametrize D Q a b z (t+diff*(a+b*z))
    (Z w) c C L B η (hBad _ hIndex)
  refine ⟨hIndex,hLow,hHigh,hCop,?_,?_⟩
  · simpa only [Qnew,hEq] using hBadNew
  · obtain ⟨pOb,bOb,hStep,hBase,hCoeff⟩ := (hRows z hz).2
    refine ⟨pOb,bOb,by simpa only [hEq] using hStep,hBase,?_⟩
    intro J hJ
    simpa only [pnew,rough_parameter_affine_spatial_projection,Nat.cast_add,Nat.cast_mul] using hCoeff J hJ

end Hindman168
