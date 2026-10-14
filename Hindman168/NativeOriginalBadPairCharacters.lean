import Hindman168.NativeOriginalResidueBoxObstruction
import Hindman168.RoughNativeBadIndexHaarComparison

/-! ACTUAL original complex bad pair, with arbitrary original boxes/tests,
now PRODUCES an original character in one fixed finite list and ALL positive
affine original spatial rows. Full and residue Haar branches both retained. -/
namespace Hindman168
open MeasureTheory MvPolynomial
open scoped Manifold ContDiff BigOperators Classical
universe u

theorem native_original_bad_pair_characters {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (n d : ℕ) (c C B η : ℝ) (L : NNReal)
    (hc : 0 < c) (hC : 0 ≤ C) (hB : 0 ≤ B) (hη : 0 < η) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∃ S : Finset (D.E →ₗ[ℝ] ℝ),
      (∀ χ ∈ S, RoughNativeHorizontalFunctional (I := D.I) D.Γ χ) ∧
      ∃ A Z0 : ℝ, 0 < A ∧ 1 ≤ Z0 ∧
      ∀ (t : ℕ), 0 < t → ∀ Z : ℝ, Z0 ≤ Z → Z0 ≤ Z/t →
        (t : ℝ) ≤ Z → (t : ℝ) ≤ (c/2)*Z →
      ∀ (Q : (Option (Fin n) → ℝ) → D.G) (p : RoughVectorMvPolynomial (Option (Fin n)) D.E),
        RoughVectorMvDegreeLE p d →
        (∀ x, nativeLieGlobalLogarithm (E := D.E) (I := D.I) (Q x) = roughVectorMvEval p x) →
      ∀ z : ℕ, RoughNativeComplexBadIndex D Q z t Z c C L B η →
        ∃ χ ∈ S, ∃ pOb : ℕ, ∃ bOb : Fin n → ℕ,
          (pOb=1 ∨ pOb=t) ∧ (∀ j, bOb j ≤ pOb) ∧
          ∀ J : Fin n → ℕ, 0 < (∑ j, J j) →
            ‖((coeff (Finsupp.equivFunOnFinite.symm J)
              (roughMvAffineSubstitution (fun j => (bOb j : ℝ)) (fun _ => (pOb : ℝ))
                (roughScalarSpatialProjection χ p (z : ℝ))) : ℝ) : UnitAddCircle)‖ ≤
                  A*((pOb : ℝ)/Z)^(∑ j, J j) := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  obtain ⟨Sf,hSf,Af,Zf,hAf,hZf,hFull⟩ := native_original_real_box_finite_obstruction
    D n d c C B (η/2) L hc hC hB (by positivity)
  obtain ⟨Sr,hSr,Ar,Zr,hAr,hZr,hRes⟩ := native_original_residue_box_obstruction
    D n d c C B (η/2) L hc hC hB (by positivity)
  let A := max Af Ar
  let Z0 := max Zf Zr
  have hA : 0 < A := hAf.trans_le (le_max_left _ _)
  refine ⟨Sf∪Sr,?_,A,Z0,hA,hZf.trans (le_max_left _ _),?_⟩
  · intro χ hχ
    exact (Finset.mem_union.mp hχ).elim (hSf χ) (hSr χ)
  · intro t ht Z hZ hZt htZ htc Q p hp hQ z hBad
    obtain ⟨lo,hi,v,F,hLip,hBound,hBox,_hStep,_hFull,hGap⟩ :=
      rough_native_complex_bad_index_haar_comparison D Q z t Z c C L B η hBad
    have hLen (j : Fin n) := (hBox j).1
    have hLenHi (j : Fin n) := (hBox j).2.1
    have hLoc (j : Fin n) := (hBox j).2.2
    have hZpos : 0 < Z := zero_lt_one.trans_le ((hZf.trans (le_max_left _ _)).trans hZ)
    rcases hGap with hGap | hGap
    · obtain ⟨χ,hχ,b,hb,hCoeff⟩ := hRes t ht Z ((le_max_right _ _).trans hZt) htZ htc
        lo hi v (fun j => ⟨hLen j,hLenHi j⟩) hLoc Q p hp hQ z F hLip hBound hGap.le
      refine ⟨χ,Finset.mem_union_right _ hχ,t,b,Or.inr rfl,fun j => (hb j).1.le,?_⟩
      intro J hJ
      exact (hCoeff J hJ).trans (mul_le_mul_of_nonneg_right (le_max_right _ _)
        (pow_nonneg (div_nonneg (Nat.cast_nonneg t) hZpos.le) _))
    · have hGap' : η/2 ≤ ‖finiteComplexSetMean
          (roughRealIntegerBox (fun j => (lo j : ℝ)) (fun j => (hi j : ℝ)))
          (fun x => F (Q (fun i => i.elim (z : ℝ) (fun j => (x j : ℝ))) : D.G ⧸ D.Γ)) -
            ∫ q, F q ∂nativeNilmanifoldQuotientProbability D‖ := by
        rw [rough_integer_real_box]
        exact hGap.le
      obtain ⟨χ,hχ,hCoeff⟩ := hFull Z ((le_max_left _ _).trans hZ)
        (fun j => (lo j : ℝ)) (fun j => (hi j : ℝ)) hLen
        (fun j => by simpa only [neg_mul] using (abs_le.mp (hLoc j).1).1)
        (fun j => (abs_le.mp (hLoc j).2).2)
        Q p hp hQ z F hLip hBound hGap'
      have he : roughMvAffineSubstitution (fun _ : Fin n => (0 : ℝ)) (fun _ => (1 : ℝ)) = RingHom.id _ := by
        apply MvPolynomial.ringHom_ext
        · intro r
          simp [roughMvAffineSubstitution]
        · intro j
          simp [roughMvAffineSubstitution]
      refine ⟨χ,Finset.mem_union_left _ hχ,1,fun _ => 0,Or.inl rfl,fun _ => Nat.zero_le _,?_⟩
      intro J hJ
      simpa only [Nat.cast_zero,Nat.cast_one,he,RingHom.id_apply,one_div] using
        (hCoeff J hJ).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
          (pow_nonneg (inv_nonneg.mpr hZpos.le) _))

end Hindman168
