import Hindman168.NativeLieAdjointDerivative

/-! Actual continuous linear adjoint equivalences and native exponential
conjugation. The inverse comes from original conjugation by the inverse
group element; no linear inverse or exponential compatibility is supplied. -/

namespace Hindman168
open Function Set Topology
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G]

attribute [local instance] lieGroup_smooth_min_three

 noncomputable def nativeLieAdjointEquiv (g : G) : E ≃L[ℝ] E where
  toLinearEquiv :=
    { toLinearMap := (nativeLieAdjoint (I := I) g).toLinearMap
      invFun := nativeLieAdjoint (I := I) g⁻¹
      left_inv := nativeLieAdjoint_inv_apply (I := I) g
      right_inv := nativeLieAdjoint_apply_inv (I := I) g }
  continuous_toFun := (nativeLieAdjoint (I := I) g).continuous
  continuous_invFun := (nativeLieAdjoint (I := I) g⁻¹).continuous

 theorem nativeLieAdjointEquiv_apply (g : G) (v : E) :
    nativeLieAdjointEquiv (I := I) g v = nativeLieAdjoint (I := I) g v := rfl

 theorem nativeLieAdjointEquiv_symm_apply (g : G) (v : E) :
    (nativeLieAdjointEquiv (I := I) g).symm v = nativeLieAdjoint (I := I) g⁻¹ v := rfl

 theorem nativeLieAdjoint_inverse (g : G) :
    (nativeLieAdjoint (I := I) g).inverse = nativeLieAdjoint (I := I) g⁻¹ :=
  ContinuousLinearMap.inverse_eq (nativeLieAdjoint_comp_inv (I := I) g)
    (nativeLieAdjoint_inv_comp (I := I) g)

 theorem nativeLieConjugation_inverse_mfderiv (g x : G) :
    (mfderiv I I (fun y : G => g * y * g⁻¹) x).inverse =
      mfderiv I I (fun y : G => g⁻¹ * y * g) (g * x * g⁻¹) := by
  let f : G → G := fun y => g * y * g⁻¹
  let h : G → G := fun y => g⁻¹ * y * g
  have hf : MDifferentiable I I f := (nativeLieConjugation_contMDiff (I := I) g).mdifferentiable (by norm_num)
  have hh : MDifferentiable I I h := by
    convert! (nativeLieConjugation_contMDiff (I := I) g⁻¹).mdifferentiable (by norm_num) using 1
    simp only [inv_inv, h]
  have he₁ : h ∘ f = id := by ext y; simp only [comp_apply, f, h, id_eq]; group
  have he₂ : f ∘ h = id := by ext y; simp only [comp_apply, f, h, id_eq]; group
  have ha : (mfderiv I I h (f x)).comp (mfderiv I I f x) = ContinuousLinearMap.id ℝ E := by
    rw [← mfderiv_comp x (hh (f x)) (hf x), he₁, mfderiv_id]
    rfl
  have hb : (mfderiv I I f x).comp (mfderiv I I h (f x)) = ContinuousLinearMap.id ℝ E := by
    have he : h (f x) = x := congrFun he₁ x
    have hd := mfderiv_comp (I := I) (I' := I) (I'' := I) (f x) (hf (h (f x))) (hh (f x))
    rw [he₂, mfderiv_id, he] at hd
    exact hd.symm
  exact ContinuousLinearMap.inverse_eq hb ha

variable [CompleteSpace E] [BoundarylessManifold I G] [T2Space G]

 theorem nativeLieAdjoint_curve_conjugation (g : G) (v : E) (t : ℝ) :
    g * lieOneParameterCurve (I := I) (G := G) v t * g⁻¹ =
      lieOneParameterCurve (I := I) (G := G) (nativeLieAdjoint (I := I) g v) t := by
  have h := congrFun (lie_hom_oneParameterCurve_map (I := I) (J := I)
    (MulAut.conj g).toMonoidHom
    ((nativeLieConjugation_contMDiff (I := I) g).mdifferentiable (by norm_num)) v) t
  exact h

 theorem nativeLieAdjoint_exponential_conjugation (g : G) (v : E) :
    g * nativeLieExponential (I := I) (G := G) v * g⁻¹ =
      nativeLieExponential (I := I) (G := G) (nativeLieAdjoint (I := I) g v) :=
  nativeLieAdjoint_curve_conjugation g v 1

 theorem nativeLieAdjoint_curve_self (v : E) (t : ℝ) :
    nativeLieAdjoint (I := I) (lieOneParameterCurve (I := I) (G := G) v t) v = v := by
  let g := lieOneParameterCurve (I := I) (G := G) v t
  have heq : (fun s : ℝ => g * lieOneParameterCurve (I := I) (G := G) v s * g⁻¹) =
      lieOneParameterCurve (I := I) (G := G) v := by
    funext s
    change lieOneParameterCurve (I := I) (G := G) v t * lieOneParameterCurve (I := I) (G := G) v s *
      (lieOneParameterCurve (I := I) (G := G) v t)⁻¹ = lieOneParameterCurve (I := I) (G := G) v s
    have hc : Commute (lieOneParameterCurve (I := I) (G := G) v t)
        (lieOneParameterCurve (I := I) (G := G) v s) := by
      change lieOneParameterCurve (I := I) (G := G) v t * lieOneParameterCurve (I := I) (G := G) v s =
        lieOneParameterCurve (I := I) (G := G) v s * lieOneParameterCurve (I := I) (G := G) v t
      rw [← lieOneParameterCurve_add, ← lieOneParameterCurve_add, add_comm]
    rw [hc.eq, mul_assoc, mul_inv_cancel, mul_one]
  have hcurve : lieOneParameterCurve (I := I) (G := G) (nativeLieAdjoint (I := I) g v) =
      lieOneParameterCurve (I := I) (G := G) v := by
    funext s
    exact (nativeLieAdjoint_curve_conjugation g v s).symm.trans (congrFun heq s)
  have hd := lieOneParameterCurve_hasMFDerivAt_zero (I := I) (G := G) (nativeLieAdjoint (I := I) g v)
  rw [hcurve] at hd
  have he := hd.mfderiv.symm.trans (lieOneParameterCurve_hasMFDerivAt_zero (I := I) (G := G) v).mfderiv
  convert! congrArg (fun L : ℝ →L[ℝ] E => L 1) he using 1
  · change nativeLieAdjoint (I := I) g v = (1 : ℝ) • nativeLieAdjoint (I := I) g v
    exact (one_smul ℝ _).symm
  · change v = (1 : ℝ) • v
    exact (one_smul ℝ v).symm

 theorem nativeLieAdjoint_exponential_self (v : E) :
    nativeLieAdjoint (I := I) (nativeLieExponential (I := I) (G := G) v) v = v :=
  nativeLieAdjoint_curve_self v 1

end Hindman168
