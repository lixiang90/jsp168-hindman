import Hindman168.NativeLieAdjointEquiv

/-! True native derivatives of original right translations and their action
on original left-invariant vector fields. These identities are needed to
compare differentiation of the adjoint with the native vector-field bracket.
They provide no assumed flow or bracket compatibility. -/

namespace Hindman168
open Function Set Topology VectorField
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G]

attribute [local instance] lieGroup_smooth_min_three

 theorem nativeLieRightTranslation_contMDiff (g : G) :
    ContMDiff I I ∞ (fun x : G => x * g) := contMDiff_mul_right

 theorem nativeLieRightTranslation_inverse_mfderiv (g x : G) :
    (mfderiv I I (fun y : G => y * g) x).inverse =
      mfderiv I I (fun y : G => y * g⁻¹) (x * g) := by
  let f : G → G := fun y => y * g
  let h : G → G := fun y => y * g⁻¹
  have hf : MDifferentiable I I f :=
    (nativeLieRightTranslation_contMDiff g).mdifferentiable (by norm_num)
  have hh : MDifferentiable I I h :=
    (nativeLieRightTranslation_contMDiff g⁻¹).mdifferentiable (by norm_num)
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

 theorem nativeLieRightTranslation_invariant_field (g x : G) (v : E) :
    mfderiv I I (fun y : G => y * g) x
        (mulInvariantVectorField (I := I) (G := G) (nativeLieAdjoint (I := I) g v) x) =
      mulInvariantVectorField (I := I) (G := G) v (x * g) := by
  let c : G → G := fun y => g * y * g⁻¹
  let l : G → G := fun y => x * y
  let r : G → G := fun y => y * g
  have hc : MDifferentiable I I c :=
    (nativeLieConjugation_contMDiff g).mdifferentiable (by norm_num)
  have hl : MDifferentiable I I l :=
    (contMDiff_mul_left : ContMDiff I I ∞ l).mdifferentiable (by norm_num)
  have hr : MDifferentiable I I r :=
    (nativeLieRightTranslation_contMDiff g).mdifferentiable (by norm_num)
  have heq : r ∘ (l ∘ c) = fun y : G => (x * g) * y := by
    ext y
    simp only [comp_apply, c, l, r]
    group
  have hd := mfderiv_comp (I := I) (I' := I) (I'' := I) (1 : G)
    (hr ((l ∘ c) 1)) ((hl (c 1)).comp 1 (hc 1))
  rw [heq, mfderiv_comp (I' := I) (1 : G) (hl (c 1)) (hc 1)] at hd
  simp only [comp_apply] at hd
  have h := congrArg (fun D : E →L[ℝ] E => D v) hd
  convert! h.symm using 1
  simp only [c, l, r]
  change mfderiv I I (fun y : G => y * g) x
      (mfderiv I I (fun y : G => x * y) 1 (nativeLieAdjoint (I := I) g v)) =
    mfderiv I I (fun y : G => y * g) (x * (g * 1 * g⁻¹))
      (mfderiv I I (fun y : G => x * y) (g * 1 * g⁻¹) (nativeLieAdjoint (I := I) g v))
  congr 2 <;> first | group | (congr 1; group)

 theorem nativeLieRightTranslation_pullback_invariant (g : G) (v : E) :
    mpullback I I (fun x : G => x * g) (mulInvariantVectorField (I := I) (G := G) v) =
      mulInvariantVectorField (I := I) (G := G) (nativeLieAdjoint (I := I) g v) := by
  funext x
  rw [mpullback_apply, nativeLieRightTranslation_inverse_mfderiv]
  have h := nativeLieRightTranslation_invariant_field (I := I) g⁻¹ (x * g)
    (nativeLieAdjoint (I := I) g v)
  rw [nativeLieAdjoint_inv_apply] at h
  convert! h using 1
  congr 1
  group

end Hindman168
