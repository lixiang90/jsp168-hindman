import Hindman168.NativeSequentialConvergentDescent
import Hindman168.NativeRationalCompactRepresentatives

/-! Initial compact normalization for arbitrary adapted sequences INSIDE
the actual rational subgroup. Compact representatives are derived from its
original lattice intersection. The right lattice factor stays on the right;
the lattice is never assumed normal. -/
namespace Hindman168
open Set
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeSubgroupConstantNormalization {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial Unit D.E) (c gamma : D.G) :
    RoughVectorMvPolynomial Unit D.E :=
  roughVectorMvZeroTrim (roughNativeProductMvPolynomial (I := D.I) (G := D.G)
    (roughVectorMvConstant (-nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) c))
    (roughNativeProductMvPolynomial (I := D.I) (G := D.G) p
      (roughVectorMvConstant (-nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) gamma))))

theorem native_subgroup_constant_normalization_weighted {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree F.layer p 0)
    (c gamma : D.G) (hc : c ∈ nativeRationalSubgroupLayer D F 0)
    (hgamma : gamma ∈ nativeRationalSubgroupLayer D F 0) :
    RoughVectorMvWeightedDegree F.layer (nativeSubgroupConstantNormalization D p c gamma) 0 :=
  rough_vector_zero_trim_weighted _ (native_rational_subgroup_product_weighted D F
    (rough_vector_constant_weighted F.layer ((F.layer 0).neg_mem
      ((native_rational_subgroup_layer_logarithm_iff D F 0 c).mp hc)))
    (native_rational_subgroup_product_weighted D F hp
      (rough_vector_constant_weighted F.layer ((F.layer 0).neg_mem
        ((native_rational_subgroup_layer_logarithm_iff D F 0 gamma).mp hgamma)))))

theorem native_subgroup_constant_normalization_exponential {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial Unit D.E) (c gamma : D.G) (b : ℝ) :
    nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
      (roughVectorMvEval (E := D.E) (nativeSubgroupConstantNormalization D p c gamma) (fun _ => b)) =
      c⁻¹ * nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
        (roughVectorMvEval (E := D.E) p (fun _ => b)) * gamma⁻¹ := by
  let exp : D.E → D.G := nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
  let log : D.G → D.E := nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G)
  have hneg (g : D.G) : exp (-log g) = g⁻¹ :=
    (nativeLieExponential_neg (E := D.E) (I := D.I) (G := D.G) (log g)).trans
      (congrArg Inv.inv (nativeLieExponential_globalLogarithm (E := D.E) (I := D.I) (G := D.G) g))
  rw [nativeSubgroupConstantNormalization, rough_vector_zero_trim_eval,
    roughNativeProductMvPolynomial_eval, nativeLieExponential_globalLogarithm,
    roughNativeProductMvPolynomial_eval, nativeLieExponential_globalLogarithm,
    rough_vector_constant_eval, rough_vector_constant_eval]
  exact (congrArg₂ (fun a d : D.G => a * (exp (roughVectorMvEval (E := D.E) p (fun _ => b)) * d))
    (hneg c) (hneg gamma)).trans (mul_assoc _ _ _).symm

theorem native_subgroup_constant_normalization_zero {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial Unit D.E) (c gamma : D.G)
    (h : nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
      (roughVectorMvEval (E := D.E) p (fun _ => (0 : ℝ))) = c * gamma) :
    roughVectorMvEval (nativeSubgroupConstantNormalization D p c gamma) (fun _ => (0 : ℝ)) = 0 := by
  have he := native_subgroup_constant_normalization_exponential D p c gamma 0
  have hg := congrArg (fun g : D.G => c⁻¹ * g * gamma⁻¹) h
  have he1 : nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
      (roughVectorMvEval (E := D.E) (nativeSubgroupConstantNormalization D p c gamma) (fun _ => (0 : ℝ))) = 1 :=
    he.trans (hg.trans (by group))
  exact nativeLieExponential_injective (E := D.E) (I := D.I) (G := D.G)
    (he1.trans (nativeLieExponential_zero (E := D.E) (I := D.I) (G := D.G)).symm)

theorem native_subgroup_constant_normalization_recovery {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial Unit D.E) (c gamma : D.G) (b : ℝ) :
    nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
      (roughVectorMvEval (E := D.E) p (fun _ => b)) =
      c * nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
        (roughVectorMvEval (E := D.E) (nativeSubgroupConstantNormalization D p c gamma) (fun _ => b)) * gamma := by
  have he := native_subgroup_constant_normalization_exponential D p c gamma b
  have hg := congrArg (fun g : D.G => c * g * gamma) he
  exact (by group : nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
    (roughVectorMvEval (E := D.E) p (fun _ => b)) =
      c * (c⁻¹ * nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
        (roughVectorMvEval (E := D.E) p (fun _ => b)) * gamma⁻¹) * gamma).trans hg.symm

theorem native_subgroup_sequence_compact_normalization {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (p : ℕ → RoughVectorMvPolynomial Unit D.E) (hp : ∀ n, RoughVectorMvWeightedDegree F.layer (p n) 0) :
    ∃ K : Set D.G, IsCompact K ∧ K ⊆ (nativeRationalSubgroupLayer D F 0 : Set D.G) ∧
      ∃ c gamma : ℕ → D.G, ∃ q : ℕ → RoughVectorMvPolynomial Unit D.E,
        ∀ n, c n ∈ K ∧ gamma n ∈ D.Γ ∧ RoughVectorMvWeightedDegree F.layer (q n) 0 ∧
          roughVectorMvEval (q n) (fun _ => (0 : ℝ)) = 0 ∧ ∀ b : ℝ,
            nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
              (roughVectorMvEval (E := D.E) (p n) (fun _ => b)) =
              c n * nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
                (roughVectorMvEval (E := D.E) (q n) (fun _ => b)) * gamma n := by
  classical
  obtain ⟨K,hK,hSub,hRep⟩ := nativeRationalLieSubalgebra_compact_representatives
    (E := D.E) (I := D.I) D.Γ (nativeRationalSubgroupLayerAlgebra D F 0) (F.rational 0)
  let g (n : ℕ) : D.G := nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
    (roughVectorMvEval (E := D.E) (p n) (fun _ => (0 : ℝ)))
  have hg (n : ℕ) : g n ∈ nativeRationalSubgroupLayer D F 0 :=
    native_rational_subgroup_layer_exp_mem D F 0 (rough_vector_weighted_eval F.layer F.antitone (hp n) _)
  choose c hc gamma hgamma hFactor using (fun n => hRep (g n) (hg n))
  have hgammaSub (n : ℕ) : gamma n ∈ nativeRationalSubgroupLayer D F 0 := by
    have he : gamma n = (c n)⁻¹ * g n := by rw [hFactor n]; group
    rw [he]
    exact (nativeRationalSubgroupLayer D F 0).mul_mem
      ((nativeRationalSubgroupLayer D F 0).inv_mem (hSub (hc n))) (hg n)
  let q (n : ℕ) := nativeSubgroupConstantNormalization D (p n) (c n) (gamma n)
  refine ⟨K,hK,hSub,c,gamma,q,?_⟩
  intro n
  exact ⟨hc n,hgamma n,
    native_subgroup_constant_normalization_weighted D F (p n) (hp n) (c n) (gamma n) (hSub (hc n)) (hgammaSub n),
    native_subgroup_constant_normalization_zero D (p n) (c n) (gamma n) (hFactor n),
    native_subgroup_constant_normalization_recovery D (p n) (c n) (gamma n)⟩

end Hindman168
