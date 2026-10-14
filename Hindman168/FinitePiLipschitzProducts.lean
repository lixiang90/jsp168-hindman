import Hindman168.CompactLipschitzAlgebra
import Mathlib.LinearAlgebra.Span.Basic

/-! Literal finite products of original coordinate Lipschitz observations.
Their COMPLEX linear span is a genuine star algebra on the full product
space; no projection metric bound is assumed. -/
namespace Hindman168
open scoped BigOperators Classical NNReal
variable {ι : Type*} [Fintype ι] (X : ι → Type*) [∀ i, MetricSpace (X i)] [∀ i, CompactSpace (X i)]

noncomputable def finitePiComplexProduct (F : ∀ i, C(X i,ℂ)) : C((∀ i, X i),ℂ) :=
  ∏ i, (F i).comp ⟨fun x => x i,continuous_apply i⟩

omit [∀ i, CompactSpace (X i)] in
theorem finite_pi_complex_product_apply (F : ∀ i, C(X i,ℂ)) (x : ∀ i, X i) :
    finitePiComplexProduct X F x=∏ i, F i (x i) := by
  simp only [finitePiComplexProduct,ContinuousMap.prod_apply,ContinuousMap.comp_apply,ContinuousMap.coe_mk]

omit [∀ i, CompactSpace (X i)] in
theorem finite_pi_complex_product_mul (F G : ∀ i, C(X i,ℂ)) :
    finitePiComplexProduct X (fun i => F i*G i)=finitePiComplexProduct X F*finitePiComplexProduct X G := by
  ext x
  simp only [finite_pi_complex_product_apply,ContinuousMap.mul_apply,Finset.prod_mul_distrib]

omit [∀ i, CompactSpace (X i)] in
theorem finite_pi_complex_product_star (F : ∀ i, C(X i,ℂ)) :
    finitePiComplexProduct X (fun i => star (F i))=star (finitePiComplexProduct X F) := by
  ext x
  simp only [finite_pi_complex_product_apply,ContinuousMap.star_apply,star_prod]

noncomputable def finitePiLipschitzProducts : Set C((∀ i, X i),ℂ) :=
  {f | ∃ F : ∀ i, C(X i,ℂ), (∀ i, ∃ K : ℝ≥0, LipschitzWith K (F i)) ∧ f=finitePiComplexProduct X F}

noncomputable def finitePiLipschitzProductSpan : Submodule ℂ C((∀ i, X i),ℂ) :=
  Submodule.span ℂ (finitePiLipschitzProducts X)

omit [∀ i, CompactSpace (X i)] in
theorem finite_pi_lipschitz_product_span_one : (1 : C((∀ i, X i),ℂ)) ∈ finitePiLipschitzProductSpan X := by
  apply Submodule.subset_span
  refine ⟨fun _ => 1,fun _ => ⟨0,LipschitzWith.of_dist_le_mul (fun _ _ => by simp)⟩,?_⟩
  ext x
  simp only [finite_pi_complex_product_apply,ContinuousMap.one_apply,Finset.prod_const_one]

theorem finite_pi_lipschitz_product_span_mul (F G : C((∀ i, X i),ℂ))
    (hF : F ∈ finitePiLipschitzProductSpan X) (hG : G ∈ finitePiLipschitzProductSpan X) :
    F*G ∈ finitePiLipschitzProductSpan X := by
  induction hF,hG using Submodule.span_induction₂ with
  | mem_mem f g hf hg =>
    obtain ⟨F,hF,rfl⟩ := hf
    obtain ⟨G,hG,rfl⟩ := hg
    rw [←finite_pi_complex_product_mul]
    apply Submodule.subset_span
    refine ⟨fun i => F i*G i,?_,rfl⟩
    intro i
    obtain ⟨K,hK⟩ := hF i
    obtain ⟨L,hL⟩ := hG i
    exact ⟨‖F i‖₊*L+K*‖G i‖₊,compact_lipschitz_mul (F i) (G i) K L hK hL⟩
  | zero_left g hg => simp only [zero_mul]; exact (finitePiLipschitzProductSpan X).zero_mem
  | zero_right f hf => simp only [mul_zero]; exact (finitePiLipschitzProductSpan X).zero_mem
  | add_left f g h hf hg hh ihf ihg =>
    rw [add_mul]; exact (finitePiLipschitzProductSpan X).add_mem ihf ihg
  | add_right f g h hf hg hh ihg ihh =>
    rw [mul_add]; exact (finitePiLipschitzProductSpan X).add_mem ihg ihh
  | smul_left c f g hf hg ih =>
    rw [smul_mul_assoc]; exact (finitePiLipschitzProductSpan X).smul_mem c ih
  | smul_right c f g hf hg ih =>
    rw [mul_smul_comm]; exact (finitePiLipschitzProductSpan X).smul_mem c ih

theorem finite_pi_lipschitz_product_span_star (F : C((∀ i, X i),ℂ))
    (hF : F ∈ finitePiLipschitzProductSpan X) : star F ∈ finitePiLipschitzProductSpan X := by
  induction hF using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨F,hF,rfl⟩ := hf
    rw [←finite_pi_complex_product_star]
    apply Submodule.subset_span
    refine ⟨fun i => star (F i),?_,rfl⟩
    intro i
    exact (compactLipschitzStarSubalgebra (X i)).star_mem' (hF i)
  | zero => simp only [star_zero]; exact (finitePiLipschitzProductSpan X).zero_mem
  | add f g hf hg ihf ihg =>
    rw [star_add]; exact (finitePiLipschitzProductSpan X).add_mem ihf ihg
  | smul c f hf ih =>
    rw [star_smul]; exact (finitePiLipschitzProductSpan X).smul_mem (star c) ih

noncomputable def finitePiLipschitzProductSubalgebra : Subalgebra ℂ C((∀ i, X i),ℂ) where
  carrier := finitePiLipschitzProductSpan X
  zero_mem' := (finitePiLipschitzProductSpan X).zero_mem
  one_mem' := finite_pi_lipschitz_product_span_one X
  add_mem' := (finitePiLipschitzProductSpan X).add_mem
  mul_mem' := fun {f g} hf hg => finite_pi_lipschitz_product_span_mul X f g hf hg
  algebraMap_mem' c := by
    rw [Algebra.algebraMap_eq_smul_one]
    exact (finitePiLipschitzProductSpan X).smul_mem c (finite_pi_lipschitz_product_span_one X)

noncomputable def finitePiLipschitzProductStarSubalgebra : StarSubalgebra ℂ C((∀ i, X i),ℂ) where
  toSubalgebra := finitePiLipschitzProductSubalgebra X
  star_mem' := fun {f} hf => finite_pi_lipschitz_product_span_star X f hf

end Hindman168
