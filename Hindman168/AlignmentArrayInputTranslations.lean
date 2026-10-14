import Hindman168.AlignmentPolynomialArrayGroup

namespace Hindman168

def alignmentArrayInputTranslation {σ G : Type*} [Group G] (v : σ → ℤ) :
    ((σ → ℤ) → G) ≃* ((σ → ℤ) → G) where
  toFun f u := f (u + v)
  invFun f u := f (u - v)
  left_inv f := by
    funext u
    change f ((u - v) + v) = f u
    rw [sub_add_cancel]
  right_inv f := by
    funext u
    change f ((u + v) - v) = f u
    rw [add_sub_cancel_right]
  map_mul' _ _ := rfl

theorem alignmentArrayInputTranslation_mem {σ G : Type*} [Group G]
    (v : σ → ℤ) {f : (σ → ℤ) → G} (hf : f ∈ alignmentPolynomialArrayGroup σ G) :
    alignmentArrayInputTranslation v f ∈ alignmentPolynomialArrayGroup σ G := by
  refine Subgroup.closure_induction (fun f hf => ?_) ?_
    (fun f h _ _ ihf ihh => ?_) (fun f _ ihf => ?_) hf
  · obtain ⟨j, g, p, hg, hp, rfl⟩ := hf
    have h := alignmentPolynomialArrayGroup_generator j g (alignmentPolynomialInputShift v p) hg
      ((alignmentPolynomialInputShift_degree v p).trans hp)
    change (fun u => g ^ MvPolynomial.eval (u + v) p) ∈ alignmentPolynomialArrayGroup σ G
    simpa only [alignmentPolynomialInputShift_eval] using h
  · exact (alignmentPolynomialArrayGroup σ G).one_mem
  · exact (alignmentPolynomialArrayGroup σ G).mul_mem ihf ihh
  · exact (alignmentPolynomialArrayGroup σ G).inv_mem ihf

def alignmentPolynomialArrayTranslation {σ G : Type*} [Group G] (v : σ → ℤ) :
    alignmentPolynomialArrayGroup σ G ≃* alignmentPolynomialArrayGroup σ G where
  toFun f := ⟨alignmentArrayInputTranslation v f.val, alignmentArrayInputTranslation_mem v f.property⟩
  invFun f := ⟨alignmentArrayInputTranslation (-v) f.val, alignmentArrayInputTranslation_mem (-v) f.property⟩
  left_inv f := by
    apply Subtype.ext
    funext u
    change f.val ((u + -v) + v) = f.val u
    rw [neg_add_cancel_right]
  right_inv f := by
    apply Subtype.ext
    funext u
    change f.val ((u + v) + -v) = f.val u
    rw [add_neg_cancel_right]
  map_mul' _ _ := rfl

theorem alignmentPolynomialArrayTranslation_eval {σ G : Type*} [Group G]
    (v u : σ → ℤ) (f : alignmentPolynomialArrayGroup σ G) :
    alignmentPolynomialArrayEvaluation u (alignmentPolynomialArrayTranslation v f) =
      alignmentPolynomialArrayEvaluation (u + v) f := rfl

end Hindman168
