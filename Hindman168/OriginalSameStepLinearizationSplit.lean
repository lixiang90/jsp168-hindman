import Mathlib.GroupTheory.SemidirectProduct

/-! Generic homomorphism and equivalence for a split group extension. -/

namespace Hindman168.OriginalSameStepLinearization

section SplitExtension

variable {P T E : Type*} [Group P] [Group T] [Group E]
  (φ : T →* MulAut P) (i : P →* E) (t : T →* E) (π : E →* T)
  (hconj : ∀ (u : T) (p : P), i (φ u p) = t u * i p * (t u)⁻¹)

/-- The multiplication map from an external semidirect product into a split extension. -/
def splitLift : (P ⋊[φ] T) →* E :=
  SemidirectProduct.lift i t (by intro u; ext p; exact hconj u p)

@[simp] theorem splitLift_apply (x : P ⋊[φ] T) :
    splitLift φ i t hconj x = i x.left * t x.right := rfl

/-- An explicit split exact sequence realizes the external semidirect product. -/
noncomputable def splitEquiv
    (hi : Function.Injective i) (hπi : ∀ p, π (i p) = 1)
    (hπt : ∀ u, π (t u) = u) (hker : ∀ e, π e = 1 → ∃ p, i p = e) :
    (P ⋊[φ] T) ≃* E :=
  MulEquiv.ofBijective (splitLift φ i t hconj) (by
    constructor
    · intro x y hxy
      have hr : x.right = y.right := by
        have h := congrArg π hxy
        simpa only [splitLift_apply, map_mul, hπi, hπt, one_mul] using h
      have hl : i x.left = i y.left := by
        apply mul_right_cancel (b := t y.right)
        simpa only [splitLift_apply, hr] using hxy
      exact SemidirectProduct.ext (hi hl) hr
    · intro e
      have he : π (e * (t (π e))⁻¹) = 1 := by simp [hπt]
      obtain ⟨p, hp⟩ := hker (e * (t (π e))⁻¹) he
      refine ⟨⟨p, π e⟩, ?_⟩
      simp only [splitLift_apply, hp, inv_mul_cancel_right])

@[simp] theorem splitEquiv_apply
    (hi : Function.Injective i) (hπi : ∀ p, π (i p) = 1)
    (hπt : ∀ u, π (t u) = u) (hker : ∀ e, π e = 1 → ∃ p, i p = e)
    (x : P ⋊[φ] T) :
    splitEquiv φ i t π hconj hi hπi hπt hker x = i x.left * t x.right := rfl

end SplitExtension

end Hindman168.OriginalSameStepLinearization
