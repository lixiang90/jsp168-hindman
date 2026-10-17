import Init

namespace AuditEndpointProbe

private def endpointProposition {P : Prop} (_proof : P) : Prop := P
theorem endpoint : ∀ n : Nat, n = n := fun _ => rfl
theorem endpointWithHiddenPremise (h : False) : True := False.elim h
theorem endpointWithImplicitPremise {h : False} : True := False.elim h
theorem endpointWithTypeclass (α : Type) [h : Nonempty α] : Nonempty α := h

example : endpointProposition (@endpoint) = (∀ n : Nat, n = n) := rfl
example : endpointProposition (@endpointWithHiddenPremise) = (False → True) := rfl
example : endpointProposition (@endpointWithImplicitPremise) = (False → True) := rfl
example : endpointProposition (@endpointWithTypeclass) =
    (∀ (α : Type), Nonempty α → Nonempty α) := rfl

example : True := by
  fail_if_success
    have : endpointProposition (@endpointWithHiddenPremise) = True := rfl
  fail_if_success
    have : endpointProposition (@endpointWithImplicitPremise) = True := rfl
  fail_if_success
    have : endpointProposition (@endpointWithTypeclass) = True := rfl
  exact True.intro

end AuditEndpointProbe
