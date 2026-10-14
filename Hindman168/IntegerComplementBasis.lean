import Hindman168.IntegerSubspaceSplit
import Mathlib.LinearAlgebra.Basis.Prod

namespace Hindman168
open Module

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  {ι κ : Type*} (P Q : Submodule R M) (hPQ : IsCompl P Q)
  (a : Basis ι R P) (c : Basis κ R Q)

noncomputable def integerComplementBasis : Basis (ι ⊕ κ) R M :=
  (a.prod c).map (P.prodEquivOfIsCompl Q hPQ)

theorem integer_complement_basis_inl (i : ι) :
    integerComplementBasis P Q hPQ a c (Sum.inl i) = (a i : M) := by
  simp [integerComplementBasis, Basis.prod_apply, Submodule.coe_prodEquivOfIsCompl']

theorem integer_complement_basis_inr (i : κ) :
    integerComplementBasis P Q hPQ a c (Sum.inr i) = (c i : M) := by
  simp [integerComplementBasis, Basis.prod_apply, Submodule.coe_prodEquivOfIsCompl']

theorem integer_complement_basis_adapted (T : Submodule R M) (hTP : T ≤ P)
    (ha : Submodule.span R (a '' {i | a i ∈ T.comap P.subtype}) = T.comap P.subtype) :
    Submodule.span R (integerComplementBasis P Q hPQ a c ''
      {i | integerComplementBasis P Q hPQ a c i ∈ T}) = T := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨i, hi, rfl⟩
    exact hi
  · have hm : (T.comap P.subtype).map P.subtype = T :=
      by rw [Submodule.map_comap_subtype, inf_eq_right.mpr hTP]
    have hs : Submodule.span R (P.subtype '' (a '' {i | a i ∈ T.comap P.subtype})) = T := by
      rw [← Submodule.map_span, ha, hm]
    calc
      T = Submodule.span R (P.subtype '' (a '' {i | a i ∈ T.comap P.subtype})) := hs.symm
      _ ≤ _ := Submodule.span_mono (by
        rintro x ⟨y, ⟨i, hi, rfl⟩, rfl⟩
        refine ⟨Sum.inl i, ?_, ?_⟩
        · change integerComplementBasis P Q hPQ a c (Sum.inl i) ∈ T
          rw [integer_complement_basis_inl]
          exact hi
        · exact integer_complement_basis_inl P Q hPQ a c i)

end Hindman168
