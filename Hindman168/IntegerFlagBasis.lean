import Hindman168.IntegerComplementBasis
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.Dimension.Free

namespace Hindman168
open Module

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

theorem integer_basis_adapted_reindex {ι κ : Type*} (b : Basis ι R M) (e : ι ≃ κ)
    (T : Submodule R M) :
    Submodule.span R (b.reindex e '' {i | b.reindex e i ∈ T}) =
      Submodule.span R (b '' {i | b i ∈ T}) := by
  congr 1
  ext x
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨e.symm i, by simpa using hi, by simp⟩
  · rintro ⟨i, hi, rfl⟩
    refine ⟨e i, ?_, ?_⟩
    · simpa using hi
    · simp

theorem split_integer_flag_basis_exists [IsDomain R] [IsPrincipalIdealRing R]
    [Module.Finite R M] [Module.Free R M] (k : ℕ)
    (P : Fin k → Submodule R M) (hP : Antitone P)
    (hsplit : ∀ j, ∃ Q : Submodule R M, IsCompl (P j) Q) :
    ∃ n : ℕ, ∃ b : Basis (Fin n) R M,
      ∀ j, Submodule.span R (b '' {i | b i ∈ P j}) = P j := by
  classical
  induction k generalizing M with
  | zero =>
      refine ⟨Module.finrank R M, Module.finBasisOfFinrankEq R M rfl, ?_⟩
      intro j
      exact j.elim0
  | succ k ih =>
      let A := P 0
      let P' : Fin k → Submodule R A := fun j => (P j.succ).comap A.subtype
      have hP' : Antitone P' := fun i j hij => Submodule.comap_mono (hP (by simpa using hij))
      have hsplit' : ∀ j, ∃ Q : Submodule R A, IsCompl (P' j) Q := by
        intro j
        obtain ⟨Q, hQ⟩ := hsplit j.succ
        exact ⟨Q.comap A.subtype,
          Submodule.isCompl_comap_subtype_of_isCompl_of_le hQ (hP (Fin.zero_le _))⟩
      obtain ⟨n, a, ha⟩ := ih P' hP' hsplit'
      obtain ⟨Q, hQ⟩ := hsplit 0
      let c := Module.finBasisOfFinrankEq R Q rfl
      let b := integerComplementBasis A Q hQ a c
      let e := Fintype.equivFin (Fin n ⊕ Fin (Module.finrank R Q))
      refine ⟨_, b.reindex e, ?_⟩
      intro j
      rw [integer_basis_adapted_reindex]
      apply integer_complement_basis_adapted A Q hQ a c (P j) (hP (Fin.zero_le _))
      refine Fin.cases ?_ (fun j => ha j) j
      have htop : A.comap A.subtype = ⊤ := by ext x; simp
      change Submodule.span R (a '' {i | a i ∈ A.comap A.subtype}) = A.comap A.subtype
      rw [htop]
      simp only [Submodule.mem_top, Set.setOf_true, Set.image_univ]
      exact a.span_eq

end Hindman168
