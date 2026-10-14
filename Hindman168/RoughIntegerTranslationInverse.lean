import Hindman168.RoughMvAffineSubstitution

namespace Hindman168
open MvPolynomial

theorem rough_mv_translation_inverse {κ R : Type*} [CommRing R]
    (b : κ → R) (p : MvPolynomial κ R) :
    roughMvAffineSubstitution (fun j => -b j) (fun _ => 1)
      (roughMvAffineSubstitution b (fun _ => 1) p) = p := by
  have h : (roughMvAffineSubstitution (fun j => -b j) (fun _ => 1)).comp
      (roughMvAffineSubstitution b (fun _ => 1)) = RingHom.id (MvPolynomial κ R) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [roughMvAffineSubstitution]
    · intro j
      simp [roughMvAffineSubstitution]
  exact RingHom.congr_fun h p

theorem rough_mv_translation_degree {κ R : Type*} [CommRing R]
    (b : κ → R) (p : MvPolynomial κ R) :
    (roughMvAffineSubstitution b (fun _ => 1) p).totalDegree = p.totalDegree := by
  apply le_antisymm (roughMvAffineSubstitution_degree _ _ _)
  calc
    p.totalDegree = (roughMvAffineSubstitution (fun j => -b j) (fun _ => 1)
      (roughMvAffineSubstitution b (fun _ => 1) p)).totalDegree :=
      congrArg totalDegree (rough_mv_translation_inverse b p).symm
    _ ≤ _ := roughMvAffineSubstitution_degree _ _ _

end Hindman168
