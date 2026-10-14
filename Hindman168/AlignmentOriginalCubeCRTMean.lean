import Hindman168.AlignmentRetainedCubeResidue
import Hindman168.ComplexMassTranslation

/-! FULL original cube residue sampling is exactly its transformed CRT grid,
with the original endpoints and normalized complex means. No endpoint rounding
change, dense subsample, coprimality between factors or nonempty assumption. -/
namespace Hindman168
open FiniteMass
open scoped Classical

theorem alignment_box_class_residue_congr {κ : Type*} [Fintype κ]
    (lo hi a b : κ → ℤ) (q : ℤ) (h : ∀ j, Int.ModEq q (a j) (b j)) :
    alignmentBoxClass lo hi a q=alignmentBoxClass lo hi b q := by
  ext y
  simp only [alignmentBoxClass,Fintype.mem_piFinset,alignmentIntervalClass,Finset.mem_filter]
  constructor
  · intro hy j
    exact ⟨(hy j).1,(h j).symm.trans (hy j).2⟩
  · intro hy j
    exact ⟨(hy j).1,(h j).trans (hy j).2⟩

theorem alignment_original_cube_crt_complex_mean {κ : Type*} [Fintype κ]
    (M d tau : ℕ) (htau : 0 < tau) (hM : Nat.Coprime M tau) (hd : Nat.Coprime d tau)
    (p Y rho : ℤ) (hrho : ((tau : ℤ)*p) % M=rho)
    (lower upper : Option κ → ℝ) (ellResidue choice : Option κ → ℤ)
    (hchoice : ∀ j, Int.ModEq d (alignmentCubeCoordinate M tau p Y j (ellResidue j)) (choice j))
    (f : (Option κ → ℤ) → ℂ) :
    complexExpectation (uniformFinsetMass
      (alignmentBoxClass (fun j => ⌈lower j⌉) (fun j => ⌈upper j⌉) ellResidue d))
      (fun ell => f (fun j => alignmentCubeCoordinate M tau p Y j (ell j)))=
    complexExpectation (uniformFinsetMass (alignmentBoxClass
      (fun j => alignmentCubeCoordinate M tau p Y j ⌈lower j⌉)
      (fun j => alignmentCubeCoordinate M tau p Y j ⌈upper j⌉)
      (alignmentRetainedCubeResidue M d tau Y rho choice) (d*tau : ℕ))) f := by
  rw [complexExpectation_uniformFinset,complexExpectation_uniformFinset]
  rw [alignment_cube_box_mean M tau p Y d (by exact_mod_cast htau)]
  have hclass := alignment_retained_cube_vector_class M d tau htau hM hd (tau : ℤ) p Y rho
    (dvd_refl _) hrho choice ellResidue hchoice
  have hmul : (tau : ℤ)*(d : ℤ)=((d*tau : ℕ) : ℤ) := by rw [Nat.cast_mul]; ring
  rw [hmul]
  rw [←alignment_box_class_residue_congr _ _
    (alignmentRetainedCubeResidue M d tau Y rho choice)
    (fun j => alignmentCubeCoordinate M tau p Y j (ellResidue j)) (d*tau : ℕ) hclass]

end Hindman168
