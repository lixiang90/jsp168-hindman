import Hindman168.NativeFinitePiRestrictedCubeProjection

/-! Repeated product slots encode a COMPLETE marginal cube.  Reassembly is an
actual quotient homeomorphism; the binary-slot projection is not silently
identified with a cube orbit. -/
namespace Hindman168
universe u

variable {κ V : Type} [Fintype κ] [Fintype V] {s : ℕ}
  (D : κ → NativeNilmanifoldData.{u} s)

noncomputable def nativeFinitePiCubeReassembly :
    ((nativeFinitePiData (fun p : κ × V => D p.1)).G ⧸
      (nativeFinitePiData (fun p : κ × V => D p.1)).Γ) ≃ₜ
    (V → (nativeFinitePiData D).G ⧸ (nativeFinitePiData D).Γ) where
  toFun x z := (nativeFinitePiCosetHomeomorph D).symm
    (fun k => nativeFinitePiCosetHomeomorph (fun p : κ × V => D p.1) x (k,z))
  invFun x := (nativeFinitePiCosetHomeomorph (fun p : κ × V => D p.1)).symm
    (fun p => nativeFinitePiCosetHomeomorph D (x p.2) p.1)
  left_inv x := by
    apply (nativeFinitePiCosetHomeomorph (fun p : κ × V => D p.1)).injective
    simp only [Homeomorph.apply_symm_apply]
  right_inv x := by
    funext z
    simp only [Homeomorph.apply_symm_apply, Homeomorph.symm_apply_apply]
  continuous_toFun := continuous_pi (fun z =>
    (nativeFinitePiCosetHomeomorph D).symm.continuous.comp
      (continuous_pi (fun k => (continuous_apply (k,z)).comp
        (nativeFinitePiCosetHomeomorph (fun p : κ × V => D p.1)).continuous)))
  continuous_invFun :=
    (nativeFinitePiCosetHomeomorph (fun p : κ × V => D p.1)).symm.continuous.comp
      (continuous_pi (fun p => (continuous_apply p.1).comp
        ((nativeFinitePiCosetHomeomorph D).continuous.comp (continuous_apply p.2))))

theorem native_finite_pi_cube_reassembly_coordinate
    (x : (nativeFinitePiData (fun p : κ × V => D p.1)).G ⧸
      (nativeFinitePiData (fun p : κ × V => D p.1)).Γ) (k : κ) (z : V) :
    nativeFinitePiCosetCoordinate D k (nativeFinitePiCubeReassembly D x z) =
      nativeFinitePiCosetCoordinate (fun p : κ × V => D p.1) (k,z) x := by
  rw [← native_finite_pi_coset_homeomorph_apply D]
  change (nativeFinitePiCosetHomeomorph D)
    ((nativeFinitePiCosetHomeomorph D).symm _) k = _
  rw [Homeomorph.apply_symm_apply, native_finite_pi_coset_homeomorph_apply]

/-- Repeating every marginal coordinate at every vertex recovers the full restricted cube. -/
theorem native_finite_pi_repeated_projection_reassembly
    {ι : Type} [Fintype ι] (A : ι → NativeNilmanifoldData.{u} s) (index : κ → ι)
    (x : V → (nativeFinitePiData A).G ⧸ (nativeFinitePiData A).Γ) :
    nativeFinitePiCubeReassembly (A ∘ index)
      (nativeFinitePiRestrictedCubeProjection A (fun p : κ × V => index p.1) Prod.snd x) =
      fun z => nativeFinitePiCosetRestriction A index (x z) := by
  funext z
  apply (nativeFinitePiCosetHomeomorph (A ∘ index)).injective
  funext k
  rw [native_finite_pi_coset_homeomorph_apply,
    native_finite_pi_coset_homeomorph_apply,
    native_finite_pi_cube_reassembly_coordinate]
  exact (native_finite_pi_restricted_cube_projection_coordinate A
    (fun p : κ × V => index p.1) Prod.snd x (k,z)).trans
      (native_finite_pi_coset_restriction_coordinate A index (x z) k).symm

/-- Exact range transport for any one source orbit map; no image-filtration premise. -/
theorem native_finite_pi_repeated_projection_range
    {ι : Type} {X : Type*} [Fintype ι] (A : ι → NativeNilmanifoldData.{u} s) (index : κ → ι)
    (orbit : X → V → (nativeFinitePiData A).G ⧸ (nativeFinitePiData A).Γ) :
    nativeFinitePiCubeReassembly (A ∘ index) ''
      Set.range (nativeFinitePiRestrictedCubeProjection A
        (fun p : κ × V => index p.1) Prod.snd ∘ orbit) =
      Set.range (fun x z => nativeFinitePiCosetRestriction A index (orbit x z)) := by
  ext y
  constructor
  · rintro ⟨z, ⟨x, rfl⟩, rfl⟩
    exact ⟨x, (native_finite_pi_repeated_projection_reassembly A index (orbit x)).symm⟩
  · rintro ⟨x, rfl⟩
    exact ⟨_, ⟨x, rfl⟩, native_finite_pi_repeated_projection_reassembly A index (orbit x)⟩

end Hindman168
