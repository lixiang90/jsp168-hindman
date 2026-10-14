import Hindman168.NativeRationalFilteredRelativeSquare
import Hindman168.NativeRationalFilteredGroupGeometry
import Hindman168.RelativeLinearModelSpan
import Hindman168.NativeProductRationalInclusions

/-! Whole genuine rational relative-square layers and their ACTUAL original
product-lattice intersections, for arbitrary finite native Lie filtrations. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_rational_relative_model_rational {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ) (i : ℕ) :
    letI := nativeProductGroup_simplyConnected (I := D.I) (J := D.I) (G := D.G) (K := D.G)
    nativeLatticeRationalSubspace (E := D.E × D.E) (I := D.I.prod D.I)
      (D.Γ.prod D.Γ) (relativeLinearFiltration F.layer i) := by
  letI := nativeProductGroup_simplyConnected (I := D.I) (J := D.I) (G := D.G) (K := D.G)
  let W := nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ
  have hmodel : relativeLinearFiltration F.layer i =
      (F.layer i).map ((LinearMap.id : D.E →ₗ[ℝ] D.E).prod LinearMap.id) ⊔
        (F.layer (i+1)).map (LinearMap.inl ℝ D.E D.E) :=
    relative_linear_model_eq_span_maps _ _ (F.antitone (Nat.le_succ i))
  unfold nativeLatticeRationalSubspace
  apply le_antisymm
  · exact Submodule.span_le.mpr (fun _ hv => hv.1)
  · conv_lhs => rw [hmodel]
    apply sup_le
    · rw [← F.rational i,Submodule.map_span]
      apply Submodule.span_le.mpr
      rintro v ⟨w,hw,rfl⟩
      apply Submodule.subset_span
      exact ⟨relative_linear_model_diagonal_mem _ _ hw.1,native_product_rational_diagonal_mem D hw.2⟩
    · rw [← F.rational (i+1),Submodule.map_span]
      apply Submodule.span_le.mpr
      rintro v ⟨w,hw,rfl⟩
      apply Submodule.subset_span
      exact ⟨relative_linear_model_first_mem _ _ (F.antitone (Nat.le_succ i)) hw.1,
        native_product_rational_first_mem D hw.2⟩

theorem native_rational_relative_subalgebra_rational {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ) (i : ℕ) :
    letI := nativeProductGroup_simplyConnected (I := D.I) (J := D.I) (G := D.G) (K := D.G)
    nativeLatticeRationalSubspace (E := D.E × D.E) (I := D.I.prod D.I) (D.Γ.prod D.Γ)
      (nativeLieSubalgebraModel (nativeRationalRelativeNativeSubalgebra D F i)) := by
  letI := nativeProductGroup_simplyConnected (I := D.I) (J := D.I) (G := D.G) (K := D.G)
  rw [native_rational_relative_subalgebra_model]
  exact native_rational_relative_model_rational D F i

theorem native_rational_relative_lattice_discrete {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ) (i : ℕ) :
    DiscreteTopology ((D.Γ.prod D.Γ).comap (nativeRationalRelativeGroupLayer D F i).subtype) := by
  letI := productLattice_discrete D.Γ D.Γ
  rw [← native_rational_relative_native_subgroup_eq D F i]
  exact nativeLieLattice_intersection_discrete (D.Γ.prod D.Γ) _

theorem native_rational_relative_lattice_cocompact {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ) (i : ℕ) :
    CompactSpace ((nativeRationalRelativeGroupLayer D F i) ⧸
      (D.Γ.prod D.Γ).comap (nativeRationalRelativeGroupLayer D F i).subtype) := by
  letI := nativeProductGroup_simplyConnected (I := D.I) (J := D.I) (G := D.G) (K := D.G)
  letI := productLattice_discrete D.Γ D.Γ
  letI := productLattice_quotient_compact D.Γ D.Γ
  rw [← native_rational_relative_native_subgroup_eq D F i]
  exact nativeRationalLieLattice_quotient_compact (D.Γ.prod D.Γ) _ (native_rational_relative_subalgebra_rational D F i)

theorem native_rational_relative_contractible {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ) (i : ℕ) :
    ContractibleSpace (nativeRationalRelativeGroupLayer D F i) := by
  letI := nativeProductGroup_simplyConnected (I := D.I) (J := D.I) (G := D.G) (K := D.G)
  rw [← native_rational_relative_native_subgroup_eq D F i]
  exact nativeLieSubalgebraSubgroup_contractible _

theorem native_rational_relative_lattice_closed {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ) (i : ℕ) :
    IsClosed (((D.Γ.prod D.Γ).comap (nativeRationalRelativeGroupLayer D F i).subtype) :
      Set (nativeRationalRelativeGroupLayer D F i)) := by
  letI := native_rational_relative_lattice_discrete D F i
  exact discreteLattice_isClosed _

end Hindman168
