import Hindman168.NativeFourierPairInvariance
import Hindman168.CentralSubgroupFactorObservable

/-! Genuine continuous descent of same-frequency pair to the ACTUAL
diagonal-center quotient/image lattice. No step decrease is asserted. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] diagonal_center_normal

abbrev nativeDiagonalFactorSpace {s : ℕ} (D : NativeNilmanifoldData.{u} s) :=
  (((D.G × D.G) ⧸ diagonalCenterSubgroup D.G) ⧸
    (D.Γ.prod D.Γ).map (QuotientGroup.mk' (diagonalCenterSubgroup D.G)))

def nativeDiagonalFactorMap {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    ((D.G × D.G) ⧸ D.Γ.prod D.Γ) → nativeDiagonalFactorSpace D :=
  centralSubgroupFactorMap (diagonalCenterSubgroup D.G) (D.Γ.prod D.Γ)

theorem native_diagonal_factor_map_openQuotient {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    IsOpenQuotientMap (nativeDiagonalFactorMap D) :=
  central_subgroup_factor_map_openQuotient _ _

theorem native_diagonal_factor_compact {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    CompactSpace (nativeDiagonalFactorSpace D) := by
  letI := productLattice_quotient_compact D.Γ D.Γ
  exact central_subgroup_factor_compact _ _

noncomputable def nativeFourierPairFactor {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (k : nativeNilmanifoldCenterIndex D → ℤ) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    C(D.G ⧸ D.Γ, ℂ) → C(nativeDiagonalFactorSpace D, ℂ) := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  intro F
  exact centralSubgroupFactorObservable _ _ (diagonal_center_le_center D.G)
    (nativeFourierPairObservable D k F) (native_fourier_pair_subgroup_invariant D k F)

theorem native_fourier_pair_factor_apply {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (k : nativeNilmanifoldCenterIndex D → ℤ) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ (F : C(D.G ⧸ D.Γ, ℂ)) (q : (D.G × D.G) ⧸ D.Γ.prod D.Γ),
      nativeFourierPairFactor D k F (nativeDiagonalFactorMap D q) = nativeFourierPairObservable D k F q := by
  intro F q
  exact central_subgroup_factor_observable_apply _ _ (diagonal_center_le_center D.G) _ _ q

theorem native_fourier_pair_factor_unique {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (k : nativeNilmanifoldCenterIndex D → ℤ) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ (F : C(D.G ⧸ D.Γ, ℂ)) (K : C(nativeDiagonalFactorSpace D, ℂ)),
      (∀ q, K (nativeDiagonalFactorMap D q) = nativeFourierPairObservable D k F q) →
        K = nativeFourierPairFactor D k F := by
  intro F K hK
  exact central_subgroup_factor_observable_unique _ _ (diagonal_center_le_center D.G) _ _ K hK

end Hindman168
