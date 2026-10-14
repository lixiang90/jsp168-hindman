import Hindman168.DiscreteCocompactFundamentalDomain
import Hindman168.NativeNilmanifoldGroupHaar
import Hindman168.NativeNilmanifoldQuotientCovering

namespace Hindman168
open Set MeasureTheory Measure
open scoped Manifold ContDiff
universe u

theorem native_nilmanifold_fundamental_domain_exists {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    ∃ F : Set D.G, MeasurableSet F ∧ IsFundamentalDomain D.Γ.op F (nativeNilmanifoldGroupHaar D) ∧
      0 < nativeNilmanifoldGroupHaar D F ∧ nativeNilmanifoldGroupHaar D F < ⊤ ∧
      ∃ K : Set D.G, IsCompact K ∧ F ⊆ K := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  letI : BorelSpace D.G := ⟨rfl⟩
  letI : LocallyCompactSpace D.G := native_nilmanifold_group_locallyCompact D
  letI : Countable D.Γ := native_nilmanifold_lattice_countable D
  letI : IsHaarMeasure (nativeNilmanifoldGroupHaar D) := native_nilmanifold_group_haar_isHaar D
  letI : IsMulRightInvariant (nativeNilmanifoldGroupHaar D) := native_nilmanifold_group_haar_rightInvariant D
  exact discrete_cocompact_fundamental_domain D.Γ (nativeNilmanifoldGroupHaar D)

noncomputable def nativeNilmanifoldFundamentalDomain {s : ℕ} (D : NativeNilmanifoldData.{u} s) : Set D.G :=
  Classical.choose (native_nilmanifold_fundamental_domain_exists D)

theorem native_nilmanifold_fundamental_domain_spec {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    MeasurableSet (nativeNilmanifoldFundamentalDomain D) ∧
      IsFundamentalDomain D.Γ.op (nativeNilmanifoldFundamentalDomain D) (nativeNilmanifoldGroupHaar D) ∧
      0 < nativeNilmanifoldGroupHaar D (nativeNilmanifoldFundamentalDomain D) ∧
      nativeNilmanifoldGroupHaar D (nativeNilmanifoldFundamentalDomain D) < ⊤ ∧
      ∃ K : Set D.G, IsCompact K ∧ nativeNilmanifoldFundamentalDomain D ⊆ K :=
  Classical.choose_spec (native_nilmanifold_fundamental_domain_exists D)

end Hindman168
