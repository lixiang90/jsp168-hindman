import Hindman168.NativeLieLogCoordinateHaar
import Hindman168.NativeLatticeFilteredDiffeomorph
import Hindman168.NativeNilmanifoldData

/-! Actual bi-invariant Haar on every ORIGINAL native group, using its
original specified lattice basis and explicit Borel measurable structures.
This is group Haar; normalized Haar on nonnormal cosets still needs its construction. -/

namespace Hindman168
open MeasureTheory Measure
open scoped Manifold ContDiff
universe u

noncomputable def nativeNilmanifoldGroupHaar {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    Measure D.G :=
  nativeLieLogCoordinateHaar (I := D.I) (G := D.G) (nativeLatticeFilteredSmoothRealBasis (I := D.I) D.Γ)

theorem native_nilmanifold_group_haar_isHaar {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    IsHaarMeasure (nativeNilmanifoldGroupHaar D) :=
  native_log_coordinate_haar_isHaar (I := D.I) (nativeLatticeFilteredSmoothRealBasis (I := D.I) D.Γ)

theorem native_nilmanifold_group_haar_rightInvariant {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    IsMulRightInvariant (nativeNilmanifoldGroupHaar D) :=
  native_log_coordinate_haar_isRightInvariant (I := D.I) (nativeLatticeFilteredSmoothRealBasis (I := D.I) D.Γ)

theorem native_nilmanifold_group_haar_sigmaFinite {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    SigmaFinite (nativeNilmanifoldGroupHaar D) :=
  native_log_coordinate_haar_sigmaFinite (I := D.I) (nativeLatticeFilteredSmoothRealBasis (I := D.I) D.Γ)

end Hindman168
