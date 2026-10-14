import Hindman168.RoughNativeKernelLogPolynomial
import Hindman168.NativeNilmanifoldData

namespace Hindman168
universe u

def roughKernelDegreeFactor (s : ℕ) : ℕ := ((s*s+1)^(s+1))^2

theorem roughKernelDegreeFactor_mono {a b : ℕ} (h : a ≤ b) :
    roughKernelDegreeFactor a ≤ roughKernelDegreeFactor b := by
  apply pow_le_pow_left'
  apply (pow_le_pow_left' (show a*a+1 ≤ b*b+1 by nlinarith) (a+1)).trans
  exact pow_le_pow_right' (by omega : 1 ≤ b*b+1) (by omega : a+1 ≤ b+1)

theorem rough_native_kernel_degree_uniform {σ E : Type*} {s d : ℕ}
    (D : NativeNilmanifoldData.{u} s) {p : RoughVectorMvPolynomial σ E}
    (hp : RoughVectorMvDegreeLE p (roughKernelDegreeFactor (Group.nilpotencyClass D.G)*d)) :
    RoughVectorMvDegreeLE p (roughKernelDegreeFactor s*d) := by
  intro a ha
  exact (hp a ha).trans (Nat.mul_le_mul_right d (roughKernelDegreeFactor_mono D.step_le))

end Hindman168
