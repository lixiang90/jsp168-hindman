import Hindman168.RoughNativeProductMvPolynomial
import Hindman168.RoughVectorMvCoordinates
import Hindman168.RoughNativeKernelFactorization
import Mathlib.Algebra.MvPolynomial.CommRing

namespace Hindman168
open scoped Manifold ContDiff

variable {σ E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]

noncomputable def roughNativeKernelLogPolynomial (V : E) (a m : MvPolynomial σ ℝ)
    (p : RoughVectorMvPolynomial σ E) : RoughVectorMvPolynomial σ E :=
  roughNativeProductMvPolynomial (I := I) (G := G)
    (roughNativeProductMvPolynomial (I := I) (G := G) [(-a,V)] p) [(-m,V)]

theorem roughNativeKernelLogPolynomial_degree (V : E) (a m : MvPolynomial σ ℝ)
    {p : RoughVectorMvPolynomial σ E} {d : ℕ} (ha : a.totalDegree ≤ d)
    (hm : m.totalDegree ≤ d) (hp : RoughVectorMvDegreeLE p d) :
    RoughVectorMvDegreeLE (roughNativeKernelLogPolynomial (I := I) (G := G) V a m p)
      ((((Group.nilpotencyClass G * Group.nilpotencyClass G + 1) ^
        (Group.nilpotencyClass G + 1)) ^ 2) * d) := by
  let c := (Group.nilpotencyClass G * Group.nilpotencyClass G + 1) ^
    (Group.nilpotencyClass G + 1)
  have hc : 1 ≤ c := Nat.one_le_pow _ _ (by omega)
  have hleft : RoughVectorMvDegreeLE [(-a,V)] d := by
    intro b hb
    simpa only [List.mem_singleton.mp hb, MvPolynomial.totalDegree_neg] using ha
  have hright : RoughVectorMvDegreeLE [(-m,V)] (c*d) := by
    intro b hb
    simp only [List.mem_singleton.mp hb, MvPolynomial.totalDegree_neg]
    exact hm.trans (by nlinarith)
  have h := roughNativeProductMvPolynomial_degree (I := I) (G := G)
    (roughNativeProductMvPolynomial_degree (I := I) (G := G) hleft hp) hright
  simpa only [roughNativeKernelLogPolynomial, c, pow_two, Nat.mul_assoc] using h

variable [Module ℚ E] [CompleteSpace E] [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G]
  [Group.IsNilpotent G] [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

theorem roughNativeKernelLogPolynomial_eval (V : E) (a m : MvPolynomial σ ℝ)
    (p : RoughVectorMvPolynomial σ E) (P : (σ → ℝ) → G)
    (hp : ∀ x, roughVectorMvEval p x = nativeLieGlobalLogarithm (E := E) (I := I) (P x))
    (x : σ → ℝ) :
    roughVectorMvEval (roughNativeKernelLogPolynomial (I := I) (G := G) V a m p) x =
      nativeLieGlobalLogarithm (E := E) (I := I) (G := G)
        (roughNativeKernelFactor (I := I) V (MvPolynomial.eval x a) (MvPolynomial.eval x m) (P x)) := by
  let exp : E → G := fun v => nativeLieExponential (I := I) (G := G) v
  let log : G → E := nativeLieGlobalLogarithm (E := E) (I := I) (G := G)
  let l : RoughVectorMvPolynomial σ E := [(-a,V)]
  let r : RoughVectorMvPolynomial σ E := [(-m,V)]
  let q := roughNativeProductMvPolynomial (I := I) (G := G) l p
  have hl : roughVectorMvEval l x = -(MvPolynomial.eval x a • V) := by
    simp [l, roughVectorMvEval]
  have hr : roughVectorMvEval r x = -(MvPolynomial.eval x m • V) := by
    simp [r, roughVectorMvEval]
  have he : exp (roughVectorMvEval p x) = P x :=
    (congrArg exp (hp x)).trans (nativeLieExponential_globalLogarithm (E := E) (I := I) (P x))
  have hq : exp (roughVectorMvEval q x) = exp (-(MvPolynomial.eval x a • V)) * P x := by
    calc
      _ = exp (log (exp (roughVectorMvEval l x) * exp (roughVectorMvEval p x))) :=
        congrArg exp (roughNativeProductMvPolynomial_eval (I := I) (G := G) l p x)
      _ = exp (roughVectorMvEval l x) * exp (roughVectorMvEval p x) :=
        nativeLieExponential_globalLogarithm (E := E) (I := I) _
      _ = _ := by rw [hl, he]
  calc
    _ = log (exp (roughVectorMvEval q x) * exp (roughVectorMvEval r x)) :=
      roughNativeProductMvPolynomial_eval (I := I) (G := G) q r x
    _ = _ := by rw [hq, hr]; rfl

theorem roughNativeKernelLogPolynomial_coordinate (V : E) (a m : MvPolynomial σ ℝ)
    (p : RoughVectorMvPolynomial σ E) (P : (σ → ℝ) → G)
    (hp : ∀ x, roughVectorMvEval p x = nativeLieGlobalLogarithm (E := E) (I := I) (P x))
    (d : ℕ) (ha : a.totalDegree ≤ d) (hm : m.totalDegree ≤ d)
    (hpd : RoughVectorMvDegreeLE p d) (ell : E →ₗ[ℝ] ℝ) :
    ∃ q : MvPolynomial σ ℝ,
      q.totalDegree ≤ ((((Group.nilpotencyClass G * Group.nilpotencyClass G + 1) ^
        (Group.nilpotencyClass G + 1)) ^ 2) * d) ∧
      ∀ x, MvPolynomial.eval x q = ell (nativeLieGlobalLogarithm (E := E) (I := I)
        (roughNativeKernelFactor (I := I) V (MvPolynomial.eval x a) (MvPolynomial.eval x m) (P x))) := by
  refine ⟨roughVectorMvProjection ell (roughNativeKernelLogPolynomial (I := I) (G := G) V a m p),
    roughVectorMvProjection_degree ell (roughNativeKernelLogPolynomial_degree V a m ha hm hpd), ?_⟩
  intro x
  rw [roughVectorMvProjection_eval, roughNativeKernelLogPolynomial_eval V a m p P hp]

theorem roughNativeKernelLogPolynomial_of_coordinates {n : ℕ}
    (b : Module.Basis (Fin n) ℝ E) (p : Fin n → MvPolynomial σ ℝ)
    (P : (σ → ℝ) → G)
    (hp : ∀ x i, MvPolynomial.eval x (p i) =
      b.repr (nativeLieGlobalLogarithm (E := E) (I := I) (P x)) i)
    (V : E) (a m : MvPolynomial σ ℝ) (d : ℕ)
    (ha : a.totalDegree ≤ d) (hm : m.totalDegree ≤ d) (hd : ∀ i, (p i).totalDegree ≤ d)
    (ell : E →ₗ[ℝ] ℝ) :
    ∃ q : MvPolynomial σ ℝ,
      q.totalDegree ≤ ((((Group.nilpotencyClass G * Group.nilpotencyClass G + 1) ^
        (Group.nilpotencyClass G + 1)) ^ 2) * d) ∧
      ∀ x, MvPolynomial.eval x q = ell (nativeLieGlobalLogarithm (E := E) (I := I)
        (roughNativeKernelFactor (I := I) V (MvPolynomial.eval x a) (MvPolynomial.eval x m) (P x))) := by
  exact roughNativeKernelLogPolynomial_coordinate V a m (roughVectorMvFromBasis b p) P
    (roughVectorMvFromBasis_represents b p _ hp) d ha hm (roughVectorMvFromBasis_degree b p hd) ell

theorem roughNativeKernelLogPolynomial_mem
    (S : LieSubalgebra ℝ (GroupLieAlgebra I G)) (F : E →ₗ[ℝ] ℝ)
    (hF : ∀ v ∈ nativeLieSubalgebraModel S, ∀ w ∈ nativeLieSubalgebraModel S,
      F (nativeLieAdjointDifferential (I := I) (G := G) v w) = 0)
    (V : E) (hV : V ∈ nativeLieSubalgebraModel S) (hFV : F V = 1)
    (a m : MvPolynomial σ ℝ) (p : RoughVectorMvPolynomial σ E) (P : (σ → ℝ) → G)
    (hp : ∀ x, roughVectorMvEval p x = nativeLieGlobalLogarithm (E := E) (I := I) (P x))
    (hP : ∀ x, P x ∈ nativeLieSubalgebraSubgroup (E := E) S)
    (hchi : ∀ x, nativeLieLogarithmCharacter (I := I) (G := G) F (P x) =
      MvPolynomial.eval x a + MvPolynomial.eval x m) (x : σ → ℝ) :
    roughVectorMvEval (roughNativeKernelLogPolynomial (I := I) (G := G) V a m p) x ∈
      nativeLieSubalgebraModel (nativeLieCharacterKernel S F hF) := by
  rw [roughNativeKernelLogPolynomial_eval V a m p P hp]
  apply (nativeLieSubalgebraSubgroup_mem_globalLogarithm_iff _ _).mp
  exact rough_native_kernel_factor_mem S F hF V hV hFV _ _ (P x) (hP x) (hchi x)

theorem roughNativeKernelLogPolynomial_intrinsic_coordinate
    (S : LieSubalgebra ℝ (GroupLieAlgebra I G)) (F : E →ₗ[ℝ] ℝ)
    (hF : ∀ v ∈ nativeLieSubalgebraModel S, ∀ w ∈ nativeLieSubalgebraModel S,
      F (nativeLieAdjointDifferential (I := I) (G := G) v w) = 0)
    (V : E) (hV : V ∈ nativeLieSubalgebraModel S) (hFV : F V = 1)
    (a m : MvPolynomial σ ℝ) (p : RoughVectorMvPolynomial σ E) (P : (σ → ℝ) → G)
    (hp : ∀ x, roughVectorMvEval p x = nativeLieGlobalLogarithm (E := E) (I := I) (P x))
    (hP : ∀ x, P x ∈ nativeLieSubalgebraSubgroup (E := E) S)
    (hchi : ∀ x, nativeLieLogarithmCharacter (I := I) (G := G) F (P x) =
      MvPolynomial.eval x a + MvPolynomial.eval x m)
    (d : ℕ) (ha : a.totalDegree ≤ d) (hm : m.totalDegree ≤ d)
    (hd : RoughVectorMvDegreeLE p d)
    (ell : nativeLieSubalgebraModel (nativeLieCharacterKernel S F hF) →ₗ[ℝ] ℝ) :
    ∃ q : MvPolynomial σ ℝ,
      q.totalDegree ≤ ((((Group.nilpotencyClass G * Group.nilpotencyClass G + 1) ^
        (Group.nilpotencyClass G + 1)) ^ 2) * d) ∧
      ∀ x, MvPolynomial.eval x q = ell
        ⟨roughVectorMvEval (roughNativeKernelLogPolynomial (I := I) (G := G) V a m p) x,
          roughNativeKernelLogPolynomial_mem S F hF V hV hFV a m p P hp hP hchi x⟩ := by
  exact roughVectorMv_subspace_coordinate _ _ _
    (roughNativeKernelLogPolynomial_degree V a m ha hm hd)
    (roughNativeKernelLogPolynomial_mem S F hF V hV hFV a m p P hp hP hchi) ell

end Hindman168
