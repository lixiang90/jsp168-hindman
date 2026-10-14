import Hindman168.WeightedShearVectorProjection
import Hindman168.WeightedShearAction
import Hindman168.RoughVectorMvSubstitution

/-!
Filtration-preserving linear maps preserve the strict coordinate inequalities
needed for the joint lift `u ↦ u + R(T(Pu)-Pu)`.  Both the change of variables
and the output projection are actual polynomial operations.
-/

namespace Hindman168
open MvPolynomial Module
open scoped BigOperators

/-- Polynomial substitutions respecting coordinate weights preserve every weighted degree bound. -/
theorem weightedShearDegreeLE_substitution {σ τ : Type*}
    (w : σ → ℕ) (v : τ → ℕ) (q : σ → MvPolynomial τ ℝ)
    (hq : ∀ i, q i ∈ weightedShearDegreeLE v (w i))
    {d : ℤ} {p : MvPolynomial σ ℝ} (hp : p ∈ weightedShearDegreeLE w d) :
    MvPolynomial.aeval q p ∈ weightedShearDegreeLE v d := by
  classical
  have hmono (a : σ →₀ ℕ) (r : ℝ) :
      MvPolynomial.aeval q (monomial a r) ∈ weightedShearDegreeLE v (Finsupp.weight w a) := by
    have hcoord (i : σ) : WeightedShearApprox v 0 (w i) (q i) (q i) :=
      ⟨hq i, hq i, by simp⟩
    have hprod := WeightedShearApprox.prod a.support (fun i => (a i : ℤ)*(w i : ℤ))
      (fun i => q i ^ a i) (fun i => q i ^ a i) (fun i _ => (hcoord i).pow (a i))
    have h := ((WeightedShearApprox.refl_C v 0 r).mul hprod).1
    have hdeg : (∑ i ∈ a.support, (a i : ℤ)*(w i : ℤ)) = (Finsupp.weight w a : ℤ) := by
      simp only [Finsupp.weight_apply, Finsupp.sum, nsmul_eq_mul,
        Nat.cast_sum, Nat.cast_mul, Nat.cast_id]
    rw [zero_add, hdeg] at h
    simpa only [MvPolynomial.aeval_monomial, MvPolynomial.algebraMap_eq, Finsupp.prod] using h
  rw [p.as_sum, map_sum]
  apply Submodule.sum_mem
  intro a ha
  exact weightedShearDegreeLE_mono v (hp a ha) (hmono a (p.coeff a))

/-- Coordinate substitution retains the exact vector filtration offset. -/
theorem weightedShearVector_substitution {σ τ E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (w : σ → ℕ) (v : τ → ℕ) (q : σ → MvPolynomial τ ℝ)
    (hq : ∀ i, q i ∈ weightedShearDegreeLE v (w i))
    (F : ℕ → Submodule ℝ E) (hF : Antitone F)
    {p : RoughVectorMvPolynomial σ E} {k : ℕ}
    (hp : AffineShearWeightedVector w F p k) :
    AffineShearWeightedVector v F (roughVectorMvSubstitution q p) k := by
  classical
  intro a ha
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
  have hdeg := weightedShearDegreeLE_substitution w v q hq (weightedShearDegreeLE_self w b.1)
  have hnat : (MvPolynomial.aeval q b.1).weightedTotalDegree v ≤ b.1.weightedTotalDegree w := by
    unfold MvPolynomial.weightedTotalDegree
    apply Finset.sup_le
    intro a ha
    exact_mod_cast hdeg a ha
  apply hF _ (hp b hb)
  exact Nat.add_le_add_right hnat k

/-- The general coordinate-projection estimate, including degree offset zero. -/
theorem weightedShearVector_projection_drop {σ E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (w : σ → ℕ) (F : ℕ → Submodule ℝ E) (hF : Antitone F)
    (ell : E →ₗ[ℝ] ℝ) (j k : ℕ) (hell : ∀ z ∈ F (j+1), ell z = 0)
    {p : RoughVectorMvPolynomial σ E} (hp : AffineShearWeightedVector w F p k) :
    roughVectorMvProjection ell p ∈ weightedShearDegreeLE w ((j : ℤ)-k) := by
  induction p with
  | nil => exact (weightedShearDegreeLE w ((j : ℤ)-k)).zero_mem
  | cons a p ih =>
      change a.1*C (ell a.2)+roughVectorMvProjection ell p ∈ _
      apply Submodule.add_mem
      · by_cases hd : a.1.weightedTotalDegree w+k ≤ j
        · exact weightedShearDegreeLE_mono w (by omega)
            (weightedShearDegreeLE_mul w (weightedShearDegreeLE_self w a.1)
              (weightedShearDegreeLE_C w (ell a.2)))
        · have hz : ell a.2 = 0 := hell _ (hF (by omega) (hp a List.mem_cons_self))
          simp only [hz, map_zero, mul_zero, Submodule.zero_mem]
      · exact ih (fun a ha => hp a (List.mem_cons_of_mem _ ha))

variable {E J : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup J] [NormedSpace ℝ J]

/-- The actual polynomial coordinate expressions of a linear projection. -/
noncomputable def weightedShearProjectionCoordinates {n m : ℕ}
    (b : Basis (Fin n) ℝ E) (c : Basis (Fin m) ℝ J) (P : E →ₗ[ℝ] J) :
    Fin m → MvPolynomial (Fin n) ℝ :=
  fun i => roughVectorMvProjection (c.coord i)
    (roughVectorMvLinearMap P (roughVectorMvFromBasis b (fun j => X j)))

theorem weightedShearProjectionCoordinates_degree {n m : ℕ}
    (w : Fin n → ℕ) (v : Fin m → ℕ)
    (F : ℕ → Submodule ℝ E) (H : ℕ → Submodule ℝ J) (hH : Antitone H)
    (b : Basis (Fin n) ℝ E) (c : Basis (Fin m) ℝ J)
    (hb : ∀ i, b i ∈ F (w i))
    (hc : ∀ i z, z ∈ H (v i+1) → c.coord i z = 0)
    (P : E →ₗ[ℝ] J) (hP : ∀ k z, z ∈ F k → P z ∈ H k) (i : Fin m) :
    weightedShearProjectionCoordinates b c P i ∈ weightedShearDegreeLE w (v i) := by
  have hvec := weightedShearVector_linearMap w F H P 0
    (fun k z hz => by simpa only [Nat.add_zero] using hP k z hz)
    (weightedShearVector_basis w F b hb)
  simpa only [weightedShearProjectionCoordinates, Int.natCast_zero, sub_zero] using
    weightedShearVector_projection_drop w H hH (c.coord i) (v i) 0 (hc i) hvec

theorem weightedShearProjectionCoordinates_eval {n m : ℕ}
    (b : Basis (Fin n) ℝ E) (c : Basis (Fin m) ℝ J) (P : E →ₗ[ℝ] J)
    (x : Fin n → ℝ) (i : Fin m) :
    MvPolynomial.eval x (weightedShearProjectionCoordinates b c P i) =
      c.equivFun (P (b.equivFun.symm x)) i := by
  rw [weightedShearProjectionCoordinates, roughVectorMvProjection_eval,
    roughVectorMvLinearMap_eval, weightedShearVector_basis_eval]
  rfl

/-- A family of strictly weighted coordinate polynomials is a vector correction of offset one. -/
theorem weightedShearVector_from_displacements {m : ℕ} (v : Fin m → ℕ)
    (hvpos : ∀ i, 0 < v i)
    (H : ℕ → Submodule ℝ J) (hH : Antitone H) (c : Basis (Fin m) ℝ J)
    (hc : ∀ i, c i ∈ H (v i)) (p : Fin m → MvPolynomial (Fin m) ℝ)
    (hp : ∀ i, p i ∈ weightedShearDegreeLE v ((v i : ℤ)-1)) :
    AffineShearWeightedVector v H (roughVectorMvFromBasis c p) 1 := by
  classical
  intro a ha
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
  change c i ∈ H ((p i).weightedTotalDegree v + 1)
  have hle : (p i).weightedTotalDegree v ≤ v i - 1 := by
    unfold MvPolynomial.weightedTotalDegree
    apply Finset.sup_le
    intro a ha
    have h := hp i a ha
    have hv := hvpos i
    omega
  exact hH (by have hv := hvpos i; omega) (hc i)

/-- Explicit coordinate polynomials for the correction in the filtered joint lift. -/
noncomputable def weightedShearLiftDisplacement {n m : ℕ}
    (b : Basis (Fin n) ℝ E) (c : Basis (Fin m) ℝ J)
    (P : E →ₗ[ℝ] J) (R : J →ₗ[ℝ] E) (p : Fin m → MvPolynomial (Fin m) ℝ) :
    Fin n → MvPolynomial (Fin n) ℝ :=
  fun i => roughVectorMvProjection (b.coord i)
    (roughVectorMvLinearMap R (roughVectorMvSubstitution (weightedShearProjectionCoordinates b c P)
      (roughVectorMvFromBasis c p)))

theorem weightedShearLiftDisplacement_degree {n m : ℕ}
    (w : Fin n → ℕ) (v : Fin m → ℕ) (hvpos : ∀ i, 0 < v i)
    (F : ℕ → Submodule ℝ E) (H : ℕ → Submodule ℝ J)
    (hF : Antitone F) (hH : Antitone H)
    (b : Basis (Fin n) ℝ E) (c : Basis (Fin m) ℝ J)
    (hb : ∀ i, b i ∈ F (w i)) (hc : ∀ i, c i ∈ H (v i))
    (hbc : ∀ i z, z ∈ F (w i+1) → b.coord i z = 0)
    (hcc : ∀ i z, z ∈ H (v i+1) → c.coord i z = 0)
    (P : E →ₗ[ℝ] J) (hP : ∀ k z, z ∈ F k → P z ∈ H k)
    (R : J →ₗ[ℝ] E) (hR : ∀ k z, z ∈ H k → R z ∈ F k)
    (p : Fin m → MvPolynomial (Fin m) ℝ)
    (hp : ∀ i, p i ∈ weightedShearDegreeLE v ((v i : ℤ)-1)) (i : Fin n) :
    weightedShearLiftDisplacement b c P R p i ∈ weightedShearDegreeLE w ((w i : ℤ)-1) := by
  have hvec := weightedShearVector_from_displacements v hvpos H hH c hc p hp
  have hq := weightedShearProjectionCoordinates_degree w v F H hH b c hb hcc P hP
  have hsub := weightedShearVector_substitution v w (weightedShearProjectionCoordinates b c P)
    hq H hH hvec
  have hmap := weightedShearVector_linearMap w H F R 0
    (fun k z hz => by simpa only [Nat.add_zero] using hR k z hz) hsub
  exact weightedShearVector_projection w F hF (b.coord i) (w i) (hbc i) hmap

theorem weightedShearLiftDisplacement_eval {n m : ℕ}
    (b : Basis (Fin n) ℝ E) (c : Basis (Fin m) ℝ J)
    (P : E →ₗ[ℝ] J) (R : J →ₗ[ℝ] E) (p : Fin m → MvPolynomial (Fin m) ℝ)
    (x : Fin n → ℝ) (i : Fin n) :
    MvPolynomial.eval x (weightedShearLiftDisplacement b c P R p i) =
      b.equivFun (R (c.equivFun.symm (fun j =>
        MvPolynomial.eval (c.equivFun (P (b.equivFun.symm x))) (p j)))) i := by
  rw [weightedShearLiftDisplacement, roughVectorMvProjection_eval, roughVectorMvLinearMap_eval,
    rough_vector_mv_substitution_eval, roughVectorMvFromBasis_eval]
  simp_rw [weightedShearProjectionCoordinates_eval]
  rw [← c.equivFun_symm_apply]
  rfl

/-- The actual section lift of a weighted shear is a weighted shear upstairs. -/
theorem weightedShear_filtered_joint_lift {n m : ℕ}
    (w : Fin n → ℕ) (v : Fin m → ℕ) (hvpos : ∀ i, 0 < v i)
    (F : ℕ → Submodule ℝ E) (H : ℕ → Submodule ℝ J)
    (hF : Antitone F) (hH : Antitone H)
    (b : Basis (Fin n) ℝ E) (c : Basis (Fin m) ℝ J)
    (hb : ∀ i, b i ∈ F (w i)) (hc : ∀ i, c i ∈ H (v i))
    (hbc : ∀ i z, z ∈ F (w i+1) → b.coord i z = 0)
    (hcc : ∀ i z, z ∈ H (v i+1) → c.coord i z = 0)
    (P : E →ₗ[ℝ] J) (hP : ∀ k z, z ∈ F k → P z ∈ H k)
    (R : J →ₗ[ℝ] E) (hR : ∀ k z, z ∈ H k → R z ∈ F k)
    (T : weightedShearGroup (R := ℝ) v) :
    ∃ U : weightedShearGroup (R := ℝ) w, ∀ x : Fin n → ℝ,
      U • x = b.equivFun (b.equivFun.symm x + R
        (c.equivFun.symm (T • c.equivFun (P (b.equivFun.symm x))) - P (b.equivFun.symm x))) := by
  obtain ⟨p, hp, heval⟩ := weightedShearPoint_displacements v T
  have hdeg := weightedShearLiftDisplacement_degree w v hvpos F H hF hH b c hb hc hbc hcc
    P hP R hR p hp
  refine ⟨weightedShearOfDisplacements w (weightedShearLiftDisplacement b c P R p) hdeg, ?_⟩
  intro x
  have hcor : c.equivFun.symm (T • c.equivFun (P (b.equivFun.symm x))) - P (b.equivFun.symm x) =
      c.equivFun.symm (fun j => MvPolynomial.eval (c.equivFun (P (b.equivFun.symm x))) (p j)) := by
    apply c.equivFun.injective
    ext j
    simp only [map_sub, LinearEquiv.apply_symm_apply, Pi.sub_apply]
    rw [heval]
    simp
  rw [hcor]
  ext i
  rw [weightedShearOfDisplacements_smul]
  change x i + MvPolynomial.eval x (weightedShearLiftDisplacement b c P R p i) = _
  rw [weightedShearLiftDisplacement_eval, map_add]
  simp only [LinearEquiv.apply_symm_apply, Pi.add_apply]

end Hindman168
