import Hindman168.NativeFinitePiCoordinates
import Hindman168.RoughVectorMvLinearMap
import Hindman168.NativeVectorPolynomialSource
import Mathlib.LinearAlgebra.Pi

/-! Actual heterogeneous product-model vector polynomial and native source.
Each original coefficient is inserted in exactly its own component. Degree,
all-real native log and original sample identities are proved. -/
namespace Hindman168
open scoped BigOperators Classical
universe u

theorem rough_vector_list_flat_map_eval {ι σ E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : ι → RoughVectorMvPolynomial σ E) (l : List ι) (x : σ → ℝ) :
    roughVectorMvEval (l.flatMap p) x = (l.map (fun i => roughVectorMvEval (p i) x)).sum := by
  induction l with
  | nil => simp [roughVectorMvEval]
  | cons i l ih =>
    rw [List.flatMap_cons,roughVectorMvEval_append,ih,List.map_cons,List.sum_cons]

noncomputable def nativeFinitePiModelInsertion {ι : Type} [Fintype ι] [DecidableEq ι] {s : ℕ}
    (D : ι → NativeNilmanifoldData.{u} s) (i : ι) : (D i).E →ₗ[ℝ] (nativeFinitePiData D).E :=
  (nativeFinitePiModelEquiv D).symm.toLinearMap.comp (LinearMap.single ℝ (fun i => (D i).E) i)

theorem native_finite_pi_model_insertion {ι : Type} [Fintype ι] [DecidableEq ι] {s : ℕ}
    (D : ι → NativeNilmanifoldData.{u} s) (i : ι) (v : (D i).E) :
    nativeFinitePiModelEquiv D (nativeFinitePiModelInsertion D i v) = Pi.single i v := by
  rw [nativeFinitePiModelInsertion,LinearMap.comp_apply]
  exact (nativeFinitePiModelEquiv D).apply_symm_apply _

noncomputable def nativeFinitePiVectorPolynomial {ι : Type} [Fintype ι] [DecidableEq ι]
    {σ : Type*} {s : ℕ} (D : ι → NativeNilmanifoldData.{u} s)
    (p : ∀ i, RoughVectorMvPolynomial σ (D i).E) :
    RoughVectorMvPolynomial σ (nativeFinitePiData D).E :=
  (Finset.univ.toList).flatMap (fun i => roughVectorMvLinearMap (nativeFinitePiModelInsertion D i) (p i))

theorem native_finite_pi_vector_polynomial_degree {ι : Type} [Fintype ι] [DecidableEq ι]
    {σ : Type*} {s : ℕ} (D : ι → NativeNilmanifoldData.{u} s)
    (p : ∀ i, RoughVectorMvPolynomial σ (D i).E) (d : ℕ)
    (hp : ∀ i, RoughVectorMvDegreeLE (p i) d) :
    RoughVectorMvDegreeLE (nativeFinitePiVectorPolynomial D p) d := by
  rintro a ha
  obtain ⟨i,_hi,ha⟩ := List.mem_flatMap.mp ha
  exact roughVectorMvLinearMap_degree (nativeFinitePiModelInsertion D i) (hp i) a ha

theorem native_finite_pi_vector_polynomial_eval {ι : Type} [Fintype ι] [DecidableEq ι]
    {σ : Type*} {s : ℕ} (D : ι → NativeNilmanifoldData.{u} s)
    (p : ∀ i, RoughVectorMvPolynomial σ (D i).E) (x : σ → ℝ) :
    nativeFinitePiModelEquiv D (roughVectorMvEval (nativeFinitePiVectorPolynomial D p) x) =
      fun i => roughVectorMvEval (p i) x := by
  rw [nativeFinitePiVectorPolynomial,rough_vector_list_flat_map_eval,Finset.sum_map_toList,map_sum]
  simp_rw [roughVectorMvLinearMap_eval,native_finite_pi_model_insertion D]
  exact LinearMap.sum_single_apply (fun i => (D i).E) (fun i => roughVectorMvEval (p i) x)

noncomputable def nativeFinitePiVectorSource {ι : Type} [Fintype ι] [DecidableEq ι]
    {σ : Type*} {s : ℕ} (D : ι → NativeNilmanifoldData.{u} s)
    (p : ∀ i, RoughVectorMvPolynomial σ (D i).E) : (σ → ℝ) → (nativeFinitePiData D).G :=
  nativeVectorPolynomialSource (nativeFinitePiData D) (nativeFinitePiVectorPolynomial D p)

theorem native_finite_pi_vector_source_coordinate {ι : Type} [Fintype ι] [DecidableEq ι]
    {σ : Type*} {s : ℕ} (D : ι → NativeNilmanifoldData.{u} s)
    (p : ∀ i, RoughVectorMvPolynomial σ (D i).E) (x : σ → ℝ) (i : ι) :
    nativeFinitePiGroupEquiv D (nativeFinitePiVectorSource D p x) i =
      nativeVectorPolynomialSource (D i) (p i) x := by
  unfold nativeFinitePiVectorSource nativeVectorPolynomialSource
  rw [native_finite_pi_native_exponential,native_finite_pi_homeomorph_coordinate,
    native_finite_pi_vector_polynomial_eval]
  rfl

theorem native_finite_pi_vector_source_log {ι : Type} [Fintype ι] [DecidableEq ι]
    {σ : Type*} {s : ℕ} (D : ι → NativeNilmanifoldData.{u} s)
    (p : ∀ i, RoughVectorMvPolynomial σ (D i).E) (x : σ → ℝ) :
    roughVectorMvEval (nativeFinitePiVectorPolynomial D p) x =
      nativeLieGlobalLogarithm (E := (nativeFinitePiData D).E) (I := (nativeFinitePiData D).I)
        (G := (nativeFinitePiData D).G) (nativeFinitePiVectorSource D p x) :=
  (native_vector_polynomial_source_log (nativeFinitePiData D) _ x).symm

theorem native_finite_pi_vector_source_samples {ι : Type} [Fintype ι] [DecidableEq ι]
    {σ : Type*} {s : ℕ} (D : ι → NativeNilmanifoldData.{u} s)
    (p : ∀ i, RoughVectorMvPolynomial σ (D i).E) (x : σ → ℝ) (a : ∀ i, (D i).G)
    (h : ∀ i, roughVectorMvEval (p i) x =
      nativeLieGlobalLogarithm (E := (D i).E) (I := (D i).I) (G := (D i).G) (a i)) :
    nativeFinitePiVectorSource D p x = nativeFinitePiGroupValue D a := by
  apply (nativeFinitePiGroupEquiv D).injective
  funext i
  rw [native_finite_pi_vector_source_coordinate]
  exact native_vector_polynomial_source_sample (D i) (p i) x (a i) (h i)

end Hindman168
