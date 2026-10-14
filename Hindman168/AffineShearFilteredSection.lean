import Hindman168.IntegerFlagBasis
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! The filtration-preserving section required in Proposition 7.5 is
constructed, rather than supplied.  An adapted basis in the quotient is
lifted at its deepest filtration level. -/
namespace Hindman168
open Module

 theorem affineShear_filtered_preimage {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (p : V →ₗ[K] W) (hp : Function.Surjective p) (k : ℕ)
    (P : Fin k → Submodule K V) (hP : Antitone P) (y : W) :
    ∃ x : V, p x = y ∧ ∀ j, y ∈ (P j).map p → x ∈ P j := by
  classical
  let S : Finset (Fin k) := Finset.univ.filter (fun j => y ∈ (P j).map p)
  by_cases hS : S.Nonempty
  · let j := S.max' hS
    have hj : y ∈ (P j).map p := (Finset.mem_filter.mp (Finset.max'_mem S hS)).2
    obtain ⟨x, hx, hxy⟩ := hj
    refine ⟨x, hxy, ?_⟩
    intro a ha
    exact hP (Finset.le_max' S a (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩)) hx
  · obtain ⟨x, hx⟩ := hp y
    refine ⟨x, hx, ?_⟩
    intro j hj
    exact False.elim (hS ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩)

 theorem affineShear_filtered_section_exists {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [Module.Finite K W]
    (p : V →ₗ[K] W) (hp : Function.Surjective p) (k : ℕ)
    (P : Fin k → Submodule K V) (hP : Antitone P) :
    ∃ R : W →ₗ[K] V, p.comp R = LinearMap.id ∧
      ∀ j, ((P j).map p).map R ≤ P j := by
  classical
  let Q : Fin k → Submodule K W := fun j => (P j).map p
  have hQ : Antitone Q := fun i j hij => Submodule.map_mono (hP hij)
  obtain ⟨n, b, hb⟩ := split_integer_flag_basis_exists k Q hQ
    (fun j => (Q j).exists_isCompl)
  choose v hv hlevel using fun i : Fin n =>
    affineShear_filtered_preimage p hp k P hP (b i)
  let R : W →ₗ[K] V := b.constr K v
  refine ⟨R, ?_, ?_⟩
  · apply b.ext
    intro i
    simpa [R] using hv i
  · intro j
    rw [Submodule.map_le_iff_le_comap]
    change Q j ≤ (P j).comap R
    rw [← hb j]
    apply Submodule.span_le.mpr
    rintro y ⟨i, hi, rfl⟩
    change R (b i) ∈ P j
    simpa [R] using hlevel i j hi

/-- The explicit cover lift has exactly the prescribed projected action. -/
 theorem affineShear_section_lift_projection {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (p : V →ₗ[K] W) (R : W →ₗ[K] V) (hR : p.comp R = LinearMap.id)
    (D : W → W) (u : V) : p (u + R (D (p u))) = p u + D (p u) := by
  have h := LinearMap.congr_fun hR (D (p u))
  simpa only [map_add, LinearMap.comp_apply, LinearMap.id_apply] using
    congrArg (fun y => p u + y) h

/-- The finite construction applies to every level of an eventually-zero
natural-number filtration, including all levels beyond its length. -/
 theorem affineShear_terminal_filtered_section_exists {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [Module.Finite K W]
    (p : V →ₗ[K] W) (hp : Function.Surjective p) (s : ℕ)
    (P : ℕ → Submodule K V) (hP : Antitone P) (hterm : P (s+1) = ⊥) :
    ∃ R : W →ₗ[K] V, p.comp R = LinearMap.id ∧
      ∀ j, ((P j).map p).map R ≤ P j := by
  obtain ⟨R, hR, hlevels⟩ := affineShear_filtered_section_exists p hp (s+1)
    (fun j => P j.val) (fun _ _ hij => hP hij)
  refine ⟨R, hR, ?_⟩
  intro j
  by_cases hj : j < s+1
  · exact hlevels ⟨j, hj⟩
  · have hzero : P j = ⊥ := le_antisymm (by
      rw [← hterm]
      exact hP (Nat.le_of_not_gt hj)) bot_le
    simp [hzero]

/-- A projected bijection lifts to a genuine bijection of the joint cover,
using the section.  The kernel coordinate is fixed by this construction. -/
 noncomputable def affineShearSectionLiftEquiv {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (p : V →ₗ[K] W) (R : W →ₗ[K] V) (hR : p.comp R = LinearMap.id)
    (e : W ≃ W) : V ≃ V where
  toFun u := u + R (e (p u) - p u)
  invFun u := u + R (e.symm (p u) - p u)
  left_inv u := by
    have hpR (w : W) : p (R w) = w := LinearMap.congr_fun hR w
    simp only [map_add, hpR, add_sub_cancel, Equiv.symm_apply_apply]
    rw [add_assoc, ← map_add]
    simp
  right_inv u := by
    have hpR (w : W) : p (R w) = w := LinearMap.congr_fun hR w
    simp only [map_add, hpR, add_sub_cancel, Equiv.apply_symm_apply]
    rw [add_assoc, ← map_add]
    simp

 theorem affineShearSectionLiftEquiv_projection {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (p : V →ₗ[K] W) (R : W →ₗ[K] V) (hR : p.comp R = LinearMap.id)
    (e : W ≃ W) (u : V) : p (affineShearSectionLiftEquiv p R hR e u) = e (p u) := by
  change p (u + R (e (p u) - p u)) = e (p u)
  rw [map_add, show p (R (e (p u) - p u)) = e (p u) - p u from
    LinearMap.congr_fun hR _]
  simp

/-- An injective linear map preserving a finite-dimensional subspace is
surjective on that subspace; the restricted map is constructed explicitly. -/
 theorem affineShear_invariant_subspace_surjective {K V : Type*} [Field K]
    [AddCommGroup V] [Module K V] [Module.Finite K V]
    (A : V →ₗ[K] V) (hA : Function.Injective A)
    (P : Submodule K V) (hP : ∀ x ∈ P, A x ∈ P) :
    ∀ y ∈ P, ∃ x ∈ P, A x = y := by
  let B : P →ₗ[K] P :=
    { toFun := fun x => ⟨A x.val, hP x.val x.property⟩
      map_add' := fun x y => Subtype.ext (A.map_add x.val y.val)
      map_smul' := fun r x => Subtype.ext (A.map_smul r x.val) }
  have hB : Function.Injective B := by
    intro x y hxy
    exact Subtype.ext (hA (congrArg Subtype.val hxy))
  have hsur : Function.Surjective B := LinearMap.injective_iff_surjective.mp hB
  intro y hy
  obtain ⟨x, hx⟩ := hsur ⟨y, hy⟩
  exact ⟨x.val, x.property, congrArg Subtype.val hx⟩

end Hindman168
