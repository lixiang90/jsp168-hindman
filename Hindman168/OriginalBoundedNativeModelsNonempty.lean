import Hindman168.OriginalBoundedNativeModelsMenu

/-! A genuine zero-dimensional rational model makes every nonnegative-budget
menu nonempty, without assuming the inverse theorem or a positive correlation. -/

namespace Hindman168.OriginalBoundedNativeModels

open Module OAI.Erdos3
open scoped TensorProduct

/-- The zero-dimensional rational Lie algebra. -/
def ZeroAlgebra := Fin 0 → ℚ

instance : AddCommGroup ZeroAlgebra := inferInstanceAs (AddCommGroup (Fin 0 → ℚ))
instance : Module ℚ ZeroAlgebra := inferInstanceAs (Module ℚ (Fin 0 → ℚ))
instance : Subsingleton ZeroAlgebra := inferInstanceAs (Subsingleton (Fin 0 → ℚ))

instance : LieRing ZeroAlgebra where
  toAddCommGroup := inferInstance
  bracket _ _ := 0
  add_lie _ _ _ := by simp
  lie_add _ _ _ := by simp
  lie_self _ := rfl
  leibniz_lie _ _ _ := by simp

instance : LieAlgebra ℚ ZeroAlgebra where
  toModule := inferInstance
  lie_smul _ _ _ := by
    change (0 : ZeroAlgebra) = _ • (0 : ZeroAlgebra)
    exact (smul_zero _).symm

noncomputable def zeroBasis : Basis (Fin 0) ℚ ZeroAlgebra :=
  Pi.basisFun ℚ (Fin 0)

noncomputable instance : FiniteDimensional ℚ ZeroAlgebra :=
  zeroBasis.finiteDimensional_of_finite

def zeroFiltration (s : ℕ) : NilpotentLieFiltration ZeroAlgebra s where
  layer _ := ⊤
  antitone _ _ _ := le_rfl
  one_eq_top := rfl
  lie_mem _ _ := Submodule.mem_top
  terminal := by
    apply le_antisymm _ bot_le
    intro x _
    simpa only [Submodule.mem_bot] using (Subsingleton.elim x 0)

noncomputable def zeroRationalModel (s : ℕ) : RationalFilteredNilmanifold ZeroAlgebra s 0 where
  filtration := zeroFiltration s
  basis := zeroBasis
  layerBasis _ := Module.finBasis ℚ _
  lattice := ⊤
  grid := 1
  grid_pos := by decide
  inner_grid := by intro x _; trivial
  outer_grid := by intro x _; exact ⟨0, fun i => Fin.elim0 i⟩

theorem zeroRationalModel_geometry (s : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    (zeroRationalModel s).GeometryComplexityLE p := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using hp
  · simpa only [zeroRationalModel, Nat.cast_one] using Real.one_le_exp_iff.mpr hp
  · intro i
    exact Fin.elim0 i
  · intro i j k
    exact Fin.elim0 k

/-- Nonemptiness is proved by the zero-dimensional Lie quotient. -/
theorem menuIndex_nonempty (s : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    Nonempty (MenuIndex s p) := by
  obtain ⟨τ, hA, hS, hT, _⟩ := exists_realification_topology_of_grid
    (zeroRationalModel s).basis (zeroRationalModel s).lattice
    (zeroRationalModel s).grid (zeroRationalModel s).grid_pos
    (zeroRationalModel s).outer_grid
  letI := τ
  letI := hA
  letI := hS
  letI := hT
  exact menuIndex_nonempty_of_model (zeroRationalModel s) hp (zeroRationalModel_geometry s hp)

/-- A positive finite list of actual native models is fixed by `s,p`. -/
theorem exists_finite_native_menu (s : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    ∃ n : ℕ, 0 < n ∧
      ∃ e : Fin n ≃ MenuIndex s p,
        ∃ models : Fin n → NativeNilmanifoldData.{0} s,
          ∀ i, models i = menuNativeModel s p (e i) := by
  classical
  letI := menuIndex_nonempty s hp
  let n := Fintype.card (MenuIndex s p)
  let e : Fin n ≃ MenuIndex s p := (Fintype.equivFin (MenuIndex s p)).symm
  exact ⟨n, Fintype.card_pos, e, fun i => menuNativeModel s p (e i), fun _ => rfl⟩

end Hindman168.OriginalBoundedNativeModels
