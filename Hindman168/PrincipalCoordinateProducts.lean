import Hindman168.PrincipalCoordinateChains
import Hindman168.MasterColumnCoefficients

/-! Relabeling keeps the actual coordinate products and master
coefficients, so arbitrary joint counts transport to the selected law. -/

namespace Hindman168
open Filter FiniteMass
open scoped BigOperators Topology Classical

namespace PrincipalCoordinateChain

def sampleProducts {n m : ℕ} (C : PrincipalCoordinateChain n m)
    (x : Fin n → ℕ) : Fin m → ℕ := fun i => ∏ k ∈ C.block i, x k

noncomputable def coefficient {n m : ℕ} (C : PrincipalCoordinateChain n m)
    (M : ℕ) (e : Fin (2*n) ↪o ℕ) (a : Fin m → ℚ) (w : ℕ) (i : Fin m) : ℕ :=
  ⌊(selectedSubsetScale M e w (C.block i) : ℚ) * a i⌋₊

theorem coefficient_lift {n m M : ℕ} (C : PrincipalCoordinateChain n m)
    (e : Fin (2*n) ↪o ℕ) (heM : ∀ j, e j < M) (a : Fin m → ℚ) (w : ℕ) :
    C.coefficient M e a w = masterColumnCoefficient M a (fun _ => (C.lift e).block) w := by
  funext i
  unfold coefficient masterColumnCoefficient
  simp only [selectedSubsetScale_eq_master e heM, C.lift_block]

theorem sampleProducts_lift {n m M : ℕ} (C : PrincipalCoordinateChain n m)
    (e : Fin (2*n) ↪o ℕ) (heM : ∀ j, e j < M) (x : Fin M → ℕ) :
    (C.lift e).sampleProducts (C.lift_range e heM) x =
      C.sampleProducts (fun k => x (selectedPrincipalIndex e heM k)) := by
  funext i
  unfold Chain.sampleProducts Chain.coordinateIndex sampleProducts
  let f : ℕ → ℕ := fun j => if hj : j < M then x ⟨j, hj⟩ else 0
  have hprod : (∏ j : (C.lift e).block i,
      x ⟨j.val, Finset.mem_range.mp (C.lift_range e heM i j.property)⟩) =
      ∏ j ∈ (C.lift e).block i, f j := by
    rw [← Finset.prod_coe_sort ((C.lift e).block i) f]
    apply Finset.prod_congr rfl
    intro j _
    dsimp only [f]
    rw [dif_pos (Finset.mem_range.mp (C.lift_range e heM i j.property))]
  rw [hprod, C.lift_block, Finset.prod_image (energyPrincipal_strictMono e).injective.injOn]
  apply Finset.prod_congr rfl
  intro k _
  dsimp only [f, selectedPrincipalIndex]
  rw [dif_pos (show energyPrincipal e k < M from heM _)]

end PrincipalCoordinateChain

theorem MasterParameterConditions.principal_chain_expectation {d n m M : ℕ}
    {A : Finset ℚ} {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions M A D F) (e : Fin (2*n) ↪o ℕ)
    (heM : ∀ j, e j < M) (C : PrincipalCoordinateChain n m) :
    ∀ᶠ w in atTop, ∀ φ : (Fin m → ℕ) → ℝ,
      expectation (globalRawMass (F.cutoff w) (primorial w) M)
        (fun x => φ ((C.lift e).sampleProducts (C.lift_range e heM) x)) =
      expectation (selectedPrincipalRawMass e F w) (fun x => φ (C.sampleProducts x)) := by
  filter_upwards [hF.selected_principal_raw_expectation e heM] with w hw
  intro φ
  simp_rw [C.sampleProducts_lift e heM]
  exact hw (fun x => φ (C.sampleProducts x))

end Hindman168
