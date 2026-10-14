import Hindman168.FinitePiGroupLie
import Hindman168.FinitePiLatticeNilpotence
import Hindman168.NativeNilmanifoldConstruction
import Hindman168.NativeLieExponentialDiffeomorph

/-! The genuine finite heterogeneous product of native nilmanifolds.
Models may live in ANY common universe; the actual finite index is small.
The group/lattice are literal dependent products, with constructed smooth
charts and a compatible quotient metric. No analytic property is a field. -/
namespace Hindman168
open scoped Manifold ContDiff
universe u

noncomputable def nativeFinitePiData {ι : Type} [Fintype ι] {s : ℕ}
    (D : ι → NativeNilmanifoldData.{u} s) : NativeNilmanifoldData.{u} s := by
  let V := ∀ i, (D i).E
  let A := ∀ i, (D i).G
  let e : ∀ i, Diffeomorph 𝓘(ℝ,(D i).E) (D i).I (D i).E (D i).G ∞ :=
    fun i => nativeLieExponentialDiffeomorph (E := (D i).E) (I := (D i).I) (G := (D i).G)
  letI := finitePiGroupChartedSpace e
  letI := finitePiGroup_lieGroup e
  letI : IsTopologicalGroup A := topologicalGroup_of_lieGroup 𝓘(ℝ,V) ∞
  letI : ContractibleSpace A := (finitePiGroupHomeomorph e).symm.contractibleSpace
  letI : SimplyConnectedSpace A := inferInstance
  let Γ := Subgroup.pi Set.univ (fun i => (D i).Γ)
  letI := finitePiSubgroup_discrete (fun i => (D i).Γ)
  letI := piCoset_quotient_compact (fun i => (D i).Γ)
  letI : Module ℚ V := Module.compHom _ (Rat.castHom ℝ)
  have hcut : ∀ i, (⊤ : Subgroup (D i).G).lowerCentralSeries s=⊥ :=
    fun i => Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mpr (D i).step_le
  letI : Group.IsNilpotent A := Subgroup.nilpotent_iff_lowerCentralSeries.mpr
    ⟨s,piGroup_lowerCentral_bot (fun i => (D i).G) s hcut⟩
  let recipe := nativeNilmanifoldOfLie (E := V) (I := 𝓘(ℝ,V)) (G := A) s
    (piGroup_nilpotencyClass_le (fun i => (D i).G) s hcut) Γ
  exact {
    E := V
    H := V
    I := 𝓘(ℝ,V)
    G := A
    charted := finitePiGroupChartedSpace e
    lie := finitePiGroup_lieGroup e
    step_le := piGroup_nilpotencyClass_le (fun i => (D i).G) s hcut
    Γ := Γ
    metric := recipe.metric
    metric_quotientMap := recipe.metric_quotientMap }

noncomputable def nativeFinitePiModelEquiv {ι : Type} [Fintype ι] {s : ℕ}
    (D : ι → NativeNilmanifoldData.{u} s) :
    (nativeFinitePiData D).E ≃ₗ[ℝ] (∀ i, (D i).E) := by
  change (∀ i, (D i).E) ≃ₗ[ℝ] (∀ i, (D i).E)
  exact LinearEquiv.refl ℝ _

def nativeFinitePiGroupEquiv {ι : Type} [Fintype ι] {s : ℕ}
    (D : ι → NativeNilmanifoldData.{u} s) :
    (nativeFinitePiData D).G ≃* (∀ i, (D i).G) := by
  change (∀ i, (D i).G) ≃* (∀ i, (D i).G)
  exact MulEquiv.refl _

def nativeFinitePiGroupValue {ι : Type} [Fintype ι] {s : ℕ}
    (D : ι → NativeNilmanifoldData.{u} s) (g : ∀ i, (D i).G) : (nativeFinitePiData D).G := g

theorem native_finite_pi_lattice_mem {ι : Type} [Fintype ι] {s : ℕ}
    (D : ι → NativeNilmanifoldData.{u} s) (g : (nativeFinitePiData D).G) :
    g ∈ (nativeFinitePiData D).Γ ↔ ∀ i, nativeFinitePiGroupEquiv D g i ∈ (D i).Γ := by
  let g' : ∀ i, (D i).G := nativeFinitePiGroupEquiv D g
  change g' ∈ Subgroup.pi Set.univ (fun i => (D i).Γ) ↔ ∀ i, g' i ∈ (D i).Γ
  simp only [Subgroup.mem_pi,Set.mem_univ,forall_const]

end Hindman168
