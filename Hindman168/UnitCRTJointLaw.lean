import Hindman168.ZModUniformUnits
import Hindman168.UniformCRT
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Algebra.Group.Units.Equiv

/-!
# Original uniform-unit CRT joint laws

The CRT ring equivalence induces the actual units-group equivalence.
Uniform group pushforward therefore gives the product of the original
uniform local unit masses, including the joint law for every parameter
coordinate. Local quotient reductions retain this joint independence.
-/

namespace Hindman168.FiniteMass

open scoped BigOperators Classical

theorem piMass_transpose {ι κ : Type*} [Fintype ι] [Fintype κ] {α : κ → Type*}
    (μ : ∀ _ : ι, ∀ k : κ, Mass (α k)) :
    (piMass (fun i => piMass (μ i))).mapDomain (fun x k i => x i k) =
      piMass (fun k => piMass (fun i => μ i k)) := by
  classical
  let e : (∀ i : ι, ∀ k : κ, α k) ≃ (∀ k : κ, ι → α k) :=
    Equiv.piComm (fun (_ : ι) k => α k)
  change (piMass (fun i => piMass (μ i))).mapDomain e = _
  ext x
  rw [Finsupp.mapDomain_equiv_apply]
  simp only [piMass_apply]
  exact Finset.prod_comm

theorem expectation_push {α β : Type*} (μ : Mass α) (stat : α → β) (f : β → ℝ) :
    expectation (μ.mapDomain stat) f = expectation μ (fun a => f (stat a)) := by
  exact Finsupp.sum_mapDomain_index (fun _ => zero_mul _)
    (fun _ _ _ => add_mul _ _ _)

end Hindman168.FiniteMass

namespace Hindman168

open scoped BigOperators Classical
open FiniteMass

theorem zmodUnitUniformMass_crt {ι : Type*} [Fintype ι]
    (m : ι → ℕ) [NeZero (∏ i, m i)] [∀ i, NeZero (m i)]
    (hc : Pairwise (fun i j => (m i).Coprime (m j))) :
    (zmodUnitUniformMass (∏ i, m i)).mapDomain (ZMod.prodEquivPi m hc) =
      piMass (fun i => zmodUnitUniformMass (m i)) := by
  classical
  let e := ZMod.prodEquivPi m hc
  let u : (ZMod (∏ i, m i))ˣ ≃* (∀ i, (ZMod (m i))ˣ) :=
    (Units.mapEquiv e.toMulEquiv).trans MulEquiv.piUnits
  have hu := uniformFintypeMass_group_push u.toMonoidHom u.surjective
  change (uniformFintypeMass (ZMod (∏ i, m i))ˣ).mapDomain u =
    uniformFintypeMass (∀ i, (ZMod (m i))ˣ) at hu
  rw [zmodUnitUniformMass, ← Finsupp.mapDomain_comp]
  change (uniformFintypeMass (ZMod (∏ i, m i))ˣ).mapDomain
    ((fun v : ∀ i, (ZMod (m i))ˣ => fun i => (v i : ZMod (m i))) ∘ u) = _
  rw [Finsupp.mapDomain_comp, hu, uniformFintypeMass_pi, piMass_map]
  rfl

theorem zmodUnitUniformMass_crt_vector {ι : Type*} [Fintype ι]
    (m : ι → ℕ) [NeZero (∏ i, m i)] [∀ i, NeZero (m i)]
    (hc : Pairwise (fun i j => (m i).Coprime (m j))) (n : ℕ) :
    (piMass (fun _ : Fin n => zmodUnitUniformMass (∏ i, m i))).mapDomain
      (fun x i j => ZMod.prodEquivPi m hc (x j) i) =
        piMass (fun i => piMass (fun _ : Fin n => zmodUnitUniformMass (m i))) := by
  have h := piMass_map (fun _ : Fin n => zmodUnitUniformMass (∏ i, m i))
    (fun _ => ZMod.prodEquivPi m hc)
  have ht := congrArg (fun μ : Mass (Fin n → ∀ i, ZMod (m i)) =>
    μ.mapDomain (fun x i j => x j i)) h
  rw [← Finsupp.mapDomain_comp] at ht
  simp only [zmodUnitUniformMass_crt m hc] at ht
  rw [piMass_transpose] at ht
  exact ht

theorem zmodUnitUniformMass_crt_vector_quotient {ι : Type*} [Fintype ι]
    (m r : ι → ℕ) [NeZero (∏ i, m i)] [∀ i, NeZero (m i)] [∀ i, NeZero (r i)]
    (hc : Pairwise (fun i j => (m i).Coprime (m j))) (hr : ∀ i, r i ∣ m i) (n : ℕ) :
    (piMass (fun _ : Fin n => zmodUnitUniformMass (∏ i, m i))).mapDomain
      (fun x i j => ZMod.castHom (hr i) (ZMod (r i)) (ZMod.prodEquivPi m hc (x j) i)) =
        piMass (fun i => piMass (fun _ : Fin n => zmodUnitUniformMass (r i))) := by
  have h := congrArg (fun μ : Mass (∀ i, Fin n → ZMod (m i)) =>
    μ.mapDomain (fun x i j => ZMod.castHom (hr i) (ZMod (r i)) (x i j)))
      (zmodUnitUniformMass_crt_vector m hc n)
  rw [← Finsupp.mapDomain_comp] at h
  rw [piMass_map (fun i => piMass (fun _ : Fin n => zmodUnitUniformMass (m i)))
    (fun i x => fun j => ZMod.castHom (hr i) (ZMod (r i)) (x j))] at h
  have hlocal (i : ι) :
      (piMass (fun _ : Fin n => zmodUnitUniformMass (m i))).mapDomain
        (fun x j => ZMod.castHom (hr i) (ZMod (r i)) (x j)) =
      piMass (fun _ : Fin n => zmodUnitUniformMass (r i)) := by
    rw [piMass_map (fun _ : Fin n => zmodUnitUniformMass (m i))
      (fun _ => ZMod.castHom (hr i) (ZMod (r i)))]
    simp only [zmodUnitUniformMass_quotient (hr i)]
  simp only [hlocal] at h
  exact h

end Hindman168
