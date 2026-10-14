import Hindman168.SubgroupCubeDimensionOne
import Hindman168.FiniteHaarDirections

namespace Hindman168
open scoped BigOperators

theorem finiteHaarMean_surjective_addHom {G H : Type*}
    [AddCommGroup G] [AddCommGroup H] [Fintype G] [Fintype H]
    (φ : G →+ H) (hs : Function.Surjective φ) (f : H → ℝ) :
    finiteHaarMean (fun x => f (φ x)) = finiteHaarMean f := by
  have hi (y : H) : finiteHaarMean (fun x => f (y + φ x)) = finiteHaarMean (fun x => f (φ x)) := by
    obtain ⟨a, rfl⟩ := hs y
    simpa only [map_add] using finiteHaarMean_add_left (fun x => f (φ x)) a
  have hj (x : G) : finiteHaarMean (fun y => f (y + φ x)) = finiteHaarMean f := by
    simpa only [add_comm] using finiteHaarMean_add_left f (φ x)
  have he := finiteHaarMean_comm (fun (y : H) (x : G) => f (y + φ x))
  simpa only [hi, hj, finiteHaarMean_const] using he

theorem subgroupHaarMean_sup {G : Type*} [AddCommGroup G]
    (Q R : AddSubgroup G) [Fintype Q] [Fintype R] [Fintype (Q ⊔ R : AddSubgroup G)]
    (f : G → ℝ) (x : G) :
    subgroupHaarMean Q (subgroupHaarMean R f) x = subgroupHaarMean (Q ⊔ R) f x := by
  let φ : Q × R →+ (Q ⊔ R : AddSubgroup G) := {
    toFun := fun a => ⟨(a.1 : G) + a.2, AddSubgroup.add_mem_sup a.1.property a.2.property⟩
    map_zero' := by ext; simp
    map_add' := by intro a b; ext; simp [add_comm, add_left_comm] }
  have hs : Function.Surjective φ := by
    intro z
    obtain ⟨u, hu, v, hv, huv⟩ := AddSubgroup.mem_sup.mp z.property
    refine ⟨(⟨u, hu⟩, ⟨v, hv⟩), ?_⟩
    exact Subtype.ext huv
  have he := finiteHaarMean_surjective_addHom φ hs (fun z => f (x + (z : G)))
  rw [finiteHaarMean_prod] at he
  simpa only [subgroupHaarMean, φ, AddMonoidHom.coe_mk, ZeroHom.coe_mk, add_assoc] using he

theorem subgroupHaarMean_commute {G : Type*} [AddCommGroup G]
    (Q R : AddSubgroup G) [Fintype Q] [Fintype R]
    (f : G → ℝ) (x : G) :
    subgroupHaarMean Q (subgroupHaarMean R f) x = subgroupHaarMean R (subgroupHaarMean Q f) x := by
  unfold subgroupHaarMean
  rw [finiteHaarMean_comm]
  simp only [add_right_comm]

theorem subgroupHaarMean_idempotent {G : Type*} [AddCommGroup G]
    (Q : AddSubgroup G) [Fintype Q] (f : G → ℝ) (x : G) :
    subgroupHaarMean Q (subgroupHaarMean Q f) x = subgroupHaarMean Q f x := by
  change finiteHaarMean (fun a : Q => subgroupHaarMean Q f (x + a)) = _
  simp only [subgroupHaarMean_translate, finiteHaarMean_const]

theorem subgroupHaarMean_self_adjoint {G : Type*} [AddCommGroup G] [Fintype G]
    (Q : AddSubgroup G) [Fintype Q] (f g : G → ℝ) :
    finiteHaarMean (fun x => subgroupHaarMean Q f x * g x) =
      finiteHaarMean (fun x => f x * subgroupHaarMean Q g x) := by
  have hs (a : Q) : finiteHaarMean (fun x => f (x + a) * g x) =
      finiteHaarMean (fun x => f x * g (x - a)) := by
    have ht := finiteHaarMean_equiv (Equiv.addRight (a : G)) (fun x => f x * g (x - a))
    change finiteHaarMean (fun x => f (x + a) * g (x + a - a)) = _ at ht
    simpa only [add_sub_cancel_right] using ht
  have hn (x : G) : finiteHaarMean (fun a : Q => g (x - a)) = subgroupHaarMean Q g x := by
    simpa only [subgroupHaarMean, Equiv.neg_apply, AddSubgroup.coe_neg, sub_eq_add_neg] using
      finiteHaarMean_equiv (Equiv.neg Q) (fun a : Q => g (x + a))
  simp only [subgroupHaarMean, ← finiteHaarMean_mul_const]
  rw [finiteHaarMean_comm]
  simp_rw [hs]
  rw [finiteHaarMean_comm]
  simp only [finiteHaarMean_const_mul, hn, subgroupHaarMean]

theorem subgroupHaarMean_pair_energy {G : Type*} [AddCommGroup G] [Fintype G]
    (Q R : AddSubgroup G) [Fintype Q] [Fintype R] [Fintype (Q ⊔ R : AddSubgroup G)]
    (f : G → ℝ) :
    finiteHaarMean (fun x => subgroupHaarMean Q f x * subgroupHaarMean R f x) =
      subgroupCubeAverage (Q ⊔ R) 1 f := by
  rw [subgroupHaarMean_self_adjoint]
  simp_rw [subgroupHaarMean_sup]
  rw [subgroupCubeAverage_one_dimension, ← subgroupHaar_correlation_square]
  simp only [finiteHaarMean_const_mul, subgroupHaarMean]

end Hindman168
