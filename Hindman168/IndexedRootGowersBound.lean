import Hindman168.IteratedRootCubeBound

namespace Hindman168
open scoped BigOperators
variable {G : Type*} [AddCommGroup G] [Fintype G] (Q : AddSubgroup G) [Fintype Q]

theorem weightedIndexedRootGowers_bound {ι β : Type*} [Fintype ι] [Fintype β] [Nonempty β]
    (p : ι → ℝ) (hp : ∀ c, 0 ≤ p c) (hsum : ∑ c, p c = 1) {d : ℕ}
    (D : β → Q →+ (G × (Fin d → Q))) (hD : ∀ j a, (D j a).1 = (a : G))
    (f : ι → β → (G × (Fin d → Q)) → ℝ)
    (hf : ∀ c j z, |f c j z| ≤ 1) (hi : ∀ c j z a, f c j (z + D j a) = f c j z)
    (h : ι → G → ℝ) :
    |∑ c, p c * finiteHaarMean (fun z => h c z.1 * ∏ j, f c j z)| ≤
      weightedSubgroupGowersValue Q p (Fintype.card β) h := by
  classical
  let e : Fin (Fintype.card β) ≃ β := (Fintype.equivFin β).symm
  have he (c : ι) (z : G × (Fin d → Q)) :
      (∏ j : Fin (Fintype.card β), f c (e j) z) = ∏ j : β, f c j z := e.prod_comp (fun j => f c j z)
  simpa only [he] using weightedIteratedRootGowers_bound Q p hp hsum
    Fintype.card_pos (fun j => D (e j)) (fun j => hD (e j))
    (fun c j => f c (e j)) (fun c j => hf c (e j)) (fun c j => hi c (e j)) h

end Hindman168

