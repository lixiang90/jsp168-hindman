import Hindman168.ProductCosetQuotient

/-! Exact original product-coordinate actions, including NONNORMAL cosets. -/

namespace Hindman168
variable {G H : Type*} [Group G] [Group H]

theorem product_coset_map_product_action (Γ : Subgroup G) (Δ : Subgroup H)
    (g : G) (h : H) (q : (G × H) ⧸ Γ.prod Δ) :
    productCosetMap Γ Δ ((g,h) • q) = (g • (productCosetMap Γ Δ q).1,h • (productCosetMap Γ Δ q).2) := by
  induction q using Quotient.inductionOn with
  | _ p => rfl

end Hindman168
