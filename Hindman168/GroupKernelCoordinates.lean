import Mathlib.Algebra.Group.Subgroup.Ker

namespace Hindman168

variable {A B G Q : Type*} [Group G] [Group Q]

def groupKernelCoordinates (c : A → G) (s : B → G) : B × A → G :=
  fun x => s x.1*c x.2

theorem group_kernel_coordinates_projection (q : G →* Q) (c : A → G) (s : B → G)
    (hc : ∀ a, q (c a) = 1) (x : B × A) :
    q (groupKernelCoordinates c s x) = q (s x.1) := by
  simp only [groupKernelCoordinates, map_mul, hc, mul_one]

theorem group_kernel_coordinates_injective (q : G →* Q) (c : A → G) (s : B → G)
    (hc : Function.Injective c) (hker : ∀ a, q (c a) = 1)
    (hs : Function.Injective (fun b => q (s b))) :
    Function.Injective (groupKernelCoordinates c s) := by
  rintro ⟨b, a⟩ ⟨d, e⟩ he
  have hb : b = d := hs (by
    simpa only [group_kernel_coordinates_projection q c s hker] using congrArg q he)
  subst d
  have ha : a = e := hc (mul_left_cancel he)
  subst e
  rfl

theorem group_kernel_coordinates_surjective (q : G →* Q) (c : A → G) (s : B → G)
    (hc : ∀ g, q g = 1 → ∃ a, c a = g)
    (hs : ∀ g : G, ∃ b, q (s b) = q g) :
    Function.Surjective (groupKernelCoordinates c s) := by
  intro g
  obtain ⟨b, hb⟩ := hs g
  have hk : q ((s b)⁻¹*g) = 1 := by
    rw [map_mul, map_inv, hb, inv_mul_cancel]
  obtain ⟨a, ha⟩ := hc ((s b)⁻¹*g) hk
  exact ⟨(b, a), by simp only [groupKernelCoordinates, ha, mul_inv_cancel_left]⟩

theorem group_kernel_coordinates_bijective (q : G →* Q) (c : A → G) (s : B → G)
    (hc : Function.Injective c) (hker : ∀ a, q (c a) = 1)
    (hcover : ∀ g, q g = 1 → ∃ a, c a = g)
    (hs : Function.Bijective (fun b => q (s b))) :
    Function.Bijective (groupKernelCoordinates c s) :=
  ⟨group_kernel_coordinates_injective q c s hc hker hs.1,
    group_kernel_coordinates_surjective q c s hcover (fun g => hs.2 (q g))⟩

theorem group_kernel_coordinates_lattice_iff (q : G →* Q) (Γ : Subgroup G)
    (c : A → G) (s : B → G) (PA : A → Prop) (PB : B → Prop)
    (hker : ∀ a, q (c a) = 1)
    (hc : ∀ a, c a ∈ Γ ↔ PA a)
    (hq : ∀ b, q (s b) ∈ Γ.map q ↔ PB b)
    (hs : ∀ b, PB b → s b ∈ Γ) (x : B × A) :
    groupKernelCoordinates c s x ∈ Γ ↔ PB x.1 ∧ PA x.2 := by
  constructor
  · intro hx
    have hb : PB x.1 := (hq _).mp (by
      rw [← group_kernel_coordinates_projection q c s hker x]
      exact Γ.mem_map_of_mem q hx)
    refine ⟨hb, (hc _).mp ?_⟩
    have he := Γ.mul_mem (Γ.inv_mem (hs _ hb)) hx
    simpa only [groupKernelCoordinates, inv_mul_cancel_left] using he
  · rintro ⟨hb, ha⟩
    exact Γ.mul_mem (hs _ hb) ((hc _).mpr ha)

end Hindman168
