import Hindman168.IndexedEnergySelection
import Mathlib.Data.Finset.Sort

/-! Alternating padding/principal indices in an increasing 2n-tuple. -/

namespace Hindman168

def energyPadding {n : ℕ} (e : Fin (2 * n) ↪o ℕ) (u : Fin n) : ℕ :=
  e ⟨2 * u.val, by omega⟩

def energyPrincipal {n : ℕ} (e : Fin (2 * n) ↪o ℕ) (u : Fin n) : ℕ :=
  e ⟨2 * u.val + 1, by omega⟩

def energyPrincipalSet {n : ℕ} (e : Fin (2 * n) ↪o ℕ) : Finset ℕ :=
  Finset.univ.image (energyPrincipal e)

theorem energyPadding_lt_principal {n : ℕ} (e : Fin (2 * n) ↪o ℕ) (u : Fin n) :
    energyPadding e u < energyPrincipal e u := by
  apply e.strictMono
  change 2 * u.val < 2 * u.val + 1
  omega

theorem energyPrincipal_lt_padding {n : ℕ} (e : Fin (2 * n) ↪o ℕ)
    {u v : Fin n} (h : u < v) : energyPrincipal e u < energyPadding e v := by
  apply e.strictMono
  change 2 * u.val + 1 < 2 * v.val
  have := h
  change u.val < v.val at this
  omega

theorem energyPadding_mono {n : ℕ} (e : Fin (2 * n) ↪o ℕ)
    {u v : Fin n} (h : u ≤ v) : energyPadding e u ≤ energyPadding e v := by
  apply e.monotone
  change 2 * u.val ≤ 2 * v.val
  exact Nat.mul_le_mul_left 2 h

theorem energyPrincipal_strictMono {n : ℕ} (e : Fin (2 * n) ↪o ℕ) :
    StrictMono (energyPrincipal e) := by
  intro u v h
  exact (energyPrincipal_lt_padding e h).trans (energyPadding_lt_principal e v)

theorem energyPrincipalSet_card {n : ℕ} (e : Fin (2 * n) ↪o ℕ) :
    (energyPrincipalSet e).card = n := by
  rw [energyPrincipalSet, Finset.card_image_of_injective _ (energyPrincipal_strictMono e).injective]
  exact Finset.card_fin n

theorem energyTail_before_padding {n : ℕ} (e : Fin (2 * n) ↪o ℕ)
    (T : Finset ℕ) (v : Fin n) (hT : T ⊆ energyPrincipalSet e)
    (hbefore : ∀ t ∈ T, t < energyPrincipal e v) :
    ∀ t ∈ T, t < energyPadding e v := by
  intro t ht
  obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp (hT ht)
  exact energyPrincipal_lt_padding e ((energyPrincipal_strictMono e).lt_iff_lt.mp (hbefore _ ht))

theorem energyTail_card_lt {n : ℕ} (e : Fin (2 * n) ↪o ℕ)
    (T : Finset ℕ) (v : Fin n) (hT : T ⊆ energyPrincipalSet e)
    (hbefore : ∀ t ∈ T, t < energyPrincipal e v) : T.card < n := by
  rw [← energyPrincipalSet_card e]
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨hT, ?_⟩
  intro he
  have hv : energyPrincipal e v ∈ T := by
    rw [he]
    exact Finset.mem_image.mpr ⟨v, Finset.mem_univ _, rfl⟩
  exact (lt_irrefl _) (hbefore _ hv)

end Hindman168
