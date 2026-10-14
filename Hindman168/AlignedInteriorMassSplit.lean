import Hindman168.MasterAlignedEndpointLoss

namespace Hindman168
open scoped BigOperators

theorem integerMass_support_in_window (X W : ℕ) :
    (integerMass X W).support ⊆ Finset.Ico (X : ℤ) (X ^ 2 : ℕ) := by
  intro y hy
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hy)
  have hw : n ∈ harmonicWindow X W :=
    (intervalMass_support X (X ^ 2 : ℕ) W _).trans (unitInterval_raw X W).subset hn
  have hb := Finset.mem_Ico.mp (Finset.mem_filter.mp hw).1
  apply Finset.mem_Ico.mpr
  constructor <;> exact_mod_cast (by tauto)

theorem integerMass_window_sum (X W : ℕ) :
    (∑ y ∈ Finset.Ico (X : ℤ) (X ^ 2 : ℕ), integerMass X W y) =
      FiniteMass.total (integerMass X W) :=
  (FiniteMass.total_eq_sum _ (integerMass_support_in_window X W)).symm

theorem alignedInterior_mass_split (X W R : ℕ) (hR : 0 < R) :
    (∑ y ∈ Finset.Ico (((X : ℤ) / R + 1) * R) (((X ^ 2 : ℕ) : ℤ) / R * R),
      integerMass X W y) +
    (∑ y ∈ Finset.Ico (X : ℤ) (X ^ 2 : ℕ) \
      Finset.Ico (((X : ℤ) / R + 1) * R) (((X ^ 2 : ℕ) : ℤ) / R * R),
      integerMass X W y) = FiniteMass.total (integerMass X W) := by
  have hs : Finset.Ico (((X : ℤ) / R + 1) * R) (((X ^ 2 : ℕ) : ℤ) / R * R) ⊆
      Finset.Ico (X : ℤ) (X ^ 2 : ℕ) := by
    intro y hy
    obtain ⟨hl, hu⟩ := Finset.mem_Ico.mp hy
    have he := alignedInterior_endpoint_bounds (X : ℤ) (X ^ 2 : ℕ) R hR
    exact Finset.mem_Ico.mpr ⟨he.1.trans hl, hu.trans_le he.2.2.2⟩
  rw [add_comm, Finset.sum_sdiff hs, integerMass_window_sum]

end Hindman168
