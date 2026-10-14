import Hindman168.CoprimeMultipleSubgroups
import Hindman168.ShortIntervalDensityBound

namespace Hindman168

def multipleCyclicIntervalEmbedding (q n : ℕ) (u : Fin n) :
    multipleAddSubgroup (ZMod (q * n)) q :=
  ⟨q • (u.val : ZMod (q * n)), ⟨(u.val : ZMod (q * n)), rfl⟩⟩

theorem multipleCyclicIntervalEmbedding_injective (q n : ℕ) (hq : 0 < q) :
    Function.Injective (multipleCyclicIntervalEmbedding q n) := by
  intro u v huv
  have he : ((q * u.val : ℕ) : ZMod (q * n)) = ((q * v.val : ℕ) : ZMod (q * n)) := by
    simpa only [multipleCyclicIntervalEmbedding, nsmul_eq_mul, Nat.cast_mul] using
      congrArg Subtype.val huv
  have hu := Nat.mul_lt_mul_of_pos_left u.isLt hq
  have hv := Nat.mul_lt_mul_of_pos_left v.isLt hq
  have hvv := congrArg ZMod.val he
  rw [ZMod.val_natCast_of_lt hu, ZMod.val_natCast_of_lt hv] at hvv
  exact Fin.ext (Nat.eq_of_mul_eq_mul_left hq hvv)

theorem multipleCyclicIntervalEmbedding_surjective (q n : ℕ) (hq : 0 < q) (hn : 0 < n) :
    Function.Surjective (multipleCyclicIntervalEmbedding q n) := by
  letI : NeZero (q * n) := ⟨Nat.ne_of_gt (Nat.mul_pos hq hn)⟩
  intro y
  obtain ⟨z, hz⟩ := y.property
  refine ⟨⟨z.val % n, Nat.mod_lt _ hn⟩, ?_⟩
  apply Subtype.ext
  change q • ((z.val % n : ℕ) : ZMod (q * n)) = (y : ZMod (q * n))
  rw [← hz]
  change q • ((z.val % n : ℕ) : ZMod (q * n)) = q • z
  have he : q * (z.val % n) + (q * n) * (z.val / n) = q * z.val := by
    have hm := Nat.mod_add_div z.val n
    nlinarith
  have hc := congrArg (fun t : ℕ => (t : ZMod (q * n))) he
  have hzero : (q : ZMod (q * n)) * n = 0 := by rw [← Nat.cast_mul, ZMod.natCast_self]
  simpa only [Nat.cast_add, Nat.cast_mul, hzero, zero_mul, add_zero,
    ZMod.natCast_zmod_val, nsmul_eq_mul] using hc

theorem multipleCyclicSubgroup_card (q n : ℕ) (hq : 0 < q) (hn : 0 < n)
    [Fintype (multipleAddSubgroup (ZMod (q * n)) q)] :
    Fintype.card (multipleAddSubgroup (ZMod (q * n)) q) = n := by
  simpa only [Fintype.card_fin] using
    (Fintype.card_congr (Equiv.ofBijective (multipleCyclicIntervalEmbedding q n)
      ⟨multipleCyclicIntervalEmbedding_injective q n hq,
       multipleCyclicIntervalEmbedding_surjective q n hq hn⟩)).symm

theorem multipleCyclicShortInterval_injective (q n L : ℕ) (hq : 0 < q) (hL : L ≤ n) :
    Function.Injective (fun u : Fin L => multipleCyclicIntervalEmbedding q n (Fin.castLE hL u)) := by
  intro u v huv
  have he := multipleCyclicIntervalEmbedding_injective q n hq huv
  exact Fin.ext (congrArg (fun t : Fin n => t.val) he)

end Hindman168

