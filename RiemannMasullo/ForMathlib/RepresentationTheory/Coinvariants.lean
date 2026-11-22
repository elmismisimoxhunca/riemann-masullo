module

public import Mathlib.RepresentationTheory.Coinvariants
public import Mathlib.RepresentationTheory.Invariants

public section

namespace RiemannMasullo

/-- A vector with finite orbit has an invariant representative of its coinvariant
class: take the normalized sum of the distinct vectors in its orbit. -/
theorem exists_invariant_mk_eq_of_finite_orbit {k G V : Type*} [Field k] [CharZero k]
    [Group G] [AddCommGroup V] [Module k V] (r : Representation k G V) (v : V)
    (O : Finset V) (hO : ∀ h, h ∈ O ↔ ∃ u, r u v = h) :
    ∃ s ∈ r.invariants, Representation.Coinvariants.mk r s = Representation.Coinvariants.mk r v := by
  classical
  have hmem (u : G) (h) (hh : h ∈ O) : r u h ∈ O := by
    obtain ⟨g, rfl⟩ := (hO h).mp hh
    exact (hO _).mpr ⟨u * g, DFunLike.congr_fun (r.map_mul u g) v⟩
  refine ⟨(O.card : k)⁻¹ • ∑ h ∈ O, h, fun u ↦ ?_, ?_⟩
  · rw [map_smul, map_sum]
    exact congrArg ((O.card : k)⁻¹ • ·) (Finset.sum_nbij' (r u) (r u⁻¹) (hmem u) (hmem u⁻¹)
      (fun h _ ↦ r.inv_self_apply u h) (fun h _ ↦ r.self_inv_apply u h) (fun _ _ ↦ rfl))
  · let q := Representation.Coinvariants.mk r
    have hq : ∑ h ∈ O, q h = ∑ _ ∈ O, q v := by
      apply Finset.sum_congr rfl
      intro h hh
      obtain ⟨u, rfl⟩ := (hO h).mp hh
      exact Representation.Coinvariants.mk_self_apply r u v
    have hcard : O.card ≠ 0 := Finset.card_ne_zero.mpr
      ⟨r 1 v, (hO _).mpr ⟨1, rfl⟩⟩
    change q _ = q v
    rw [map_smul, map_sum, hq, Finset.sum_const, ← Nat.cast_smul_eq_nsmul k,
      inv_smul_smul₀ (Nat.cast_ne_zero.mpr hcard)]

end RiemannMasullo
