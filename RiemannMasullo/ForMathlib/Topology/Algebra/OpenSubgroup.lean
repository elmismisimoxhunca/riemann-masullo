module

public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.Separation.Regular

/-!
# Compact open subgroups

Van Dantzig's theorem: a locally compact Hausdorff totally disconnected group has a
neighborhood basis at the identity consisting of compact open subgroups.
-/

@[expose] public section

open Set Filter Topology
open scoped Pointwise

namespace RiemannMasullo

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- A compact open set `W` admits a neighborhood `T` of the identity with `W * T ⊆ W`. -/
lemma exists_mul_closure_nhds_of_isCompact {W : Set G} (hW : IsCompact W) (hWopen : IsOpen W) :
    ∃ T ∈ 𝓝 (1 : G), W * T ⊆ W := by
  apply hW.induction_on (p := fun S ↦ ∃ T ∈ 𝓝 (1 : G), S * T ⊆ W)
    ⟨Set.univ, by simp only [univ_mem, empty_mul, empty_subset, and_self]⟩
    (fun _ _ huv ⟨T, hT, mem⟩ ↦ ⟨T, hT, (mul_subset_mul_right huv).trans mem⟩)
    (fun U V ⟨T₁, hT₁, mem1⟩ ⟨T₂, hT₂, mem2⟩ ↦ ⟨T₁ ∩ T₂, inter_mem hT₁ hT₂, by
      rw [union_mul]
      exact union_subset
        ((mul_subset_mul_left inter_subset_left).trans mem1)
        ((mul_subset_mul_left inter_subset_right).trans mem2)⟩)
  intro x hx
  have hxW : (x, (1 : G)) ∈ (fun p : G × G ↦ p.1 * p.2) ⁻¹' W := by simp [hx]
  obtain ⟨U, V, Uopen, Vopen, xmemU, onememV, prodsub⟩ :=
    isOpen_prod_iff.mp (continuous_mul.isOpen_preimage W hWopen) x 1 hxW
  have hUV : U * V ⊆ W := by
    intro y hy
    obtain ⟨u, hu, v, hv, rfl⟩ := hy
    exact prodsub (mk_mem_prod hu hv)
  refine ⟨U ∩ W, ?_, V, Vopen.mem_nhds onememV, ?_⟩
  · exact mem_nhdsWithin.mpr ⟨U, Uopen, xmemU, subset_rfl⟩
  · exact (mul_subset_mul_right (inter_subset_left (s := U) (t := W))).trans hUV

/-- A compact open set `W` admits a symmetric open neighborhood `T` of the identity with
`W * T ⊆ W`. -/
lemma exists_mulInvClosureNhd_of_isCompact {W : Set G} (hW : IsCompact W) (hWopen : IsOpen W) :
    ∃ T, IsTopologicalGroup.mulInvClosureNhd T W := by
  obtain ⟨S, hS, hSW⟩ := exists_mul_closure_nhds_of_isCompact hW hWopen
  obtain ⟨U, hUS, hUopen, h1U⟩ := mem_nhds_iff.mp hS
  refine ⟨U ∩ U⁻¹, ?_, ?_, ?_, ?_⟩
  · exact inter_mem (hUopen.mem_nhds h1U) (inv_mem_nhds_one G (hUopen.mem_nhds h1U))
  · rw [Set.inter_inv, inv_inv, Set.inter_comm]
  · exact hUopen.inter hUopen.inv
  · intro y hy
    exact hSW ((mul_subset_mul_left (inter_subset_left.trans hUS)) hy)

/-- A compact open neighborhood of the identity contains an open subgroup. -/
lemma exists_openSubgroup_subset_isCompact_isOpen {W : Set G} (hW : IsCompact W)
    (hWopen : IsOpen W) (h1 : (1 : G) ∈ W) :
    ∃ H : OpenSubgroup G, (H : Set G) ⊆ W := by
  obtain ⟨V, hV⟩ := exists_mulInvClosureNhd_of_isCompact hW hWopen
  let S : Subgroup G := {
    carrier := ⋃ n, V ^ (n + 1)
    mul_mem' := fun ha hb ↦ by
      rcases mem_iUnion.mp ha with ⟨k, hk⟩
      rcases mem_iUnion.mp hb with ⟨l, hl⟩
      apply mem_iUnion.mpr
      refine ⟨k + 1 + l, ?_⟩
      rw [add_assoc, pow_add]
      exact Set.mul_mem_mul hk hl
    one_mem' := by
      apply mem_iUnion.mpr
      refine ⟨0, ?_⟩
      simp [mem_of_mem_nhds hV.nhds]
    inv_mem' := fun ha ↦ by
      rcases mem_iUnion.mp ha with ⟨k, hk⟩
      apply mem_iUnion.mpr
      refine ⟨k, ?_⟩
      rw [← hV.inv]
      simpa only [inv_pow, Set.mem_inv, inv_inv] using hk }
  have hSopen : IsOpen (S : Set G) := by
    refine isOpen_iUnion (fun n ↦ ?_)
    rw [pow_succ]
    exact hV.isOpen.mul_left
  refine ⟨⟨S, hSopen⟩, ?_⟩
  have mulVpow (n : ℕ) : W * V ^ (n + 1) ⊆ W := by
    induction n with
    | zero => simpa using hV.mul
    | succ n ih =>
      rw [pow_succ, ← mul_assoc]
      exact (Set.mul_subset_mul_right ih).trans hV.mul
  have hpow (n : ℕ) : V ^ (n + 1) ⊆ W * V ^ (n + 1) := by
    intro x hx
    exact ⟨1, h1, x, hx, one_mul x⟩
  intro x hx
  obtain ⟨n, hn⟩ := mem_iUnion.mp hx
  exact mulVpow n (hpow n hn)

/-- Every neighborhood of the identity in a locally compact Hausdorff totally disconnected
group contains a compact open subgroup. -/
theorem exists_isCompact_openSubgroup_subset [T2Space G] [LocallyCompactSpace G]
    [TotallyDisconnectedSpace G] {W : Set G} (hW : W ∈ 𝓝 (1 : G)) :
    ∃ H : OpenSubgroup G, IsCompact (H : Set G) ∧ (H : Set G) ⊆ W := by
  obtain ⟨U, hUW, hUopen, h1U⟩ := mem_nhds_iff.mp hW
  obtain ⟨K, hKcomp, h1K, hKU⟩ := exists_compact_subset hUopen h1U
  obtain ⟨V, hVclopen, h1V, hVK⟩ := exists_isClopen_mem_of_isOpen isOpen_interior h1K
  have hVcomp : IsCompact V :=
    hKcomp.of_isClosed_subset hVclopen.1 (hVK.trans interior_subset)
  obtain ⟨H, hHV⟩ := exists_openSubgroup_subset_isCompact_isOpen hVcomp hVclopen.2 h1V
  exact ⟨H, hVcomp.of_isClosed_subset H.isClosed hHV,
    hHV.trans (hVK.trans (interior_subset.trans (hKU.trans hUW)))⟩

end RiemannMasullo
