module

public import RiemannMasullo.ForMathlib.Analysis.Distribution.SchwartzSpace.Montel
import all RiemannMasullo.ForMathlib.Analysis.Distribution.SchwartzSpace.Montel
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv

/-! # Precompact neighborhoods for individual real-line Schwartz seminorms -/

public section

namespace RiemannMasullo

open Filter Function Metric Set Topology
open scoped SchwartzMap BoundedContinuousFunction OnePoint

/-- Uniform bounds for the function, its derivative and its first moment give a
neighborhood with relatively compact image in the supremum norm. -/
private theorem schwartzMap_compactified_precompact_nhds :
    ∃ W ∈ 𝓝 (0 : 𝓢(ℝ, ℂ)), IsCompact (closure (compactifiedSchwartz '' W)) := by
  let p := schwartzSeminormFamily ℂ ℝ ℂ
  let W := (p (0, 0)).ball 0 1 ∩ (p (1, 0)).ball 0 1 ∩ (p (0, 1)).ball 0 1
  have hn (i) := (p i).ball_mem_nhds ((schwartz_withSeminorms ℂ ℝ ℂ).continuous_seminorm i)
    (zero_lt_one : (0 : ℝ) < 1)
  refine ⟨W, inter_mem (inter_mem (hn _) (hn _)) (hn _), ?_⟩
  have hb (f : 𝓢(ℝ, ℂ)) (hf : f ∈ W) : p (0, 0) f < 1 ∧ p (1, 0) f < 1 ∧ p (0, 1) f < 1 :=
    ⟨((p _).mem_ball_zero).mp hf.1.1, ((p _).mem_ball_zero).mp hf.1.2,
      ((p _).mem_ball_zero).mp hf.2⟩
  apply BoundedContinuousFunction.arzela_ascoli (closedBall 0 1) (isCompact_closedBall _ _)
  · rintro _ x ⟨f, hf, rfl⟩
    induction x using OnePoint.rec with
    | infty => exact mem_closedBall_self zero_le_one
    | coe x =>
      change dist (f x) 0 ≤ 1
      rw [dist_zero_right]
      exact (f.norm_le_seminorm ℂ x).trans (hb f hf).1.le
  · intro z
    induction z using OnePoint.rec with
    | infty =>
      rw [Metric.equicontinuousAt_iff_right]
      intro ε hε
      apply OnePoint.hasBasis_nhds_infty.eventually_iff.mpr
      refine ⟨closedBall 0 (1 / ε), ⟨isClosed_closedBall, isCompact_closedBall _ _⟩, ?_⟩
      rintro _ (⟨x, hx, rfl⟩ | hz) ⟨_, f, hf, rfl⟩
      · change dist 0 (f x) < ε
        rw [dist_zero_left]
        have hx' : 1 / ε < ‖x‖ := by simpa [mem_closedBall, dist_zero_right] using hx
        have hh : ‖x‖ * ‖f x‖ < 1 := by
          simpa using (f.norm_pow_mul_le_seminorm ℂ 1 x).trans_lt (hb f hf).2.1
        exact lt_of_mul_lt_mul_left (hh.trans (by linarith [(div_lt_iff₀ hε).mp hx'])) (norm_nonneg x)
      · subst hz
        simpa using hε
    | coe x =>
      rw [Metric.equicontinuousAt_iff_right]
      intro ε hε
      rw [OnePoint.nhds_coe_eq, Filter.eventually_map]
      filter_upwards [Metric.ball_mem_nhds x hε] with y hy
      rintro ⟨_, f, hf, rfl⟩
      change dist (f x) (f y) < ε
      have hlip : LipschitzWith 1 (⇑f) := by
        apply lipschitzWith_of_nnNorm_deriv_le f.differentiable
        intro t
        change ‖deriv f t‖ ≤ 1
        simpa using (f.le_seminorm' ℂ 0 1 t).trans (hb f hf).2.2.le
      exact (hlip.dist_le_mul x y).trans_lt (by simpa [dist_comm] using hy)

/-- In the real-line Schwartz space, every continuous seminorm admits a zero-neighborhood
which is totally bounded for that seminorm's pseudometric. -/
theorem schwartzMap_real_exists_totallyBounded_nhds (p : Seminorm ℂ 𝓢(ℝ, ℂ)) (hp : Continuous p) :
    ∃ V ∈ 𝓝 (0 : 𝓢(ℝ, ℂ)), @TotallyBounded _ p.toSeminormedAddCommGroup.toUniformSpace V := by
  classical
  let P := schwartzSeminormFamily ℂ ℝ ℂ
  obtain ⟨s, C, _, hC⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ ℝ ℂ) p hp
  obtain ⟨W, hW, hK⟩ := schwartzMap_compactified_precompact_nhds
  let D (i : s) := schwartzWeightedDeriv i.val.1 i.val.2
  let V := ⋂ i : s, D i ⁻¹' W
  have hV : V ∈ 𝓝 0 := Filter.iInter_mem.mpr fun i ↦ by
    apply (D i).continuous.continuousAt.preimage_mem_nhds
    rwa [map_zero]
  let J (f : 𝓢(ℝ, ℂ)) (i : s) := schwartzCoordinates f i.val
  have hJ : TotallyBounded (J '' V) := by
    apply (isCompact_univ_pi (fun _ : s ↦ hK)).totallyBounded.subset
    rintro _ ⟨f, hf, rfl⟩ i _
    exact subset_closure (mem_image_of_mem _ (mem_iInter.mp hf i))
  refine ⟨V, hV, ?_⟩
  let q := s.sup P
  have hnorm (f : 𝓢(ℝ, ℂ)) : q f = ‖J f‖ := by
    apply le_antisymm
    · apply Seminorm.finset_sup_apply_le (norm_nonneg _)
      intro i hi
      exact (norm_schwartzCoordinates i f).symm.le.trans (norm_le_pi_norm (J f) ⟨i, hi⟩)
    · apply (pi_norm_le_iff_of_nonneg (apply_nonneg q f)).mpr
      intro i
      rw [show J f i = schwartzCoordinates f i.val from rfl, norm_schwartzCoordinates]
      exact (Finset.le_sup (f := P) i.property : _ ≤ q) f
  let := q.toSeminormedAddCommGroup
  let : UniformSpace 𝓢(ℝ, ℂ) := q.toSeminormedAddCommGroup.toUniformSpace
  have hisom : Isometry J := Isometry.of_dist_eq fun f g ↦ by
    rw [dist_eq_norm_sub, dist_eq_norm_sub, show J f - J g = J (f - g) by
      funext i; exact (congrFun (map_sub schwartzCoordinates f g) i.val).symm]
    exact (hnorm _).symm
  have hq := (totallyBounded_image_iff hisom.isUniformInducing).mp hJ
  have hLip := @LipschitzWith.of_dist_le_mul _ _ q.toSeminormedAddCommGroup.toPseudoMetricSpace
    p.toSeminormedAddCommGroup.toPseudoMetricSpace C id (fun x y ↦ by
      rw [@dist_eq_norm_sub _ p.toSeminormedAddCommGroup, @dist_eq_norm_sub _ q.toSeminormedAddCommGroup]
      exact hC (x - y))
  rw [← image_id V]
  exact @TotallyBounded.image _ _ _ p.toSeminormedAddCommGroup.toUniformSpace id V hq
    (@LipschitzWith.uniformContinuous _ _ _ p.toSeminormedAddCommGroup.toPseudoEMetricSpace C id hLip)

end RiemannMasullo
