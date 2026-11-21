module

public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.UrysohnsLemma

/-! # Absolutely summable compact-test expansions for integrable functions -/

public section

open MeasureTheory Filter Set Topology
open scoped ENNReal NNReal

namespace RiemannMasullo

variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] {μ : Measure X}

/-- Absolute convergence in integral norm implies integrability of the pointwise sum. -/
theorem integrable_tsum_of_lintegral_eNorm [CompleteSpace E] {g : ℕ → X → E}
    (hm : ∀ n, AEStronglyMeasurable (g n) μ) (hs : ∑' n, ∫⁻ x, ‖g n x‖ₑ ∂μ ≠ ⊤) :
    Integrable (fun x ↦ ∑' n, g n x) μ := by
  refine ⟨.tsum hm, hasFiniteIntegral_iff_eNorm.mpr ?_⟩
  refine lt_of_le_of_lt (lintegral_mono fun x ↦ eNorm_tsum_le_tsum_eNorm) ?_
  rwa [lintegral_tsum (fun n ↦ (hm n).eNorm), lt_top_iff_ne_top]

variable [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [BorelSpace X]
  [μ.Regular] [NormedSpace ℝ E]

/-- Compact-test density for a locally compact Hausdorff domain, without a normality
assumption: regularity sandwiches each finite-measure set between a compact and an open set. -/
private theorem exists_compactTest_eLpNorm_sub_le {f : X → E} (hf : Integrable f μ)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) : ∃ g, eLpNorm (f - g) 1 μ ≤ ε ∧ Continuous g ∧ HasCompactSupport g := by
  classical
  apply (memLp_one_iff_integrable.mpr hf).induction_dense (by simp) _ _ _ hε
  · intro c s hsm hsf δ hδ
    obtain ⟨η, hη, hsmall⟩ := exists_eLpNorm_indicator_le (p := 1) (μ := μ) (by simp) c hδ
    have hη' : (η : ℝ≥0∞) / 2 ≠ 0 := (ENNReal.half_pos (ENNReal.coe_ne_zero.mpr hη.ne')).ne'
    obtain ⟨U, hsU, hU, -, hUs⟩ := hsm.exists_isOpen_sdiff_lt hsf.ne hη'
    obtain ⟨K, hKs, hK, hsK⟩ := hsm.exists_isCompact_sdiff_lt hsf.ne hη'
    obtain ⟨b, hbK, hbU, hbs, hb⟩ := exists_continuous_one_zero_of_isCompact hK hU.isClosed_compl
      (disjoint_compl_right_iff_subset.mpr (hKs.trans hsU))
    have hμ : μ (U \ K) ≤ η := calc
      _ ≤ μ ((U \ s) ∪ (s \ K)) := measure_mono (by grind)
      _ ≤ _ := measure_union_le _ _
      _ ≤ _ := (add_le_add hUs.le hsK.le).trans_eq (ENNReal.add_halves _)
    let g (x : X) := b x • c
    have hc : Continuous g := b.continuous.smul continuous_const
    have hs : HasCompactSupport g := hbs.comp_left (g := fun t : ℝ ↦ t • c) (zero_smul _ _)
    refine ⟨g, ?_, hc, hs⟩
    refine (eLpNorm_mono ((hc.integrable_of_hasCompactSupport hs).1.sub (aestronglyMeasurable_const.indicator hsm))
      (g := (U \ K).indicator (fun _ ↦ c)) ?_).trans
      (hsmall _ hμ (hU.measurableSet.diff hK.measurableSet).nullMeasurableSet)
    intro x
    by_cases hxK : x ∈ K
    · simp [g, hxK, hKs hxK, show b x = 1 from hbK hxK]
    by_cases hxs : x ∈ s
    · simp only [Pi.sub_apply, indicator_of_mem hxs, indicator_of_mem
        (show x ∈ U \ K from ⟨hsU hxs, hxK⟩), g]
      rw [show b x • c - c = (b x - 1) • c by rw [sub_smul, one_smul], norm_smul]
      have hle : ‖b x - 1‖ ≤ 1 := by
        rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [(hb x).1, (hb x).2]
      simpa using mul_le_mul_of_nonneg_right hle (norm_nonneg c)
    · by_cases hxU : x ∈ U
      · simpa [g, hxU, hxK, hxs, norm_smul, Real.norm_eq_abs, abs_of_nonneg (hb x).1] using
          mul_le_mul_of_nonneg_right (hb x).2 (norm_nonneg c)
      · simp [g, hxU, hxs, show b x = 0 from hbU hxU]
  · exact fun _ _ ⟨hc, hs⟩ ⟨hc', hs'⟩ ↦ ⟨hc.add hc', hs.add hs'⟩

/-- Expand an integrable function almost everywhere in compactly supported continuous
functions whose integral norms sum to a finite number. -/
theorem exists_compactTest_tsum {f : X → E} (hf : Integrable f μ) :
    ∃ g : ℕ → X → E, (∀ n, Continuous (g n) ∧ HasCompactSupport (g n)) ∧
      (∑' n, ∫⁻ x, ‖g n x‖ₑ ∂μ) ≠ ⊤ ∧ (f =ᵐ[μ] fun x ↦ ∑' n, g n x) := by
  obtain ⟨δ, hδ, hδs⟩ := ENNReal.exists_pos_sum_of_countable' (ε := ⊤) (by simp) ℕ
  choose a ha hac has using fun n ↦ exists_compactTest_eLpNorm_sub_le hf (hδ n).ne'
  let g : ℕ → X → E := fun n ↦ Nat.casesOn n (a 0) (fun k ↦ a (k + 1) - a k)
  have hg (n) : Continuous (g n) ∧ HasCompactSupport (g n) := by
    cases n with
    | zero => exact ⟨hac 0, has 0⟩
    | succ n => exact ⟨(hac _).sub (hac n), (has _).sub (has n)⟩
  have htail (n : ℕ) : eLpNorm (g (n + 1)) 1 μ ≤ δ n + δ (n + 1) := by
    have he : g (n+1) = (f - a n) - (f - a (n + 1)) := by dsimp [g]; abel
    exact he ▸ (eLpNorm_sub_le le_rfl).trans (add_le_add (ha n) (ha (n + 1)))
  have hsum : ∑' n, eLpNorm (g n) 1 μ ≠ ⊤ := by
    intro h
    have h0 : eLpNorm (g 0) 1 μ ≠ ⊤ := (memLp_one_iff_integrable.mpr
      ((hac 0).integrable_of_hasCompactSupport (has 0))).eLpNorm_lt_top.ne
    have ht := ENNReal.tsum_add_one_eq_top h h0
    have hh := tsum_le_tsum (f := fun n ↦ eLpNorm (g (n + 1)) 1 μ) (g := fun n ↦ δ n + δ (n + 1)) htail
    rw [ht, tsum_add] at hh
    exact (not_le_of_gt (ENNReal.add_lt_top.mpr ⟨hδs,
      (tsum_comp_le_tsum_of_injective Nat.succ_injective δ).trans_lt hδs⟩)) hh
  refine ⟨g, hg, ?_, ?_⟩
  · have he n := eLpNorm_one_eq_lintegral_eNorm (((hg n).1.integrable_of_hasCompactSupport (μ := μ) (hg n).2).1)
    simpa only [he] using hsum
  · have herr := summable_norm_of_tsum_eLpNorm_ne_top (le_refl (1 : ℝ≥0∞))
        ((tsum_le_tsum (f := fun n ↦ eLpNorm (f - a n) 1 μ) (g := δ) ha).trans_lt hδs).ne
    filter_upwards [herr, summable_norm_of_tsum_eLpNorm_ne_top le_rfl hsum] with x hx hx'
    symm
    apply HasSum.tsum_eq
    apply (hasSum_iff_tendsto_nat_of_summable_norm hx').mpr
    apply (tendsto_add_atTop_iff_nat 1).mp
    have hpart (n : ℕ) : ∑ i ∈ Finset.range (n+1), g i x = a n x := by
      induction n with
      | zero => simp [g]
      | succ n ih => rw [Finset.sum_range_succ, ih]; dsimp [g]; abel
    simp_rw [hpart]
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simpa only [Pi.sub_apply, norm_sub_rev (f x)] using hx.tendsto_atTop_zero

end RiemannMasullo
