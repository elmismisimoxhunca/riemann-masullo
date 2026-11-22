module

public import Mathlib.Analysis.Meromorphic.Complex
public import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne

/-! # Pole orders of the archimedean gamma factors -/

public section

open Complex Filter Set
open scoped Topology

namespace RiemannMasullo

/-- The gamma function has a simple pole at each nonpositive integer. -/
theorem meromorphicOrderAt_Gamma_neg_nat (n : ℕ) :
    meromorphicOrderAt Gamma (-(n : ℂ)) = -1 := by
  have step (s : ℂ) : meromorphicOrderAt Gamma s =
      meromorphicOrderAt Gamma (s + 1) - meromorphicOrderAt id s := by
    have he : Gamma =ᶠ[𝓝[≠] s] (Gamma ∘ (· + 1)) / id := by
      filter_upwards [(nhdsNE_le_cofinite s) (eventually_cofinite_ne 0)] with z hz
      change Gamma z = Gamma (z + 1) / z
      rw [Gamma_add_one z hz, mul_div_cancel_left₀ _ hz]
    rw [meromorphicOrderAt_congr he, meromorphicOrderAt_div
      ((Meromorphic.Gamma (s + 1)).comp_analyticAt (g := (· + 1)) (analyticAt_id.add analyticAt_const))
      analyticAt_id.meromorphicAt, meromorphicOrderAt_comp_add_const_eq_meromorphicOrderAt]
  induction n with
  | zero =>
    simp only [Nat.cast_zero, neg_zero]
    rw [step, zero_add, meromorphicOrderAt_id,
      (MeromorphicNFOn.Gamma (mem_univ 1)).meromorphicOrderAt_eq_zero_iff.mpr (by simp)]
    rfl
  | succ n ih =>
    have hn : -((n + 1 : ℕ) : ℂ) ≠ 0 :=
      neg_ne_zero.mpr (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n))
    rw [step, analyticAt_id.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr hn,
      sub_zero, Nat.cast_succ, show -((n : ℂ) + 1) + 1 = -n by ring]
    exact ih

/-- The pole order of the gamma function is at most one. -/
theorem neg_one_le_meromorphicOrderAt_Gamma (s : ℂ) :
    -1 ≤ meromorphicOrderAt Gamma s := by
  by_cases h : Gamma s = 0
  · obtain ⟨n, rfl⟩ := (Gamma_eq_zero_iff s).mp h
    exact (meromorphicOrderAt_Gamma_neg_nat n).ge
  · rw [(MeromorphicNFOn.Gamma (mem_univ s)).meromorphicOrderAt_eq_zero_iff.mpr h]
    decide

/-- The Deligne gamma factor for a real place has at most a simple pole. -/
theorem neg_one_le_meromorphicOrderAt_Gammaℝ (s : ℂ) :
    -1 ≤ meromorphicOrderAt Gammaℝ s := by
  have hπ : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  change -1 ≤ meromorphicOrderAt ((fun z : ℂ ↦ (Real.pi : ℂ) ^ (-z / 2)) *
    (Gamma ∘ (· / 2))) s
  rw [meromorphicOrderAt_mul_of_ne_zero
    (((differentiable_neg.div_const (2 : ℂ)).const_cpow (.inl hπ)).analyticAt s)
    (cpow_ne_zero_iff.mpr (.inl hπ)), meromorphicOrderAt_comp_of_deriv_ne_zero
    (g := fun z : ℂ ↦ z / 2) analyticAt_id.div_const (by simp)]
  exact neg_one_le_meromorphicOrderAt_Gamma _

/-- The Deligne gamma factor for a complex place has at most a simple pole. -/
theorem neg_one_le_meromorphicOrderAt_Gammaℂ (s : ℂ) :
    -1 ≤ meromorphicOrderAt Gammaℂ s := by
  have h : (2 * (Real.pi : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero)
  change -1 ≤ meromorphicOrderAt ((fun z : ℂ ↦ 2 * (2 * (Real.pi : ℂ)) ^ (-z)) * Gamma) s
  rw [meromorphicOrderAt_mul_of_ne_zero
    (((differentiable_neg.const_cpow (.inl h)).const_mul (2 : ℂ)).analyticAt s)
    (mul_ne_zero two_ne_zero (cpow_ne_zero_iff.mpr (.inl h)))]
  exact neg_one_le_meromorphicOrderAt_Gamma _

end RiemannMasullo
