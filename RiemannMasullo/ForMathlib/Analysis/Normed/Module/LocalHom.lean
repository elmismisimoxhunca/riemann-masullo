module

public import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Tactic.Linarith

/-! # Extending a local additive map on a ball -/

public section

namespace RiemannMasullo

/-- An additive map on a ball about zero in a real normed space extends to an additive
map on the whole space, obtained by subdividing each vector into sufficiently small pieces. -/
theorem exists_addMonoidHom_of_addOn_ball {E A : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [AddCommGroup A] (h : E → A) {r : ℝ} (hr : 0 < r)
    (hadd : ∀ x y, ‖x‖ < r → ‖y‖ < r → ‖x + y‖ < r → h (x + y) = h x + h y) :
    ∃ f : E →+ A, ∀ x, ‖x‖ < r → f x = h x := by
  have hzero : h 0 = 0 := by
    simpa using hadd 0 0 (by simpa using hr) (by simpa using hr) (by simpa using hr)
  have hmul (v : E) (n : ℕ) (hv : n * ‖v‖ < r) : h (n • v) = n • h v := by
    induction n with
    | zero => simp [hzero]
    | succ n ih =>
      have hn : n * ‖v‖ < r := by push_cast at hv; nlinarith [norm_nonneg v]
      have hv' : ‖v‖ < r := by push_cast at hv; nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) n) (norm_nonneg v)]
      rw [succ_nsmul, hadd, ih hn, succ_nsmul]
      · exact norm_nsmul_le.trans_lt hn
      · exact hv'
      · simpa only [← succ_nsmul] using (norm_nsmul_le (n := n + 1) (a := v)).trans_lt hv
  have hdiv (x : E) (n : ℕ) (hn : 0 < n) (hx : ‖x‖ < r) :
      h x = n • h ((n : ℝ)⁻¹ • x) := by
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have he := hmul ((n : ℝ)⁻¹ • x) n (by
      rwa [norm_smul_of_nonneg (inv_nonneg.mpr hn'.le), ← mul_assoc, mul_inv_cancel₀ hn'.ne', one_mul])
    rwa [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, mul_inv_cancel₀ hn'.ne', one_smul] at he
  have hlarge (x : E) : ∃ n : ℕ, 0 < n ∧ ‖(n : ℝ)⁻¹ • x‖ < r := by
    obtain ⟨n, hn⟩ := exists_nat_gt (‖x‖ / r)
    have hn' : (0 : ℝ) < n := (div_nonneg (norm_nonneg x) hr.le).trans_lt hn
    refine ⟨n, by exact_mod_cast hn', ?_⟩
    rw [norm_smul_of_nonneg (inv_nonneg.mpr hn'.le), inv_mul_lt_iff₀ hn']
    exact (div_lt_iff₀ hr).mp hn
  choose N hpos hsmall using hlarge
  let f (x : E) := N x • h ((N x : ℝ)⁻¹ • x)
  have hform (x : E) (n : ℕ) (hn : 0 < n) (hx : ‖(n : ℝ)⁻¹ • x‖ < r) :
      f x = n • h ((n : ℝ)⁻¹ • x) := by
    unfold f
    rw [hdiv _ n hn (hsmall x), hdiv _ (N x) (hpos x) hx,
      smul_comm (n : ℝ)⁻¹ (N x : ℝ)⁻¹, smul_comm (N x) n]
  have hlocal (x : E) (hx : ‖x‖ < r) : f x = h x := by simpa using hform x 1 one_pos (by simpa using hx)
  refine ⟨{ toFun := f, map_zero' := (hlocal 0 (by simpa using hr)).trans hzero, map_add' := ?_ }, hlocal⟩
  intro x y
  obtain ⟨n, hn⟩ := exists_nat_gt ((‖x‖ + ‖y‖) / r)
  have hn' : (0 : ℝ) < n := (div_nonneg (add_nonneg (norm_nonneg x) (norm_nonneg y)) hr.le).trans_lt hn
  have hn0 : 0 < n := by exact_mod_cast hn'
  have hlt (v : E) (hv : ‖v‖ ≤ ‖x‖ + ‖y‖) : ‖(n : ℝ)⁻¹ • v‖ < r := by
    rw [norm_smul_of_nonneg (inv_nonneg.mpr hn'.le), inv_mul_lt_iff₀ hn']
    exact hv.trans_lt ((div_lt_iff₀ hr).mp hn)
  have hx := hlt x (le_add_of_nonneg_right (norm_nonneg y))
  have hy := hlt y (le_add_of_nonneg_left (norm_nonneg x))
  have hxy := hlt _ (norm_add_le x y)
  rw [hform _ n hn0 hxy, hform x n hn0 hx, hform y n hn0 hy, smul_add,
    hadd _ _ hx hy (by rwa [← smul_add]), nsmul_add]

end RiemannMasullo
