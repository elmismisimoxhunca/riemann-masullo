module

public import Mathlib.Topology.Algebra.PontryaginDual
public import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import RiemannMasullo.ForMathlib.Topology.Covering.AddCircle

/-! # Smoothness of continuous characters on a real normed space -/

public section

namespace RiemannMasullo

/-- A continuous character of a real normed space is smooth: its phase lifts to a
continuous linear functional. -/
theorem contDiff_vector_character {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (χ : PontryaginDual (Multiplicative E)) (p : WithTop ℕ∞) :
    ContDiff ℝ p (fun x : E ↦ (χ (Multiplicative.ofAdd x) : ℂ)) := by
  let q := AddCircle.homeomorphCircle (one_ne_zero : (1 : ℝ) ≠ 0)
  let a : E →+ AddCircle (1 : ℝ) :=
    { toFun := fun x ↦ q.symm (χ (Multiplicative.ofAdd x))
      map_zero' := by
        apply q.injective
        rw [q.apply_symm_apply, AddCircle.homeomorphCircle_apply, AddCircle.toCircle_zero]
        exact map_one χ
      map_add' := fun x y ↦ by
        apply q.injective
        rw [q.apply_symm_apply, AddCircle.homeomorphCircle_apply, AddCircle.toCircle_add]
        simp only [← AddCircle.homeomorphCircle_apply one_ne_zero, q, Homeomorph.apply_symm_apply]
        exact map_mul χ (Multiplicative.ofAdd x) (Multiplicative.ofAdd y) }
  obtain ⟨L, hL⟩ := exists_addCircle_coe_linearMap_eq a (q.symm.continuous.comp χ.continuous)
  have he (x : E) : (χ (Multiplicative.ofAdd x) : ℂ) =
      Complex.exp (((2 * Real.pi * L x : ℝ) : ℂ) * Complex.I) := by
    have h := congrArg q (hL x)
    change q ((L x : ℝ) : AddCircle (1 : ℝ)) = q (q.symm _) at h
    rw [q.apply_symm_apply, AddCircle.homeomorphCircle_apply, AddCircle.toCircle_apply_mk] at h
    rw [← h, Circle.coe_exp, div_one]
  simp_rw [he]
  exact Complex.contDiff_exp.comp ((Complex.ofRealCLM.contDiff.comp
    (contDiff_const.mul L.contDiff)).mul contDiff_const)

end RiemannMasullo
