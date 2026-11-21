module

public import RiemannMasullo.AppC_LCTVS.Sec5a
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
public import Mathlib.MeasureTheory.VectorMeasure.WithDensity
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Liouville
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.Analysis.Normed.Module.Completion
import RiemannMasullo.ForMathlib.Analysis.LocallyConvex.HahnBanach
import RiemannMasullo.ForMathlib.MeasureTheory.VectorMeasure.Integral

/-!
# Holomorphic and meromorphic vector-valued functions

Masullo, Appendix C, §§C.5.2–C.5.4. Functions on a subset of the plane are
represented by ambient functions restricted to that subset.
-/

@[expose] public noncomputable section

open Bornology Filter Function MeasureTheory Set Topology
open scoped ContDiff

namespace RiemannMasullo

attribute [local instance] IsTopologicalAddGroup.rightUniformSpace

section Holomorphy

variable {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
variable {Ω : Set ℂ}

/-- Paper: Definition C.5.2.1(1), p. 737. Weak continuity is continuity after
evaluation by each continuous complex-linear functional. -/
def WeaklyContinuousOn (f : ℂ → E) (Ω : Set ℂ) : Prop :=
  ∀ φ : StrongDual ℂ E, ContinuousOn (φ ∘ f) Ω

/-- Paper: Definition C.5.2.1(2), p. 737. Weak continuous differentiability through
order `k` is continuous differentiability through that order after scalar evaluation.
Deviation: The scalar `C^k` condition uses real derivatives on the complex plane. -/
def WeaklyContDiffOrderOn (k : ℕ) (f : ℂ → E) (Ω : Set ℂ) : Prop :=
  ∀ φ : StrongDual ℂ E, ContDiffOn ℝ k (φ ∘ f) Ω

/-- Paper: Definition C.5.2.1(3), p. 737. Weak holomorphy is weak differentiability
over the complex field as in §C.5.1. -/
abbrev WeaklyHolomorphicOn (f : ℂ → E) (Ω : Set ℂ) : Prop :=
  WeaklyDifferentiableOn ℂ f Ω

/-- Paper: Definition C.5.2.1(1–3), p. 737. Scalar testing on the complex line
recovers ordinary continuity, real smoothness of the specified order, and holomorphy.
Deviation: This is a sanity check for the three weak definitions. -/
theorem weakComplexRegularity_iff (f : ℂ → ℂ) (k : ℕ) :
    (WeaklyContinuousOn f Ω ↔ ContinuousOn f Ω) ∧
      (WeaklyContDiffOrderOn k f Ω ↔ ContDiffOn ℝ k f Ω) ∧
      (WeaklyHolomorphicOn f Ω ↔ DifferentiableOn ℂ f Ω) := by
  refine ⟨⟨fun h ↦ h (ContinuousLinearMap.id ℂ ℂ), ?_⟩,
    ⟨fun h ↦ h (ContinuousLinearMap.id ℂ ℂ), ?_⟩,
    ⟨fun h ↦ h (ContinuousLinearMap.id ℂ ℂ), ?_⟩⟩
  · exact fun hf φ ↦ φ.continuous.comp_continuousOn hf
  · exact fun hf φ ↦ (φ.restrictScalars ℝ).contDiff.comp_contDiffOn hf
  · exact fun hf φ ↦ φ.differentiable.comp_differentiableOn hf

variable [ContinuousSMul ℂ E]

/-- Paper: Definition C.5.2.1(4), p. 737. Holomorphy is differentiability over
the complex field with values in the given topological vector space. -/
abbrev VectorHolomorphicOn (f : ℂ → E) (Ω : Set ℂ) : Prop :=
  DifferentiableOn ℂ f Ω

/-- Paper: (C.5.2.1), p. 737. On an open set, holomorphy means the complex
difference quotients have a limit in the target at every point. -/
theorem vectorHolomorphicOn_iff_tendsto (hΩ : IsOpen Ω) [IsTopologicalAddGroup E]
    (f : ℂ → E) :
    VectorHolomorphicOn f Ω ↔ ∀ z ∈ Ω, ∃ v : E,
      Tendsto (fun w ↦ (w - z)⁻¹ • (f w - f z)) (𝓝[≠] z) (𝓝 v) := by
  have slope_iff (z : ℂ) (v : E) : HasDerivAt f v z ↔
      Tendsto (fun w ↦ (w - z)⁻¹ • (f w - f z)) (𝓝[≠] z) (𝓝 v) := by
    rw [hasDerivAt_iff_hasFDerivAt, ← hasFDerivWithinAt_univ,
      ← hasFDerivWithinAt_sdiff_singleton_self, ← Set.compl_eq_univ_sdiff,
      hasFDerivWithinAt_iff_isLittleOTVS]
    change (fun w ↦ f w - f z - (w - z) • v) =o[ℂ; 𝓝[≠] z] (fun w ↦ w - z) ↔ _
    rw [Asymptotics.isLittleOTVS_iff_tendsto_inv_smul (by
      filter_upwards with w hw
      simp [sub_eq_zero.mp hw])]
    conv_rhs => rw [← tendsto_sub_nhds_zero_iff]
    apply tendsto_congr'
    filter_upwards [eventually_mem_nhdsWithin] with w hw
    simp [smul_sub, inv_smul_smul₀ (sub_ne_zero.mpr hw)]
  constructor
  · intro hf z hz
    obtain ⟨L, hL⟩ := hf z hz
    exact ⟨L 1, (slope_iff z _).mp (hL.hasFDerivAt (hΩ.mem_nhds hz)).hasDerivAt⟩
  · intro hf z hz
    obtain ⟨v, hv⟩ := hf z hz
    exact ⟨_, ((slope_iff z v).mpr hv).hasFDerivAt.hasFDerivWithinAt⟩

omit [ContinuousSMul ℂ E] in
/-- A continuous linear map sends the derivative of a vector-valued holomorphic
function to the derivative of the composite. -/
private theorem VectorHolomorphicOn.hasDerivAt_comp
    [IsTopologicalAddGroup E] {F : Type*} [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
    [IsTopologicalAddGroup F] [ContinuousSMul ℂ F] {f : ℂ → E}
    (hf : VectorHolomorphicOn f Ω) (hΩ : IsOpen Ω) (j : E →L[ℂ] F) (x : Ω) :
    HasDerivAt (j ∘ f) (j (deriv f x)) (x : ℂ) := by
  have h := hf.hasFDerivAt (hΩ.mem_nhds x.property)
  have hj : HasFDerivAt (j ∘ f) (j.comp (fderiv ℂ f x)) (x : ℂ) := by
    apply HasFDerivAt.of_isLittleOTVS
    simpa only [Function.comp_def, ContinuousLinearMap.comp_apply, map_sub]
      using j.isBigOTVS_comp.trans_isLittleOTVS h.isLittleOTVS
  exact hj.hasDerivAt

/-- Paper: Remark C.5.2.2, p. 737. On a complex domain, holomorphy agrees with
the strong continuous differential of §C.5.1 in one complex variable. -/
theorem vectorHolomorphicOn_iff_vectorContDiffOn (hΩ : IsOpen Ω) (hconn : IsConnected Ω)
    [IsTopologicalAddGroup E] [T2Space E] [PolynormableSpace ℂ E] (f : ℂ → E) :
    VectorHolomorphicOn f Ω ↔ VectorContDiffOn (k := ℂ) Ω f := by
  clear hconn
  have scalar_remainder (x : Ω) (v : E) (φ : StrongDual ℂ E) :
      HasDerivWithinAt (φ ∘ f) (φ v) Ω (x : ℂ) ↔
        Tendsto (fun y : ℂ ↦ ((‖y - (x : ℂ)‖⁻¹ : ℝ) : ℂ) *
          (φ (f y) - φ (f x) - (y - (x : ℂ)) * φ v))
          (𝓝[Ω \ {(x : ℂ)}] (x : ℂ)) (𝓝 0) := by
    rw [hasDerivWithinAt_iff_hasFDerivWithinAt, ← hasFDerivWithinAt_sdiff_singleton_self,
      ← hasDerivWithinAt_iff_hasFDerivWithinAt, hasDerivWithinAt_iff_tendsto]
    conv_rhs => rw [tendsto_zero_iff_norm_tendsto_zero]
    simp only [Function.comp_apply, smul_eq_mul, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg _)]
  let ev (φ : StrongDual ℂ E) : PettisWeakCompletion E →L[ℂ] ℂ := WeakBilin.eval _ φ
  have heval (φ : StrongDual ℂ E) (v : E) : ev φ (toPettisWeakCompletion E v) = φ v := rfl
  let remainder (D : Ω × ℂ → E) (x : Ω) (y : ℂ) : PettisWeakCompletion E :=
    ((‖y - (x : ℂ)‖⁻¹ : ℝ) : ℂ) •
      (toPettisWeakCompletion E (f y) - toPettisWeakCompletion E (f x) -
        (toPettisWeakCompletion E ∘ D) (x, y - (x : ℂ)))
  constructor
  · intro hf
    have hcontinuous : Continuous (fun x : Ω ↦ deriv f x) := by
      rw [continuous_iff_continuousAt]
      intro x
      apply ((PolynormableSpace.withSeminorms ℂ E).tendsto_nhds _ _).2
      intro p ε hε
      -- Put the seminorm topology on a copy of E and pass to its Banach completion.
      let e : ULift.{0} E ≃ₗ[ℂ] E := ULift.moduleEquiv
      let q : Seminorm ℂ (ULift.{0} E) := p.val.comp e.toLinearMap
      let group : SeminormedAddCommGroup (ULift.{0} E) := q.toSeminormedAddCommGroup
      let : UniformSpace (ULift.{0} E) := group.toUniformSpace
      let : TopologicalSpace (ULift.{0} E) := group.toUniformSpace.toTopologicalSpace
      let : NormedSpace ℂ (ULift.{0} E) := ⟨fun c v ↦ (map_smul_eq_mul q c v).le⟩
      let j₀ := UniformSpace.Completion.toComplL (S := ℂ) (α := ULift.{0} E)
      have he : Continuous e.symm := by
        rw [continuous_iff_continuousAt]
        intro v
        apply Metric.tendsto_nhds.mpr
        intro r hr
        have hp : Continuous (fun y : E ↦ p.val (y - v)) :=
          p.property.comp (continuous_id.sub continuous_const)
        simp only [dist_eq_norm, ← map_sub]
        change ∀ᶠ y : E in 𝓝 v, p.val (y - v) < r
        exact (hp.continuousAt (x := v)).eventually_lt continuousAt_const (by simpa using hr)
      let j : E →L[ℂ] UniformSpace.Completion (ULift.{0} E) :=
        ⟨j₀.toLinearMap.comp e.symm.toLinearMap, j₀.continuous.comp he⟩
      have hg : DifferentiableOn ℂ (j ∘ f) Ω := fun y hy ↦
        (hf.hasDerivAt_comp hΩ j ⟨y, hy⟩).differentiableAt.differentiableWithinAt
      have hj (y : Ω) : deriv (j ∘ f) y = j (deriv f y) := (hf.hasDerivAt_comp hΩ j y).deriv
      have ht : Continuous (fun y : Ω ↦ j (deriv f y)) :=
        (continuousOn_iff_continuous_domRestrict.mp (hg.deriv hΩ).continuousOn).congr
          fun y ↦ hj y
      filter_upwards [Metric.tendsto_nhds.mp (ht.continuousAt (x := x)) ε hε] with y hy
      rw [dist_eq_norm, ← map_sub] at hy
      change ‖(↑(e.symm (deriv f y - deriv f x)) : UniformSpace.Completion (ULift.{0} E))‖ < ε at hy
      rwa [UniformSpace.Completion.norm_coe] at hy
    let D : Ω × ℂ → E := fun p ↦ p.2 • deriv f p.1
    have hD : Continuous D := continuous_snd.smul (hcontinuous.comp continuous_fst)
    refine ⟨D, hD, continuous_toPettisWeakCompletion.comp hD, fun x ↦ ?_⟩
    refine ⟨⟨(toPettisWeakCompletion E).comp
      ((LinearMap.id : ℂ →ₗ[ℂ] ℂ).smulRight (deriv f x)), fun _ ↦ rfl⟩, ?_⟩
    apply (WeakBilin.tendsto_iff_forall_eval_tendsto _ injective_id).2
    intro φ
    change Tendsto (fun y ↦ ev φ (remainder D x y)) (𝓝[Ω \ {(x : ℂ)}] (x : ℂ)) (𝓝 (ev φ 0))
    simpa only [remainder, D, Function.comp_apply, map_zero, map_sub, map_smul, heval,
      smul_eq_mul] using (scalar_remainder x _ φ).mp (hf.hasDerivAt_comp hΩ φ x).hasDerivWithinAt
  · rintro ⟨D, hD, _, hweak⟩
    let d : Ω → E := fun x ↦ D (x, 1)
    have hd : Continuous d := hD.comp (continuous_id.prodMk continuous_const)
    have hscalar (φ : StrongDual ℂ E) (x : Ω) :
        HasDerivAt (φ ∘ f) (φ (d x)) (x : ℂ) := by
      obtain ⟨⟨L, hL⟩, hrem⟩ := hweak x
      have hdir (w : ℂ) : ev φ (toPettisWeakCompletion E (D (x, w))) = w * φ (d x) := by
        change ev φ ((toPettisWeakCompletion E ∘ D) (x, w)) = _
        rw [hL w, show L w = w • L 1 by rw [← map_smul, smul_eq_mul, mul_one], ← hL 1,
          map_smul, Function.comp_apply, heval, smul_eq_mul]
      apply HasDerivWithinAt.hasDerivAt _ (hΩ.mem_nhds x.property)
      apply (scalar_remainder x _ φ).mpr
      have h := (WeakBilin.tendsto_iff_forall_eval_tendsto _ injective_id).mp hrem φ
      change Tendsto (fun y ↦ ev φ (remainder D x y)) _ (𝓝 (ev φ 0)) at h
      simpa only [Function.comp_apply, remainder, map_zero, map_smul, map_sub, hdir, heval,
        smul_eq_mul] using h
    apply (vectorHolomorphicOn_iff_tendsto hΩ f).2
    intro z hz
    let x : Ω := ⟨z, hz⟩
    refine ⟨d x, ((PolynormableSpace.withSeminorms ℂ E).tendsto_nhds _ _).2 ?_⟩
    intro p ε hε
    have hnear : ∀ᶠ y : Ω in 𝓝 x, p.val (d y - d x) < ε / 2 :=
      (p.property.comp (hd.sub continuous_const)).continuousAt.eventually_lt
        continuousAt_const (by simpa [d] using half_pos hε)
    obtain ⟨r, hr, hcontrol⟩ := Metric.eventually_nhds_iff.mp hnear
    have hnear' : Ω ∩ Metric.ball z r ∈ 𝓝 z :=
      inter_mem (hΩ.mem_nhds hz) (Metric.ball_mem_nhds z hr)
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hnear'
    filter_upwards [mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds z hδ),
      self_mem_nhdsWithin] with w hw hwz
    have hwz' : w - z ≠ 0 := sub_ne_zero.mpr hwz
    obtain ⟨φ, hφ, heq⟩ := exists_dual_norm_eq_seminorm p.val p.property
      ((w - z)⁻¹ • (f w - f z) - d x)
    -- Estimate the scalar remainder using a functional attaining its seminorm.
    let g (y : ℂ) := φ (f y) - y * φ (d x)
    have hg (y : ℂ) (hy : y ∈ Metric.ball z δ) :
        HasDerivAt g (φ (d ⟨y, (hball hy).1⟩ - d x)) y := by
      simpa [g, Pi.sub_def, Function.comp_apply, map_sub] using
        (hscalar φ ⟨y, (hball hy).1⟩).sub ((hasDerivAt_id' y).mul_const (φ (d x)))
    have hmean : ‖g w - g z‖ ≤ ε / 2 * ‖w - z‖ :=
      (convex_ball z δ).norm_image_sub_le_of_norm_deriv_le
        (fun y hy ↦ (hg y hy).differentiableAt) (fun y hy ↦ by
          rw [(hg y hy).deriv]
          exact (hφ _).trans (hcontrol (y := ⟨y, (hball hy).1⟩) (hball hy).2).le)
        (Metric.mem_ball_self hδ) hw
    rw [← heq]
    have hquot : φ ((w - z)⁻¹ • (f w - f z) - d x) = (w - z)⁻¹ • (g w - g z) := by
      simp only [g, map_sub, map_smul, smul_eq_mul]
      field_simp [hwz']
      ring
    rw [hquot, norm_smul, norm_inv]
    apply lt_of_le_of_lt _ (half_lt_self hε)
    exact (inv_mul_le_iff₀ (norm_pos_iff.mpr hwz')).2 (by simpa [mul_comm] using hmean)

end Holomorphy

/-- Paper: Arc convention before Theorem C.5.2.4, p. 738. A contour is a closed,
continuous path with finitely many continuously differentiable pieces.
Deviation: The parameter interval is normalized to `[0, 1]` and the parametrization
is extended continuously to the real line. -/
structure ComplexContour where
  toContinuousMap : C(ℝ, ℂ)
  closed : toContinuousMap 1 = toContinuousMap 0
  piecewiseContDiff : ∃ (n : ℕ) (t : Fin (n + 1) → ℝ),
    StrictMono t ∧ t 0 = 0 ∧ t (Fin.last n) = 1 ∧
      ∀ i : Fin n, ContDiffOn ℝ 1 toContinuousMap (Icc (t i.castSucc) (t i.succ))

/-- Paper: Arc convention before Theorem C.5.2.4, p. 738. The trace is the image of
the parameter interval. -/
def ComplexContour.trace (γ : ComplexContour) : Set ℂ :=
  γ.toContinuousMap '' Icc 0 1

/-- Paper: Remark C.5.2.5, p. 738. The contour measure is the pushforward of
Lebesgue measure weighted by the complex velocity on the parameter interval. -/
def ComplexContour.measure (γ : ComplexContour) : ComplexMeasure ℂ :=
  ((volume.restrict (Icc (0 : ℝ) 1)).withDensityᵥ
    (deriv (fun t ↦ γ.toContinuousMap t))).map γ.toContinuousMap

/-- Paper: Winding number notation in Theorem C.5.4.1, p. 741. The winding number
off the trace is expressed by its normalized scalar contour integral.
Deviation: It is represented by its value in `ℂ`. -/
def ComplexContour.index (γ : ComplexContour) (z : ℂ) : ℂ :=
  (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
    (PettisMeasure.complex γ.measure).scalarIntegral (fun w ↦ (w - z)⁻¹)

/-- Paper: Contours in Theorem C.5.2.4, p. 738. A positively oriented simple
contour is injective before the repeated endpoint and has index zero or one off its trace. -/
def PositiveSimpleContour :=
  { γ : ComplexContour // InjOn γ.toContinuousMap (Ico 0 1) ∧
    ∀ z ∉ γ.trace, γ.index z = 0 ∨ γ.index z = 1 }

/-- Paper: Contour interior in Theorem C.5.2.4, p. 738. The interior of a positively
oriented simple contour consists of points off the trace with index one. -/
def PositiveSimpleContour.interior (γ : PositiveSimpleContour) : Set ℂ :=
  {z | z ∉ γ.val.trace ∧ γ.val.index z = 1}

/-- Paper: Contours in Theorem C.5.2.4, p. 738. The counterclockwise round circle has
the usual trace and interior, and its velocity measure gives the reciprocal integral.
Deviation: This is a sanity check for the contour, measure, and index definitions. -/
theorem exists_positiveSimpleContour_circle (z : ℂ) {r : ℝ} (hr : 0 < r) :
    ∃ γ : PositiveSimpleContour,
      (∀ t ∈ Icc (0 : ℝ) 1, γ.val.toContinuousMap t = circleMap z r (2 * Real.pi * t)) ∧
      γ.val.trace = Metric.sphere z r ∧ γ.interior = Metric.ball z r ∧ γ.val.index z = 1 ∧
      HasPettisIntegral (.complex γ.val.measure) (fun w ↦ (w - z)⁻¹)
        (2 * (Real.pi : ℂ) * Complex.I) := by
  let p (t : ℝ) := circleMap z r (2 * Real.pi * t)
  have hscale : ContDiff ℝ 1 (fun t : ℝ ↦ 2 * Real.pi * t) := contDiff_const.mul contDiff_id
  have hp : ContDiff ℝ 1 p := (contDiff_circleMap z r).comp hscale
  let γ : ComplexContour :=
    { toContinuousMap := ⟨p, hp.continuous⟩
      closed := by simpa [p] using periodic_circleMap z r 0
      piecewiseContDiff := by
        refine ⟨1, fun i ↦ (i.val : ℝ), ?_, by norm_num, by norm_num, fun _ ↦ hp.contDiffOn⟩
        intro i j hij
        change (i.val : ℝ) < (j.val : ℝ)
        exact_mod_cast (show i.val < j.val from hij) }
  have htrace : γ.trace = Metric.sphere z r := by
    change p '' Icc 0 1 = _
    simp only [p, ← image_image, image_mul_left_Icc' Real.two_pi_pos, mul_zero, mul_one]
    apply le_antisymm
    · rintro _ ⟨θ, _, rfl⟩
      exact circleMap_mem_sphere z hr.le θ
    · rw [← show circleMap z r '' Ioc 0 (2 * Real.pi) = Metric.sphere z r by
        simpa only [abs_of_pos hr] using image_circleMap_Ioc z r]
      exact image_mono Ioc_subset_Icc_self
  have hinj : InjOn γ.toContinuousMap (Ico 0 1) := by
    intro s hs t ht heq
    have hmaps : MapsTo (fun x : ℝ ↦ 2 * Real.pi * x) (Ico 0 1) (Ico 0 (2 * Real.pi)) := by
      intro x hx
      exact ⟨mul_nonneg Real.two_pi_pos.le hx.1, by
        simpa only [mul_one] using mul_lt_mul_of_pos_left hx.2 Real.two_pi_pos⟩
    have hang := (injOn_circleMap_of_abs_sub_le' (c := z) hr.ne'
      (a := 0) (b := 2 * Real.pi) (by simp)) (hmaps hs) (hmaps ht) heq
    exact mul_left_cancel₀ Real.two_pi_pos.ne' hang
  have hvel (t : ℝ) :
      deriv p t = (2 * Real.pi) • deriv (circleMap z r) (2 * Real.pi * t) := by
    rw [deriv_circleMap]
    exact ((hasDerivAt_circleMap z r (2 * Real.pi * t)).scomp t
      (by simpa only [mul_one] using (hasDerivAt_id' t).const_mul (2 * Real.pi))).deriv
  have hcontVel : Continuous (deriv p) := by
    rw [show deriv p = _ from funext hvel]
    simp only [deriv_circleMap]
    fun_prop
  let μ : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1)
  let ν : ComplexMeasure ℝ := μ.withDensityᵥ (deriv p)
  have hvelInt : Integrable (deriv p) μ :=
    hcontVel.continuousOn.integrableOn_compact isCompact_Icc
  have hintegral {f : ℂ → ℂ} (hfm : Measurable f) (hfc : ContinuousOn f (Metric.sphere z r)) :
      Integrable f (PettisMeasure.complex γ.measure).variation ∧
        (PettisMeasure.complex γ.measure).scalarIntegral f = circleIntegral f z r := by
    have hcomp : ContinuousOn (f ∘ p) (Icc 0 1) :=
      hfc.comp hp.continuous.continuousOn (fun t _ ↦ circleMap_mem_sphere z hr.le _)
    have hfi : ν.Integrable (f ∘ p) := by
      change Integrable (f ∘ p) (μ.withDensityᵥ (deriv p)).variation
      rw [Measure.variation_withDensityᵥ hvelInt]
      exact (integrable_withDensity_iff_integrable_smul hcontVel.nnNorm.measurable).2
        ((hcontVel.norm.continuousOn.smul hcomp).integrableOn_compact isCompact_Icc)
    have hfm' := hfm.aestronglyMeasurable (μ := ν.variation.map p)
    refine ⟨hfi.map hfm', ?_⟩
    change (ν.map p).integral f (ContinuousLinearMap.mul ℝ ℂ) = _
    rw [VectorMeasure.integral_map hp.continuous.measurable hfm' hfi]
    change (μ.withDensityᵥ (deriv p)).integral (f ∘ p) (ContinuousLinearMap.mul ℝ ℂ) = _
    rw [VectorMeasure.integral_withDensityᵥ_mul hvelInt hcontVel.measurable hfi]
    change (∫ t in Icc (0 : ℝ) 1, f (p t) * deriv p t) = _
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
    simp_rw [hvel, mul_smul_comm, mul_comm (f (p _))]
    let F (θ : ℝ) := deriv (circleMap z r) θ • f (circleMap z r θ)
    change (∫ t in (0 : ℝ)..1, (2 * Real.pi) • F (2 * Real.pi * t)) = _
    rw [intervalIntegral.integral_smul, intervalIntegral.smul_integral_comp_mul_left]
    simp [circleIntegral, F]
  have hkernel (w : ℂ) (hw : w ∉ Metric.sphere z r) :
      Integrable (fun v ↦ (v - w)⁻¹) (PettisMeasure.complex γ.measure).variation ∧
        (PettisMeasure.complex γ.measure).scalarIntegral (fun v ↦ (v - w)⁻¹) =
          circleIntegral (fun v ↦ (v - w)⁻¹) z r := by
    apply hintegral ((measurable_id.sub_const w).inv)
    exact (continuousOn_id.sub continuousOn_const).inv₀ fun v hv ↦
      sub_ne_zero.mpr (ne_of_mem_of_not_mem hv hw)
  have hconst : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
  have hnotSphere {w : ℂ} (hw : w ∈ Metric.ball z r) : w ∉ Metric.sphere z r :=
    fun hs ↦ (Metric.mem_ball.mp hw).ne (Metric.mem_sphere.mp hs)
  have hballIndex (w : ℂ) (hw : w ∈ Metric.ball z r) : γ.index w = 1 := by
    rw [ComplexContour.index, (hkernel w (hnotSphere hw)).2,
      circleIntegral.integral_sub_inv_of_mem_ball hw, inv_mul_cancel₀ hconst]
  have houtIndex (w : ℂ) (hw : w ∉ Metric.closedBall z r) : γ.index w = 0 := by
    have hd : DifferentiableOn ℂ (fun v : ℂ ↦ (v - w)⁻¹) (Metric.closedBall z r) :=
      (differentiableOn_id.sub_const w).inv fun v hv ↦
        sub_ne_zero.mpr (ne_of_mem_of_not_mem hv hw)
    have hc : DiffContOnCl ℂ (fun v : ℂ ↦ (v - w)⁻¹) (Metric.ball z r) :=
      (show DifferentiableOn ℂ _ (closure (Metric.ball z r)) by
        rwa [closure_ball z hr.ne']).diffContOnCl
    rw [ComplexContour.index, (hkernel w (fun hs ↦ hw (Metric.sphere_subset_closedBall hs))).2,
      hc.circleIntegral_eq_zero hr.le, mul_zero]
  have houtside {w : ℂ} (hs : w ∉ Metric.sphere z r) (hb : w ∉ Metric.ball z r) :
      w ∉ Metric.closedBall z r := by
    intro hc
    apply hb
    rw [← Metric.closedBall_sdiff_sphere]
    exact ⟨hc, hs⟩
  let Γ : PositiveSimpleContour := ⟨γ, hinj, fun w hw ↦ by
    rw [htrace] at hw
    by_cases hb : w ∈ Metric.ball z r
    · exact Or.inr (hballIndex w hb)
    · exact Or.inl (houtIndex w (houtside hw hb))⟩
  have hz : z ∈ Metric.ball z r := Metric.mem_ball_self hr
  have hzs := hnotSphere hz
  refine ⟨Γ, fun _ _ ↦ rfl, htrace, ?_, hballIndex z hz, ?_⟩
  · ext w
    change w ∉ γ.trace ∧ γ.index w = 1 ↔ w ∈ Metric.ball z r
    rw [htrace]
    constructor
    · rintro ⟨hs, hi⟩
      by_contra hb
      exact zero_ne_one ((houtIndex w (houtside hs hb)).symm.trans hi)
    · exact fun hw ↦ ⟨hnotSphere hw, hballIndex w hw⟩
  · refine (pettisIntegral_complex_iff _ _ _).2.2.mpr ⟨(hkernel z hzs).1, ?_⟩
    rw [(hkernel z hzs).2, circleIntegral.integral_sub_inv_of_mem_ball hz]

/-- A point of the parameter interval lies on one smooth piece of a piecewise partition. -/
private lemma exists_mem_contourPiece {n : ℕ} {t : Fin (n + 1) → ℝ}
    (hmono : StrictMono t) (ht0 : t 0 = 0) (ht1 : t (Fin.last n) = 1)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    ∃ i : Fin n, x ∈ Icc (t i.castSucc) (t i.succ) := by
  cases n with
  | zero =>
      have : (0 : ℝ) = 1 := by simpa [Fin.last, ht0] using ht1
      exact absurd this zero_ne_one
  | succ n =>
      classical
      let S : Finset (Fin (n + 2)) := Finset.univ.filter fun j => t j ≤ x
      have hS : S.Nonempty := ⟨0, by simp [S, ht0, hx.1]⟩
      obtain ⟨j, hj, hjmax⟩ := S.exists_max_image (fun j : Fin (n + 2) => (j : ℕ)) hS
      have hjle : t j ≤ x := by simpa [S] using hj
      rcases Fin.eq_castSucc_or_eq_last j with ⟨i, rfl⟩ | rfl
      · refine ⟨i, hjle, ?_⟩
        by_contra hge
        have hle : t i.succ ≤ x := (lt_of_not_ge hge).le
        have hiS : i.succ ∈ S := by simp [S, hle]
        have hval := hjmax _ hiS
        simp only [Fin.coe_castSucc, Fin.val_succ] at hval
        omega
      · have hx1 : x = 1 := le_antisymm hx.2 (by simpa [ht1] using hjle)
        refine ⟨Fin.last n, ?_, by simp [Fin.succ_last, ht1, hx1]⟩
        have hlt : (Fin.last n).castSucc < Fin.last (n + 1) := Fin.castSucc_lt_last _
        simpa [hx1, ht1] using (hmono hlt).le

/-- The velocity of a piecewise `C¹` contour is integrable on the parameter interval. -/
lemma ComplexContour.integrable_deriv (γ : ComplexContour) :
    Integrable (deriv (γ.toContinuousMap : ℝ → ℂ)) (volume.restrict (Icc (0 : ℝ) 1)) := by
  obtain ⟨n, t, hmono, ht0, ht1, hcd⟩ := γ.piecewiseContDiff
  let p : ℝ → ℂ := γ.toContinuousMap
  have hmeas : AEStronglyMeasurable (deriv p) (volume.restrict (Icc (0 : ℝ) 1)) :=
    aestronglyMeasurable_deriv p _
  cases n with
  | zero =>
      have : (0 : ℝ) = 1 := by simpa [Fin.last, ht0] using ht1
      exact absurd this zero_ne_one
  | succ n =>
      have hcont (i : Fin (n + 1)) :
          ContinuousOn (derivWithin p (Icc (t i.castSucc) (t i.succ)))
            (Icc (t i.castSucc) (t i.succ)) :=
        (hcd i).continuousOn_derivWithin (uniqueDiffOn_Icc (hmono i.castSucc_lt_succ)) le_rfl
      have hbound (i : Fin (n + 1)) :
          BddAbove ((fun s => ‖derivWithin p (Icc (t i.castSucc) (t i.succ)) s‖) ''
            Icc (t i.castSucc) (t i.succ)) :=
        (isCompact_Icc.image_of_continuousOn (hcont i).norm).bddAbove
      let bound (i : Fin (n + 1)) : ℝ :=
        sSup ((fun s => ‖derivWithin p (Icc (t i.castSucc) (t i.succ)) s‖) ''
          Icc (t i.castSucc) (t i.succ))
      have hnn (i : Fin (n + 1)) : 0 ≤ bound i := by
        have hab : t i.castSucc < t i.succ := hmono i.castSucc_lt_succ
        exact (norm_nonneg _).trans <|
          le_csSup (hbound i) (mem_image_of_mem _ (left_mem_Icc.mpr hab.le))
      let C : ℝ := ∑ i : Fin (n + 1), bound i
      have hleC (i : Fin (n + 1)) : bound i ≤ C := by
        simpa [C] using Finset.single_le_sum (fun j _ => hnn j) (Finset.mem_univ i)
      have hderiv_eq (i : Fin (n + 1)) {s : ℝ}
          (hs : s ∈ Ioo (t i.castSucc) (t i.succ)) :
          deriv p s = derivWithin p (Icc (t i.castSucc) (t i.succ)) s := by
        have hs' : s ∈ Icc (t i.castSucc) (t i.succ) := Ioo_subset_Icc_self hs
        have hwithin : HasDerivWithinAt p
            (derivWithin p (Icc (t i.castSucc) (t i.succ)) s)
            (Icc (t i.castSucc) (t i.succ)) s :=
          ((hcd i).differentiableOn one_ne_zero s hs').hasDerivWithinAt
        exact (hwithin.hasDerivAt (Icc_mem_nhds hs.1 hs.2)).deriv
      have hsub : {s | s ∈ Icc (0 : ℝ) 1 ∧ C < ‖deriv p s‖} ⊆ range t := by
        intro s hs
        obtain ⟨i, hi⟩ := exists_mem_contourPiece hmono ht0 ht1 hs.1
        have hnot : s ∉ Ioo (t i.castSucc) (t i.succ) := by
          intro hio
          have hle : ‖deriv p s‖ ≤ C := by
            rw [hderiv_eq i hio]
            exact (le_csSup (hbound i)
              (mem_image_of_mem _ (Ioo_subset_Icc_self hio))).trans (hleC i)
          exact not_lt_of_ge hle hs.2
        have hend : s = t i.castSucc ∨ s = t i.succ := by
          rcases hi with ⟨hL, hR⟩
          by_cases hlt : t i.castSucc < s
          · have hge : t i.succ ≤ s := by
              by_contra hlt'
              exact hnot ⟨hlt, lt_of_not_ge hlt'⟩
            exact Or.inr (le_antisymm hR hge)
          · exact Or.inl (le_antisymm (le_of_not_gt hlt) hL)
        rcases hend with rfl | rfl
        · exact ⟨i.castSucc, rfl⟩
        · exact ⟨i.succ, rfl⟩
      have hae : ∀ᵐ s ∂(volume.restrict (Icc (0 : ℝ) 1)), ‖deriv p s‖ ≤ C := by
        rw [ae_restrict_iff' measurableSet_Icc]
        refine measure_mono_null ?_ ((Set.finite_range t).countable.measure_zero volume)
        intro s hs
        obtain ⟨hsI, hsN⟩ := not_imp.mp hs
        exact hsub ⟨hsI, lt_of_not_ge hsN⟩
      exact ⟨hmeas, HasFiniteIntegral.of_bounded hae⟩

/-- Scalar integration against a contour measure is the piecewise path integral. -/
lemma ComplexContour.scalarIntegral_eq_intervalIntegral (γ : ComplexContour) {f : ℂ → ℂ}
    (hf : ContinuousOn f γ.trace) :
    Integrable f (PettisMeasure.complex γ.measure).variation ∧
      (PettisMeasure.complex γ.measure).scalarIntegral f =
        ∫ t in (0 : ℝ)..1, f (γ.toContinuousMap t) *
          deriv (γ.toContinuousMap : ℝ → ℂ) t := by
  classical
  let p : ℝ → ℂ := γ.toContinuousMap
  let μ : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1)
  let v : ℝ → ℂ := deriv p
  have hv : Integrable v μ := γ.integrable_deriv
  have hvm : Measurable v := measurable_deriv p
  let ν : ComplexMeasure ℝ := μ.withDensityᵥ v
  have hfp : ContinuousOn (f ∘ p) (Icc (0 : ℝ) 1) :=
    hf.comp γ.toContinuousMap.continuous.continuousOn fun t ht => ⟨t, ht, rfl⟩
  have hne : (Icc (0 : ℝ) 1).Nonempty := ⟨0, by simp⟩
  obtain ⟨t0, ht0, hmax⟩ := isCompact_Icc.exists_isMaxOn hne hfp.norm
  have hM (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : ‖f (p t)‖ ≤ ‖f (p t0)‖ := hmax ht
  have hmul : Integrable (fun t => f (p t) * v t) μ :=
    hv.bdd_mul (hfp.aestronglyMeasurable_of_isCompact isCompact_Icc measurableSet_Icc)
      (by
        filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
        exact hM t ht)
  have hnn : Measurable fun t => ‖v t‖₊ := hvm.nnNorm
  have hsmul : Integrable (fun t => ‖v t‖₊ • f (p t)) μ := by
    refine hmul.mono ?_ ?_
    · exact hnn.aestronglyMeasurable.smul
        (hfp.aestronglyMeasurable_of_isCompact isCompact_Icc measurableSet_Icc)
    · filter_upwards with t
      rw [NNReal.smul_def, norm_smul, mul_comm]
      simp
  have hfi : ν.Integrable (f ∘ p) := by
    change Integrable (f ∘ p) (μ.withDensityᵥ v).variation
    rw [Measure.variation_withDensityᵥ hv]
    exact (integrable_withDensity_iff_integrable_smul hnn).2 hsmul
  let f0 : ℂ → ℂ := γ.trace.piecewise f (fun _ => 0)
  have htr : MeasurableSet γ.trace :=
    (isCompact_Icc.image γ.toContinuousMap.continuous).isClosed.measurableSet
  have hf0 : Measurable f0 := hf.measurable_piecewise continuousOn_const htr
  have hf0sm : AEStronglyMeasurable f0 (ν.variation.map p) :=
    hf0.stronglyMeasurable.aestronglyMeasurable
  have hcomp : f0 ∘ p =ᵐ[μ] f ∘ p := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    change γ.trace.piecewise f (fun _ => 0) (p t) = f (p t)
    exact Set.piecewise_eq_of_mem γ.trace f (fun _ => 0) ⟨t, ht, rfl⟩
  have hcompν : f0 ∘ p =ᵐ[ν.variation] f ∘ p := by
    rw [show ν.variation = μ.withDensity (fun t => ‖v t‖ₑ) from Measure.variation_withDensityᵥ hv]
    exact (withDensity_absolutelyContinuous μ (fun t => ‖v t‖ₑ)).ae_eq hcomp
  have hf0i : ν.Integrable (f0 ∘ p) := hfi.congr hcompν.symm
  have hpre : MeasurableSet (p ⁻¹' γ.traceᶜ) :=
    γ.toContinuousMap.continuous.measurable htr.compl
  have hnull : μ (p ⁻¹' γ.traceᶜ) = 0 := by
    change (volume.restrict (Icc (0 : ℝ) 1)) (p ⁻¹' γ.traceᶜ) = 0
    rw [Measure.restrict_apply hpre]
    refine measure_mono_null ?_ measure_empty
    intro t ht
    exact ht.1 ⟨t, ht.2, rfl⟩
  have hvar0 : ν.variation (p ⁻¹' γ.traceᶜ) = 0 := by
    rw [Measure.variation_withDensityᵥ hv, withDensity_apply _ hpre]
    exact setLIntegral_measure_zero _ _ hnull
  have hsupp : ∀ᵐ w ∂(ν.variation.map p), w ∈ γ.trace := by
    rw [ae_iff]
    change (ν.variation.map p) γ.traceᶜ = 0
    rw [Measure.map_apply (μ := ν.variation) γ.toContinuousMap.continuous.measurable htr.compl]
    exact hvar0
  have hfeq : f =ᵐ[ν.variation.map p] f0 := by
    filter_upwards [hsupp] with w hw
    exact (Set.piecewise_eq_of_mem γ.trace f (fun _ => 0) hw).symm
  have hle : (ν.map p).variation ≤ ν.variation.map p := VectorMeasure.variation_map_le
  have hfeq' : f =ᵐ[(ν.map p).variation] f0 :=
    (Measure.absolutelyContinuous_of_le hle).ae_eq hfeq
  refine ⟨(hf0i.map hf0sm).congr hfeq'.symm, ?_⟩
  simp only [PettisMeasure.scalarIntegral, ComplexContour.measure]
  rw [VectorMeasure.integral_congr_ae hfeq']
  rw [VectorMeasure.integral_map γ.toContinuousMap.continuous.measurable hf0sm hf0i]
  have hint_mul := VectorMeasure.integral_withDensityᵥ_mul (f := f0 ∘ p) (g := v) hv hvm hf0i
  rw [show (μ.withDensityᵥ v).integral (fun t => f0 (p t)) (ContinuousLinearMap.mul ℝ ℂ) =
      (μ.withDensityᵥ v).integral (f0 ∘ p) (ContinuousLinearMap.mul ℝ ℂ) from rfl]
  rw [hint_mul]
  have hint : (fun x => (f0 ∘ p) x * v x) =ᵐ[μ] fun x => f (p x) * v x := by
    filter_upwards [hcomp] with t ht
    simp only [Function.comp_apply] at ht ⊢
    rw [ht]
  rw [integral_congr_ae hint]
  change ∫ x in Icc (0 : ℝ) 1, f (p x) * v x = _
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]


/-- The iterated difference quotient at a point recovers the Taylor coefficient. -/
private theorem iterate_dslope_self_eq_iteratedDeriv_div {g : ℂ → ℂ} {z : ℂ} (hg : AnalyticAt ℂ g z)
    (k : ℕ) : (swap dslope z)^[k] g z = iteratedDeriv k g z / (k.factorial : ℂ) := by
  have h := hg.hasFPowerSeriesAt.has_fpower_series_iterate_dslope_fslope k
  rw [← h.coeff_zero (fun _ ↦ 1)]
  have := FormalMultilinearSeries.coeff_iterate_fslope
    (p := FormalMultilinearSeries.ofScalars ℂ (fun n ↦ iteratedDeriv n g z / n.factorial)) k 0
  rw [FormalMultilinearSeries.coeff, zero_add, FormalMultilinearSeries.coeff_ofScalars] at this
  convert this

/-- A point of `(0,1)` off the partition of a piecewise `C¹` contour is a point of
differentiability. -/
lemma ComplexContour.exists_countable_hasDerivAt (γ : ComplexContour) :
    ∃ s : Set ℝ, s.Countable ∧ ∀ x ∈ Ioo (0 : ℝ) 1 \ s,
      HasDerivAt (γ.toContinuousMap : ℝ → ℂ) (deriv (γ.toContinuousMap : ℝ → ℂ) x) x := by
  obtain ⟨n, t, hmono, ht0, ht1, hcd⟩ := γ.piecewiseContDiff
  refine ⟨range t, (finite_range t).countable, fun x hx ↦ ?_⟩
  obtain ⟨i, hi⟩ := exists_mem_contourPiece hmono ht0 ht1 (Ioo_subset_Icc_self hx.1)
  have hL : t i.castSucc < x := lt_of_le_of_ne hi.1 fun h ↦ hx.2 ⟨_, h⟩
  have hR : x < t i.succ := lt_of_le_of_ne hi.2 fun h ↦ hx.2 ⟨_, h.symm⟩
  have hwithin := ((hcd i).differentiableOn one_ne_zero x hi).hasDerivWithinAt
  exact (hwithin.hasDerivAt (Icc_mem_nhds hL hR)).differentiableAt.hasDerivAt

/-- The trace of a contour is compact. -/
lemma ComplexContour.isCompact_trace (γ : ComplexContour) : IsCompact γ.trace :=
  isCompact_Icc.image γ.toContinuousMap.continuous

/-- A function continuous on the trace, times the velocity, is interval integrable. -/
lemma ComplexContour.intervalIntegrable_mul_deriv (γ : ComplexContour) {h : ℂ → ℂ}
    (hh : ContinuousOn h γ.trace) :
    IntervalIntegrable (fun t ↦ h (γ.toContinuousMap t) * deriv (γ.toContinuousMap : ℝ → ℂ) t)
      volume 0 1 := by
  have hfp : ContinuousOn (fun t ↦ h (γ.toContinuousMap t)) (Icc (0 : ℝ) 1) :=
    hh.comp γ.toContinuousMap.continuous.continuousOn fun t ht => ⟨t, ht, rfl⟩
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hfp
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one]
  exact γ.integrable_deriv.bdd_mul
    (hfp.aestronglyMeasurable_of_isCompact isCompact_Icc measurableSet_Icc)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      exact hC t ht)

/-- The path integral of a derivative over a closed contour vanishes. -/
lemma ComplexContour.integral_deriv_eq_zero (γ : ComplexContour) {Q q : ℂ → ℂ}
    (hQ : ∀ w ∈ γ.trace, HasDerivAt Q (q w) w) (hq : ContinuousOn q γ.trace) :
    ∫ t in (0 : ℝ)..1, q (γ.toContinuousMap t) * deriv (γ.toContinuousMap : ℝ → ℂ) t = 0 := by
  obtain ⟨s, hs, hd⟩ := γ.exists_countable_hasDerivAt
  have hmem {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : γ.toContinuousMap t ∈ γ.trace := ⟨t, ht, rfl⟩
  rw [integral_eq_of_hasDerivAt_off_countable_of_le (fun t ↦ Q (γ.toContinuousMap t)) _
    zero_le_one hs ?_ ?_ (γ.intervalIntegrable_mul_deriv hq), γ.closed, sub_self]
  · intro t ht
    exact ((hQ _ (hmem ht)).continuousAt.comp_continuousWithinAt
      γ.toContinuousMap.continuous.continuousWithinAt)
  · intro t ht
    exact (hQ _ (hmem (Ioo_subset_Icc_self ht.1))).comp t (hd t ht)

/-- The holomorphically extended difference quotient of a holomorphic function is
bounded on compact subsets of its domain, uniformly in both variables. -/
private lemma exists_bound_dslope {Ω K : Set ℂ} (hΩ : IsOpen Ω) {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ C, ∀ w ∈ K, ∀ ζ ∈ K, ‖dslope g w ζ‖ ≤ C := by
  obtain ⟨δ, hδ, hsub⟩ := hK.exists_cthickening_subset_open hΩ hKΩ
  have hL : IsCompact (Metric.cthickening δ K) := hK.cthickening
  obtain ⟨M, hM⟩ := hL.exists_bound_of_continuousOn (hg.continuousOn.mono hsub)
  obtain ⟨M', hM'⟩ := hL.exists_bound_of_continuousOn ((hg.deriv hΩ).continuousOn.mono hsub)
  refine ⟨max M' (2 * M / δ), fun w hw ζ hζ ↦ ?_⟩
  have hball : Metric.closedBall w δ ⊆ Metric.cthickening δ K :=
    Metric.closedBall_subset_cthickening hw δ
  have hwK : w ∈ Metric.cthickening δ K := Metric.self_subset_cthickening K hw
  have hζK : ζ ∈ Metric.cthickening δ K := Metric.self_subset_cthickening K hζ
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM w hwK)
  by_cases hwz : ζ = w
  · subst hwz
    rw [dslope_same]
    exact (hM' _ hwK).trans (le_max_left _ _)
  rw [dslope_of_ne _ hwz, slope_def_field]
  have hpos : 0 < ‖ζ - w‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hwz)
  rw [norm_div, div_le_iff₀ hpos]
  by_cases hd : ‖ζ - w‖ < δ
  · have hmv := (convex_ball w δ).norm_image_sub_le_of_norm_deriv_le (f := g) (C := M')
      (fun y hy ↦ (hg y (hsub (hball (Metric.ball_subset_closedBall hy)))).differentiableAt
        (hΩ.mem_nhds (hsub (hball (Metric.ball_subset_closedBall hy)))))
      (fun y hy ↦ hM' y (hball (Metric.ball_subset_closedBall hy)))
      (Metric.mem_ball_self hδ) (show ζ ∈ Metric.ball w δ by rwa [Metric.mem_ball, dist_eq_norm])
    exact hmv.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hpos.le)
  · push Not at hd
    calc ‖g ζ - g w‖ ≤ ‖g ζ‖ + ‖g w‖ := norm_sub_le _ _
      _ ≤ 2 * M := by linarith [hM ζ hζK, hM w hwK]
      _ = 2 * M / δ * δ := by field_simp
      _ ≤ max M' (2 * M / δ) * ‖ζ - w‖ :=
        mul_le_mul (le_max_right _ _) hd hδ.le
          ((div_nonneg (by linarith) hδ.le).trans (le_max_right _ _))

/-- A parametric integral against an integrable weight of functions holomorphic in the
parameter and locally uniformly bounded is holomorphic in the parameter. -/
lemma differentiableOn_intervalIntegral_mul {U : Set ℂ} (hU : IsOpen U) {Φ : ℝ → ℂ → ℂ}
    {v : ℝ → ℂ} (hv : IntervalIntegrable v volume 0 1)
    (hdiff : ∀ t ∈ Icc (0 : ℝ) 1, DifferentiableOn ℂ (Φ t) U)
    (hcont : ∀ z ∈ U, ContinuousOn (fun t ↦ Φ t z) (Icc 0 1))
    (hbound : ∀ K ⊆ U, IsCompact K → ∃ C, ∀ t ∈ Icc (0 : ℝ) 1, ∀ z ∈ K, ‖Φ t z‖ ≤ C) :
    DifferentiableOn ℂ (fun z ↦ ∫ t in (0 : ℝ)..1, Φ t z * v t) U := by
  intro z₀ hz₀
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU z₀ hz₀
  set R := r / 2 with hRdef
  have hR : 0 < R := half_pos hr
  have hK : Metric.closedBall z₀ R ⊆ U :=
    (Metric.closedBall_subset_ball (half_lt_self hr)).trans hball
  obtain ⟨C, hC⟩ := hbound _ hK (isCompact_closedBall z₀ R)
  set ε := R / 2 with hεdef
  have hε : 0 < ε := half_pos hR
  have hεR : ε < R := half_lt_self hR
  have hIoc : uIoc (0 : ℝ) 1 = Ioc 0 1 := uIoc_of_le zero_le_one
  have hvIcc : IntegrableOn v (Icc (0 : ℝ) 1) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).1 hv
  have hballU : Metric.ball z₀ ε ⊆ U :=
    (Metric.ball_subset_ball (hεR.le.trans (half_lt_self hr).le)).trans hball
  have hderiv : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ Metric.ball z₀ ε, ‖deriv (Φ t) x‖ ≤ C / ε := by
    intro t ht x hx
    have hxR : Metric.closedBall x ε ⊆ Metric.closedBall z₀ R := by
      intro y hy
      rw [Metric.mem_closedBall] at hy ⊢
      have := dist_triangle y x z₀
      rw [Metric.mem_ball] at hx
      linarith
    apply Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hε
    · exact (hdiff t ht).diffContOnCl_ball (hxR.trans hK)
    · intro y hy
      exact hC t ht y (hxR (Metric.sphere_subset_closedBall hy))
  have hmeas : ∀ z ∈ U,
      AEStronglyMeasurable (fun t ↦ Φ t z * v t) (volume.restrict (uIoc 0 1)) := by
    intro z hz
    rw [hIoc]
    exact (((hcont z hz).aestronglyMeasurable measurableSet_Icc).mono_measure
      (Measure.restrict_mono Ioc_subset_Icc_self le_rfl)).mul hv.1.aestronglyMeasurable
  have hdx : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt (Φ t) (deriv (Φ t) z₀) z₀ := fun t ht ↦
    ((hdiff t ht).differentiableAt (hU.mem_nhds hz₀)).hasDerivAt
  have hF'meas : AEStronglyMeasurable (fun t ↦ deriv (Φ t) z₀ * v t)
      (volume.restrict (uIoc 0 1)) := by
    rw [hIoc]
    let δ : ℕ → ℂ := fun n ↦ ((ε / ((n : ℝ) + 2) : ℝ) : ℂ)
    have hδpos (n : ℕ) : 0 < ε / ((n : ℝ) + 2) := div_pos hε (by positivity)
    have hδ0 : Tendsto δ atTop (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n ↦ ?_⟩
      · have h1 : Tendsto (fun n : ℕ ↦ ε / ((n : ℝ) + 2)) atTop (𝓝 0) :=
          tendsto_const_nhds.div_atTop
            (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
        have h2 := (Complex.continuous_ofReal.tendsto 0).comp h1
        rw [Complex.ofReal_zero] at h2
        exact h2
      · simp only [δ, mem_compl_iff, mem_singleton_iff, Complex.ofReal_eq_zero]
        exact (hδpos n).ne'
    have hδU (n : ℕ) : z₀ + δ n ∈ U := by
      apply hballU
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
      simp only [δ, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hδpos n)]
      exact div_lt_self hε (by
        have : (0 : ℝ) ≤ n := n.cast_nonneg
        linarith)
    refine (aestronglyMeasurable_of_tendsto_ae atTop
      (f := fun n t ↦ (δ n)⁻¹ • (Φ t (z₀ + δ n) - Φ t z₀)) (fun n ↦ ?_) ?_).mul
      hv.1.aestronglyMeasurable
    · exact ((((hcont _ (hδU n)).sub (hcont _ hz₀)).const_smul (δ n)⁻¹).aestronglyMeasurable
        measurableSet_Icc).mono_measure (Measure.restrict_mono Ioc_subset_Icc_self le_rfl)
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact ((hdx t (Ioc_subset_Icc_self ht)).tendsto_slope_zero).comp hδ0
  have hmain := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := 0) (b := 1) (F := fun x t ↦ Φ t x * v t)
    (F' := fun x t ↦ deriv (Φ t) x * v t) (x₀ := z₀) (bound := fun t ↦ C / ε * ‖v t‖)
    (Metric.ball_mem_nhds z₀ hε) (eventually_of_mem (hU.mem_nhds hz₀) hmeas) ?_ hF'meas ?_
    (hv.norm.const_mul (C / ε)) ?_
  · exact hmain.2.differentiableAt.differentiableWithinAt
  · rw [intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one]
    exact hvIcc.bdd_mul ((hcont z₀ hz₀).aestronglyMeasurable measurableSet_Icc) (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      exact hC t ht z₀ (Metric.mem_closedBall_self hR.le))
  · refine Eventually.of_forall fun t ht x hx ↦ ?_
    rw [hIoc] at ht
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hderiv t (Ioc_subset_Icc_self ht) x hx) (norm_nonneg _)
  · refine Eventually.of_forall fun t ht x hx ↦ ?_
    rw [hIoc] at ht
    exact (((hdiff t (Ioc_subset_Icc_self ht)).differentiableAt
      (hU.mem_nhds (hballU hx))).hasDerivAt).mul_const (v t)

/-- The holomorphically extended difference quotient of a holomorphic function at a
point of an open domain is holomorphic on that domain. -/
private lemma differentiableOn_dslope_of_isOpen {Ω : Set ℂ} (hΩ : IsOpen Ω) {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g Ω) {z : ℂ} (hz : z ∈ Ω) : DifferentiableOn ℂ (dslope g z) Ω := by
  intro w hw
  by_cases hwz : w = z
  · subst hwz
    obtain ⟨P, hP⟩ := hg.analyticAt (hΩ.mem_nhds hw)
    exact hP.dslope_fslope.differentiableAt.differentiableWithinAt
  · exact ((differentiableAt_dslope_of_ne hwz).2
      ((hg w hw).differentiableAt (hΩ.mem_nhds hw))).differentiableWithinAt

/-- The holomorphically extended difference quotient is symmetric. -/
private lemma dslope_comm' (g : ℂ → ℂ) (a b : ℂ) : dslope g a b = dslope g b a := by
  by_cases h : b = a
  · rw [h]
  · rw [dslope_of_ne _ h, dslope_of_ne _ (Ne.symm h), slope_comm]

/-- A Cauchy-type integral along a contour is holomorphic off the trace. -/
lemma ComplexContour.differentiableOn_cauchyIntegral (γ : ComplexContour) {h : ℂ → ℂ}
    (hh : ContinuousOn h γ.trace) :
    DifferentiableOn ℂ (fun z ↦ ∫ t in (0 : ℝ)..1, (γ.toContinuousMap t - z)⁻¹ *
      h (γ.toContinuousMap t) * deriv (γ.toContinuousMap : ℝ → ℂ) t) γ.traceᶜ := by
  have hmem {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : γ.toContinuousMap t ∈ γ.trace := ⟨t, ht, rfl⟩
  apply differentiableOn_intervalIntegral_mul γ.isCompact_trace.isClosed.isOpen_compl
    ((intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).2 γ.integrable_deriv)
    (Φ := fun t z ↦ (γ.toContinuousMap t - z)⁻¹ * h (γ.toContinuousMap t))
  · intro t ht z hz
    have hne : γ.toContinuousMap t - z ≠ 0 :=
      sub_ne_zero.2 (ne_of_mem_of_not_mem (hmem ht) hz)
    exact (((differentiableAt_const _).sub differentiableAt_id).inv hne).mul_const _
      |>.differentiableWithinAt
  · intro z hz
    exact ((γ.toContinuousMap.continuous.sub continuous_const).continuousOn.inv₀
      fun t ht ↦ sub_ne_zero.2 (ne_of_mem_of_not_mem (hmem ht) hz)).mul
      (hh.comp γ.toContinuousMap.continuous.continuousOn fun t ht ↦ hmem ht)
  · intro K hK hKc
    have hc : ContinuousOn (fun x : ℂ × ℂ ↦ (x.1 - x.2)⁻¹ * h x.1) (γ.trace ×ˢ K) :=
      ((continuousOn_fst.sub continuousOn_snd).inv₀ fun x (hx : x ∈ γ.trace ×ˢ K) ↦
        sub_ne_zero.2 (ne_of_mem_of_not_mem hx.1 (hK hx.2))).mul
        (hh.comp continuousOn_fst fun x (hx : x ∈ γ.trace ×ˢ K) ↦ hx.1)
    obtain ⟨C, hC⟩ := (γ.isCompact_trace.prod hKc).exists_bound_of_continuousOn hc
    exact ⟨C, fun t ht z hz ↦ hC (_, z) ⟨hmem ht, hz⟩⟩

/-- Dixon's form of the Cauchy theorem along a contour: if every point off `Ω` has index
zero, the holomorphically extended difference quotient integrates to zero. -/
private theorem ComplexContour.integral_dslope_eq_zero (γ : ComplexContour) {Ω : Set ℂ}
    (hΩ : IsOpen Ω) {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g Ω) (htrace : γ.trace ⊆ Ω)
    (h01 : ∀ z ∉ γ.trace, γ.index z = 0 ∨ γ.index z = 1)
    (hout : ∀ z ∉ Ω, γ.index z = 0) {z : ℂ} (hz : z ∈ Ω) :
    ∫ t in (0 : ℝ)..1, dslope g z (γ.toContinuousMap t) *
      deriv (γ.toContinuousMap : ℝ → ℂ) t = 0 := by
  classical
  set p : ℝ → ℂ := (γ.toContinuousMap : ℝ → ℂ) with hp
  set v : ℝ → ℂ := deriv p with hvdef
  have hmem {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : p t ∈ γ.trace := ⟨t, ht, rfl⟩
  have hcompact := γ.isCompact_trace
  have hopen : IsOpen γ.traceᶜ := hcompact.isClosed.isOpen_compl
  have hv : IntervalIntegrable v volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).2 γ.integrable_deriv
  have hgc : ContinuousOn g γ.trace := hg.continuousOn.mono htrace
  set c : ℂ := 2 * (Real.pi : ℂ) * Complex.I with hcdef
  have hc : c ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
  let F : ℂ → ℂ := fun z ↦ ∫ t in (0 : ℝ)..1, dslope g z (p t) * v t
  let G : ℂ → ℂ := fun z ↦ ∫ t in (0 : ℝ)..1, (p t - z)⁻¹ * g (p t) * v t
  let Ind : ℂ → ℂ := fun z ↦ ∫ t in (0 : ℝ)..1, (p t - z)⁻¹ * v t
  have hinvc {z : ℂ} (hz : z ∉ γ.trace) : ContinuousOn (fun w ↦ (w - z)⁻¹) γ.trace :=
    (continuousOn_id.sub continuousOn_const).inv₀ fun w hw ↦
      sub_ne_zero.2 (ne_of_mem_of_not_mem hw hz)
  have hindex (z : ℂ) (hz : z ∉ γ.trace) : γ.index z = c⁻¹ * Ind z := by
    rw [ComplexContour.index, (γ.scalarIntegral_eq_intervalIntegral (hinvc hz)).2]
  have hFd : DifferentiableOn ℂ F Ω := by
    have := differentiableOn_intervalIntegral_mul hΩ hv (Φ := fun t z ↦ dslope g (p t) z)
      (fun t ht ↦ differentiableOn_dslope_of_isOpen hΩ hg (htrace (hmem ht)))
      (fun z hz ↦ by
        have hd := (differentiableOn_dslope_of_isOpen hΩ hg hz).continuousOn.comp
          γ.toContinuousMap.continuous.continuousOn fun t ht ↦ htrace (hmem ht)
        refine hd.congr fun t _ ↦ ?_
        simp only [Function.comp_apply]
        exact dslope_comm' g _ _)
      (fun K hKΩ hK ↦ by
        obtain ⟨C, hC⟩ := exists_bound_dslope hΩ hg (hcompact.union hK) (union_subset htrace hKΩ)
        exact ⟨C, fun t ht z hz ↦ hC _ (Or.inl (hmem ht)) _ (Or.inr hz)⟩)
    refine this.congr fun z _ ↦ ?_
    simp only [F]
    congr 1
    ext t
    rw [dslope_comm']
  have hGd : DifferentiableOn ℂ G γ.traceᶜ := γ.differentiableOn_cauchyIntegral hgc
  have hId : DifferentiableOn ℂ Ind γ.traceᶜ := by
    refine (γ.differentiableOn_cauchyIntegral (h := fun _ ↦ (1 : ℂ)) continuousOn_const).congr
      fun z _ ↦ ?_
    simp only [Ind, mul_one]
    rfl
  have hFG (z : ℂ) (hz : z ∉ γ.trace) : F z = G z - g z * Ind z := by
    have hne (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : p t ≠ z := fun he ↦ hz (he ▸ hmem ht)
    have h1 : IntervalIntegrable (fun t ↦ (p t - z)⁻¹ * g (p t) * v t) volume 0 1 :=
      γ.intervalIntegrable_mul_deriv (h := fun w ↦ (w - z)⁻¹ * g w) ((hinvc hz).mul hgc)
    have h2 : IntervalIntegrable (fun t ↦ (p t - z)⁻¹ * v t) volume 0 1 :=
      γ.intervalIntegrable_mul_deriv (h := fun w ↦ (w - z)⁻¹) (hinvc hz)
    simp only [F, G, Ind]
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub h1 (h2.const_mul _)]
    refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [uIcc_of_le zero_le_one] at ht
    have hne' : p t - z ≠ 0 := sub_ne_zero.2 (hne t ht)
    rw [dslope_of_ne _ (hne t ht), slope_def_field]
    field_simp
  let W : Set ℂ := {z | z ∉ γ.trace ∧ γ.index z = 0}
  have hIndW {z : ℂ} (hz : z ∈ W) : Ind z = 0 := by
    have := hindex z hz.1
    rw [hz.2] at this
    exact (mul_eq_zero.mp this.symm).resolve_left (inv_ne_zero hc)
  have hidx_small {z : ℂ} (hz : z ∉ γ.trace) (hs : ‖c⁻¹ * Ind z‖ < 1 / 2) : z ∈ W := by
    refine ⟨hz, (h01 z hz).resolve_right fun h1 ↦ ?_⟩
    rw [← hindex z hz, h1, norm_one] at hs
    norm_num at hs
  have hW : IsOpen W := by
    rw [isOpen_iff_mem_nhds]
    intro z hzW
    have hcz : ContinuousAt (fun y ↦ c⁻¹ * Ind y) z :=
      continuousAt_const.mul (hId.continuousOn.continuousAt (hopen.mem_nhds hzW.1))
    have hs : Metric.ball (0 : ℂ) (1 / 2) ∈ 𝓝 (c⁻¹ * Ind z) := by
      rw [hIndW hzW, mul_zero]
      exact Metric.ball_mem_nhds _ one_half_pos
    filter_upwards [hcz.eventually_mem hs, hopen.mem_nhds hzW.1] with y hy hyt
    rw [Metric.mem_ball, dist_zero_right] at hy
    exact hidx_small hyt hy
  let H : ℂ → ℂ := fun z ↦ if z ∈ Ω then F z else G z
  have hHG {z : ℂ} (hz : z ∈ W) : H z = G z := by
    by_cases hzΩ : z ∈ Ω
    · simp only [H, hzΩ, ↓reduceIte, hFG z hz.1, hIndW hz, mul_zero, sub_zero]
    · simp only [H, hzΩ, ↓reduceIte]
  have hH : Differentiable ℂ H := by
    intro z
    by_cases hzΩ : z ∈ Ω
    · have hev : H =ᶠ[𝓝 z] F := by
        filter_upwards [hΩ.mem_nhds hzΩ] with y hy
        simp only [H, hy, ↓reduceIte]
      exact ((hFd z hzΩ).differentiableAt (hΩ.mem_nhds hzΩ)).congr_of_eventuallyEq hev
    · have hzt : z ∉ γ.trace := fun h ↦ hzΩ (htrace h)
      have hzW : z ∈ W := ⟨hzt, hout z hzΩ⟩
      have hev : H =ᶠ[𝓝 z] G := by
        filter_upwards [hW.mem_nhds hzW] with y hy
        exact hHG hy
      exact ((hGd z hzt).differentiableAt (hopen.mem_nhds hzt)).congr_of_eventuallyEq hev
  -- Decay at infinity.
  obtain ⟨M, hM⟩ := hcompact.exists_bound_of_continuousOn continuousOn_id
  have htend (h : ℂ → ℂ) (Mh : ℝ) (hMh : ∀ w ∈ γ.trace, ‖h w‖ ≤ Mh) :
      Tendsto (fun z ↦ ∫ t in (0 : ℝ)..1, (p t - z)⁻¹ * h (p t) * v t) (cocompact ℂ) (𝓝 0) := by
    have hMh0 : 0 ≤ Mh := (norm_nonneg _).trans (hMh _ (hmem (left_mem_Icc.2 zero_le_one)))
    have hbd : ∀ᶠ z in cocompact ℂ, ‖∫ t in (0 : ℝ)..1, (p t - z)⁻¹ * h (p t) * v t‖ ≤
        (‖z‖ - M)⁻¹ * (Mh * ∫ t in (0 : ℝ)..1, ‖v t‖) := by
      filter_upwards [tendsto_norm_cocompact_atTop.eventually_gt_atTop M] with z hz
      have hpos : 0 < ‖z‖ - M := sub_pos.2 hz
      rw [← mul_assoc, ← intervalIntegral.integral_const_mul]
      refine intervalIntegral.norm_integral_le_of_norm_le zero_le_one
        (Eventually.of_forall fun t ht ↦ ?_) (hv.norm.const_mul _)
      have htI := Ioc_subset_Icc_self ht
      have hle : ‖z‖ - M ≤ ‖p t - z‖ := by
        have h1 := hM _ (hmem htI)
        have h2 := norm_sub_norm_le z (p t)
        rw [norm_sub_rev] at h2
        simp only [id] at h1
        linarith
      rw [norm_mul, norm_mul, norm_inv]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      exact mul_le_mul (inv_anti₀ hpos hle) (hMh _ (hmem htI)) (norm_nonneg _)
        (inv_nonneg.2 hpos.le)
    refine squeeze_zero_norm' hbd ?_
    have hlim : Tendsto (fun z : ℂ ↦ ‖z‖ - M) (cocompact ℂ) atTop := by
      simpa [sub_eq_add_neg] using
        tendsto_atTop_add_const_right _ (-M) (tendsto_norm_cocompact_atTop (E := ℂ))
    simpa using (tendsto_inv_atTop_zero.comp hlim).mul_const (Mh * ∫ t in (0 : ℝ)..1, ‖v t‖)
  obtain ⟨Mg, hMg⟩ := hcompact.exists_bound_of_continuousOn hgc
  have hGt : Tendsto G (cocompact ℂ) (𝓝 0) := htend g Mg hMg
  have hIt : Tendsto Ind (cocompact ℂ) (𝓝 0) := by
    have := htend (fun _ ↦ 1) 1 (fun _ _ ↦ by simp)
    simpa [Ind] using this
  have hevW : ∀ᶠ z in cocompact ℂ, z ∈ W := by
    have hsmall : ∀ᶠ z in cocompact ℂ, ‖c⁻¹ * Ind z‖ < 1 / 2 := by
      have := (hIt.const_mul c⁻¹).norm
      rw [mul_zero, norm_zero] at this
      exact this.eventually (gt_mem_nhds one_half_pos)
    filter_upwards [hsmall, hcompact.compl_mem_cocompact] with z hs hzt
    exact hidx_small hzt hs
  have hHt : Tendsto H (cocompact ℂ) (𝓝 0) :=
    hGt.congr' (by
      filter_upwards [hevW] with z hz
      exact (hHG hz).symm)
  have := hH.apply_eq_of_tendsto_cocompact z hHt
  simpa only [H, hz, ↓reduceIte] using this

/-- Cauchy's formula for iterated difference quotients along a contour whose index
vanishes off the domain, at a point of index one. -/
private theorem ComplexContour.integral_inv_pow_mul_eq (γ : ComplexContour) {Ω : Set ℂ}
    (hΩ : IsOpen Ω) (htrace : γ.trace ⊆ Ω)
    (h01 : ∀ z ∉ γ.trace, γ.index z = 0 ∨ γ.index z = 1)
    (hout : ∀ z ∉ Ω, γ.index z = 0) {z : ℂ} (hzΩ : z ∈ Ω) (hzt : z ∉ γ.trace)
    (hz1 : γ.index z = 1) (k : ℕ) :
    ∀ {g : ℂ → ℂ}, DifferentiableOn ℂ g Ω →
      ∫ t in (0 : ℝ)..1, ((γ.toContinuousMap t - z) ^ (k + 1))⁻¹ * g (γ.toContinuousMap t) *
        deriv (γ.toContinuousMap : ℝ → ℂ) t =
        2 * (Real.pi : ℂ) * Complex.I * (swap dslope z)^[k] g z := by
  set p : ℝ → ℂ := (γ.toContinuousMap : ℝ → ℂ) with hp
  set v : ℝ → ℂ := deriv p with hvdef
  have hmem {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : p t ∈ γ.trace := ⟨t, ht, rfl⟩
  have hne {w : ℂ} (hw : w ∈ γ.trace) : w - z ≠ 0 :=
    sub_ne_zero.2 (ne_of_mem_of_not_mem hw hzt)
  have hpow (n : ℕ) : ContinuousOn (fun w ↦ ((w - z) ^ n)⁻¹) γ.trace :=
    ((continuousOn_id.sub continuousOn_const).pow n).inv₀ fun w hw ↦ pow_ne_zero _ (hne hw)
  have hsplit {g : ℂ → ℂ} (n : ℕ) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ((p t - z) ^ (n + 1))⁻¹ * g (p t) * v t =
        g z * (((p t - z) ^ (n + 1))⁻¹ * v t) + ((p t - z) ^ n)⁻¹ * dslope g z (p t) * v t := by
    have h := sub_smul_dslope g z (p t)
    rw [smul_eq_mul] at h
    have hz0 := hne (hmem ht)
    rw [show g (p t) = g z + (p t - z) * dslope g z (p t) by rw [h]; ring]
    field_simp
    ring
  have hint {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g Ω) (n : ℕ) :
      ∫ t in (0 : ℝ)..1, ((p t - z) ^ (n + 1))⁻¹ * g (p t) * v t =
        g z * (∫ t in (0 : ℝ)..1, ((p t - z) ^ (n + 1))⁻¹ * v t) +
          ∫ t in (0 : ℝ)..1, ((p t - z) ^ n)⁻¹ * dslope g z (p t) * v t := by
    have hds : ContinuousOn (dslope g z) γ.trace :=
      (differentiableOn_dslope_of_isOpen hΩ hg hzΩ).continuousOn.mono htrace
    rw [intervalIntegral.integral_congr (g := fun t ↦ g z * (((p t - z) ^ (n + 1))⁻¹ * v t) +
      ((p t - z) ^ n)⁻¹ * dslope g z (p t) * v t) fun t ht ↦ hsplit n t (by
        rwa [uIcc_of_le zero_le_one] at ht)]
    have h1 : IntervalIntegrable (fun t ↦ g z * (((p t - z) ^ (n + 1))⁻¹ * v t)) volume 0 1 :=
      (γ.intervalIntegrable_mul_deriv (hpow (n + 1))).const_mul _
    have h2 : IntervalIntegrable (fun t ↦ ((p t - z) ^ n)⁻¹ * dslope g z (p t) * v t)
        volume 0 1 :=
      γ.intervalIntegrable_mul_deriv (h := fun w ↦ ((w - z) ^ n)⁻¹ * dslope g z w)
        ((hpow n).mul hds)
    rw [intervalIntegral.integral_add h1 h2, intervalIntegral.integral_const_mul]
  induction k with
  | zero =>
    intro g hg
    have hI : ∫ t in (0 : ℝ)..1, ((p t - z) ^ (0 + 1))⁻¹ * v t =
        2 * (Real.pi : ℂ) * Complex.I := by
      have hc : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 :=
        mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero))
          Complex.I_ne_zero
      have := hz1
      rw [ComplexContour.index, (γ.scalarIntegral_eq_intervalIntegral (f := fun w ↦ (w - z)⁻¹)
        ((continuousOn_id.sub continuousOn_const).inv₀ fun w hw ↦ hne hw)).2] at this
      simp only [zero_add, pow_one]
      rw [inv_mul_eq_one₀ hc] at this
      exact this.symm
    rw [hint hg 0, hI]
    simp only [pow_zero, inv_one, one_mul, Function.iterate_zero, id]
    rw [γ.integral_dslope_eq_zero hΩ hg htrace h01 hout hzΩ]
    ring
  | succ k ih =>
    intro g hg
    rw [hint hg (k + 1), Function.iterate_succ_apply,
      ← ih (differentiableOn_dslope_of_isOpen hΩ hg hzΩ)]
    have hzero : ∫ t in (0 : ℝ)..1, ((p t - z) ^ (k + 1 + 1))⁻¹ * v t = 0 := by
      refine γ.integral_deriv_eq_zero
        (Q := fun w ↦ -((k + 1 : ℂ))⁻¹ * ((w - z) ^ (k + 1))⁻¹)
        (q := fun w ↦ ((w - z) ^ (k + 1 + 1))⁻¹) (fun w hw ↦ ?_) (hpow _)
      have hw0 := hne hw
      have hk : (k + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
      have h1 := ((((hasDerivAt_id w).sub_const z).pow (k + 1)).inv
        (pow_ne_zero _ hw0)).const_mul (-((k + 1 : ℂ))⁻¹)
      refine h1.congr_deriv ?_
      simp only [id, Nat.add_sub_cancel, Pi.pow_apply, Nat.cast_add, Nat.cast_one]
      field_simp
      ring
    rw [hzero, mul_zero, zero_add]

section Criteria

variable {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] [T2Space E] [PolynormableSpace ℂ E]
variable {Ω : Set ℂ} (hΩ : IsOpen Ω) (hconn : IsConnected Ω) (f : ℂ → E)
include hΩ hconn

/-- Paper: Theorem C.5.2.4(1–2), p. 738. Weak holomorphy is equivalent to weak
continuity and vanishing weak Pettis integrals around simple contours in the domain. -/
theorem weaklyHolomorphicOn_iff_contourIntegral_eq_zero :
    WeaklyHolomorphicOn f Ω ↔ WeaklyContinuousOn f Ω ∧
      ∀ γ : PositiveSimpleContour, γ.val.trace ⊆ Ω → γ.interior ⊆ Ω →
        ∃ hi : PettisWeaklyIntegrable (.complex γ.val.measure) f,
          pettisWeakIntegral (.complex γ.val.measure) f hi = 0 := by sorry

/-- Paper: Theorem C.5.2.4(1,3), p. 738. Weak holomorphy is equivalent to weak
continuity and the Cauchy formula in the algebraic dual of the continuous dual. -/
theorem weaklyHolomorphicOn_iff_weak_cauchyIntegral :
    WeaklyHolomorphicOn f Ω ↔ WeaklyContinuousOn f Ω ∧
      ∀ (γ : PositiveSimpleContour), γ.val.trace ⊆ Ω → γ.interior ⊆ Ω →
        ∀ z ∈ γ.interior,
          ∃ hi : PettisWeaklyIntegrable (.complex γ.val.measure) (fun w ↦ (w - z)⁻¹ • f w),
            toPettisWeakCompletion E (f z) =
              (2 * (Real.pi : ℂ) * Complex.I)⁻¹ •
                pettisWeakIntegral (.complex γ.val.measure) (fun w ↦ (w - z)⁻¹ • f w) hi := by
  sorry

variable [QuasiCompleteSpace ℂ E]

/-- Paper: Theorem C.5.2.6(1–2), p. 738. Weak holomorphy is equivalent to
continuous complex differentiability of every finite order of each scalar evaluation. -/
theorem weaklyHolomorphicOn_iff_scalar_contDiffOn :
    WeaklyHolomorphicOn f Ω ↔ ∀ (φ : StrongDual ℂ E) (k : ℕ), ContDiffOn ℂ k (φ ∘ f) Ω := by
  sorry

/-- Paper: Theorem C.5.2.6(1,3), p. 738. Weak holomorphy is equivalent to the
existence of complex derivatives in the original target of every order. -/
theorem weaklyHolomorphicOn_iff_all_derivatives :
    WeaklyHolomorphicOn f Ω ↔ ∀ k : ℕ, DifferentiableOn ℂ (deriv^[k] f) Ω := by sorry

/-- Paper: (C.5.2.4), p. 738. The higher derivatives are given by Pettis
contour integrals with the Cauchy kernel and the factorial factor. -/
theorem hasPettisIntegral_cauchy_derivative (hf : ∀ k : ℕ, DifferentiableOn ℂ (deriv^[k] f) Ω)
    (γ : PositiveSimpleContour) (htrace : γ.val.trace ⊆ Ω) (hinterior : γ.interior ⊆ Ω)
    {z : ℂ} (hz : z ∈ γ.interior) (k : ℕ) :
    HasPettisIntegral (.complex γ.val.measure) (fun w ↦ ((w - z) ^ (k + 1))⁻¹ • f w)
      ((2 * (Real.pi : ℂ) * Complex.I / (k.factorial : ℂ)) • (deriv^[k] f) z) := by
  have hzΩ : z ∈ Ω := hinterior hz
  have h01 := γ.property.2
  have hout : ∀ a ∉ Ω, γ.val.index a = 0 := by
    intro a ha
    have hat : a ∉ γ.val.trace := fun h ↦ ha (htrace h)
    exact (h01 a hat).resolve_right fun h1 ↦ ha (hinterior ⟨hat, h1⟩)
  have hcomm (φ : StrongDual ℂ E) (n : ℕ) :
      ∀ x ∈ Ω, deriv^[n] (φ ∘ f) x = φ (deriv^[n] f x) := by
    induction n with
    | zero => exact fun x _ ↦ rfl
    | succ n ih =>
      intro x hx
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      have hev : deriv^[n] (φ ∘ f) =ᶠ[𝓝 x] φ ∘ deriv^[n] f := by
        filter_upwards [hΩ.mem_nhds hx] with y hy
        exact ih y hy
      rw [hev.deriv_eq]
      exact (VectorHolomorphicOn.hasDerivAt_comp (hf n) hΩ φ ⟨x, hx⟩).deriv
  have hg (φ : StrongDual ℂ E) : DifferentiableOn ℂ (φ ∘ f) Ω := fun x hx ↦
    (VectorHolomorphicOn.hasDerivAt_comp (hf 0) hΩ φ ⟨x, hx⟩).differentiableAt
      |>.differentiableWithinAt
  have hpow : ContinuousOn (fun w ↦ ((w - z) ^ (k + 1))⁻¹) γ.val.trace :=
    ((continuousOn_id.sub continuousOn_const).pow (k + 1)).inv₀ fun w hw ↦
      pow_ne_zero _ (sub_ne_zero.2 (ne_of_mem_of_not_mem hw hz.1))
  have hscalar (φ : StrongDual ℂ E) :=
    γ.val.scalarIntegral_eq_intervalIntegral (f := fun w ↦ φ (((w - z) ^ (k + 1))⁻¹ • f w))
      ((hpow.mul ((hg φ).continuousOn.mono htrace)).congr fun w _ ↦ by
        simp only [map_smul, smul_eq_mul, Pi.mul_apply, Function.comp_apply])
  refine ⟨fun φ ↦ (hscalar φ).1, LinearMap.ext fun φ ↦ ?_⟩
  change φ ((2 * (Real.pi : ℂ) * Complex.I / (k.factorial : ℂ)) • (deriv^[k] f) z) =
    (PettisMeasure.complex γ.val.measure).scalarIntegral
      (fun w ↦ φ (((w - z) ^ (k + 1))⁻¹ • f w))
  rw [(hscalar φ).2]
  have hformula := γ.val.integral_inv_pow_mul_eq hΩ htrace h01 hout hzΩ hz.1 hz.2 k (hg φ)
  simp only [map_smul, smul_eq_mul, Function.comp_apply] at hformula ⊢
  rw [hformula, iterate_dslope_self_eq_iteratedDeriv_div ((hg φ).analyticAt (hΩ.mem_nhds hzΩ)),
    iteratedDeriv_eq_iterate, hcomm φ k z hzΩ]
  ring

/-- Paper: Theorem C.5.2.6(1,4), p. 738. Weak holomorphy is equivalent to a
power series at every center that converges uniformly to the function on each closed
disc about that center contained in the domain. -/
theorem weaklyHolomorphicOn_iff_taylor :
    WeaklyHolomorphicOn f Ω ↔ ∀ z ∈ Ω, ∃ a : ℕ → E,
      ∀ r : ℝ, 0 < r → Metric.closedBall z r ⊆ Ω →
        TendstoUniformlyOn (fun n w ↦ ∑ k ∈ Finset.range n, (w - z) ^ k • a k)
          f atTop (Metric.closedBall z r) := by sorry

/-- Paper: (C.5.2.5), p. 738. The Taylor coefficients are the vector derivatives
at the center divided by the corresponding factorials. -/
theorem tendstoUniformlyOn_taylor_derivatives (hf : ∀ k : ℕ,
    DifferentiableOn ℂ (deriv^[k] f) Ω) {z : ℂ} {r : ℝ} (hr : 0 < r)
    (hdisc : Metric.closedBall z r ⊆ Ω) :
    TendstoUniformlyOn
      (fun n w ↦ ∑ k ∈ Finset.range n,
        ((w - z) ^ k / (k.factorial : ℂ)) • (deriv^[k] f) z)
      f atTop (Metric.closedBall z r) := by sorry

/-- Paper: Theorem C.5.2.6, p. 738. In the quasi-complete case weak holomorphy
implies holomorphy in the target topology. -/
theorem WeaklyHolomorphicOn.vectorHolomorphicOn (hf : WeaklyHolomorphicOn f Ω) :
    VectorHolomorphicOn f Ω := by sorry

omit [QuasiCompleteSpace ℂ E] in
/-- Paper: (C.5.2.6), p. 739. The weak derivative evaluates each continuous
linear functional to the corresponding scalar complex derivative. -/
theorem WeaklyHolomorphicOn.existsUnique_weakDerivative (hf : WeaklyHolomorphicOn f Ω)
    {z : ℂ} (hz : z ∈ Ω) (k : ℕ) :
    ∃! v : PettisWeakCompletion E, ∀ φ : StrongDual ℂ E,
      (show Module.Dual ℂ (StrongDual ℂ E) from v) φ = iteratedDeriv k (φ ∘ f) z := by sorry

end Criteria

section Meromorphy

variable {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℂ E]
variable {Ω D : Set ℂ} {f : ℂ → E} {z : ℂ}

-- TODO(paper-gap): Definition C.5.3.1 prints k ≥ 0 as the lower Laurent exponent,
-- contradicting its pole-clearing condition and the signed lower exponent in (C.5.3.4).

/-- Paper: Definition C.5.3.1, p. 739. A meromorphic pair is holomorphic off a
discrete exceptional set, and at each exceptional point a power of the local
coordinate times the function extends holomorphically.
Deviation: Uses the paper's parenthetical pole-clearing criterion. The punctured
domain is explicitly open, so the exceptional set is relatively closed. -/
def IsVectorMeromorphicOn (f : ℂ → E) (Ω D : Set ℂ) : Prop :=
  D ⊆ Ω ∧ IsDiscrete D ∧ IsOpen (Ω \ D) ∧ VectorHolomorphicOn f (Ω \ D) ∧
    ∀ z ∈ D, ∃ (n : ℕ) (r : ℝ) (g : ℂ → E),
      0 < r ∧ Metric.ball z r \ {z} ⊆ Ω \ D ∧ VectorHolomorphicOn g (Metric.ball z r) ∧
      EqOn g (fun w ↦ (w - z) ^ n • f w) (Metric.ball z r \ {z})

/-- Paper: (C.5.3.2), p. 739. A local Laurent expansion has an
integer lower bound and its partial sums converge uniformly on compact subsets
of a punctured disc around the center.
Deviation: Uses the signed lower bound displayed in (C.5.3.4), with zero coefficients
below that bound. -/
def HasVectorLaurentSeriesAt (f : ℂ → E) (z : ℂ) (a : ℤ → E) : Prop :=
  ∃ (N : ℤ) (r : ℝ), 0 < r ∧ (∀ k < N, a k = 0) ∧
    ∀ K : Set ℂ, K ⊆ Metric.ball z r \ {z} → IsCompact K →
      TendstoUniformlyOn
        (fun n w ↦ ∑ j ∈ Finset.range n, (w - z) ^ (N + (j : ℤ)) • a (N + (j : ℤ)))
        f atTop K

-- TODO(paper-gap): The zero germ has no finite order. The lower summation bound
-- alone cannot define order because one can always pad the series with initial zeros.

/-- Paper: Definition C.5.3.1(1), p. 739. A finite order is the least Laurent
exponent with nonzero coefficient.
Deviation: This is a relation for finite order. The zero germ has no finite order. -/
def HasVectorMeromorphicOrderAt (f : ℂ → E) (z : ℂ) (k : ℤ) : Prop :=
  ∃ a : ℤ → E, HasVectorLaurentSeriesAt f z a ∧ a k ≠ 0 ∧ ∀ j < k, a j = 0

/-- Paper: Definition C.5.3.1(2), p. 739. A point is a pole if its Laurent order
is strictly negative. -/
def IsVectorPoleAt (f : ℂ → E) (z : ℂ) : Prop :=
  ∃ k : ℤ, k < 0 ∧ HasVectorMeromorphicOrderAt f z k

/-- Paper: Definition C.5.3.1, p. 739. The reciprocal is meromorphic with a simple
pole at zero and Laurent coefficient one at exponent minus one.
Deviation: This is a sanity check for meromorphy, the Laurent expansion, and order. -/
theorem vectorMeromorphic_inv :
    IsVectorMeromorphicOn (fun w : ℂ ↦ w⁻¹) univ {0} ∧
      HasVectorLaurentSeriesAt (fun w : ℂ ↦ w⁻¹) 0 (fun k ↦ if k = -1 then 1 else 0) ∧
      HasVectorMeromorphicOrderAt (fun w : ℂ ↦ w⁻¹) 0 (-1) ∧
      IsVectorPoleAt (fun w : ℂ ↦ w⁻¹) 0 := by
  let a : ℤ → ℂ := fun k ↦ if k = -1 then 1 else 0
  have hsum (n : ℕ) (hn : 1 ≤ n) (w : ℂ) :
      ∑ j ∈ Finset.range n, (w - 0) ^ (-1 + (j : ℤ)) • a (-1 + (j : ℤ)) = w⁻¹ := by
    rw [Finset.sum_eq_single 0]
    · simp [a]
    · intro j _ hj
      have : (-1 + (j : ℤ)) ≠ -1 := by omega
      simp [a, this]
    · intro h
      exact absurd (Finset.mem_range.mpr hn) h
  have hL : HasVectorLaurentSeriesAt (fun w : ℂ ↦ w⁻¹) 0 a := by
    refine ⟨-1, 1, one_pos, fun k hk ↦ ?_, fun K _ _ ↦ ?_⟩
    · simp [a, hk.ne]
    · intro u hu
      filter_upwards [eventually_ge_atTop 1] with n hn x _
      rw [hsum n hn x]
      exact @refl_mem_uniformity ℂ (IsTopologicalAddGroup.rightUniformSpace ℂ) _ _ hu
  have hO : HasVectorMeromorphicOrderAt (fun w : ℂ ↦ w⁻¹) 0 (-1) :=
    ⟨a, hL, by simp [a], fun j hj ↦ by simp [a, hj.ne]⟩
  refine ⟨⟨subset_univ _, Set.subsingleton_singleton.isDiscrete,
    isOpen_univ.sdiff isClosed_singleton, fun w hw ↦ ?_, ?_⟩, hL, hO, ⟨-1, by norm_num, hO⟩⟩
  · have hw0 : w ≠ 0 := hw.2
    exact (differentiableAt_inv (𝕜 := ℂ) hw0).differentiableWithinAt
  · rintro z rfl
    refine ⟨1, 1, fun _ ↦ 1, one_pos, fun w hw ↦ ⟨mem_univ w, hw.2⟩,
      differentiableOn_const 1, fun w hw ↦ ?_⟩
    have hw0 : w ≠ 0 := hw.2
    simp [hw0]

-- TODO(paper-gap): The pairs (f, D) have no specified identification when D
-- changes. Residue linearity below uses the common domain of the representatives.

variable [T2Space E] [PolynormableSpace ℂ E] [QuasiCompleteSpace ℂ E]

/-- Paper: Definition C.5.3.1, p. 739. Every point of the domain of a meromorphic
pair has a unique local Laurent expansion in the original target.
Deviation: Includes the ordinary Taylor expansion at points outside the exceptional set. -/
theorem IsVectorMeromorphicOn.existsUnique_laurentSeries (hΩ : IsOpen Ω)
    (hf : IsVectorMeromorphicOn f Ω D) (hz : z ∈ Ω) :
    ∃! a : ℤ → E, HasVectorLaurentSeriesAt f z a := by sorry

/-- Paper: Coefficient notation in Lemma C.5.3.2, p. 740. A coefficient is read
from the local Laurent expansion, with existence supplied as evidence. -/
def vectorLaurentCoeff (h : ∃ a : ℤ → E, HasVectorLaurentSeriesAt f z a) (k : ℤ) : E :=
  Classical.choose h k

/-- Paper: Coefficient notation in Lemma C.5.3.2, p. 740. Reading a coefficient
from a specified expansion reproduces the coefficient at the requested exponent.
Deviation: This is a sanity check for the coefficient operation. -/
theorem vectorLaurentCoeff_eq {a : ℤ → E} (ha : HasVectorLaurentSeriesAt f z a)
    (h : ∃ a : ℤ → E, HasVectorLaurentSeriesAt f z a) (k : ℤ) :
    vectorLaurentCoeff h k = a k := by sorry

-- TODO(paper-gap): C.5.3.2 omits the interior-containment hypothesis of C.5.2.4.
-- On 1 < |w| < 4, take f(w) = 1/w, z = 2, the circle |w| = 3, and k = -1.

/-- Paper: Lemma C.5.3.2, p. 740. The Laurent coefficient is the normalized
Pettis contour integral against the reciprocal power of the local coordinate.
Deviation: Restores interior containment from the cited Theorem C.5.2.4.
An extension across removable exceptional points supplies the contour values. -/
theorem hasPettisIntegral_laurentCoeff (hΩ : IsOpen Ω) (hconn : IsConnected Ω)
    (hf : IsVectorMeromorphicOn f Ω D) (γ : PositiveSimpleContour)
    (htrace : γ.val.trace ⊆ Ω) (hinterior : γ.interior ⊆ Ω) (hz : z ∈ γ.interior)
    (havoid : ∀ w ∈ γ.val.trace, ¬ IsVectorPoleAt f w)
    (honly : ∀ w ∈ γ.interior, IsVectorPoleAt f w → w = z) (k : ℤ) :
    ∃ g : ℂ → E, EqOn g f (Ω \ D) ∧
      VectorHolomorphicOn g (Ω \ {w | IsVectorPoleAt f w}) ∧
      HasPettisIntegral (.complex γ.val.measure) (fun w ↦ ((w - z) ^ (k + 1))⁻¹ • g w)
        ((2 * (Real.pi : ℂ) * Complex.I) •
          vectorLaurentCoeff (hf.existsUnique_laurentSeries hΩ (hinterior hz)).exists k) := by sorry

/-- Paper: (C.5.3.5), p. 740. The residue is the coefficient of exponent minus one. -/
def vectorResidue (h : ∃ a : ℤ → E, HasVectorLaurentSeriesAt f z a) : E :=
  vectorLaurentCoeff h (-1)

/-- Paper: (C.5.3.5), p. 740. The residue of the reciprocal at zero is one.
Deviation: This is a sanity check for the residue operation. -/
theorem vectorResidue_inv
    (h : ∃ a : ℤ → ℂ, HasVectorLaurentSeriesAt (fun w : ℂ ↦ w⁻¹) 0 a) :
    vectorResidue h = 1 := by sorry

/-- Paper: Lemma C.5.3.3(1), p. 740. The residue preserves complex linear
combinations.
Deviation: The linear combination uses the common domain of both representatives. -/
theorem vectorResidue_linear (hΩ : IsOpen Ω) (hconn : IsConnected Ω) (hz : z ∈ Ω)
    {g : ℂ → E} {D' : Set ℂ} (hf : IsVectorMeromorphicOn f Ω D)
    (hg : IsVectorMeromorphicOn g Ω D') (a b : ℂ) :
    ∃ h : IsVectorMeromorphicOn (a • f + b • g) Ω (D ∪ D'),
      vectorResidue (h.existsUnique_laurentSeries hΩ hz).exists =
        a • vectorResidue (hf.existsUnique_laurentSeries hΩ hz).exists +
          b • vectorResidue (hg.existsUnique_laurentSeries hΩ hz).exists := by sorry

-- TODO(paper-gap): The unrestricted wording of C.5.3.3(2) allows an annular hole
-- inside the contour and never explicitly requires z to be inside it.

/-- Paper: Lemma C.5.3.3(2), p. 740. The normalized contour integral around an
enclosed point gives its residue when the only possible interior pole is that point.
Deviation: The point is explicitly enclosed, and the contour and interior
satisfy the conditions of the Laurent coefficient formula above. -/
theorem hasPettisIntegral_vectorResidue (hΩ : IsOpen Ω) (hconn : IsConnected Ω)
    (hf : IsVectorMeromorphicOn f Ω D) (γ : PositiveSimpleContour)
    (htrace : γ.val.trace ⊆ Ω) (hinterior : γ.interior ⊆ Ω) (hz : z ∈ γ.interior)
    (havoid : ∀ w ∈ γ.val.trace, ¬ IsVectorPoleAt f w)
    (honly : ∀ w ∈ γ.interior, IsVectorPoleAt f w → w = z) :
    ∃ g : ℂ → E, EqOn g f (Ω \ D) ∧
      VectorHolomorphicOn g (Ω \ {w | IsVectorPoleAt f w}) ∧
      HasPettisIntegral (.complex γ.val.measure) g
        ((2 * (Real.pi : ℂ) * Complex.I) •
          vectorResidue (hf.existsUnique_laurentSeries hΩ (hinterior hz)).exists) := by sorry

-- TODO(paper-gap): C.5.3.3(3) multiplies by (w - z)^(k - 1) at a pole of
-- order k. For f(w) = 1/w at z = 0 the printed limit does not exist.

/-- Paper: Lemma C.5.3.3(4), p. 740. Continuous complex-linear maps preserve
meromorphy and commute with taking residues.
Deviation: The source of the identity is E₁-valued, and both targets satisfy the
local convexity hypotheses of the meromorphic function space. -/
theorem vectorResidue_comp_continuousLinearMap
    {F : Type*} [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
    [IsTopologicalAddGroup F] [ContinuousSMul ℂ F] [T2Space F] [PolynormableSpace ℂ F]
    [QuasiCompleteSpace ℂ F] (hΩ : IsOpen Ω) (hconn : IsConnected Ω) (hz : z ∈ Ω)
    (hf : IsVectorMeromorphicOn f Ω D) (T : E →L[ℂ] F) :
    ∃ h : IsVectorMeromorphicOn (T ∘ f) Ω D,
      vectorResidue (h.existsUnique_laurentSeries hΩ hz).exists =
        T (vectorResidue (hf.existsUnique_laurentSeries hΩ hz).exists) := by sorry

end Meromorphy

/-- Paper: Cycle convention before Theorem C.5.4.1, p. 740. A cycle is a finite
formal integer combination of positively oriented simple contours. -/
abbrev ComplexContourCycle := PositiveSimpleContour →₀ ℤ

/-- Paper: Cycle convention before Theorem C.5.4.1, p. 740. The trace of a cycle
is the union of the traces of its terms with nonzero coefficients. -/
def ComplexContourCycle.trace (Γ : ComplexContourCycle) : Set ℂ :=
  ⋃ γ ∈ Γ.support, γ.val.trace

/-- Paper: (C.5.4.1), p. 741. Integration over a cycle uses the integer-weighted
sum of the contour measures. -/
def ComplexContourCycle.measure (Γ : ComplexContourCycle) : ComplexMeasure ℂ :=
  Γ.sum (fun γ n ↦ n • γ.val.measure)

/-- Paper: Winding number in Theorem C.5.4.1, p. 741. The index of a cycle off its
trace is the integer-weighted sum of the indices of its constituent contours. -/
def ComplexContourCycle.index (Γ : ComplexContourCycle) (z : ℂ) : ℂ :=
  Γ.sum (fun γ n ↦ n • γ.val.index z)

/-- Paper: Cycle convention before Theorem C.5.4.1, p. 740. A cycle with one
contour and nonzero multiplicity has its trace and scales its measure and index.
Deviation: This is a sanity check for the cycle operations. -/
theorem complexContourCycle_single (γ : PositiveSimpleContour) {n : ℤ} (hn : n ≠ 0) (z : ℂ) :
    let Γ : ComplexContourCycle := Finsupp.single γ n
    Γ.trace = γ.val.trace ∧ Γ.measure = n • γ.val.measure ∧ Γ.index z = n • γ.val.index z := by
  refine ⟨?_, ?_, ?_⟩
  · simp [ComplexContourCycle.trace, Finsupp.support_single_ne_zero γ hn]
  · simp [ComplexContourCycle.measure, Finsupp.sum_single_index]
  · simp [ComplexContourCycle.index, Finsupp.sum_single_index]

section ResidueTheorem

variable {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] [T2Space E] [PolynormableSpace ℂ E]
  [QuasiCompleteSpace ℂ E]
variable {Ω D : Set ℂ} {f : ℂ → E}

/-- Paper: Theorem C.5.4.1, p. 741. The normalized cycle integral equals the
finite sum of residues weighted by winding numbers.
Deviation: Null homology uses the planar winding-number condition outside Ω.
A representative extending across removable points supplies the contour values.
The identity is pointwise on meromorphic functions satisfying the pole avoidance condition. -/
theorem vectorResidueTheorem (hΩ : IsOpen Ω) (hconn : IsConnected Ω)
    (hf : IsVectorMeromorphicOn f Ω D) (Γ : ComplexContourCycle) (htrace : Γ.trace ⊆ Ω)
    (hnull : ∀ z ∉ Ω, Γ.index z = 0)
    (havoid : ∀ z ∈ Γ.trace, ¬ IsVectorPoleAt f z) :
    ∃ (g : ℂ → E) (S : Finset Ω),
      EqOn g f (Ω \ D) ∧ VectorHolomorphicOn g (Ω \ {z | IsVectorPoleAt f z}) ∧
      (∀ z : Ω, z ∈ S ↔ IsVectorPoleAt f z ∧ Γ.index z ≠ 0) ∧
      HasPettisIntegral (.complex Γ.measure) g
        ((2 * (Real.pi : ℂ) * Complex.I) •
          ∑ z ∈ S, Γ.index z • vectorResidue (hf.existsUnique_laurentSeries hΩ z.property).exists) :=
  by sorry

/-- Paper: Lemma C.5.4.2, p. 741. Local boundedness away from the discrete set
gives a holomorphic extension unique on the original domain. -/
theorem existsUnique_vectorHolomorphicOn_extension (hΩ : IsOpen Ω) (hconn : IsConnected Ω)
    (hDΩ : D ⊆ Ω) (hD : IsDiscrete D) (hf : VectorHolomorphicOn f (Ω \ D))
    (hb : ∀ z ∈ Ω, ∃ r : ℝ, 0 < r ∧ Metric.ball z r ⊆ Ω ∧
      IsVonNBounded ℂ (f '' (Metric.ball z r \ D))) :
    ∃ g : ℂ → E, VectorHolomorphicOn g Ω ∧ EqOn g f (Ω \ D) ∧
      ∀ g' : ℂ → E, VectorHolomorphicOn g' Ω → EqOn g' f (Ω \ D) → EqOn g' g Ω := by sorry

/-- Paper: Lemma C.5.4.3, p. 741. Two meromorphic functions that agree on a
nonempty disc agree everywhere both representatives are defined. -/
theorem IsVectorMeromorphicOn.eqOn_of_eqOn_ball (hΩ : IsOpen Ω) (hconn : IsConnected Ω)
    {g : ℂ → E} {D' : Set ℂ} (hf : IsVectorMeromorphicOn f Ω D)
    (hg : IsVectorMeromorphicOn g Ω D') {z : ℂ} {r : ℝ}
    (hr : 0 < r) (hball : Metric.ball z r ⊆ Ω \ (D ∪ D'))
    (heq : EqOn f g (Metric.ball z r)) :
    EqOn f g (Ω \ (D ∪ D')) := by sorry

end ResidueTheorem

end RiemannMasullo
