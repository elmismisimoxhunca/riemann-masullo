module

public import RiemannMasullo.Ch07_SchauderBasesZeta.Sec1a
import Mathlib.Algebra.Field.ULift
import all RiemannMasullo.Ch03_IdelicZeta.Sec3

/-! # §7.1.1–7.1.2 Statements that are false as printed -/

@[expose] public noncomputable section

open Asymptotics Filter IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped BigOperators NNReal

namespace RiemannMasullo

set_option quotPrecheck false

universe u

local notation "Places(" F ")" => HeightOneSpectrum (𝓞 F)
local notation "Jₛ(" F ", " S ")" => SIdeleQuotient F S
local notation "Tests(" F ", " S ")" => SchwartzBruhat (Multiplicative (SAdeleRing F S))
local notation "normₛ(" F ", " S ")" => sIdeleQuotientNorm F S
local notation "twistₛ(" F ", " S ")" =>
  quasiCharacterNormTwist (G := Jₛ(F, S)) normₛ(F, S) (isProperMap_sIdeleQuotientNorm F S).continuous
local notation "circleToComplex" => (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ)
local notation "period(" v ")" => (2 * Real.pi / Real.log (Ideal.absNorm (HeightOneSpectrum.asIdeal v) : ℝ))

/-- Paper: Before Lemma 7.1.1.1, p. 313.
As printed: Each point of every unshifted lattice is a zero of the product
(7.1.1.1) with real phases tᵥ. The shift in the repaired finite-place pole list is in
`finiteHeckeEulerFactor_poles_iff`. See ERRATA F85. -/
def Printed.reciprocalPartialHeckeEulerProduct_unshifted_zeros : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (S : Finset Places(F)) (t : S → ℝ)
    (v : S) (m : ℤ),
    let s : ℂ := ((m : ℝ) * period(v.val) : ℝ) * Complex.I
    ∏ w : S, (1 - (w.val.asIdeal.absNorm : ℂ) ^ (-s - (t w : ℂ) * Complex.I)) = 0

/-- Paper: Before Lemma 7.1.1.1, p. 313.
Take the rational field, the singleton place above 2, and tᵥ = π/(2 log 2).
At m = 0 the factor is 1 − exp(−iπ/2) = 1 + i. -/
theorem Printed.reciprocalPartialHeckeEulerProduct_unshifted_zeros_false :
    ¬ Printed.reciprocalPartialHeckeEulerProduct_unshifted_zeros := by sorry

/-- Paper: Lemma 7.1.2.2(1), p. 317.
As printed: At every complex place of angular weight k, a nonpositive integer in
`|k|/2 - ℕ` gives a pole of the correcting factor after the local imaginary shift.
This is the inclusion from the complex-place part of the pole list. The repaired list is
`sLocalRhoFactor_poles_iff`. See ERRATA F86. -/
def Printed.sLocalRhoFactor_complex_positive_shift : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (S : Finset Places(F))
    (χ : PontryaginDual Jₛ(F, S)) (w : InfinitePlace F) (hw : w.IsComplex) (m : ℤ),
    let chart := twistₛ(F, S) ((circleToComplex).comp χ)
    let p := (complexLocalEulerParameters w hw (sLocalInfiniteRestriction w (chart 0))).exists.choose
    m ≤ 0 → (∃ n : ℕ, (m : ℝ) = (p.2.natAbs : ℝ) / 2 - n) →
      meromorphicOrderAt (fun z ↦ sLocalRhoFactor (chart z)) ((m : ℂ) - p.1) < 0

/-- Paper: Lemma 7.1.2.2(1), p. 317.
Take ℚ(i) with only its complex place and the character `(z/|z|)^4`, which descends
through the four units. The printed list includes zero, but the numerator Γℂ(s + 2)
and the denominator Γℂ(3 − s) are regular and nonzero there. -/
theorem Printed.sLocalRhoFactor_complex_positive_shift_false :
    ¬ Printed.sLocalRhoFactor_complex_positive_shift := by sorry

section Theta

variable {F : Type u} [Field F] [NumberField F] {S : Finset Places(F)}

local instance printedCh07Sec1aNormOneMeasurableSpace :
    MeasurableSpace (normₛ(F, S)).ker := borel _

local instance printedCh07Sec1aNormOneHaar :
    (sLocalNormOneQuotientMeasure F S).IsHaarMeasure :=
  (sLocalNormOneQuotientMeasure_normProduct (F := F) (S := S)).1

open Classical in
/-- Paper: Theorem 7.1.2.3, equation (7.1.2.3), p. 318.
As printed: This is the scalar expansion for every A > 0. The first sum uses
0 < m < A. Its coefficient is evaluated at the printed expression for cᵥ,ₘ,χ,
with exponent m − itᵥ from p. 317, while its norm weight has exponent m + itᵥ.
The pole list on p. 316 only admits m ≤ 0. For positive m the displayed
expression is in the holomorphic half-plane and the inner sum is empty.
At A = 1/2 even the outer integer range is empty, independently of this
index conflict. Each unramified finite place contributes its own copy of
the full Laurent coefficients.
The series converges uniformly on compact sets along horizontal contour cutoffs
(p. 322), and the scalar remainder is of order `O(|g|^A)`.
See `sLocalHomogeneousAdelicTheta_rat_not_isBigO_sqrt` and ERRATA F87–F89. -/
def Printed.sLocalHomogeneousAdelicTheta_asymptotic : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (S : Finset Places(F))
    (χ : PontryaginDual Jₛ(F, S)) (f : Tests(F, S)) (A : ℝ), 0 < A →
    let chart := twistₛ(F, S) ((circleToComplex).comp χ)
    let normℝ (g : Jₛ(F, S)) := ((normₛ(F, S) g : ℝ≥0) : ℝ)
    let ω := χ.comp (⟨(normₛ(F, S)).ker.subtype, continuous_subtype_val⟩ :
      (normₛ(F, S)).ker →ₜ* Jₛ(F, S))
    let term (a weight : ℂ) (g : Jₛ(F, S)) :=
      ∑ j ∈ Finset.range (sLocalPolarMultiplicity f (chart a)),
        (-1 : ℂ) ^ j * sLocalZLaurentCoeff f (chart a) (j : ℤ) / (j.factorial : ℂ) *
          star (χ g : ℂ) * (normℝ g : ℂ) ^ weight * (Real.log (normℝ g) : ℂ) ^ j
    let archPhase (w : InfinitePlace F) :=
      let c := sLocalInfiniteRestriction w (chart 0)
      if hw : w.IsReal then (realLocalEulerParameters w hw c).exists.choose.1
      else
        (complexLocalEulerParameters w (InfinitePlace.not_isReal_iff_isComplex.mp hw) c).exists.choose.1
    let archSum (g : Jₛ(F, S)) :=
      ∑ w : InfinitePlace F, ∑ m ∈ Finset.Ioo 0 (Nat.ceil A),
        term ((m : ℂ) - archPhase w) ((m : ℂ) + archPhase w) g
    let phase (v : S) (t : ℝ) :=
      t ∈ Ico 0 (period(v.val)) ∧ ∀ x : (v.val.adicCompletion F)ˣ,
        sLocalFiniteRestriction v (chart 0) x =
          (‖(x : v.val.adicCompletion F)‖ : ℂ) ^ ((t : ℂ) * Complex.I)
    let finitePlaces := Finset.univ.filter (fun v : S ↦ ∃ t, phase v t)
    let partialSum (height : ℝ) (g : Jₛ(F, S)) :=
      ∑ v : ↥finitePlaces,
        let t := (Finset.mem_filter.mp v.property).2.choose
        let d := period(v.val.val)
        ∑ m ∈ Finset.Ioo ⌊(t - height) / d⌋ ⌈(t + height) / d⌉,
          let a : ℂ := ((m : ℝ) * d - t : ℝ) * Complex.I
          term a (-a) g
    ∃ (T : ℕ → ℝ) (finiteSum : Jₛ(F, S) → ℂ), Tendsto T atTop atTop ∧
      (∀ K : Set Jₛ(F, S), IsCompact K →
        TendstoUniformlyOn (fun n ↦ partialSum (T n)) finiteSum atTop K) ∧
      IsBigO (comap normℝ (𝓝[>] 0))
        (fun g ↦ sLocalHomogeneousAdelicTheta F S (sLocalNormOneQuotientMeasure F S) ω f g -
          (archSum g + finiteSum g))
        (fun g ↦ Real.rpow (normℝ g) A)

/-- Paper: Theorem 7.1.2.3, equation (7.1.2.3), p. 318.
Over ℚ with only the real place, take the trivial character, `A = 1/2`, and a real
Gaussian. Both sums are empty and theta has a positive limit at norm zero.
For the finite-place overlap take ℚ with finite places 2 and 3, the trivial character,
and `A = 1/2`. At the finite places use the integer-ring indicators. At the real place
take a positive log-profile obtained by convolving a nonzero nonnegative smooth bump in
(0,1) with the indicators of [0, log 2] and [0, log 3]. The zeta function is a positive
constant times `6^s H(s)/s^2`, where H is the Mellin transform of the original bump
in the log coordinate. The origin is its only pole. Each finite-place series contributes
the printed logarithmic coefficient `-a₁`, whereas the inverse Mellin transform has
coefficient `-a₋₂`. The ratio 2a₁/a₋₂ is the bump-weighted mean of
(u + log 6)³/3, which exceeds one on (0,1). -/
theorem Printed.sLocalHomogeneousAdelicTheta_asymptotic_false :
    ¬ Printed.sLocalHomogeneousAdelicTheta_asymptotic := by sorry

end Theta

/-- Paper: Theorem 7.1.2.3, equation (7.1.2.3), p. 318.
As printed: In the finite-place contribution of a pole to Mellin inversion, the coefficient of
`(-log t)^(k-1)/(k-1)!` is the Laurent coefficient of index k − 1. This states the
residue formula in the centered coordinate, with the common weight at the center removed.
The signed indices are those of `sLocalZLaurentCoeff`. See ERRATA F89. -/
def Printed.sLocalZLaurentCoeff_mellinResidue : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (S : Finset Places(F))
    (χ : PontryaginDual Jₛ(F, S)) (v : S) (tᵥ : ℝ) (m : ℤ) (f : Tests(F, S)),
    let chart := twistₛ(F, S) ((circleToComplex).comp χ)
    tᵥ ∈ Ico 0 (period(v.val)) →
    (∀ x : (v.val.adicCompletion F)ˣ, sLocalFiniteRestriction v (chart 0) x =
      (‖(x : v.val.adicCompletion F)‖ : ℂ) ^ ((tᵥ : ℂ) * Complex.I)) →
    let c := chart (((m : ℝ) * period(v.val) - tᵥ : ℝ) * Complex.I)
    ∀ t : ℝ, 0 < t →
      complexResidue (fun z ↦ (t : ℂ) ^ (-z) * sLocalIdelicZFunction f (twistₛ(F, S) c z)) 0 =
        ∑ j ∈ Finset.range (sLocalPolarMultiplicity f c),
          sLocalZLaurentCoeff f c (j : ℤ) * (-(Real.log t : ℂ)) ^ j / (j.factorial : ℂ)

/-- Paper: Theorem 7.1.2.3, equation (7.1.2.3), p. 318.
Over ℚ take the place above 2, χ = 1, tᵥ = m = 0 and t = 1. Use a smooth
nonzero nonnegative real bump supported in (exp 1, exp 2) times the indicator of ℤ₂.
Its transform is B(s)/(1 − 2⁻ˢ), where B′(0) > B(0) > 0 since log x > 1
on the bump. The residue is B(0)/log 2. The printed coefficient is
a₀ = B′(0)/log 2 + B(0)/2, strictly larger. -/
theorem Printed.sLocalZLaurentCoeff_mellinResidue_false :
    ¬ Printed.sLocalZLaurentCoeff_mellinResidue := by sorry

/-- Paper: Proof of Theorem 7.1.2.3, p. 322.
As printed: The continued S-local zeta transform has a finite L¹ norm on the vertical
line of real part −A for every positive A, as required for the stated remainder
bound. The obstruction is recorded in `Sec1a`. See ERRATA F90. -/
def Printed.sLocalIdelicZFunction_verticalIntegrable_neg : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (S : Finset Places(F))
    (χ : PontryaginDual Jₛ(F, S)) (f : Tests(F, S)) (A : ℝ), 0 < A →
      Complex.VerticalIntegrable
        (fun s ↦ sLocalIdelicZFunction f (twistₛ(F, S) ((circleToComplex).comp χ) s)) (-A)

/-- Paper: Proof of Theorem 7.1.2.3, p. 322.
Take ℚ(√2), only its two real places, the trivial character, and at each place
`x² exp(-πx²)`. The zeta transform is a nonzero constant times Γℝ(s + 2)².
At A = 2 its norm on the vertical line is of order `|Im s|⁻²` near −2. -/
theorem Printed.sLocalIdelicZFunction_verticalIntegrable_neg_false :
    ¬ Printed.sLocalIdelicZFunction_verticalIntegrable_neg := by sorry

/-- Paper: Discussion of Theorem 7.1.2.3, p. 320.
As printed: Each nonnegative Laurent coefficient at c is an S-local eigendistribution
of weight c. This states the eigencharacter law using the scalar coefficient
`sLocalZLaurentCoeff` and the translation action of §5.5. See ERRATA F91. -/
def Printed.sLocalZLaurentCoeff_eigendistribution : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (S : Finset Places(F))
    (c : QuasiCharacter Jₛ(F, S)) (m : ℕ) (g : (SAdeleRing F S)ˣ) (f : Tests(F, S)),
    sLocalZLaurentCoeff (schwartzBruhatUnitTranslate g f) c (m : ℤ) =
      c (QuotientGroup.mk g) * sLocalZLaurentCoeff f c (m : ℤ)

/-- At a regular center the Laurent coefficient of index one is the derivative. -/
private theorem sLocalZLaurentCoeff_eigendistribution_false_deriv
    {F : Type u} [Field F] [NumberField F] {S : Finset Places(F)}
    (f : Tests(F, S)) (c : QuasiCharacter Jₛ(F, S))
    (H : ℂ → ℂ) (hH : ∀ z, H z = sLocalIdelicZFunction f (twistₛ(F, S) c z))
    (ha : AnalyticAt ℂ H 0) : sLocalZLaurentCoeff f c 1 = deriv H 0 := by
  obtain ⟨R, hR, hA⟩ := ha.exists_ball_analyticOnNhd
  unfold sLocalZLaurentCoeff complexResidue
  refine (tendsto_const_nhds.congr' ?_).limUnder_eq
  filter_upwards [Ioo_mem_nhdsGT hR] with r hr
  have hd := (hA.differentiableOn.mono (Metric.closedBall_subset_ball hr.2)).deriv_eq_smul_circleIntegral hr.1
  symm
  apply (div_eq_iff (by simp [Real.pi_ne_zero, Complex.I_ne_zero])).mpr
  rw [mul_comm]
  simpa only [← hH, sub_zero, smul_eq_mul, one_div, div_eq_inv_mul, mul_one,
    show (1 : ℤ) + 1 = (2 : ℕ) by decide, zpow_natCast] using hd

private theorem sLocalZLaurentCoeff_eigendistribution_false_translate
    {F : Type u} [Field F] [NumberField F] {S : Finset Places(F)}
    (f : Tests(F, S)) (g : (SAdeleRing F S)ˣ) (c : QuasiCharacter Jₛ(F, S)) :
    sLocalIdelicZetaIntegral (schwartzBruhatUnitTranslate g f) c =
      c (QuotientGroup.mk g) * sLocalIdelicZetaIntegral f c := by
  let : MeasurableSpace (SAdeleRing F S) := instMeasurableSpaceSAdeleRing F S
  have := sIdeleGroup_borelSpace (F := F) (S := S)
  have := sMultiplicativeTamagawaMeasure_isHaarMeasure (F := F) (S := S)
  let u (x : (SAdeleRing F S)ˣ) := f (Multiplicative.ofAdd x.val)
  let χ := c.toMonoidHom.comp (QuotientGroup.mk' _)
  change (∫ x, u (g⁻¹ * x) * χ x ∂sMultiplicativeTamagawaMeasure F S) =
    χ g * ∫ x, u x * χ x ∂sMultiplicativeTamagawaMeasure F S
  rw [← integral_mul_left_eq_self (μ := sMultiplicativeTamagawaMeasure F S)
    (fun x ↦ u (g⁻¹ * x) * χ x) g, ← integral_const_mul]
  exact integral_congr_ae (.of_forall fun x ↦ by simp only [mul_inv_cancel_left, map_mul, mul_left_comm])

/-- Use index one at the regular character of exponent one. Translation by a
norm-two idele differentiates the weight as well as the zeta integral. -/
private theorem sLocalZLaurentCoeff_eigendistribution_false_field
    (F : Type u) [Field F] [NumberField F]
    (h : Printed.sLocalZLaurentCoeff_eigendistribution.{u}) : False := by
  let S : Finset Places(F) := ∅
  let χ : PontryaginDual Jₛ(F, S) := 1
  let chart := twistₛ(F, S) ((circleToComplex).comp χ)
  let c := chart 1
  let Z (f : Tests(F, S)) (z : ℂ) := sLocalIdelicZFunction f (chart (1 + z))
  have htw (z : ℂ) : twistₛ(F, S) c z = chart (1 + z) := by
    ext1 x
    let N : ℂ := (((normₛ(F, S) x : ℝ≥0) : ℝ) : ℂ)
    have hn : N ≠ 0 := Complex.ofReal_ne_zero.mpr (NNReal.coe_ne_zero.mpr (normₛ(F, S) x).ne_zero)
    change (((χ x : Circle) : ℂ) * N ^ (1 : ℂ)) * N ^ z = ((χ x : Circle) : ℂ) * N ^ (1 + z)
    rw [mul_assoc, Complex.cpow_add _ _ hn]
  have hpos : ∀ᶠ z : ℂ in 𝓝 0, 0 < (1 + z).re :=
    (isOpen_lt continuous_const (Complex.continuous_re.comp (continuous_const.add continuous_id))).mem_nhds
      (by simp)
  have hZ (f : Tests(F, S)) : Z f =ᶠ[𝓝 0] (fun z ↦ sLocalIdelicZetaIntegral f (chart (1 + z))) := by
    filter_upwards [hpos] with z hz
    exact sLocalIdelicZFunction_eq_integral f ⟨χ, 1 + z, hz, rfl⟩
  have ha (f : Tests(F, S)) : AnalyticAt ℂ (Z f) 0 := by
    apply AnalyticAt.congr _ (hZ f).symm
    exact (sLocalIdelicZetaIntegral_analyticOn f χ (1 + (0 : ℂ)) (by simp)).comp
      (analyticAt_const.add analyticAt_id)
  have hcoeff (f : Tests(F, S)) : sLocalZLaurentCoeff f c 1 = deriv (Z f) 0 :=
    sLocalZLaurentCoeff_eigendistribution_false_deriv f c (Z f)
      (fun z ↦ congrArg (sLocalIdelicZFunction f) (htw z).symm) (ha f)
  obtain ⟨f, -, hf⟩ := sLocal_exists_real_test c ⟨χ, 1, by simp, rfl⟩
  have hne : Z f 0 ≠ 0 := by
    rw [(hZ f).eq_of_nhds, add_zero]
    exact hf
  obtain ⟨σ, hσ⟩ := sIdeleQuotientNorm_exists_section F S
  let two := Units.mk0 (2 : ℝ≥0) (by norm_num)
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (σ two)
  let q : Jₛ(F, S) := QuotientGroup.mk g
  have hn : (((normₛ(F, S) q : ℝ≥0) : ℝ) : ℂ) = 2 :=
    congrArg (fun t : ℝ≥0ˣ ↦ ((t.val : ℝ) : ℂ)) ((congrArg normₛ(F, S) hg).trans (hσ two))
  have hw (s : ℂ) : chart s q = (2 : ℂ) ^ s := by
    change ((χ q : Circle) : ℂ) * (((normₛ(F, S) q : ℝ≥0) : ℝ) : ℂ) ^ s = _
    simp [χ, hn]
  have he : Z (schwartzBruhatUnitTranslate g f) =ᶠ[𝓝 0]
      (fun z ↦ (2 : ℂ) ^ (1 + z) * Z f z) := by
    filter_upwards [hZ (schwartzBruhatUnitTranslate g f), hZ f] with z hz hfz
    rw [hz, hfz, sLocalZLaurentCoeff_eigendistribution_false_translate, ← hw]
  have hd : HasDerivAt (fun z : ℂ ↦ (2 : ℂ) ^ (1 + z)) (2 * Complex.log 2) 0 := by
    simpa using ((hasDerivAt_id' (0 : ℂ)).const_add 1).const_cpow (c := (2 : ℂ)) (Or.inl (by norm_num))
  have h1 := h F S c 1 g f
  change sLocalZLaurentCoeff _ c 1 = chart 1 q * sLocalZLaurentCoeff f c 1 at h1
  rw [hcoeff, hcoeff, hw, Complex.cpow_one, he.deriv_eq,
    (hd.fun_mul (ha f).differentiableAt.hasDerivAt).deriv] at h1
  have hlog : Complex.log 2 ≠ 0 := by
    intro h0
    have := Complex.exp_log (by norm_num : (2 : ℂ) ≠ 0)
    rw [h0, Complex.exp_zero] at this
    norm_num at this
  exact (mul_ne_zero (mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0) hlog) hne) (by simpa using h1)

/-- Paper: Discussion of Theorem 7.1.2.3, p. 320.
Over ℚ with only the real place and the trivial center, use m = 0 and the
Gaussian `exp(-πx²)`. Replacing it by `exp(-π(x/2)²)` multiplies its zeta
transform by `2^s`. The residue is 2, so the constant coefficient changes
by `2 log 2`, contrary to the trivial weight law. -/
theorem Printed.sLocalZLaurentCoeff_eigendistribution_false :
    ¬ Printed.sLocalZLaurentCoeff_eigendistribution := by
  intro h
  have : CharZero (ULift ℚ) := ⟨fun a b hab ↦ by simpa using congrArg ULift.down hab⟩
  have : NumberField (ULift ℚ) := ⟨⟩
  exact sLocalZLaurentCoeff_eigendistribution_false_field (ULift ℚ) h

/-- Paper: Discussion of Theorem 7.1.2.3, p. 321.
As printed: The coefficient whose Laurent index equals the finite-place lattice
index is supported on the corresponding periodic locus. In particular it vanishes on
tests whose support misses the inverse image of that locus, where the indicated
finite coordinate is zero. The scalar coefficient is `sLocalZLaurentCoeff`.
See ERRATA F92. -/
def Printed.sLocalZLaurentCoeff_finitePlace_support : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (S : Finset Places(F))
    (χ : PontryaginDual Jₛ(F, S)) (v : S) (t : ℝ) (m : ℤ) (f : Tests(F, S)),
    let chart := twistₛ(F, S) ((circleToComplex).comp χ)
    t ∈ Ico 0 (period(v.val)) →
      (∀ x : (v.val.adicCompletion F)ˣ, sLocalFiniteRestriction v (chart 0) x =
        (‖(x : v.val.adicCompletion F)‖ : ℂ) ^ ((t : ℂ) * Complex.I)) →
      Disjoint (tsupport (fun x ↦ f x))
        {x : Multiplicative (SAdeleRing F S) | x.toAdd.2 v = 0} →
      sLocalZLaurentCoeff f (chart ((((m : ℝ) * period(v.val) - t : ℝ) : ℂ) * Complex.I)) m = 0

/-- Paper: Discussion of Theorem 7.1.2.3, p. 321.
Take ℚ with the real place and the place above 2, the trivial character and m = 0.
Use a nonzero nonnegative smooth bump supported in (1,2) times the indicator of
ℤ₂ˣ. The support avoids the zero at the finite coordinate, but the zeta integral
is holomorphic at zero and its constant term is strictly positive. -/
theorem Printed.sLocalZLaurentCoeff_finitePlace_support_false :
    ¬ Printed.sLocalZLaurentCoeff_finitePlace_support := by sorry

/-- Paper: Proof of Theorem 7.1.2.3, p. 321.
As printed: For every test the trivial-character zeta function has pole order equal
to the number of infinite places at the origin. The test-dependent order is
`sLocalPolarMultiplicity`. See ERRATA F93. -/
def Printed.sLocalPolarMultiplicity_trivial_origin : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (S : Finset Places(F)) (f : Tests(F, S)),
    sLocalPolarMultiplicity f 1 = Fintype.card (InfinitePlace F)

/-- Paper: Proof of Theorem 7.1.2.3, p. 321.
The zero test over ℚ with only the real place has no pole. Over ℚ with the real
place and the place above 2, the Gaussian times the indicator of ℤ₂ instead
has a double pole from Γℝ(s) and the Euler factor at 2. -/
theorem Printed.sLocalPolarMultiplicity_trivial_origin_false :
    ¬ Printed.sLocalPolarMultiplicity_trivial_origin := by sorry

/-- Paper: Coefficient formula after Theorem 7.1.2.3, p. 323.
As printed: The Laurent coefficient of index k − 1 is given by the contour integral
around any continuously differentiable simple contour enclosing the center.
The local coefficient is `sLocalZLaurentCoeff`. See ERRATA F94. -/
def Printed.sLocalZLaurentCoeff_any_contour : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (S : Finset Places(F))
    (χ : PontryaginDual Jₛ(F, S)) (f : Tests(F, S)) (a : ℂ) (k : ℕ), 1 ≤ k →
    ∀ γ : ComplexContour, ContDiffOn ℝ 1 γ.toContinuousMap (Icc 0 1) →
      InjOn γ.toContinuousMap (Ico 0 1) → a ∉ γ.trace → γ.index a ≠ 0 →
        let chart := twistₛ(F, S) ((circleToComplex).comp χ)
        let integrand := fun s ↦ sLocalIdelicZFunction f (chart s) / (s - a) ^ k
        HasPettisIntegral (PettisMeasure.complex γ.measure) integrand
          (2 * (Real.pi : ℂ) * Complex.I * sLocalZLaurentCoeff f (chart a) ((k : ℤ) - 1))

/-- Paper: Coefficient formula after Theorem 7.1.2.3, p. 323.
For ℚ with only its real place take the Gaussian, the trivial character,
a = 0 and k = 1. The counterclockwise circle of radius 3 centered at zero also
encloses −2. The residue of Γℝ(s)/s at −2 adds π to the local coefficient. -/
theorem Printed.sLocalZLaurentCoeff_any_contour_false :
    ¬ Printed.sLocalZLaurentCoeff_any_contour := by sorry

end RiemannMasullo
