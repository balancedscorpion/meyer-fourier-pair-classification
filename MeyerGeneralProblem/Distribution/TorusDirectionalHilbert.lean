module

public import MeyerGeneralProblem.Distribution.TorusPoissonFourierMultiplier
public import Mathlib.Data.Real.Sign

@[expose] public section

/-!
# The directional Hilbert transform on the phase torus

The diagonal multiplier on the square-summable Fourier coefficients
uses the real frequency along the flow. This constructs the bounded
Hilbert transform and the positive-frequency part, with half of the
zero-frequency coefficient.
-/

namespace MeyerGeneralProblem

noncomputable section

open MeasureTheory UnitAddTorus
open scoped ComplexConjugate ENNReal NNReal

/-- Use normalized Haar measure on the circle factors of the phase torus. -/
local instance directionalHilbertCircleMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

local instance directionalHilbertCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

local notation:max "TorusL2(" d ")" => Lp ℂ 2 (volume : Measure (UnitAddTorus d))

/-- Multiply the entries of a square-summable sequence by a bounded
complex sequence. The supplied bound also bounds the resulting
operator norm. -/
def lpDiagonalMul {ι : Type*} (m : ι → ℂ) {C : ℝ}
    (hC : 0 ≤ C) (hm : ∀ i, ‖m i‖ ≤ C) :
    lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2 := by
  have hBound (f : lp (fun _ : ι => ℂ) 2) (i : ι) :
      ‖m i * f i‖ ≤ ‖(((C : ℂ) • f) : lp (fun _ : ι => ℂ) 2) i‖ := by
    rw [lp.coeFn_smul, Pi.smul_apply, norm_mul, norm_smul, Complex.norm_real,
      Real.norm_of_nonneg hC]
    exact mul_le_mul_of_nonneg_right (hm i) (norm_nonneg _)
  let D : lp (fun _ : ι => ℂ) 2 →ₗ[ℂ] lp (fun _ : ι => ℂ) 2 :=
    { toFun := fun f => ⟨fun i => m i * f i, (lp.memℓp (((C : ℂ) • f) : lp (fun _ : ι => ℂ) 2)).norm.mono (hBound f)⟩
      map_add' := by
        intro f g
        ext i
        change m i * (f i + g i) = m i * f i + m i * g i
        exact mul_add _ _ _
      map_smul' := by
        intro c f
        ext i
        change m i * (c * f i) = c * (m i * f i)
        ring }
  exact D.mkContinuous C (fun f => by
    calc
      _ ≤ ‖(C : ℂ) • f‖ := lp.norm_mono (by norm_num) (hBound f)
      _ = _ := by rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hC])

@[simp]
theorem lpDiagonalMul_apply {ι : Type*} (m : ι → ℂ) {C : ℝ}
    (hC : 0 ≤ C) (hm : ∀ i, ‖m i‖ ≤ C) (f : lp (fun _ : ι => ℂ) 2) (i : ι) :
    lpDiagonalMul m hC hm f i = m i * f i := rfl

theorem norm_lpDiagonalMul_apply_le {ι : Type*} (m : ι → ℂ) {C : ℝ}
    (hC : 0 ≤ C) (hm : ∀ i, ‖m i‖ ≤ C) (f : lp (fun _ : ι => ℂ) 2) :
    ‖lpDiagonalMul m hC hm f‖ ≤ C * ‖f‖ := by
  calc
    _ ≤ ‖(C : ℂ) • f‖ := lp.norm_mono (by norm_num) fun i => by
      rw [lpDiagonalMul_apply, lp.coeFn_smul, Pi.smul_apply, norm_mul, norm_smul,
        Complex.norm_real, Real.norm_of_nonneg hC]
      exact mul_le_mul_of_nonneg_right (hm i) (norm_nonneg _)
    _ = _ := by rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hC]

/-- The Fourier multiplier on torus `L²` defined by a bounded
coefficient sequence in the normalized Haar Fourier basis. -/
def torusL2FourierMultiplier {d : Type*} [Fintype d] (m : (d → ℤ) → ℂ) {C : ℝ}
    (hC : 0 ≤ C) (hm : ∀ n, ‖m n‖ ≤ C) : TorusL2(d) →L[ℂ] TorusL2(d) :=
  let e := (mFourierBasis (d := d)).repr.toContinuousLinearEquiv
  e.symm.toContinuousLinearMap.comp ((lpDiagonalMul m hC hm).comp e.toContinuousLinearMap)

theorem mFourierCoeff_torusL2FourierMultiplier {d : Type*} [Fintype d]
    (m : (d → ℤ) → ℂ) {C : ℝ} (hC : 0 ≤ C) (hm : ∀ n, ‖m n‖ ≤ C)
    (f : TorusL2(d)) (n : d → ℤ) :
    mFourierCoeff (torusL2FourierMultiplier m hC hm f) n = m n * mFourierCoeff f n := by
  rw [← mFourierBasis_repr, ← mFourierBasis_repr]
  change (mFourierBasis.repr (mFourierBasis.repr.symm
    (lpDiagonalMul m hC hm (mFourierBasis.repr f)))) n = _
  rw [LinearIsometryEquiv.apply_symm_apply, lpDiagonalMul_apply]

theorem norm_torusL2FourierMultiplier_apply_le {d : Type*} [Fintype d]
    (m : (d → ℤ) → ℂ) {C : ℝ} (hC : 0 ≤ C) (hm : ∀ n, ‖m n‖ ≤ C)
    (f : TorusL2(d)) :
    ‖torusL2FourierMultiplier m hC hm f‖ ≤ C * ‖f‖ := by
  change ‖mFourierBasis.repr.symm (lpDiagonalMul m hC hm (mFourierBasis.repr f))‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  exact (norm_lpDiagonalMul_apply_le m hC hm _).trans_eq
    (by rw [LinearIsometryEquiv.norm_map])

theorem norm_directionalHilbertMultiplier_le_one (b : ℝ) :
    ‖-Complex.I * (Real.sign b : ℂ)‖ ≤ 1 := by
  rcases lt_trichotomy b 0 with hb | rfl | hb
  · simp [Real.sign_of_neg hb]
  · simp
  · simp [Real.sign_of_pos hb]

/-- The directional Hilbert transform with multiplier
`-i sign(β · n)` on the normalized Haar phase torus. -/
def torusDirectionalHilbert {d : Type*} [Fintype d] (β : d → ℝ) :
    TorusL2(d) →L[ℂ] TorusL2(d) :=
  torusL2FourierMultiplier (fun n => -Complex.I * (Real.sign (torusDirectionalFrequency β n) : ℂ))
    zero_le_one (fun _ => norm_directionalHilbertMultiplier_le_one _)

theorem mFourierCoeff_torusDirectionalHilbert {d : Type*} [Fintype d]
    (β : d → ℝ) (f : TorusL2(d)) (n : d → ℤ) :
    mFourierCoeff (torusDirectionalHilbert β f) n =
      (-Complex.I * (Real.sign (torusDirectionalFrequency β n) : ℂ)) * mFourierCoeff f n :=
  mFourierCoeff_torusL2FourierMultiplier _ _ _ f n

theorem norm_torusDirectionalHilbert_apply_le {d : Type*} [Fintype d]
    (β : d → ℝ) (f : TorusL2(d)) :
    ‖torusDirectionalHilbert β f‖ ≤ ‖f‖ := by
  simpa only [torusDirectionalHilbert, one_mul] using norm_torusL2FourierMultiplier_apply_le _ zero_le_one
    (fun n => norm_directionalHilbertMultiplier_le_one (torusDirectionalFrequency β n)) f

private theorem mFourierCoeff_add_torusL2 {d : Type*} [Fintype d]
    (f g : TorusL2(d)) (n : d → ℤ) :
    mFourierCoeff (f + g : TorusL2(d)) n = mFourierCoeff f n + mFourierCoeff g n := by
  simp only [← mFourierBasis_repr, map_add, lp.coeFn_add, Pi.add_apply]

private theorem mFourierCoeff_smul_torusL2 {d : Type*} [Fintype d]
    (c : ℂ) (f : TorusL2(d)) (n : d → ℤ) :
    mFourierCoeff (c • f : TorusL2(d)) n = c * mFourierCoeff f n := by
  simp only [← mFourierBasis_repr, map_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]

/-- The positive-frequency field `(f + i Hβ f)/2` with the zero
coefficient shared equally between the two spectral halves. -/
def torusPositiveFrequencyPart {d : Type*} [Fintype d] (β : d → ℝ) :
    TorusL2(d) →L[ℂ] TorusL2(d) :=
  (2 : ℂ)⁻¹ • (ContinuousLinearMap.id ℂ (TorusL2(d)) +
    Complex.I • torusDirectionalHilbert β)

theorem mFourierCoeff_torusPositiveFrequencyPart {d : Type*} [Fintype d]
    (β : d → ℝ) (f : TorusL2(d)) (n : d → ℤ) :
    mFourierCoeff (torusPositiveFrequencyPart β f) n =
      (1 + (Real.sign (torusDirectionalFrequency β n) : ℂ)) / 2 * mFourierCoeff f n := by
  change mFourierCoeff ((2 : ℂ)⁻¹ • (f + Complex.I • torusDirectionalHilbert β f) :
    TorusL2(d)) n = _
  rw [mFourierCoeff_smul_torusL2, mFourierCoeff_add_torusL2, mFourierCoeff_smul_torusL2,
    mFourierCoeff_torusDirectionalHilbert]
  simp only [mul_assoc]
  rw [← mul_assoc Complex.I (-Complex.I), mul_neg, Complex.I_mul_I, neg_neg, one_mul]
  ring

theorem mFourierCoeff_torusPositiveFrequencyPart_eq_zero_of_neg {d : Type*} [Fintype d]
    (β : d → ℝ) (f : TorusL2(d)) (n : d → ℤ) (hn : torusDirectionalFrequency β n < 0) :
    mFourierCoeff (torusPositiveFrequencyPart β f) n = 0 := by
  rw [mFourierCoeff_torusPositiveFrequencyPart, Real.sign_of_neg hn]
  norm_num

theorem norm_torusPositiveFrequencyPart_apply_le {d : Type*} [Fintype d]
    (β : d → ℝ) (f : TorusL2(d)) :
    ‖torusPositiveFrequencyPart β f‖ ≤ ‖f‖ := by
  change ‖(2 : ℂ)⁻¹ • (f + Complex.I • torusDirectionalHilbert β f)‖ ≤ ‖f‖
  rw [norm_smul, norm_inv, show ‖(2 : ℂ)‖ = 2 by norm_num]
  refine (mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)).trans ?_
  rw [norm_smul, Complex.norm_I, one_mul]
  linarith only [norm_torusDirectionalHilbert_apply_le β f]

private theorem mFourierCoeff_congr_ae_torus {d : Type*} [Fintype d]
    {f g : UnitAddTorus d → ℂ} (hfg : f =ᵐ[volume] g) (n : d → ℤ) :
    mFourierCoeff f n = mFourierCoeff g n :=
  integral_congr_ae (hfg.mono fun θ hθ => congrArg (fun w => mFourier (-n) θ • w) hθ)

private theorem mFourierCoeff_pointwise_conj {d : Type*} [Fintype d]
    (f : UnitAddTorus d → ℂ) (n : d → ℤ) :
    mFourierCoeff (fun θ => conj (f θ)) n = conj (mFourierCoeff f (-n)) := by
  simp only [mFourierCoeff, smul_eq_mul, neg_neg, ← integral_conj, map_mul, mFourier_neg]

private theorem memLp_conj_torusL2 {d : Type*} [Fintype d] (f : TorusL2(d)) :
    MemLp (fun θ => conj (f θ)) 2 (volume : Measure (UnitAddTorus d)) :=
  (Lp.memLp f).congr_norm (Complex.continuous_conj.comp_aestronglyMeasurable (Lp.memLp f).aestronglyMeasurable)
    (ae_of_all _ fun θ => (Complex.norm_conj (f θ)).symm)

private def torusL2Conj {d : Type*} [Fintype d] (f : TorusL2(d)) :
    TorusL2(d) := (memLp_conj_torusL2 f).toLp _

private theorem coeFn_torusL2Conj {d : Type*} [Fintype d] (f : TorusL2(d)) :
    (torusL2Conj f : UnitAddTorus d → ℂ) =ᵐ[volume] fun θ => conj (f θ) :=
  MemLp.coeFn_toLp (memLp_conj_torusL2 f)

private theorem mFourierCoeff_torusL2Conj {d : Type*} [Fintype d]
    (f : TorusL2(d)) (n : d → ℤ) :
    mFourierCoeff (torusL2Conj f) n = conj (mFourierCoeff f (-n)) :=
  (mFourierCoeff_congr_ae_torus (coeFn_torusL2Conj f) n).trans
    (mFourierCoeff_pointwise_conj f n)

private theorem torusDirectionalFrequency_neg {d : Type*} [Fintype d]
    (β : d → ℝ) (n : d → ℤ) :
    torusDirectionalFrequency β (-n) = -torusDirectionalFrequency β n := by
  simp [torusDirectionalFrequency, Finset.sum_neg_distrib]

private theorem torusPositiveFrequencyPart_add_conj_of_real {d : Type*} [Fintype d]
    (β : d → ℝ) (f : TorusL2(d)) (hReal : ∀ᵐ θ ∂volume, (f θ).im = 0) :
    torusPositiveFrequencyPart β f + torusL2Conj (torusPositiveFrequencyPart β f) = f := by
  have hConj : (fun θ => conj (f θ)) =ᵐ[volume] f := by
    filter_upwards [hReal] with θ hθ
    exact Complex.ext (Complex.conj_re _) (by rw [Complex.conj_im, hθ, neg_zero])
  have hSym (n : d → ℤ) : conj (mFourierCoeff f (-n)) = mFourierCoeff f n :=
    (mFourierCoeff_pointwise_conj f n).symm.trans (mFourierCoeff_congr_ae_torus hConj n)
  apply (mFourierBasis (d := d)).repr.injective
  ext n
  rw [mFourierBasis_repr, mFourierBasis_repr, mFourierCoeff_add_torusL2,
    mFourierCoeff_torusL2Conj, mFourierCoeff_torusPositiveFrequencyPart,
    mFourierCoeff_torusPositiveFrequencyPart, torusDirectionalFrequency_neg, Real.sign_neg]
  simp only [map_mul, map_div₀, map_add, map_one, map_ofNat, Complex.conj_ofReal, hSym]
  push_cast
  ring

/-- For a real torus field the real part of the positive-frequency
field is one half of the original value, as an almost-everywhere
equality of the actual `L²` representatives. -/
theorem ae_re_torusPositiveFrequencyPart_of_real {d : Type*} [Fintype d]
    (β : d → ℝ) (f : TorusL2(d)) (hReal : ∀ᵐ θ ∂volume, (f θ).im = 0) :
    ∀ᵐ θ ∂volume, (torusPositiveFrequencyPart β f θ).re = (f θ).re / 2 := by
  let G := torusPositiveFrequencyPart β f
  have hEq : G + torusL2Conj G = f := torusPositiveFrequencyPart_add_conj_of_real β f hReal
  filter_upwards [Lp.coeFn_add G (torusL2Conj G), coeFn_torusL2Conj G] with θ hAdd hConj
  have hVal : (f θ) = G θ + conj (G θ) := by
    rw [← hConj, ← Pi.add_apply, ← hAdd, hEq]
  have hRe := congrArg Complex.re hVal
  simp only [Complex.add_re, Complex.conj_re] at hRe
  linarith

section SupportPoissonField

open Adaptive ProbabilityTheory Set

theorem memLp_supportPoissonField_ofReal {d : Type*} [Fintype d]
    (S : UnitAddTorus d → LocallyFiniteCarrier) (T : UnitAddTorus d → TemperedDistribution ℝ ℂ)
    (hT : ∀ θ, DistributionSupportedOn (S θ).carrier (T θ))
    (hCont : ∀ f : SchwartzMap ℝ ℂ, HasCompactSupport (f : ℝ → ℂ) →
      Continuous (fun θ => T θ f))
    {K : ℕ} (hCount : ∀ θ r, ((S θ).carrier ∩ Ico r (r + 1)).ncard ≤ K) (y : ℝ≥0) :
    MemLp (fun θ => Complex.ofReal (∫ x, cauchyPDFReal 0 y x ∂discreteSupportCount (T θ)))
      2 (volume : Measure (UnitAddTorus d)) := by
  have hReal : MemLp (fun θ => ∫ x, cauchyPDFReal 0 y x ∂discreteSupportCount (T θ))
      2 (volume : Measure (UnitAddTorus d)) := by
    by_cases hy : y = 0
    · simp [hy, cauchyPDFReal_scale_zero]
    · exact (memLp_poisson_discreteSupportCount S T hT hCont hCount volume 0
        (pos_iff_ne_zero.mpr hy)).mono_exponent le_top
  exact hReal.congr_norm (Complex.continuous_ofReal.comp_aestronglyMeasurable hReal.aestronglyMeasurable)
    (ae_of_all _ fun _ => (Complex.norm_real _).symm)

/-- The real Poisson field of the actual support count, represented
in the complex normalized Haar `L²` space. -/
def torusSupportPoissonL2 {d : Type*} [Fintype d]
    (S : UnitAddTorus d → LocallyFiniteCarrier) (T : UnitAddTorus d → TemperedDistribution ℝ ℂ)
    (hT : ∀ θ, DistributionSupportedOn (S θ).carrier (T θ))
    (hCont : ∀ f : SchwartzMap ℝ ℂ, HasCompactSupport (f : ℝ → ℂ) →
      Continuous (fun θ => T θ f))
    {K : ℕ} (hCount : ∀ θ r, ((S θ).carrier ∩ Ico r (r + 1)).ncard ≤ K) (y : ℝ≥0) :
    TorusL2(d) :=
  (memLp_supportPoissonField_ofReal S T hT hCont hCount y).toLp _

theorem coeFn_torusSupportPoissonL2 {d : Type*} [Fintype d]
    (S : UnitAddTorus d → LocallyFiniteCarrier) (T : UnitAddTorus d → TemperedDistribution ℝ ℂ)
    (hT : ∀ θ, DistributionSupportedOn (S θ).carrier (T θ))
    (hCont : ∀ f : SchwartzMap ℝ ℂ, HasCompactSupport (f : ℝ → ℂ) →
      Continuous (fun θ => T θ f))
    {K : ℕ} (hCount : ∀ θ r, ((S θ).carrier ∩ Ico r (r + 1)).ncard ≤ K) (y : ℝ≥0) :
    (torusSupportPoissonL2 S T hT hCont hCount y : UnitAddTorus d → ℂ) =ᵐ[volume]
      fun θ => Complex.ofReal (∫ x, cauchyPDFReal 0 y x ∂discreteSupportCount (T θ)) :=
  MemLp.coeFn_toLp (memLp_supportPoissonField_ofReal S T hT hCont hCount y)

/-- The positive-frequency `L²` part of the original support
detector at a fixed Poisson height. -/
def torusSupportPositivePoissonL2 {d : Type*} [Fintype d]
    (β : d → ℝ) (S : UnitAddTorus d → LocallyFiniteCarrier)
    (T : UnitAddTorus d → TemperedDistribution ℝ ℂ)
    (hT : ∀ θ, DistributionSupportedOn (S θ).carrier (T θ))
    (hCont : ∀ f : SchwartzMap ℝ ℂ, HasCompactSupport (f : ℝ → ℂ) →
      Continuous (fun θ => T θ f))
    {K : ℕ} (hCount : ∀ θ r, ((S θ).carrier ∩ Ico r (r + 1)).ncard ≤ K) (y : ℝ≥0) :
    TorusL2(d) :=
  torusPositiveFrequencyPart β (torusSupportPoissonL2 S T hT hCont hCount y)

/-- Half of the actual real Poisson detector is the real part of the
positive-frequency field. In particular this real part is nonnegative. -/
theorem ae_re_torusSupportPositivePoissonL2 {d : Type*} [Fintype d]
    (β : d → ℝ) (S : UnitAddTorus d → LocallyFiniteCarrier)
    (T : UnitAddTorus d → TemperedDistribution ℝ ℂ)
    (hT : ∀ θ, DistributionSupportedOn (S θ).carrier (T θ))
    (hCont : ∀ f : SchwartzMap ℝ ℂ, HasCompactSupport (f : ℝ → ℂ) →
      Continuous (fun θ => T θ f))
    {K : ℕ} (hCount : ∀ θ r, ((S θ).carrier ∩ Ico r (r + 1)).ncard ≤ K) (y : ℝ≥0) :
    ∀ᵐ θ ∂volume, (torusSupportPositivePoissonL2 β S T hT hCont hCount y θ).re =
      (∫ x, cauchyPDFReal 0 y x ∂discreteSupportCount (T θ)) / 2 := by
  let f := torusSupportPoissonL2 S T hT hCont hCount y
  have hF := coeFn_torusSupportPoissonL2 S T hT hCont hCount y
  have hReal : ∀ᵐ θ ∂volume, (f θ).im = 0 := by
    filter_upwards [hF] with θ hθ
    rw [show f θ = _ from hθ, Complex.ofReal_im]
  filter_upwards [ae_re_torusPositiveFrequencyPart_of_real β f hReal, hF] with θ hG hθ
  change (torusPositiveFrequencyPart β f θ).re = _
  rw [hG, show f θ = _ from hθ, Complex.ofReal_re]

theorem mFourierCoeff_torusSupportPositivePoissonL2_eq_zero_of_neg {d : Type*} [Fintype d]
    (β : d → ℝ) (S : UnitAddTorus d → LocallyFiniteCarrier)
    (T : UnitAddTorus d → TemperedDistribution ℝ ℂ)
    (hT : ∀ θ, DistributionSupportedOn (S θ).carrier (T θ))
    (hCont : ∀ f : SchwartzMap ℝ ℂ, HasCompactSupport (f : ℝ → ℂ) →
      Continuous (fun θ => T θ f))
    {K : ℕ} (hCount : ∀ θ r, ((S θ).carrier ∩ Ico r (r + 1)).ncard ≤ K) (y : ℝ≥0)
    (n : d → ℤ) (hn : torusDirectionalFrequency β n < 0) :
    mFourierCoeff (torusSupportPositivePoissonL2 β S T hT hCont hCount y) n = 0 :=
  mFourierCoeff_torusPositiveFrequencyPart_eq_zero_of_neg β _ n hn

/-- The exact positive-frequency `L²` coefficients propagate by the
same Poisson multiplier as the real field. -/
theorem mFourierCoeff_torusSupportPositivePoissonL2_add {d : Type*} [Fintype d]
    (β : d → ℝ) (S : UnitAddTorus d → LocallyFiniteCarrier)
    (T : UnitAddTorus d → TemperedDistribution ℝ ℂ)
    (hT : ∀ θ, DistributionSupportedOn (S θ).carrier (T θ))
    (hAdvance : ∀ t θ, T (unitAddTorusFlow β t θ) = combDistributionTranslation (-t) (T θ))
    (hCont : ∀ f : SchwartzMap ℝ ℂ, HasCompactSupport (f : ℝ → ℂ) →
      Continuous (fun θ => T θ f))
    {K : ℕ} (hCount : ∀ θ r, ((S θ).carrier ∩ Ico r (r + 1)).ncard ≤ K)
    {s y : ℝ≥0} (hs : 0 < s) (hy : 0 < y) (n : d → ℤ) :
    mFourierCoeff (torusSupportPositivePoissonL2 β S T hT hCont hCount (s + y)) n =
      (Real.exp (-(2 * Real.pi * (s : ℝ)) * |torusDirectionalFrequency β n|) : ℂ) *
        mFourierCoeff (torusSupportPositivePoissonL2 β S T hT hCont hCount y) n := by
  simp only [torusSupportPositivePoissonL2, mFourierCoeff_torusPositiveFrequencyPart]
  rw [mFourierCoeff_congr_ae_torus (coeFn_torusSupportPoissonL2 S T hT hCont hCount (s + y)) n,
    mFourierCoeff_congr_ae_torus (coeFn_torusSupportPoissonL2 S T hT hCont hCount y) n,
    mFourierCoeff_poisson_discreteSupportCount_add β S T hT hAdvance hCont hCount hs hy]
  ring

end SupportPoissonField

end
end MeyerGeneralProblem
