module

public import MeyerGeneralProblem.Sampling.KNSLocalizerFourier
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.Analysis.Calculus.Deriv.Support

@[expose] public section

/-!
# Genuine finite regularity of the KNS localizer

A box convolution is an actual sliding interval integral. Integrable input
gives continuity; continuous input gives a continuous first derivative.
Consequently every KNS localizer of order at least two is genuinely C1.
This is enough to multiply a C1 unknown function for localized Dirichlet
Poincare, without assigning it Schwartz regularity or using moment estimates.
-/

namespace MeyerGeneralProblem

noncomputable section

open MeasureTheory Set Convolution
open scoped ContDiff Topology FourierTransform

/-- Convolution with the actual symmetric box is exactly the sliding
interval integral, including its two endpoints. -/
theorem convolution_knsBox_eq_intervalIntegral (g : ℝ → ℝ) {r : ℝ} (hr : 0 ≤ r) (x : ℝ) :
    (g ⋆[ContinuousLinearMap.mul ℝ ℝ] knsBox r) x = ∫ t in (x-r)..(x+r), g t := by
  rw [convolution_def, intervalIntegral.integral_of_le (by linarith : x-r ≤ x+r),
    ← integral_Icc_eq_integral_Ioc, ← integral_indicator measurableSet_Icc]
  apply integral_congr_ae
  filter_upwards [] with t
  have he : x-t ∈ Icc (-r) r ↔ t ∈ Icc (x-r) (x+r) := by
    constructor <;> intro h <;> obtain ⟨h₁,h₂⟩ := h <;> constructor <;> linarith
  by_cases ht : t ∈ Icc (x-r) (x+r)
  · simp [knsBox, he, ht]
  · simp [knsBox, he, ht]

private theorem knsBox_convolution_eq_primitive_sub {g : ℝ → ℝ} (hg : Integrable g)
    {r : ℝ} (hr : 0 ≤ r) (x : ℝ) :
    (g ⋆[ContinuousLinearMap.mul ℝ ℝ] knsBox r) x =
      (∫ t in (0:ℝ)..(x+r), g t) - ∫ t in (0:ℝ)..(x-r), g t := by
  rw [convolution_knsBox_eq_intervalIntegral g hr]
  have h := intervalIntegral.integral_add_adjacent_intervals
    (hg.intervalIntegrable (a := 0) (b := x-r))
    (hg.intervalIntegrable (a := x-r) (b := x+r))
  linarith

/-- Sliding a finite box over arbitrary integrable real data gives a
continuous actual convolution, even if the input has jump discontinuities. -/
theorem continuous_convolution_knsBox {g : ℝ → ℝ} (hg : Integrable g)
    {r : ℝ} (hr : 0 ≤ r) : Continuous (g ⋆[ContinuousLinearMap.mul ℝ ℝ] knsBox r) := by
  have hprim : Continuous (fun x : ℝ => ∫ t in (0:ℝ)..x, g t) :=
    intervalIntegral.continuous_primitive (fun _ _ => hg.intervalIntegrable) 0
  have he : (g ⋆[ContinuousLinearMap.mul ℝ ℝ] knsBox r) =
      fun x => (∫ t in (0:ℝ)..(x+r), g t) - ∫ t in (0:ℝ)..(x-r), g t :=
    funext (knsBox_convolution_eq_primitive_sub hg hr)
  rw [he]
  exact (hprim.comp (continuous_id.add continuous_const)).sub
    (hprim.comp (continuous_id.sub continuous_const))

/-- The derivative of an actual box convolution is the difference of
the two moving boundary values. -/
theorem hasDerivAt_convolution_knsBox {g : ℝ → ℝ} (hg : Integrable g) (hc : Continuous g)
    {r : ℝ} (hr : 0 ≤ r) (x : ℝ) :
    HasDerivAt (g ⋆[ContinuousLinearMap.mul ℝ ℝ] knsBox r) (g (x+r)-g (x-r)) x := by
  have he : (g ⋆[ContinuousLinearMap.mul ℝ ℝ] knsBox r) =
      fun x => (∫ t in (0:ℝ)..(x+r), g t) - ∫ t in (0:ℝ)..(x-r), g t :=
    funext (knsBox_convolution_eq_primitive_sub hg hr)
  rw [he]
  convert! ((hc.integral_hasStrictDerivAt 0 (x+r)).hasDerivAt.comp x
    ((hasDerivAt_id x).add_const r)).sub
    ((hc.integral_hasStrictDerivAt 0 (x-r)).hasDerivAt.comp x
      ((hasDerivAt_id x).sub_const r)) using 1
  simp only [mul_one]

/-- One box convolution gains C1 regularity from continuous integrable input. -/
theorem contDiff_one_convolution_knsBox {g : ℝ → ℝ} (hg : Integrable g) (hc : Continuous g)
    {r : ℝ} (hr : 0 ≤ r) : ContDiff ℝ 1 (g ⋆[ContinuousLinearMap.mul ℝ ℝ] knsBox r) := by
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun x => (hasDerivAt_convolution_knsBox hg hc hr x).differentiableAt, ?_⟩
  have he : deriv (g ⋆[ContinuousLinearMap.mul ℝ ℝ] knsBox r) =
      fun x => g (x+r)-g (x-r) := funext (fun x => (hasDerivAt_convolution_knsBox hg hc hr x).deriv)
  rw [he]
  exact (hc.comp (continuous_id.add continuous_const)).sub
    (hc.comp (continuous_id.sub continuous_const))

private theorem kns_realConvolution_comm (f g : ℝ → ℝ) :
    f ⋆[ContinuousLinearMap.mul ℝ ℝ] g = g ⋆[ContinuousLinearMap.mul ℝ ℝ] f := by
  have hf : (ContinuousLinearMap.mul ℝ ℝ).flip = ContinuousLinearMap.mul ℝ ℝ := by
    apply ContinuousLinearMap.ext
    intro x
    apply ContinuousLinearMap.ext
    intro y
    exact mul_comm y x
  have h := convolution_flip (L := ContinuousLinearMap.mul ℝ ℝ)
    (μ := (volume : Measure ℝ)) (f := f) (g := g)
  rw [hf] at h
  exact h.symm

/-- A normalized short-box convolution is continuous for any integrable
input, so actual repeated boxes need no assumed continuous base kernel. -/
theorem continuous_knsBeta_convolution (n : ℕ) {u : ℝ} (hu : 0 < u)
    {g : ℝ → ℝ} (hg : Integrable g) :
    Continuous (knsBeta n u ⋆[ContinuousLinearMap.mul ℝ ℝ] g) := by
  have he : knsBeta n u ⋆[ContinuousLinearMap.mul ℝ ℝ] g =
      fun x => (n : ℝ)/u * (g ⋆[ContinuousLinearMap.mul ℝ ℝ] knsBox (u/(2*n))) x := by
    rw [kns_realConvolution_comm]
    funext x
    simp only [convolution_def, ContinuousLinearMap.mul_apply', knsBeta]
    rw [← integral_const_mul]
    congr 1
    funext t
    ring
  rw [he]
  exact (continuous_convolution_knsBox hg (by positivity)).const_mul _

/-- Every actual B-spline formed from at least two short boxes is
continuous, despite the discontinuous individual box. -/
theorem continuous_knsBSpline {n : ℕ} (hn : 2 ≤ n) {u : ℝ} (hu : 0 < u) :
    Continuous (knsBSpline n u) := by
  have he : n-1=(n-2)+1 := by omega
  unfold knsBSpline
  rw [he, knsBoxConvolution]
  exact continuous_knsBeta_convolution n hu
    (integrable_knsBoxConvolution (integrable_knsBeta n u) (n-2))

/-- At order two and every larger order the genuine localizer is C1,
with no smoothing replacement and no hypothesis on the unknown function. -/
theorem contDiff_one_knsMomentLocalizer {n : ℕ} (hn : 2 ≤ n) {u : ℝ} (hu : 0 < u) :
    ContDiff ℝ 1 (knsMomentLocalizer n u) :=
  contDiff_one_convolution_knsBox (integrable_knsBSpline n u) (continuous_knsBSpline hn hu) hu.le

/-- The actual first derivative is an explicit difference of translated
B-spline values, with the precise long-box radius u. -/
theorem deriv_knsMomentLocalizer {n : ℕ} (hn : 2 ≤ n) {u : ℝ} (hu : 0 < u) (x : ℝ) :
    deriv (knsMomentLocalizer n u) x = knsBSpline n u (x+u)-knsBSpline n u (x-u) :=
  (hasDerivAt_convolution_knsBox (integrable_knsBSpline n u) (continuous_knsBSpline hn hu) hu.le x).deriv

/-- Even the first-order localizer is continuous, although no C1
assertion is made at that order. -/
theorem continuous_knsMomentLocalizer (n : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    Continuous (knsMomentLocalizer n u) :=
  continuous_convolution_knsBox (integrable_knsBSpline n u) hu

/-- The genuine localizer has compact topological support. -/
theorem hasCompactSupport_knsMomentLocalizer {n : ℕ} (hn : 1 ≤ n) (u : ℝ) :
    HasCompactSupport (knsMomentLocalizer n u) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc (support_knsMomentLocalizer_subset hn u)

/-- Continuity sharpens the localizer's pointwise support to the open
outer interval, so its values at both outer endpoints really vanish. -/
theorem support_knsMomentLocalizer_subset_open {n : ℕ} (hn : 1 ≤ n) {u : ℝ} (hu : 0 ≤ u) :
    Function.support (knsMomentLocalizer n u) ⊆ Ioo (-(3*u/2)) (3*u/2) := by
  have h := (continuous_knsMomentLocalizer n hu).isOpen_support.subset_interior_iff.mpr
    (support_knsMomentLocalizer_subset hn u)
  simpa only [interior_Icc] using h

/-- The actual first derivative vanishes at and beyond both outer
support endpoints at every C1 order. -/
theorem deriv_knsMomentLocalizer_eq_zero_of_outer {n : ℕ} (hn : 2 ≤ n) {u : ℝ} (hu : 0 < u)
    {x : ℝ} (hx : 3*u/2 ≤ |x|) : deriv (knsMomentLocalizer n u) x = 0 := by
  have hs : Function.support (deriv (knsMomentLocalizer n u)) ⊆ Icc (-(3*u/2)) (3*u/2) :=
    support_deriv_subset.trans (closure_minimal (support_knsMomentLocalizer_subset (by omega) u) isClosed_Icc)
  have hc := (contDiff_one_iff_deriv.mp (contDiff_one_knsMomentLocalizer hn hu)).2
  have ho := hc.isOpen_support.subset_interior_iff.mpr hs
  rw [interior_Icc] at ho
  by_contra h
  have hlt : |x| < 3*u/2 := abs_lt.mpr (ho h)
  linarith

/-- On the entire closed central plateau the actual derivative is zero,
including the two join points. -/
theorem deriv_knsMomentLocalizer_eq_zero_on_plateau {n : ℕ} (hn : 2 ≤ n) {u : ℝ} (hu : 0 < u)
    {x : ℝ} (hx : |x| ≤ u/2) : deriv (knsMomentLocalizer n u) x = 0 := by
  have hs := (continuous_knsBSpline hn hu).isOpen_support.subset_interior_iff.mpr
    (support_knsBSpline_subset (by omega) u)
  rw [interior_Icc] at hs
  have hx' := abs_le.mp hx
  have hplus : knsBSpline n u (x+u)=0 := by
    by_contra h
    have hlt := (hs h).2
    linarith
  have hminus : knsBSpline n u (x-u)=0 := by
    by_contra h
    have hlt := (hs h).1
    linarith
  rw [deriv_knsMomentLocalizer hn hu, hplus, hminus, sub_self]

/-- The actual translated localization of a complex-valued function. -/
def knsLocalizedFunction (n : ℕ) (u v : ℝ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  f x * (knsMomentLocalizer n u (x-v) : ℂ)

/-- An arbitrary C1 unknown times the actual order-at-least-two
localizer is genuinely C1. No global decay or Schwartz hypothesis is needed. -/
theorem contDiff_one_knsLocalizedFunction {n : ℕ} (hn : 2 ≤ n) {u : ℝ} (hu : 0 < u)
    (v : ℝ) {f : ℝ → ℂ} (hf : ContDiff ℝ 1 f) :
    ContDiff ℝ 1 (knsLocalizedFunction n u v f) := by
  have hF := contDiff_one_knsMomentLocalizer hn hu
  exact hf.mul (Complex.ofRealCLM.contDiff.comp (hF.comp (contDiff_id.sub contDiff_const)))

/-- Actual localization confines the support of every function to the
translated closed interval of radius 3u/2. -/
theorem support_knsLocalizedFunction_subset {n : ℕ} (hn : 1 ≤ n) (u v : ℝ) (f : ℝ → ℂ) :
    Function.support (knsLocalizedFunction n u v f) ⊆ Icc (v-3*u/2) (v+3*u/2) := by
  intro x hx
  have hF : knsMomentLocalizer n u (x-v) ≠ 0 := by
    intro h
    exact hx (by simp [knsLocalizedFunction, h])
  have hs := support_knsMomentLocalizer_subset hn u hF
  constructor <;> linarith [hs.1, hs.2]

/-- Compact support of the localized function is a conclusion even
when the unknown function is unbounded or nonintegrable. -/
theorem hasCompactSupport_knsLocalizedFunction {n : ℕ} (hn : 1 ≤ n) (u v : ℝ) (f : ℝ → ℂ) :
    HasCompactSupport (knsLocalizedFunction n u v f) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc (support_knsLocalizedFunction_subset hn u v f)

/-- A C1 unknown yields an actual localized H1 function: both the
function and its classical derivative belong to L2. -/
theorem memLp_knsLocalizedFunction_and_deriv {n : ℕ} (hn : 2 ≤ n) {u : ℝ} (hu : 0 < u)
    (v : ℝ) {f : ℝ → ℂ} (hf : ContDiff ℝ 1 f) :
    MemLp (knsLocalizedFunction n u v f) 2 ∧ MemLp (deriv (knsLocalizedFunction n u v f)) 2 := by
  have hc := contDiff_one_knsLocalizedFunction hn hu v hf
  have hs := hasCompactSupport_knsLocalizedFunction (by omega : 1 ≤ n) u v f
  exact ⟨hc.continuous.memLp_of_hasCompactSupport hs,
    (contDiff_one_iff_deriv.mp hc).2.memLp_of_hasCompactSupport hs.deriv⟩

/-- The same actual localized function and derivative are also L1,
so their ordinary Fourier integrals require no additional decay premise. -/
theorem integrable_knsLocalizedFunction_and_deriv {n : ℕ} (hn : 2 ≤ n) {u : ℝ} (hu : 0 < u)
    (v : ℝ) {f : ℝ → ℂ} (hf : ContDiff ℝ 1 f) :
    Integrable (knsLocalizedFunction n u v f) ∧ Integrable (deriv (knsLocalizedFunction n u v f)) := by
  have hc := contDiff_one_knsLocalizedFunction hn hu v hf
  have hs := hasCompactSupport_knsLocalizedFunction (by omega : 1 ≤ n) u v f
  exact ⟨hc.continuous.integrable_of_hasCompactSupport hs,
    (contDiff_one_iff_deriv.mp hc).2.integrable_of_hasCompactSupport hs.deriv⟩

/-- The localized classical derivative has the genuine Fourier multiplier
2 pi I eta in the negative-exponential convention. -/
theorem fourier_deriv_knsLocalizedFunction {n : ℕ} (hn : 2 ≤ n) {u : ℝ} (hu : 0 < u)
    (v : ℝ) {f : ℝ → ℂ} (hf : ContDiff ℝ 1 f) :
    𝓕 (deriv (knsLocalizedFunction n u v f)) =
      fun η : ℝ => (2 * (Real.pi : ℂ) * Complex.I * (η : ℂ)) *
        𝓕 (knsLocalizedFunction n u v f) η := by
  obtain ⟨hL1, hD1⟩ := integrable_knsLocalizedFunction_and_deriv hn hu v hf
  simpa only [smul_eq_mul] using Real.fourier_deriv hL1
    ((contDiff_one_knsLocalizedFunction hn hu v hf).differentiable (by norm_num)) hD1

/-- The actual localized derivative has the ordinary product rule and
the explicit difference-of-B-splines cutoff derivative. -/
theorem deriv_knsLocalizedFunction {n : ℕ} (hn : 2 ≤ n) {u : ℝ} (hu : 0 < u)
    (v : ℝ) {f : ℝ → ℂ} (hf : ContDiff ℝ 1 f) (x : ℝ) :
    deriv (knsLocalizedFunction n u v f) x =
      deriv f x * (knsMomentLocalizer n u (x-v) : ℂ) +
        f x * ((knsBSpline n u (x-v+u)-knsBSpline n u (x-v-u) : ℝ) : ℂ) := by
  have hFr := (hasDerivAt_convolution_knsBox (integrable_knsBSpline n u)
    (continuous_knsBSpline hn hu) hu.le (x-v)).comp x ((hasDerivAt_id x).sub_const v)
  have hF : HasDerivAt (fun t : ℝ => knsMomentLocalizer n u (t-v))
      (knsBSpline n u (x-v+u)-knsBSpline n u (x-v-u)) x := by
    convert! hFr using 1
    simp only [mul_one]
  have hFc := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt x hF
  have hfd := (hf.differentiable (by norm_num) x).hasDerivAt
  convert! (hfd.mul hFc).deriv using 1

/-- Original point zeros are preserved exactly by localization. -/
theorem knsLocalizedFunction_eq_zero_of_zero (n : ℕ) (u v : ℝ) {f : ℝ → ℂ}
    {x : ℝ} (hx : f x = 0) : knsLocalizedFunction n u v f x = 0 := by
  simp [knsLocalizedFunction, hx]

/-- The actual function is unchanged on the entire translated closed
plateau, with no regularity needed for this exact identity. -/
theorem knsLocalizedFunction_eq_on_plateau {n : ℕ} (hn : 1 ≤ n) {u : ℝ} (hu : 0 < u)
    (v : ℝ) (f : ℝ → ℂ) {x : ℝ} (hx : |x-v| ≤ u/2) :
    knsLocalizedFunction n u v f x = f x := by
  simp [knsLocalizedFunction, knsMomentLocalizer_eq_one hn hu hx]

/-- The localized function vanishes at both translated support endpoints
and beyond, with no regularity required of the unknown. -/
theorem knsLocalizedFunction_eq_zero_of_outer {n : ℕ} (hn : 1 ≤ n) {u : ℝ} (hu : 0 < u)
    (v : ℝ) (f : ℝ → ℂ) {x : ℝ} (hx : 3*u/2 ≤ |x-v|) :
    knsLocalizedFunction n u v f x = 0 := by
  have hF : knsMomentLocalizer n u (x-v) = 0 := by
    by_contra h
    have hlt := abs_lt.mpr (support_knsMomentLocalizer_subset_open hn hu.le h)
    linarith
  simp [knsLocalizedFunction, hF]

/-- At C1 orders the localized derivative also vanishes at both outer
endpoints and beyond. -/
theorem deriv_knsLocalizedFunction_eq_zero_of_outer {n : ℕ} (hn : 2 ≤ n) {u : ℝ} (hu : 0 < u)
    (v : ℝ) {f : ℝ → ℂ} (hf : ContDiff ℝ 1 f) {x : ℝ} (hx : 3*u/2 ≤ |x-v|) :
    deriv (knsLocalizedFunction n u v f) x = 0 := by
  have hs : Function.support (deriv (knsLocalizedFunction n u v f)) ⊆
      Icc (v-3*u/2) (v+3*u/2) :=
    support_deriv_subset.trans (closure_minimal (support_knsLocalizedFunction_subset (by omega) u v f) isClosed_Icc)
  have hc := (contDiff_one_iff_deriv.mp (contDiff_one_knsLocalizedFunction hn hu v hf)).2
  have ho := hc.isOpen_support.subset_interior_iff.mpr hs
  rw [interior_Icc] at ho
  by_contra h
  have hxs := ho h
  have hlt : |x-v| < 3*u/2 := abs_lt.mpr (by constructor <;> linarith [hxs.1, hxs.2])
  linarith

end

end MeyerGeneralProblem
