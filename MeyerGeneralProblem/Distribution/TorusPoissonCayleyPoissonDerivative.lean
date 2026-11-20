module

public import MeyerGeneralProblem.Distribution.TorusPoissonCayleyPoissonAverage
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import Mathlib.Analysis.Calculus.ParametricIntegral

@[expose] public section

/-!
# The Poisson derivative estimate for the Cayley leaf

Differentiation of the kernel and integration by parts transfer the
derivative to the real boundary path. The resulting norm is bounded by
the Poisson-smoothed positive phase mass.
-/

namespace MeyerGeneralProblem

noncomputable section

open Adaptive Filter MeasureTheory Metric ProbabilityTheory Set UnitAddTorus
open scoped ENNReal NNReal Topology

private def poissonCenterDerivative (y : ℝ≥0) (x t : ℝ) : ℝ :=
  2 * (t - x) / ((t - x) ^ 2 + (y : ℝ) ^ 2) * cauchyPDFReal x y t

private theorem hasDerivAt_poissonCenter {y : ℝ≥0} (hy : 0 < y) (x t : ℝ) :
    HasDerivAt (fun a => cauchyPDFReal a y t) (poissonCenterDerivative y x t) x := by
  have hy' : 0 < (y : ℝ) := hy
  have hDen : (t - x) ^ 2 + (y : ℝ) ^ 2 ≠ 0 := by positivity
  have h := ((((hasDerivAt_id x).const_sub t).pow 2).add_const ((y : ℝ) ^ 2)).inv hDen
  have he : Real.pi⁻¹ * (y : ℝ) *
      (-(2 * (t - x) ^ (2 - 1) * (-1)) / ((t - x) ^ 2 + (y : ℝ) ^ 2) ^ 2) =
        poissonCenterDerivative y x t := by
    rw [poissonCenterDerivative, cauchyPDFReal_def]
    norm_num
    field_simp
  simpa only [cauchyPDFReal_def, Pi.inv_apply, Pi.pow_apply, Nat.cast_ofNat, id_eq, he] using h.const_mul (Real.pi⁻¹ * (y : ℝ))

private theorem hasDerivAt_poissonTime {y : ℝ≥0} (hy : 0 < y) (x t : ℝ) :
    HasDerivAt (cauchyPDFReal x y) (-(poissonCenterDerivative y x t)) t := by
  have hInner : HasDerivAt (fun v : ℝ => t + x - v) (-1) t :=
    (hasDerivAt_id t).const_sub (t + x)
  have h := (hasDerivAt_poissonCenter hy x t).comp_of_eq t hInner (by ring)
  have he (v : ℝ) : cauchyPDFReal (t + x - v) y t = cauchyPDFReal x y v := by
    simp only [cauchyPDFReal_def, show t - (t + x - v) = v - x by ring]
  simpa only [Function.comp_def, he, mul_neg, mul_one] using h

private theorem abs_poissonCenterDerivative_le {y : ℝ≥0} (hy : 0 < y) (x t : ℝ) :
    |poissonCenterDerivative y x t| ≤ (y : ℝ)⁻¹ * cauchyPDFReal x y t := by
  have hy' : 0 < (y : ℝ) := hy
  have hd : 0 < (t - x) ^ 2 + (y : ℝ) ^ 2 := by positivity
  have h : 2 * |t - x| ≤ (y : ℝ)⁻¹ * ((t - x) ^ 2 + (y : ℝ) ^ 2) := by
    rw [← one_div, div_mul_eq_mul_div, one_mul, (le_div_iff₀ hy')]
    nlinarith only [sq_nonneg (|t - x| - (y : ℝ)), sq_abs (t - x)]
  have hp := (cauchyPDF_pos x hy.ne' t).le
  rw [poissonCenterDerivative, abs_mul, abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
    abs_of_pos hd, abs_of_nonneg hp]
  exact mul_le_mul_of_nonneg_right ((div_le_iff₀ hd).mpr h) hp

private theorem poisson_le_mul_of_dist_lt_one {y : ℝ≥0} (hy : 0 < y) {a x : ℝ}
    (ha : a ∈ ball x 1) (t : ℝ) :
    cauchyPDFReal a y t ≤ (2 + 2 / (y : ℝ) ^ 2) * cauchyPDFReal x y t := by
  have hy' : 0 < (y : ℝ) := hy
  let D (r : ℝ) := (t - r) ^ 2 + (y : ℝ) ^ 2
  have hd (r : ℝ) : 0 < D r := by unfold D; positivity
  have hda : |a - x| < 1 := by simpa only [mem_ball, Real.dist_eq] using ha
  have hs : (a - x) ^ 2 ≤ 1 := by
    simpa only [sq_abs, one_pow] using pow_le_pow_left₀ (abs_nonneg (a - x)) hda.le 2
  let C := 2 + 2 / (y : ℝ) ^ 2
  have hh : D x ≤ C * D a := by
    have hX : (t - x) ^ 2 ≤ 2 * (t - a) ^ 2 + 2 := by
      nlinarith only [hs, sq_nonneg ((t - a) - (a - x))]
    have he : (2 / (y : ℝ) ^ 2) * (y : ℝ) ^ 2 = 2 :=
      div_mul_cancel₀ _ (pow_ne_zero 2 hy'.ne')
    have hnon : 0 ≤ (2 / (y : ℝ) ^ 2) * (t - a) ^ 2 := by positivity
    dsimp only [D, C]
    rw [add_mul, mul_add (2 / (y : ℝ) ^ 2), he]
    nlinarith only [hX, hnon, sq_nonneg (y : ℝ)]
  have hInv : (D a)⁻¹ ≤ C * (D x)⁻¹ := by
    rw [← div_eq_mul_inv, ← one_div, div_le_div_iff₀ (hd a) (hd x), one_mul]
    exact hh
  change Real.pi⁻¹ * (y : ℝ) * (D a)⁻¹ ≤ C * (Real.pi⁻¹ * (y : ℝ) * (D x)⁻¹)
  rw [mul_left_comm C]
  exact mul_le_mul_of_nonneg_left hInv (by positivity)

private theorem hasDerivAt_integral_poisson_mul_of_bounded {y : ℝ≥0} (hy : 0 < y)
    {f : ℝ → ℂ} (hf : Measurable f) (hBound : ∀ t, ‖f t‖ ≤ 1) (x : ℝ) :
    HasDerivAt (fun a => ∫ t, (cauchyPDFReal a y t : ℂ) * f t)
      (∫ t, (poissonCenterDerivative y x t : ℂ) * f t) x := by
  let F (a t : ℝ) := (cauchyPDFReal a y t : ℂ) * f t
  let D (a t : ℝ) := (poissonCenterDerivative y a t : ℂ) * f t
  have hMeasF (a : ℝ) : Measurable (F a) :=
    (Complex.continuous_ofReal.measurable.comp (measurable_cauchyPDFReal a y)).mul hf
  have hMeasD (a : ℝ) : Measurable (D a) := by
    have hp : Measurable (poissonCenterDerivative y a) := by
      unfold poissonCenterDerivative
      exact (by fun_prop : Measurable fun t : ℝ => 2 * (t - a) / ((t - a) ^ 2 + (y : ℝ) ^ 2)).mul
        (measurable_cauchyPDFReal a y)
    exact (Complex.continuous_ofReal.measurable.comp hp).mul hf
  have hP : Integrable (cauchyPDFReal x y) := integrable_cauchyPDFReal x (γ := y)
  have hFInt : Integrable (F x) := hP.mono' (hMeasF x).aestronglyMeasurable (ae_of_all _ fun t => by
    rw [show F x t = _ from rfl, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (cauchyPDF_pos x hy.ne' t).le]
    exact mul_le_of_le_one_right (cauchyPDF_pos x hy.ne' t).le (hBound t))
  have hDNorm (a t : ℝ) : ‖D a t‖ ≤ (y : ℝ)⁻¹ * cauchyPDFReal a y t := by
    rw [show D a t = _ from rfl, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact (mul_le_of_le_one_right (abs_nonneg _) (hBound t)).trans
      (abs_poissonCenterDerivative_le hy a t)
  let C := (y : ℝ)⁻¹ * (2 + 2 / (y : ℝ) ^ 2)
  have hDom : ∀ᵐ t ∂volume, ∀ a ∈ ball x 1, ‖D a t‖ ≤ C * cauchyPDFReal x y t :=
    ae_of_all _ fun t a ha => (hDNorm a t).trans (by
      dsimp only [C]
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (poisson_le_mul_of_dist_lt_one hy ha t) (by positivity))
  have hDer : ∀ᵐ t ∂volume, ∀ a ∈ ball x 1, HasDerivAt (fun v => F v t) (D a t) a :=
    ae_of_all _ fun t a _ => ((hasDerivAt_poissonCenter hy a t).ofReal_comp).mul_const (f t)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (ball_mem_nhds x one_pos) (Eventually.of_forall fun a => (hMeasF a).aestronglyMeasurable)
    hFInt (hMeasD x).aestronglyMeasurable hDom (hP.const_mul C) hDer).2

/-- The Poisson average of a bounded measurable path is continuous
in its real center at every positive height. -/
theorem continuous_integral_poisson_mul_of_bounded {y : ℝ≥0} (hy : 0 < y)
    {f : ℝ → ℂ} (hf : Measurable f) (hBound : ∀ t, ‖f t‖ ≤ 1) :
    Continuous (fun a => ∫ t, (cauchyPDFReal a y t : ℂ) * f t) :=
  continuous_iff_continuousAt.mpr fun x =>
    (hasDerivAt_integral_poisson_mul_of_bounded hy hf hBound x).continuousAt

/-- A bounded differentiable path can be differentiated through its
Poisson integral by transferring the derivative to the path. -/
theorem hasDerivAt_integral_poisson_mul_eq_integral_mul_deriv {y : ℝ≥0} (hy : 0 < y)
    {f : ℝ → ℂ} (hf : ∀ t, DifferentiableAt ℝ f t) (hBound : ∀ t, ‖f t‖ ≤ 1) (x : ℝ)
    (hInt : Integrable (fun t => (cauchyPDFReal x y t : ℂ) * deriv f t)) :
    HasDerivAt (fun a => ∫ t, (cauchyPDFReal a y t : ℂ) * f t)
      (∫ t, (cauchyPDFReal x y t : ℂ) * deriv f t) x := by
  have hm : Measurable f := (continuous_iff_continuousAt.mpr fun t => (hf t).continuousAt).measurable
  let u (t : ℝ) := (cauchyPDFReal x y t : ℂ)
  let q (t : ℝ) := (poissonCenterDerivative y x t : ℂ)
  have hP : Integrable (cauchyPDFReal x y) := integrable_cauchyPDFReal x (γ := y)
  have hU : Measurable u :=
    Complex.continuous_ofReal.measurable.comp (measurable_cauchyPDFReal x y)
  have hQ : Measurable q := by
    apply Complex.continuous_ofReal.measurable.comp
    unfold poissonCenterDerivative
    exact (by fun_prop : Measurable fun t : ℝ => 2 * (t - x) / ((t - x) ^ 2 + (y : ℝ) ^ 2)).mul
      (measurable_cauchyPDFReal x y)
  have hUI : Integrable (u * f) := hP.mono' (hU.mul hm).aestronglyMeasurable (ae_of_all _ fun t => by
    change ‖(cauchyPDFReal x y t : ℂ) * f t‖ ≤ _
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (cauchyPDF_pos x hy.ne' t).le]
    exact mul_le_of_le_one_right (cauchyPDF_pos x hy.ne' t).le (hBound t))
  have hQI : Integrable (q * f) :=
    (hP.const_mul (y : ℝ)⁻¹).mono' (hQ.mul hm).aestronglyMeasurable (ae_of_all _ fun t => by
      change ‖(poissonCenterDerivative y x t : ℂ) * f t‖ ≤ _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact (mul_le_of_le_one_right (abs_nonneg _) (hBound t)).trans
        (abs_poissonCenterDerivative_le hy x t))
  have hByParts := integral_mul_deriv_eq_deriv_mul_of_integrable (u := u) (v := f)
    (u' := -q) (v' := deriv f)
    (fun t _ => by simpa only [Pi.neg_apply, Complex.ofReal_neg] using (hasDerivAt_poissonTime hy x t).ofReal_comp)
    (fun t _ => (hf t).hasDerivAt) hInt (by simpa only [neg_mul] using hQI.neg) hUI
  simp only [Pi.neg_apply, neg_mul, integral_neg, neg_neg] at hByParts
  have h := hasDerivAt_integral_poisson_mul_of_bounded hy hm hBound x
  rw [hByParts]
  exact h

/-- Use normalized Haar measure on each circle factor. -/
local instance cayleyPoissonPhaseCircleMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

local instance cayleyPoissonPhaseCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

section PhasePoissonMean

variable {d : Type*} [Fintype d]
variable (β : d → ℝ) (S : UnitAddTorus d → LocallyFiniteCarrier)
variable (T : UnitAddTorus d → TemperedDistribution ℝ ℂ)
variable (hT : ∀ θ, DistributionSupportedOn (S θ).carrier (T θ))
variable (hCont : ∀ f : SchwartzMap ℝ ℂ, HasCompactSupport (f : ℝ → ℂ) →
  Continuous (fun θ => T θ f))
variable {K : ℕ} (hCount : ∀ θ r, ((S θ).carrier ∩ Ico r (r + 1)).ncard ≤ K)
variable (hAdvance : ∀ t θ, T (unitAddTorusFlow β t θ) = combDistributionTranslation (-t) (T θ))

include hAdvance in
/-- The Poisson-weighted phase density is integrable on the joint space,
and its total integral is the Haar mean of the boundary phase density. -/
theorem integrable_prod_and_integral_poisson_phaseDensity (x : ℝ) (y : ℝ≥0) (hy : 0 < y) :
    let W (p : UnitAddTorus d × ℝ) :=
      cauchyPDFReal x y p.2 * torusPoissonCayleyPhaseDensity β S T hT hCont hCount p.1 p.2
    let μ := (volume : Measure (UnitAddTorus d)).prod (volume : Measure ℝ)
    Integrable W μ ∧
      (∫ p, W p ∂μ) = (torusPoissonCayleyMeanPhaseDensity β S T hT hCont hCount).toReal := by
  let μ := (volume : Measure (UnitAddTorus d))
  let ν := (volume : Measure ℝ)
  let g := torusPoissonCayleyPhaseDensity β S T hT hCont hCount
  let W (p : UnitAddTorus d × ℝ) := cauchyPDFReal x y p.2 * g p.1 p.2
  let M := torusPoissonCayleyMeanPhaseDensity β S T hT hCont hCount
  change Integrable W (μ.prod ν) ∧ (∫ p, W p ∂μ.prod ν) = M.toReal
  have hg (θ : UnitAddTorus d) (t : ℝ) : 0 ≤ g θ t :=
    div_nonneg (norm_nonneg _) Real.two_pi_pos.le
  have hW0 (p : UnitAddTorus d × ℝ) : 0 ≤ W p :=
    mul_nonneg (cauchyPDF_pos x hy.ne' p.2).le (hg p.1 p.2)
  have hM : M < ∞ :=
    (torusPoissonCayleyMeanPhaseDensity_le_unitCap β S T hT hCont hCount hAdvance).trans_lt
      (ENNReal.add_lt_top.mpr ⟨ENNReal.natCast_lt_top K, ENNReal.one_lt_top⟩)
  have hG := aemeasurable_torusPoissonCayleyPhaseDensity β S T hT hCont hCount hAdvance
  have hMeasW : AEMeasurable W (μ.prod ν) :=
    ((measurable_cauchyPDFReal x y).comp measurable_snd).aemeasurable.mul hG.2
  have hEq : (∫⁻ p, ENNReal.ofReal (W p) ∂μ.prod ν) = M := by
    change (∫⁻ p, (ENNReal.ofReal ∘ W) p ∂μ.prod ν) = M
    rw [lintegral_prod_symm _ (ENNReal.measurable_ofReal.comp_aemeasurable hMeasW)]
    have hi (t : ℝ) : (∫⁻ θ, ENNReal.ofReal (W (θ, t)) ∂μ) = cauchyPDF x y t * M := by
      simp only [W, ENNReal.ofReal_mul (cauchyPDF_pos x hy.ne' t).le, ← cauchyPDF_def]
      have hmeas : AEMeasurable (fun θ => ENNReal.ofReal (g θ t)) μ :=
        ENNReal.measurable_ofReal.comp_aemeasurable (hG.1 t)
      rw [lintegral_const_mul'' _ hmeas]
      exact congrArg (cauchyPDF x y t * ·)
        (lintegral_torusPoissonCayleyPhaseDensity_eq_mean β S T hT hCont hCount hAdvance t)
    change (∫⁻ t, ∫⁻ θ, ENNReal.ofReal (W (θ, t)) ∂μ ∂ν) = M
    rw [lintegral_congr hi]
    rw [lintegral_mul_const _ (measurable_cauchyPDF x y), lintegral_cauchyPDF_eq_one x hy.ne', one_mul]
  refine ⟨⟨hMeasW.aestronglyMeasurable, ?_⟩, ?_⟩
  · rw [hasFiniteIntegral_iff_norm]
    have hEnorm (p : UnitAddTorus d × ℝ) : ‖W p‖ = W p := Real.norm_of_nonneg (hW0 p)
    simp only [hEnorm, hEq, hM]
  · rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hW0) hMeasW.aestronglyMeasurable, hEq]

end PhasePoissonMean

section CayleyPoissonDerivative

variable {d : Type*} [Fintype d]
variable (β : d → ℝ) (S : UnitAddTorus d → LocallyFiniteCarrier)
variable (T : UnitAddTorus d → TemperedDistribution ℝ ℂ)
variable (hT : ∀ θ, DistributionSupportedOn (S θ).carrier (T θ))
variable (hCont : ∀ f : SchwartzMap ℝ ℂ, HasCompactSupport (f : ℝ → ℂ) →
  Continuous (fun θ => T θ f))
variable {K : ℕ} (hCount : ∀ θ r, ((S θ).carrier ∩ Ico r (r + 1)).ncard ≤ K)
variable (hAdvance : ∀ t θ, T (unitAddTorusFlow β t θ) = combDistributionTranslation (-t) (T θ))

include hAdvance in
/-- On a common full-measure set of phases for each positive height,
the Poisson representation holds at every real center. -/
theorem ae_forall_real_poisson_integral_torusPoissonCayleyExtendedLeaf (y : ℝ≥0) (hy : 0 < y) :
    ∀ᵐ θ : UnitAddTorus d ∂volume, ∀ x : ℝ,
      (∫ t : ℝ, (cauchyPDFReal x y t : ℂ) *
        torusPoissonCayleyExtendedLeaf β S T hT hCont hCount θ (t : ℂ)) =
      torusPoissonCayleyExtendedLeaf β S T hT hCont hCount θ
        ((x : ℂ) + ((y : ℝ) : ℂ) * Complex.I) := by
  let F := torusPoissonCayleyExtendedLeaf β S T hT hCont hCount
  let z : ℂ := ((y : ℝ) : ℂ) * Complex.I
  have hz (x : ℝ) : 0 < ((x : ℂ) + z).im := by simpa [z, Complex.mul_im] using hy
  have hRat : ∀ᵐ θ : UnitAddTorus d ∂volume, ∀ r : ℚ,
      (∫ t : ℝ, (cauchyPDFReal (r : ℝ) y t : ℂ) * F θ (t : ℂ)) = F θ (((r : ℝ) : ℂ) + z) := by
    apply ae_all_iff.mpr
    intro r
    exact ae_poisson_integral_torusPoissonCayleyExtendedLeaf β S T hT hCont hCount hAdvance (r : ℝ) y hy
  filter_upwards [hRat,
    ae_analyticAt_norm_torusPoissonCayleyExtendedLeaf β S T hT hCont hCount hAdvance,
    ae_analyticOnNhd_norm_torusPoissonCayleyField β S T hT hCont hCount hAdvance]
    with θ hRatθ hReal hUpper
  let f (t : ℝ) := F θ (t : ℂ)
  have hContF : Continuous f :=
    continuous_iff_continuousAt.mpr fun t =>
      (hReal t).1.continuousAt.comp Complex.continuous_ofReal.continuousAt
  have hP : Continuous (fun x => ∫ t : ℝ, (cauchyPDFReal x y t : ℂ) * f t) :=
    continuous_integral_poisson_mul_of_bounded hy hContF.measurable (fun t => (hReal t).2.le)
  have hContRight : Continuous (fun x : ℝ => F θ ((x : ℂ) + z)) := by
    have hU : IsOpen {w : ℂ | 0 < w.im} := isOpen_lt continuous_const Complex.continuous_im
    have hC : ContinuousOn (fun w => torusPoissonCayleyField β S T hT hCont hCount w θ)
        {w : ℂ | 0 < w.im} := hUpper.1.differentiableOn.continuousOn
    have hLine : Continuous (fun x : ℝ => (x : ℂ) + z) :=
      Complex.continuous_ofReal.add continuous_const
    have hE : (fun x : ℝ => F θ ((x : ℂ) + z)) =
        (fun w => torusPoissonCayleyField β S T hT hCont hCount w θ) ∘ (fun x : ℝ => (x : ℂ) + z) :=
      funext fun x => torusPoissonCayleyExtendedLeaf_eq_field β S T hT hCont hCount θ (hz x)
    rw [hE]
    exact hC.comp_continuous hLine hz
  have hClosed : IsClosed {x : ℝ | (∫ t : ℝ, (cauchyPDFReal x y t : ℂ) * f t) =
      F θ ((x : ℂ) + z)} := isClosed_eq hP hContRight
  have hSub : range ((↑) : ℚ → ℝ) ⊆ {x : ℝ |
      (∫ t : ℝ, (cauchyPDFReal x y t : ℂ) * f t) = F θ ((x : ℂ) + z)} := by
    rintro _ ⟨r, rfl⟩
    exact hRatθ r
  intro x
  exact closure_minimal hSub hClosed (Rat.isDenseEmbedding_coe_real.dense x)

include hAdvance in
/-- The derivative in the upper half-plane is dominated by the
Poisson-smoothed positive phase mass of the actual real boundary. -/
theorem ae_norm_deriv_torusPoissonCayleyExtendedLeaf_le (x : ℝ) (y : ℝ≥0) (hy : 0 < y) :
    ∀ᵐ θ : UnitAddTorus d ∂volume,
      ‖deriv (torusPoissonCayleyExtendedLeaf β S T hT hCont hCount θ)
          ((x : ℂ) + ((y : ℝ) : ℂ) * Complex.I)‖ ≤
      (2 * Real.pi) * ∫ t, cauchyPDFReal x y t *
        torusPoissonCayleyPhaseDensity β S T hT hCont hCount θ t := by
  let F := torusPoissonCayleyExtendedLeaf β S T hT hCont hCount
  let G := torusPoissonCayleyPhaseDensity β S T hT hCont hCount
  let z : ℂ := ((y : ℝ) : ℂ) * Complex.I
  have hMass := (integrable_prod_and_integral_poisson_phaseDensity
    β S T hT hCont hCount hAdvance x y hy).1
  filter_upwards [hMass.prod_right_ae,
    ae_forall_real_poisson_integral_torusPoissonCayleyExtendedLeaf β S T hT hCont hCount hAdvance y hy,
    ae_analyticAt_norm_torusPoissonCayleyExtendedLeaf β S T hT hCont hCount hAdvance,
    ae_analyticOnNhd_norm_torusPoissonCayleyField β S T hT hCont hCount hAdvance]
    with θ hInt hEq hReal hUpper
  let f (t : ℝ) := F θ (t : ℂ)
  have hf (t : ℝ) : DifferentiableAt ℝ f t :=
    (hReal t).1.differentiableAt.hasDerivAt.comp_ofReal.differentiableAt
  have hP : Measurable (fun t => (cauchyPDFReal x y t : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp (measurable_cauchyPDFReal x y)
  have hNorm (t : ℝ) : ‖(cauchyPDFReal x y t : ℂ) * deriv f t‖ =
      (2 * Real.pi) * (cauchyPDFReal x y t * G θ t) := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (cauchyPDF_pos x hy.ne' t).le]
    change cauchyPDFReal x y t * ‖deriv f t‖ =
      (2 * Real.pi) * (cauchyPDFReal x y t * (‖deriv f t‖ / (2 * Real.pi)))
    field_simp [Real.two_pi_pos.ne']
  have hIntD : Integrable (fun t => (cauchyPDFReal x y t : ℂ) * deriv f t) := by
    refine (hInt.const_mul (2 * Real.pi)).mono' (hP.mul (measurable_deriv f)).aestronglyMeasurable ?_
    exact ae_of_all _ fun t => (hNorm t).le
  have hDer := hasDerivAt_integral_poisson_mul_eq_integral_mul_deriv hy hf
    (fun t => (hReal t).2.le) x hIntD
  have hEvent : (fun a : ℝ => F θ ((a : ℂ) + z)) =ᶠ[𝓝 x]
      (fun a => ∫ t, (cauchyPDFReal a y t : ℂ) * f t) :=
    Eventually.of_forall fun a => (hEq a).symm
  have hDer' : HasDerivAt (fun a : ℝ => F θ ((a : ℂ) + z))
      (∫ t, (cauchyPDFReal x y t : ℂ) * deriv f t) x :=
    hDer.congr_of_eventuallyEq hEvent
  have hz : 0 < ((x : ℂ) + z).im := by simpa [z, Complex.mul_im] using hy
  have hOpen : IsOpen {w : ℂ | 0 < w.im} := isOpen_lt continuous_const Complex.continuous_im
  have hAnalytic : AnalyticAt ℂ (F θ) ((x : ℂ) + z) := by
    refine (hUpper.1 _ hz).congr ?_
    filter_upwards [hOpen.mem_nhds hz] with w hw
    exact (torusPoissonCayleyExtendedLeaf_eq_field β S T hT hCont hCount θ hw).symm
  have hLine : HasDerivAt (fun a : ℂ => a + z) 1 (x : ℂ) :=
    (hasDerivAt_id' (x : ℂ)).add_const z
  have hDerF : HasDerivAt (fun a : ℂ => F θ (a + z)) (deriv (F θ) ((x : ℂ) + z)) (x : ℂ) := by
    simpa only [Function.comp_def, mul_one] using hAnalytic.differentiableAt.hasDerivAt.comp (x : ℂ) hLine
  change ‖deriv (F θ) ((x : ℂ) + z)‖ ≤ (2 * Real.pi) * ∫ t, cauchyPDFReal x y t * G θ t
  rw [hDerF.comp_ofReal.unique hDer']
  calc
    _ ≤ ∫ t, ‖(cauchyPDFReal x y t : ℂ) * deriv f t‖ :=
      norm_integral_le_integral_norm _
    _ = _ := by simp_rw [hNorm, integral_const_mul]

end CayleyPoissonDerivative

end
end MeyerGeneralProblem
