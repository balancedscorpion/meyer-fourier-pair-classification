module

public import MeyerGeneralProblem.Distribution.DiscreteSupportPoissonFlow

@[expose] public section

/-!
# Poisson smoothing of Fourier coefficients along a flow

Integrating a mode against an invariant finite measure reduces
Poisson smoothing along the flow to the scalar multiplier at that
mode's real frequency. The support-count semigroup then propagates
the original Poisson field's coefficients between any two heights.
-/

namespace MeyerGeneralProblem

noncomputable section

open Adaptive MeasureTheory ProbabilityTheory Set
open scoped ComplexConjugate ENNReal FourierTransform NNReal

private theorem integral_cauchyPDFReal_mul_character {s : ℝ≥0} (hs : 0 < s) (b : ℝ) :
    (∫ t : ℝ, (cauchyPDFReal 0 s t : ℂ) * combModulationCharacter b t) =
      (Real.exp (-(2 * Real.pi * (s : ℝ)) * |b|) : ℂ) := by
  have h := fourier_cauchyPDFReal_ofReal hs (-b)
  rw [Real.fourier_real_eq_integral_exp_smul, abs_neg] at h
  rw [← h]
  apply integral_congr_ae
  filter_upwards with t
  rw [combModulationCharacter_eq_exp, smul_eq_mul, mul_comm]
  congr 2
  push_cast
  ring

/-- Averaging a bounded measurable function along a measure-preserving
flow with the Poisson kernel multiplies each unit mode by exponential damping. -/
theorem integral_poisson_average_mul_conj {Θ : Type*} [MeasurableSpace Θ]
    (ν : Measure Θ) [IsFiniteMeasure ν] (advance : ℝ → Θ → Θ)
    (hJoint : Measurable (Function.uncurry advance))
    (hInvariant : ∀ t, MeasurePreserving (advance t) ν ν)
    (F χ : Θ → ℂ) (hF : Measurable F) (hχ : Measurable χ)
    {C : ℝ} (hBound : ∀ θ, ‖F θ‖ ≤ C) (hNorm : ∀ θ, ‖χ θ‖ = 1)
    (b : ℝ) (hMode : ∀ t θ, χ (advance t θ) = combModulationCharacter b t * χ θ)
    {s : ℝ≥0} (hs : 0 < s) :
    (∫ θ, (∫ t : ℝ, (cauchyPDFReal 0 s t : ℂ) * F (advance t θ)) * conj (χ θ) ∂ν) =
      (Real.exp (-(2 * Real.pi * (s : ℝ)) * |b|) : ℂ) *
        ∫ θ, F θ * conj (χ θ) ∂ν := by
  let P (t : ℝ) := (cauchyPDFReal 0 s t : ℂ)
  let E (t : ℝ) := combModulationCharacter b t
  let G (θ : Θ) := F θ * conj (χ θ)
  let H (p : Θ × ℝ) := P p.2 * F (advance p.2 p.1) * conj (χ p.1)
  have hConj : Measurable (fun θ => conj (χ θ)) :=
    Complex.continuous_conj.measurable.comp hχ
  have hG : Measurable G := hF.mul hConj
  have hP : Measurable P := Complex.continuous_ofReal.measurable.comp (measurable_cauchyPDFReal 0 s)
  have hH : Measurable H :=
    ((hP.comp measurable_snd).mul (hF.comp (hJoint.comp measurable_swap))).mul
      (hConj.comp measurable_fst)
  have hDom : Integrable (fun p : Θ × ℝ => C * cauchyPDFReal 0 s p.2)
      (ν.prod volume) := by
    exact (integrable_const (μ := ν) C).mul_prod (integrable_cauchyPDFReal 0 (γ := s))
  have hInt : Integrable H (ν.prod volume) := by
    refine hDom.mono' hH.aestronglyMeasurable ?_
    filter_upwards with p
    simp only [H, P, norm_mul, Complex.norm_real, Real.norm_of_nonneg (cauchyPDF_pos 0 hs.ne' _).le,
      Complex.norm_conj, hNorm, mul_one]
    rw [mul_comm C]
    exact mul_le_mul_of_nonneg_left (hBound _) (cauchyPDF_pos 0 hs.ne' _).le
  have hInner (t : ℝ) : (∫ θ, H (θ, t) ∂ν) = (P t * E t) * ∫ θ, G θ ∂ν := by
    have hUnit : E t * conj (E t) = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, show ‖E t‖ = 1 from
        norm_combModulationCharacter b t, one_pow, Complex.ofReal_one]
    have hMode' (θ : Θ) : E t * conj (χ (advance t θ)) = conj (χ θ) := by
      rw [hMode, map_mul, ← mul_assoc, hUnit, one_mul]
    have hPres : (∫ θ, G (advance t θ) ∂ν) = ∫ θ, G θ ∂ν := by
      calc
        _ = ∫ θ, G θ ∂Measure.map (advance t) ν :=
          (integral_map (hInvariant t).measurable.aemeasurable hG.aestronglyMeasurable).symm
        _ = _ := by rw [(hInvariant t).map_eq]
    calc
      _ = ∫ θ, (P t * E t) * G (advance t θ) ∂ν := by
        apply integral_congr_ae
        filter_upwards with θ
        dsimp only [H, G]
        rw [← hMode' θ]
        ring
      _ = _ := by rw [integral_const_mul, hPres]
  calc
    _ = ∫ θ, (∫ t : ℝ, H (θ, t)) ∂ν := by
      apply integral_congr_ae
      filter_upwards with θ
      exact (integral_mul_const (conj (χ θ)) (fun t => P t * F (advance t θ))).symm
    _ = ∫ t : ℝ, ∫ θ, H (θ, t) ∂ν := integral_integral_swap hInt
    _ = ∫ t : ℝ, (P t * E t) * ∫ θ, G θ ∂ν := by
      exact integral_congr_ae (ae_of_all _ hInner)
    _ = _ := by
      rw [integral_mul_const, show (∫ t : ℝ, P t * E t) = _ from integral_cauchyPDFReal_mul_character hs b]

/-- Every unit character of an invariant phase flow rescales the corresponding
original support-detector coefficient by the Poisson multiplier. -/
theorem integral_poisson_discreteSupportCount_mul_conj_mode {Θ : Type*}
    [TopologicalSpace Θ] [MeasurableSpace Θ] [OpensMeasurableSpace Θ]
    (ν : Measure Θ) [IsFiniteMeasure ν]
    (S : Θ → LocallyFiniteCarrier) (T : Θ → TemperedDistribution ℝ ℂ)
    (advance : ℝ → Θ → Θ)
    (hJoint : Measurable (Function.uncurry advance))
    (hInvariant : ∀ t, MeasurePreserving (advance t) ν ν)
    (hT : ∀ θ, DistributionSupportedOn (S θ).carrier (T θ))
    (hAdvance : ∀ t θ, T (advance t θ) = combDistributionTranslation (-t) (T θ))
    (hCont : ∀ f : SchwartzMap ℝ ℂ, HasCompactSupport (f : ℝ → ℂ) →
      Continuous (fun θ => T θ f))
    {K : ℕ} (hCount : ∀ θ r, ((S θ).carrier ∩ Ico r (r + 1)).ncard ≤ K)
    (χ : Θ → ℂ) (hχ : Measurable χ) (hNorm : ∀ θ, ‖χ θ‖ = 1)
    (b : ℝ) (hMode : ∀ t θ, χ (advance t θ) = combModulationCharacter b t * χ θ)
    {s y : ℝ≥0} (hs : 0 < s) (hy : 0 < y) :
    (∫ θ, Complex.ofReal (∫ x, cauchyPDFReal 0 (s + y) x ∂discreteSupportCount (T θ)) *
        conj (χ θ) ∂ν) =
      (Real.exp (-(2 * Real.pi * (s : ℝ)) * |b|) : ℂ) *
        ∫ θ, Complex.ofReal (∫ x, cauchyPDFReal 0 y x ∂discreteSupportCount (T θ)) * conj (χ θ) ∂ν := by
  let F (θ : Θ) := Complex.ofReal (∫ x, cauchyPDFReal 0 y x ∂discreteSupportCount (T θ))
  have hF : Measurable F := by
    simp only [F, integral_poisson_discreteSupportCount_eq _ _ hy]
    change Measurable (Complex.ofReal ∘ fun θ =>
      (∫⁻ x, cauchyPDF 0 y x ∂discreteSupportCount (T θ)).toReal)
    exact Complex.continuous_ofReal.measurable.comp
      (measurable_lintegral_poisson_discreteSupportCount S T hT hCont 0 y).ennreal_toReal
  obtain ⟨C, hC, hBound⟩ := exists_lintegral_poisson_bound_of_discreteSupportCount K hy
  have hFB (θ : Θ) : ‖F θ‖ ≤ C.toReal := by
    change ‖Complex.ofReal (∫ x, cauchyPDFReal 0 y x ∂discreteSupportCount (T θ))‖ ≤ C.toReal
    rw [integral_poisson_discreteSupportCount_eq _ _ hy, Complex.norm_real,
      Real.norm_of_nonneg ENNReal.toReal_nonneg]
    exact ENNReal.toReal_mono hC.ne (hBound (S θ) (T θ) (hT θ) (hCount θ) 0)
  have h := integral_poisson_average_mul_conj ν advance hJoint hInvariant
    F χ hF hχ hFB hNorm b hMode hs
  have hFlow (θ : Θ) :
      (∫ t : ℝ, (cauchyPDFReal 0 s t : ℂ) * F (advance t θ)) =
        Complex.ofReal (∫ x, cauchyPDFReal 0 (s + y) x ∂discreteSupportCount (T θ)) := by
    simp only [F, ← Complex.ofReal_mul, integral_complex_ofReal]
    congr 1
    exact integral_poisson_discreteSupportCount_along_flow S T advance hT hAdvance hCount hs hy θ
  simpa only [hFlow, F] using h

end
end MeyerGeneralProblem
