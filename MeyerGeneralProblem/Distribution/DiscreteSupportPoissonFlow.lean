module

public import MeyerGeneralProblem.Distribution.DiscreteSupportPoisson
public import MeyerGeneralProblem.Distribution.RealPoissonSemigroup

@[expose] public section

/-!
# The Poisson semigroup on support detectors

Tonelli's theorem applies to the positive Poisson kernels and the
locally finite counting measure. Translation covariance then gives
the height addition law along the phase flow.
-/

namespace MeyerGeneralProblem

noncomputable section

open Adaptive MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

private theorem measurable_joint_cauchyPDF (y : ℝ≥0) :
    Measurable (fun p : ℝ × ℝ => cauchyPDF p.1 y p.2) := by
  simp only [cauchyPDF_def, cauchyPDFReal_def]
  fun_prop

/-- Iterated positive Poisson smoothing of a single actual support
count is the Poisson integral at the sum of the two heights. -/
theorem lintegral_poisson_discreteSupportCount_add (S : LocallyFiniteCarrier)
    (T : TemperedDistribution ℝ ℂ) (hT : DistributionSupportedOn S.carrier T)
    {s y : ℝ≥0} (hs : 0 < s) (hy : 0 < y) :
    (∫⁻ t : ℝ, cauchyPDF 0 s t *
        (∫⁻ x, cauchyPDF t y x ∂discreteSupportCount T)) =
      ∫⁻ x, cauchyPDF 0 (s + y) x ∂discreteSupportCount T := by
  let μ := discreteSupportCount T
  let _ : IsLocallyFiniteMeasure μ := isLocallyFiniteMeasure_discreteSupportCount S T hT
  have hJoint : Measurable (fun p : ℝ × ℝ => cauchyPDF 0 s p.1 * cauchyPDF p.1 y p.2) :=
    ((measurable_cauchyPDF 0 s).comp measurable_fst).mul (measurable_joint_cauchyPDF y)
  calc
    _ = ∫⁻ t : ℝ, ∫⁻ x, cauchyPDF 0 s t * cauchyPDF t y x ∂μ :=
      lintegral_congr fun t => (lintegral_const_mul _ (measurable_cauchyPDF t y)).symm
    _ = ∫⁻ x, (∫⁻ t : ℝ, cauchyPDF 0 s t * cauchyPDF t y x) ∂μ :=
      lintegral_lintegral_swap (μ := volume) (ν := μ)
        (f := fun t x => cauchyPDF 0 s t * cauchyPDF t y x) hJoint.aemeasurable
    _ = _ := lintegral_congr (lintegral_cauchyPDF_mul_cauchyPDF hs hy)

/-- The semigroup identity also holds for the real Poisson fields
when the node counts have a uniform unit-window bound. -/
theorem integral_poisson_discreteSupportCount_add (S : LocallyFiniteCarrier)
    (T : TemperedDistribution ℝ ℂ) (hT : DistributionSupportedOn S.carrier T)
    {K : ℕ} (hCount : ∀ t : ℝ, (S.carrier ∩ Ico t (t + 1)).ncard ≤ K)
    {s y : ℝ≥0} (hs : 0 < s) (hy : 0 < y) :
    (∫ t : ℝ, cauchyPDFReal 0 s t *
        (∫ x, cauchyPDFReal t y x ∂discreteSupportCount T)) =
      ∫ x, cauchyPDFReal 0 (s + y) x ∂discreteSupportCount T := by
  let μ := discreteSupportCount T
  let _ : IsLocallyFiniteMeasure μ := isLocallyFiniteMeasure_discreteSupportCount S T hT
  let G (t : ℝ) := ∫⁻ x, cauchyPDF t y x ∂μ
  let F (t : ℝ) := cauchyPDFReal 0 s t * (G t).toReal
  have hG : Measurable G :=
    (measurable_joint_cauchyPDF y).lintegral_prod_right'
  have hF : Measurable F := (measurable_cauchyPDFReal 0 s).mul hG.ennreal_toReal
  have hFpos : ∀ t, 0 ≤ F t :=
    fun t => mul_nonneg (cauchyPDF_pos 0 hs.ne' t).le ENNReal.toReal_nonneg
  obtain ⟨C, hC, hBound⟩ := exists_lintegral_poisson_bound_of_discreteSupportCount K hy
  have hEnn (t : ℝ) : ENNReal.ofReal (F t) = cauchyPDF 0 s t * G t := by
    unfold F
    rw [ENNReal.ofReal_mul (cauchyPDF_pos 0 hs.ne' t).le,
      ENNReal.ofReal_toReal ((hBound S T hT hCount t).trans_lt hC).ne, ← cauchyPDF_def]
  calc
    _ = ∫ t, F t := by
      apply integral_congr_ae
      filter_upwards with t
      rw [integral_poisson_discreteSupportCount_eq _ _ hy]
    _ = (∫⁻ t : ℝ, cauchyPDF 0 s t * G t).toReal := by
      rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hFpos) hF.aestronglyMeasurable]
      simp_rw [hEnn]
    _ = _ := by
      rw [integral_poisson_discreteSupportCount_eq _ _ (add_pos hs hy)]
      exact congrArg ENNReal.toReal (lintegral_poisson_discreteSupportCount_add S T hT hs hy)

/-- Height addition along a covariant original phase family. The
parameter advance acts by physical translation through the negative
of the flow time, as in the one-record hull convention. -/
theorem integral_poisson_discreteSupportCount_along_flow {Θ : Type*}
    (S : Θ → LocallyFiniteCarrier) (T : Θ → TemperedDistribution ℝ ℂ)
    (advance : ℝ → Θ → Θ)
    (hT : ∀ θ, DistributionSupportedOn (S θ).carrier (T θ))
    (hAdvance : ∀ t θ, T (advance t θ) = combDistributionTranslation (-t) (T θ))
    {K : ℕ} (hCount : ∀ θ r, ((S θ).carrier ∩ Ico r (r + 1)).ncard ≤ K)
    {s y : ℝ≥0} (hs : 0 < s) (hy : 0 < y) (θ : Θ) :
    (∫ t : ℝ, cauchyPDFReal 0 s t *
        (∫ x, cauchyPDFReal 0 y x ∂discreteSupportCount (T (advance t θ)))) =
      ∫ x, cauchyPDFReal 0 (s + y) x ∂discreteSupportCount (T θ) := by
  have hShift (t : ℝ) :
      (∫ x, cauchyPDFReal 0 y x ∂discreteSupportCount (T (advance t θ))) =
        ∫ x, cauchyPDFReal t y x ∂discreteSupportCount (T θ) := by
    rw [hAdvance, integral_poisson_discreteSupportCount_translation _ _ _ hy, sub_neg_eq_add,
      zero_add]
  simp_rw [hShift]
  exact integral_poisson_discreteSupportCount_add (S θ) (T θ) (hT θ) (hCount θ) hs hy

end
end MeyerGeneralProblem
