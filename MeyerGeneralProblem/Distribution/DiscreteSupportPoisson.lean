module

public import MeyerGeneralProblem.Distribution.DiscreteSupportCountTranslation
public import Mathlib.Analysis.PSeries
public import Mathlib.Probability.Distributions.Cauchy

@[expose] public section

/-!
# Poisson smoothing of the actual support count

At positive height a common unit-window count bounds the Poisson
integrals uniformly in the original distribution and observation point.
-/

namespace MeyerGeneralProblem

noncomputable section

open Adaptive Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology

private theorem summable_inverse_unitCell_weight :
    Summable (fun n : ℤ => (1 + (n : ℝ) ^ 2)⁻¹) := by
  have h : Summable (fun n : ℤ => 1 / (n : ℝ) ^ 2) :=
    Real.summable_one_div_int_pow.mpr (by norm_num)
  apply h.of_norm_bounded_eventually
  filter_upwards [eventually_cofinite_ne (0 : ℤ)] with n hn
  have hn₀ : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  rw [Real.norm_of_nonneg (by positivity), ← one_div]
  exact one_div_le_one_div_of_le (sq_pos_of_ne_zero hn₀) (by linarith)

private theorem cauchyPDFReal_le_on_unitCell (x : ℝ) {γ : ℝ≥0} (hγ : 0 < γ)
    (n : ℤ) {t : ℝ} (ht : t ∈ Ico (x + n) (x + n + 1)) :
    cauchyPDFReal x γ t ≤
      (3 * (Real.pi⁻¹ * (γ : ℝ)) / min 1 ((γ : ℝ) ^ 2)) * (1 + (n : ℝ) ^ 2)⁻¹ := by
  let d := min (1 : ℝ) ((γ : ℝ) ^ 2)
  have hγ' : 0 < (γ : ℝ) := hγ
  have hd : 0 < d := lt_min one_pos (sq_pos_of_pos hγ')
  have hd₁ : d ≤ 1 := min_le_left _ _
  have hd₂ : d ≤ (γ : ℝ) ^ 2 := min_le_right _ _
  have ht₀ : (n : ℝ) ≤ t - x := by linarith only [ht.1]
  have ht₁ : t - x ≤ (n : ℝ) + 1 := by linarith only [ht.2]
  have hAbs : |(n : ℝ)| ≤ |t - x| + 1 := by
    refine abs_le.mpr ⟨?_, ?_⟩
    · linarith only [ht₁, neg_abs_le (t - x)]
    · linarith only [ht₀, le_abs_self (t - x)]
  have hSquare := pow_le_pow_left₀ (abs_nonneg (n : ℝ)) hAbs 2
  rw [sq_abs] at hSquare
  have hCells : 1 + (n : ℝ) ^ 2 ≤ 3 * (1 + (t - x) ^ 2) := by
    nlinarith only [hSquare, sq_abs (t - x), sq_nonneg (|t - x| - 1), sq_nonneg (t - x)]
  have hDenom : d / 3 * (1 + (n : ℝ) ^ 2) ≤ (t - x) ^ 2 + (γ : ℝ) ^ 2 := by
    calc
      _ ≤ d / 3 * (3 * (1 + (t - x) ^ 2)) :=
        mul_le_mul_of_nonneg_left hCells (by positivity)
      _ = d + d * (t - x) ^ 2 := by ring
      _ ≤ _ := by linarith only [hd₂, mul_le_mul_of_nonneg_right hd₁ (sq_nonneg (t - x))]
  rw [cauchyPDFReal_def]
  calc
    _ ≤ Real.pi⁻¹ * (γ : ℝ) * (d / 3 * (1 + (n : ℝ) ^ 2))⁻¹ :=
      mul_le_mul_of_nonneg_left
        ((inv_le_inv₀ (add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos hγ'))
          (mul_pos (div_pos hd (by norm_num)) (by positivity))).mpr hDenom)
        (mul_nonneg (inv_nonneg.mpr Real.pi_pos.le) hγ'.le)
    _ = _ := by
      change _ = (3 * (Real.pi⁻¹ * (γ : ℝ)) / d) * (1 + (n : ℝ) ^ 2)⁻¹
      field_simp [hd.ne', show (1 + (n : ℝ) ^ 2) ≠ 0 by positivity]

/-- A single finite constant bounds the Poisson integral at positive
height for every actual support detector with the given unit-window cap. -/
theorem exists_lintegral_poisson_bound_of_discreteSupportCount (K : ℕ)
    {γ : ℝ≥0} (hγ : 0 < γ) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ (S : LocallyFiniteCarrier) (T : TemperedDistribution ℝ ℂ),
      DistributionSupportedOn S.carrier T →
      (∀ t : ℝ, (S.carrier ∩ Ico t (t + 1)).ncard ≤ K) →
      ∀ x : ℝ, (∫⁻ t, cauchyPDF x γ t ∂discreteSupportCount T) ≤ C := by
  let p (n : ℤ) := (3 * (Real.pi⁻¹ * (γ : ℝ)) / min 1 ((γ : ℝ) ^ 2)) *
    (1 + (n : ℝ) ^ 2)⁻¹
  have hSum : Summable p := summable_inverse_unitCell_weight.mul_left _
  have hp (n : ℤ) : 0 ≤ p n := by
    dsimp only [p]
    exact mul_nonneg (div_nonneg (by positivity) (le_min zero_le_one (sq_nonneg _)))
      (by positivity)
  refine ⟨ENNReal.ofReal (∑' n, p n) * (K : ℝ≥0∞),
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.natCast_lt_top _), ?_⟩
  intro S T hT hCount x
  let J (n : ℤ) := Ico (x + n) (x + n + 1)
  have hCover : (⋃ n, J n) = univ := by
    apply eq_univ_of_forall
    intro t
    refine mem_iUnion.mpr ⟨⌊t - x⌋, ?_⟩
    exact ⟨by linarith only [Int.floor_le (t - x)],
      by linarith only [Int.lt_floor_add_one (t - x)]⟩
  have hCell (n : ℤ) :
      (∫⁻ t in J n, cauchyPDF x γ t ∂discreteSupportCount T) ≤
        ENNReal.ofReal (p n) * (K : ℝ≥0∞) := by
    have hDom : (∫⁻ t in J n, cauchyPDF x γ t ∂discreteSupportCount T) ≤
        ∫⁻ _ in J n, ENNReal.ofReal (p n) ∂discreteSupportCount T := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem (measurableSet_Ico : MeasurableSet (J n))] with t ht
      exact ENNReal.ofReal_le_ofReal (cauchyPDFReal_le_on_unitCell x hγ n ht)
    rw [lintegral_const, Measure.restrict_apply_univ] at hDom
    apply hDom.trans
    gcongr
    exact discreteSupportCount_unit_window_le S T hT hCount (x + n)
  calc
    (∫⁻ t, cauchyPDF x γ t ∂discreteSupportCount T) =
        ∫⁻ t in ⋃ n, J n, cauchyPDF x γ t ∂discreteSupportCount T := by
          rw [hCover, Measure.restrict_univ]
    _ ≤ ∑' n, ∫⁻ t in J n, cauchyPDF x γ t ∂discreteSupportCount T :=
      lintegral_iUnion_le J _
    _ ≤ ∑' n, ENNReal.ofReal (p n) * (K : ℝ≥0∞) := ENNReal.tsum_le_tsum hCell
    _ = _ := by rw [ENNReal.tsum_mul_right, ← ENNReal.ofReal_tsum_of_nonneg hp hSum]

/-- The Poisson-smoothed actual support count is measurable in the
parameter of the original weakly continuous family. -/
theorem measurable_lintegral_poisson_discreteSupportCount {Θ : Type*} [TopologicalSpace Θ]
    [MeasurableSpace Θ] [OpensMeasurableSpace Θ]
    (S : Θ → LocallyFiniteCarrier) (T : Θ → TemperedDistribution ℝ ℂ)
    (hT : ∀ θ, DistributionSupportedOn (S θ).carrier (T θ))
    (hCont : ∀ f : SchwartzMap ℝ ℂ, HasCompactSupport (f : ℝ → ℂ) →
      Continuous (fun θ => T θ f))
    (x : ℝ) (γ : ℝ≥0) :
    Measurable (fun θ => ∫⁻ t, cauchyPDF x γ t ∂discreteSupportCount (T θ)) :=
  measurable_lintegral_discreteSupportCount S T hT hCont (measurable_cauchyPDF x γ)

/-- At positive height each nonzero original support gives a positive
Poisson-smoothed detector. -/
theorem lintegral_poisson_discreteSupportCount_pos (S : LocallyFiniteCarrier)
    (T : TemperedDistribution ℝ ℂ) (hT : DistributionSupportedOn S.carrier T)
    (hNonzero : T ≠ 0) (x : ℝ) {γ : ℝ≥0} (hγ : 0 < γ) :
    0 < (∫⁻ t, cauchyPDF x γ t ∂discreteSupportCount T) := by
  rw [lintegral_pos_iff_support (measurable_cauchyPDF x γ)]
  have hFull : Function.support (cauchyPDF x γ) = univ := by
    apply eq_univ_of_forall
    intro t
    exact (ENNReal.ofReal_pos.mpr (cauchyPDF_pos x hγ.ne' t)).ne'
  rw [hFull]
  exact pos_iff_ne_zero.mpr (fun h => discreteSupportCount_ne_zero S T hT hNonzero
    (Measure.measure_univ_eq_zero.mp h))

/-- The Cauchy density is integrable against the actual support count
at positive height. -/
theorem integrable_poisson_discreteSupportCount (S : LocallyFiniteCarrier)
    (T : TemperedDistribution ℝ ℂ) (hT : DistributionSupportedOn S.carrier T)
    {K : ℕ} (hCount : ∀ t : ℝ, (S.carrier ∩ Ico t (t + 1)).ncard ≤ K)
    (x : ℝ) {γ : ℝ≥0} (hγ : 0 < γ) :
    Integrable (cauchyPDFReal x γ) (discreteSupportCount T) := by
  refine ⟨(measurable_cauchyPDFReal x γ).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  simp only [Real.norm_of_nonneg ((cauchyPDF_pos x hγ.ne' _).le)]
  obtain ⟨C, hC, hBound⟩ := exists_lintegral_poisson_bound_of_discreteSupportCount K hγ
  exact (hBound S T hT hCount x).trans_lt hC

/-- Real and nonnegative integral formulas for the same Poisson field. -/
theorem integral_poisson_discreteSupportCount_eq (T : TemperedDistribution ℝ ℂ)
    (x : ℝ) {γ : ℝ≥0} (hγ : 0 < γ) :
    (∫ t, cauchyPDFReal x γ t ∂discreteSupportCount T) =
      (∫⁻ t, cauchyPDF x γ t ∂discreteSupportCount T).toReal :=
  integral_eq_lintegral_of_nonneg_ae
    (ae_of_all _ fun t => (cauchyPDF_pos x hγ.ne' t).le)
    (measurable_cauchyPDFReal x γ).aestronglyMeasurable

/-- The Poisson field translates by the same shift as its detector. -/
theorem integral_poisson_discreteSupportCount_translation (T : TemperedDistribution ℝ ℂ)
    (a x : ℝ) {γ : ℝ≥0} (hγ : 0 < γ) :
    (∫ t, cauchyPDFReal x γ t ∂discreteSupportCount (combDistributionTranslation a T)) =
      ∫ t, cauchyPDFReal (x - a) γ t ∂discreteSupportCount T := by
  rw [integral_poisson_discreteSupportCount_eq _ _ hγ,
    integral_poisson_discreteSupportCount_eq _ _ hγ, discreteSupportCount_combDistributionTranslation,
    lintegral_map (measurable_cauchyPDF x γ) (by fun_prop)]
  congr 1
  apply lintegral_congr
  intro t
  have he : a + t - x = t - (x - a) := by ring
  simp only [cauchyPDF_def, cauchyPDFReal_def, he]

/-- The real Poisson field of a weak family with a common unit-window
cap is in `L∞` at every positive height, including for Haar measure. -/
theorem memLp_poisson_discreteSupportCount {Θ : Type*} [TopologicalSpace Θ]
    [MeasurableSpace Θ] [OpensMeasurableSpace Θ]
    (S : Θ → LocallyFiniteCarrier) (T : Θ → TemperedDistribution ℝ ℂ)
    (hT : ∀ θ, DistributionSupportedOn (S θ).carrier (T θ))
    (hCont : ∀ f : SchwartzMap ℝ ℂ, HasCompactSupport (f : ℝ → ℂ) →
      Continuous (fun θ => T θ f))
    {K : ℕ} (hCount : ∀ θ t, ((S θ).carrier ∩ Ico t (t + 1)).ncard ≤ K)
    (ν : Measure Θ) (x : ℝ) {γ : ℝ≥0} (hγ : 0 < γ) :
    MemLp (fun θ => ∫ t, cauchyPDFReal x γ t ∂discreteSupportCount (T θ)) ⊤ ν := by
  have hMeas := (measurable_lintegral_poisson_discreteSupportCount S T hT hCont x γ).ennreal_toReal
  obtain ⟨C, hC, hBound⟩ := exists_lintegral_poisson_bound_of_discreteSupportCount K hγ
  simp only [integral_poisson_discreteSupportCount_eq _ x hγ]
  apply memLp_top_of_bound hMeas.aestronglyMeasurable C.toReal
  filter_upwards with θ
  rw [Real.norm_of_nonneg ENNReal.toReal_nonneg]
  exact ENNReal.toReal_mono hC.ne (hBound (S θ) (T θ) (hT θ) (hCount θ) x)

end
end MeyerGeneralProblem
