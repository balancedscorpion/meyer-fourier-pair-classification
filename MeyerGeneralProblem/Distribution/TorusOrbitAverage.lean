module

public import MeyerGeneralProblem.Distribution.TorusWeightedOrbit
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

@[expose] public section

/-!
# Integration along the real flow on a torus

The orbit averaging map satisfies the L¹ convolution bound. Finite
Fourier sums and that bound identify kernels that fix a given L² input.
-/

namespace MeyerGeneralProblem

noncomputable section

open Filter MeasureTheory UnitAddTorus
open scoped ENNReal Topology

/-- Use normalized Haar measure on each circle factor. -/
local instance orbitAverageCircleMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

/-- Normalized Haar measure gives each circle factor total mass one. -/
local instance orbitAverageCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

local notation:max "TorusL2(" d ")" => Lp ℂ 2 (volume : Measure (UnitAddTorus d))

section

variable {d : Type*} [Fintype d]

/-- Scalar averaging along the real torus flow. -/
def torusOrbitAverage (β : d → ℝ) (k : ℝ → ℂ) (F : UnitAddTorus d → ℂ)
    (θ : UnitAddTorus d) : ℂ :=
  ∫ t, k t * F (unitAddTorusFlow β t θ)

theorem measurable_torusOrbitAverage (β : d → ℝ) {k : ℝ → ℂ} {F : UnitAddTorus d → ℂ}
    (hk : Measurable k) (hF : Measurable F) :
    Measurable (torusOrbitAverage β k F) := by
  have hJ : Measurable (fun p : UnitAddTorus d × ℝ => k p.2 * F (unitAddTorusFlow β p.2 p.1)) :=
    (hk.comp measurable_snd).mul (hF.comp ((continuous_unitAddTorusFlow β).measurable.comp measurable_swap))
  exact hJ.stronglyMeasurable.integral_prod_right'.measurable

private theorem integral_norm_torusOrbit_eq (β : d → ℝ) (t : ℝ)
    {F : UnitAddTorus d → ℂ} (hF : Measurable F) :
    (∫ θ, ‖F (unitAddTorusFlow β t θ)‖) = ∫ θ, ‖F θ‖ := by
  have hPres := measurePreserving_unitAddTorusFlow β t
  have h := integral_map (μ := (volume : Measure (UnitAddTorus d)))
    hPres.measurable.aemeasurable hF.norm.aestronglyMeasurable
  rw [hPres.map_eq] at h
  exact h.symm

private theorem integrable_torusOrbitAverage_integrand (β : d → ℝ)
    {k : ℝ → ℂ} {F : UnitAddTorus d → ℂ}
    (hk : Measurable k) (hF : Measurable F) (hki : Integrable k) (hFi : Integrable F) :
    Integrable (fun p : UnitAddTorus d × ℝ => k p.2 * F (unitAddTorusFlow β p.2 p.1))
      ((volume : Measure (UnitAddTorus d)).prod (volume : Measure ℝ)) := by
  have hJ : Measurable (fun p : UnitAddTorus d × ℝ => k p.2 * F (unitAddTorusFlow β p.2 p.1)) :=
    (hk.comp measurable_snd).mul (hF.comp ((continuous_unitAddTorusFlow β).measurable.comp measurable_swap))
  apply (integrable_prod_iff' hJ.aestronglyMeasurable).mpr
  refine ⟨Eventually.of_forall fun t => ?_, ?_⟩
  · have hi := (measurePreserving_unitAddTorusFlow β t).integrable_comp_of_integrable hFi
    change Integrable (fun θ => k t * F (unitAddTorusFlow β t θ))
    simpa only [Function.comp_apply] using hi.const_mul (k t)
  · have hEq (t : ℝ) :
        (∫ θ, ‖k t * F (unitAddTorusFlow β t θ)‖) = ‖k t‖ * ∫ θ, ‖F θ‖ := by
      simp only [norm_mul, integral_const_mul, integral_norm_torusOrbit_eq β t hF]
    simpa only [hEq] using hki.norm.mul_const (∫ θ, ‖F θ‖)

/-- Integrable phase data have an integrable orbit average, with the
usual L¹ convolution bound. -/
theorem integrable_and_integral_norm_torusOrbitAverage_le (β : d → ℝ)
    {k : ℝ → ℂ} {F : UnitAddTorus d → ℂ}
    (hk : Measurable k) (hF : Measurable F) (hki : Integrable k) (hFi : Integrable F) :
    Integrable (torusOrbitAverage β k F) ∧
      (∫ θ, ‖torusOrbitAverage β k F θ‖) ≤ (∫ t, ‖k t‖) * ∫ θ, ‖F θ‖ := by
  let H (p : UnitAddTorus d × ℝ) := k p.2 * F (unitAddTorusFlow β p.2 p.1)
  have hI : Integrable H ((volume : Measure (UnitAddTorus d)).prod (volume : Measure ℝ)) :=
    integrable_torusOrbitAverage_integrand β hk hF hki hFi
  have ha : Integrable (torusOrbitAverage β k F) := hI.integral_prod_left
  refine ⟨ha, ?_⟩
  calc
    _ ≤ ∫ θ, ∫ t, ‖H (θ, t)‖ := by
      apply integral_mono_ae ha.norm hI.norm.integral_prod_left
      filter_upwards [hI.prod_right_ae] with θ hθ
      exact norm_integral_le_integral_norm _
    _ = ∫ t, ∫ θ, ‖H (θ, t)‖ := integral_integral_swap hI.norm
    _ = _ := by
      simp only [H, norm_mul, integral_const_mul, integral_norm_torusOrbit_eq β _ hF,
        integral_mul_const]

private theorem ae_torusOrbitAverage_sub (β : d → ℝ) {k : ℝ → ℂ}
    {F G : UnitAddTorus d → ℂ} (hk : Measurable k) (hF : Measurable F) (hG : Measurable G)
    (hki : Integrable k) (hFi : Integrable F) (hGi : Integrable G) :
    torusOrbitAverage β k (fun θ => F θ - G θ) =ᵐ[volume]
      fun θ => torusOrbitAverage β k F θ - torusOrbitAverage β k G θ := by
  filter_upwards [(integrable_torusOrbitAverage_integrand β hk hF hki hFi).prod_right_ae,
    (integrable_torusOrbitAverage_integrand β hk hG hki hGi).prod_right_ae] with θ h1 h2
  unfold torusOrbitAverage
  simp_rw [mul_sub]
  exact integral_sub h1 h2

private theorem integral_norm_le_torusL2_norm {F : UnitAddTorus d → ℂ} (f : TorusL2(d))
    (hRep : F =ᵐ[volume] f) : (∫ θ, ‖F θ‖) ≤ ‖f‖ := by
  have hMem := (memLp_congr_ae hRep).mpr (Lp.memLp f)
  rw [← lpNorm_one_eq_integral_norm hMem.aestronglyMeasurable, Lp.norm_def, lpNorm,
    ite_eq_left hMem.aestronglyMeasurable, eLpNorm_congr_ae hRep]
  exact ENNReal.toReal_mono (Lp.memLp f).2.ne
    (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      (Lp.aestronglyMeasurable f))

/-- The average fixes a torus L² input if the time kernel has multiplier
one at every frequency carrying a nonzero coefficient. -/
theorem ae_torusOrbitAverage_eq_of_multiplier_one (β : d → ℝ)
    {k : ℝ → ℂ} {F : UnitAddTorus d → ℂ} (f : TorusL2(d))
    (hk : Measurable k) (hki : Integrable k) (hF : Measurable F) (hRep : F =ᵐ[volume] f)
    (hMultiplier : ∀ n : d → ℤ, mFourierCoeff f n ≠ 0 →
      (∫ t, k t * combModulationCharacter (torusDirectionalFrequency β n) t) = 1) :
    torusOrbitAverage β k F =ᵐ[volume] F := by
  classical
  let c := mFourierCoeff f
  let P (s : Finset (d → ℤ)) (θ : UnitAddTorus d) := ∑ n ∈ s, c n * mFourier n θ
  let p (s : Finset (d → ℤ)) : TorusL2(d) := ∑ n ∈ s, c n • mFourierLp 2 n
  have hP (s : Finset (d → ℤ)) : Continuous (P s) :=
    continuous_finsetSum _ fun n _ => continuous_const.mul (mFourier n).continuous
  have hp (s : Finset (d → ℤ)) : P s =ᵐ[volume] p s := by
    have he (n : d → ℤ) : (fun θ => c n * mFourier n θ) =ᵐ[volume] (c n • mFourierLp 2 n : TorusL2(d)) :=
      ((Lp.coeFn_smul (c n) (mFourierLp 2 n)).trans
        ((coeFn_mFourierLp 2 n).fun_comp (fun z => c n * z))).symm
    have hPSum : P s = ∑ n ∈ s, fun θ => c n * mFourier n θ := by
      funext θ
      simp only [P, Finset.sum_apply]
    rw [hPSum]
    exact (eventuallyEq_sum fun n (_ : n ∈ s) => he n).trans (Lp.coeFn_finsetSum s _).symm
  have hFixed (s : Finset (d → ℤ)) (θ : UnitAddTorus d) :
      torusOrbitAverage β k (P s) θ = P s θ := by
    have hTerm (n : d → ℤ) (t : ℝ) :
        k t * (c n * mFourier n (unitAddTorusFlow β t θ)) =
          (c n * mFourier n θ) * (k t * combModulationCharacter (torusDirectionalFrequency β n) t) := by
      rw [mFourier_unitAddTorusFlow]
      ring
    have hInt (n : d → ℤ) :
        Integrable (fun t => k t * (c n * mFourier n (unitAddTorusFlow β t θ))) := by
      simp_rw [hTerm]
      have hc : Continuous (combModulationCharacter (torusDirectionalFrequency β n)) := by
        have he : combModulationCharacter (torusDirectionalFrequency β n) =
            fun t : ℝ => Complex.exp (2 * Real.pi * Complex.I * (torusDirectionalFrequency β n : ℂ) * (t : ℂ)) :=
          funext (combModulationCharacter_eq_exp _)
        rw [he]
        fun_prop
      have hu : Integrable (fun t => k t * combModulationCharacter (torusDirectionalFrequency β n) t) := by
        refine hki.norm.mono' (hk.mul hc.measurable).aestronglyMeasurable (Eventually.of_forall fun t => ?_)
        rw [norm_mul, norm_combModulationCharacter, mul_one]
      exact hu.const_mul _
    simp only [torusOrbitAverage, P, Finset.mul_sum]
    rw [integral_finsetSum _ fun n _ => hInt n]
    apply Finset.sum_congr rfl
    intro n _
    simp_rw [hTerm, integral_const_mul]
    by_cases hn : c n = 0
    · simp [hn]
    · rw [hMultiplier n hn, mul_one]
  have hFi : Integrable F := ((memLp_congr_ae hRep).mpr (Lp.memLp f)).integrable (by norm_num)
  have hPi (s : Finset (d → ℤ)) : Integrable (P s) :=
    ((memLp_congr_ae (hp s)).mpr (Lp.memLp (p s))).integrable (by norm_num)
  have hInt := (integrable_and_integral_norm_torusOrbitAverage_le β hk hF hki hFi).1
  let err := ∫ θ, ‖torusOrbitAverage β k F θ - F θ‖
  let C := ∫ t, ‖k t‖
  have hErr (s : Finset (d → ℤ)) : err ≤ (C + 1) * ‖f - p s‖ := by
    let G (θ : UnitAddTorus d) := F θ - P s θ
    have hG : Measurable G := hF.sub (hP s).measurable
    have hGi : Integrable G := hFi.sub (hPi s)
    have hGRep : G =ᵐ[volume] (⇑(f - p s) : UnitAddTorus d → ℂ) :=
      (hRep.sub (hp s)).trans (Lp.coeFn_sub f (p s)).symm
    have hAE : (fun θ => torusOrbitAverage β k F θ - F θ) =ᵐ[volume]
        fun θ => torusOrbitAverage β k G θ - G θ := by
      filter_upwards [ae_torusOrbitAverage_sub β hk hF (hP s).measurable hki hFi (hPi s)]
        with θ hθ
      change torusOrbitAverage β k G θ = _ at hθ
      rw [hθ, hFixed]
      dsimp [G]
      abel
    have hAvg := integrable_and_integral_norm_torusOrbitAverage_le β hk hG hki hGi
    calc
      err = ∫ θ, ‖torusOrbitAverage β k G θ - G θ‖ :=
        integral_congr_ae (hAE.fun_comp norm)
      _ ≤ ∫ θ, ‖torusOrbitAverage β k G θ‖ + ‖G θ‖ := by
        apply integral_mono (hAvg.1.sub hGi).norm (hAvg.1.norm.add hGi.norm)
        intro θ
        exact norm_sub_le _ _
      _ ≤ (C + 1) * ∫ θ, ‖G θ‖ := by
        rw [integral_add hAvg.1.norm hGi.norm, add_mul, one_mul]
        exact add_le_add hAvg.2 le_rfl
      _ ≤ _ := mul_le_mul_of_nonneg_left (integral_norm_le_torusL2_norm (f - p s) hGRep)
          (add_nonneg (integral_nonneg fun _ => norm_nonneg _) zero_le_one)
  have hT : Tendsto p atTop (𝓝 f) := hasSum_mFourier_series_L2 f
  have hLim : Tendsto (fun s => (C + 1) * ‖f - p s‖) atTop (𝓝 0) := by
    simpa only [sub_self, norm_zero, mul_zero] using
      ((tendsto_const_nhds (x := f)).sub hT).norm.const_mul (C + 1)
  have hz : err = 0 := le_antisymm (ge_of_tendsto hLim (Eventually.of_forall hErr))
    (integral_nonneg fun _ => norm_nonneg _)
  have hAE := (integral_eq_zero_iff_of_nonneg (fun θ => norm_nonneg (torusOrbitAverage β k F θ - F θ))
    (hInt.sub hFi).norm).mp hz
  exact hAE.mono fun θ hθ => sub_eq_zero.mp (norm_eq_zero.mp hθ)

end
end
end MeyerGeneralProblem
