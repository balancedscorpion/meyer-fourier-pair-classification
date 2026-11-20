module

public import MeyerGeneralProblem.Distribution.DiskPositivePoissonRepresentation

@[expose] public section

/-!
# Poisson representation from local angular limits

Continuous cutoffs vanishing around one circle point recover the
contribution from its complement. The contribution at the remaining
point is the nonnegative mass of a singleton.
-/

namespace MeyerGeneralProblem

noncomputable section

open Filter MeasureTheory Metric Set
open scoped Topology

private def diskBoundaryCutoff (p : DiskUnitBoundary) (n : ℕ) : C(DiskUnitBoundary, ℝ) :=
  ⟨fun q => min 1 (max 0 (((n : ℝ) + 1) * dist q p - 1)), by fun_prop⟩

private theorem diskBoundaryCutoff_nonneg (p q : DiskUnitBoundary) (n : ℕ) :
    0 ≤ diskBoundaryCutoff p n q := le_min zero_le_one (le_max_left _ _)

private theorem diskBoundaryCutoff_le_one (p q : DiskUnitBoundary) (n : ℕ) :
    diskBoundaryCutoff p n q ≤ 1 := min_le_left _ _

private theorem diskBoundaryCutoff_eventually_zero (p : DiskUnitBoundary) (n : ℕ) :
    ∀ᶠ q in 𝓝 p, diskBoundaryCutoff p n q = 0 := by
  have hn : 0 < (n : ℝ) + 1 := by positivity
  filter_upwards [ball_mem_nhds p (one_div_pos.mpr hn)] with q hq
  have hdist := (lt_div_iff₀ hn).mp (mem_ball.mp hq)
  change min 1 (max 0 (((n : ℝ) + 1) * dist q p - 1)) = 0
  rw [max_eq_left (by linarith only [hdist]), min_eq_right zero_le_one]

private theorem diskBoundaryCutoff_tendsto_one {p q : DiskUnitBoundary} (hq : q ≠ p) :
    Tendsto (fun n => diskBoundaryCutoff p n q) atTop (𝓝 1) := by
  have hPos : 0 < dist q p := dist_pos.mpr hq
  have hLarge : ∀ᶠ n : ℕ in atTop, 2 / dist q p ≤ (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop _
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [hLarge] with n hn
  have hMul := (div_le_iff₀ hPos).mp hn
  change 1 = min 1 (max 0 (((n : ℝ) + 1) * dist q p - 1))
  refine (min_eq_left ((show (1 : ℝ) ≤ ((n : ℝ) + 1) * dist q p - 1 by
    linarith only [hMul, hPos]).trans (le_max_right _ _))).symm

private theorem tendsto_integral_mul_diskBoundaryCutoff {X : Type*} [MeasurableSpace X]
    {ν : Measure X} {g : X → ℝ} (hg : Integrable g ν)
    {k : X → DiskUnitBoundary} (hk : Measurable k) (p : DiskUnitBoundary) :
    Tendsto (fun n => ∫ x, g x * diskBoundaryCutoff p n (k x) ∂ν) atTop
      (𝓝 (∫ x in k ⁻¹' ({p} : Set DiskUnitBoundary)ᶜ, g x ∂ν)) := by
  let S := k ⁻¹' ({p} : Set DiskUnitBoundary)ᶜ
  have hS : MeasurableSet S := hk (measurableSet_singleton p).compl
  change Tendsto _ atTop (𝓝 (∫ x in S, g x ∂ν))
  rw [← integral_indicator hS]
  apply tendsto_integral_of_dominated_convergence (fun x => ‖g x‖)
  · intro n
    exact hg.aestronglyMeasurable.mul ((diskBoundaryCutoff p n).continuous.measurable.comp hk).aestronglyMeasurable
  · exact hg.norm
  · intro n
    exact ae_of_all _ fun x => by
      rw [norm_mul, Real.norm_eq_abs (diskBoundaryCutoff p n (k x)),
        abs_of_nonneg (diskBoundaryCutoff_nonneg _ _ _)]
      exact (mul_le_mul_of_nonneg_left (diskBoundaryCutoff_le_one _ _ _) (norm_nonneg _)).trans_eq
        (mul_one _)
  · refine ae_of_all _ fun x => ?_
    by_cases hx : k x = p
    · rw [indicator_of_notMem (show x ∉ S from by simp [S, hx])]
      have hZero : (fun n => g x * diskBoundaryCutoff p n (k x)) = fun _ => 0 := by
        funext n
        simp [hx, diskBoundaryCutoff]
      rw [hZero]
      exact tendsto_const_nhds
    · rw [indicator_of_mem (show x ∈ S from hx)]
      simpa only [mul_one] using
        (tendsto_const_nhds (x := g x)).mul (diskBoundaryCutoff_tendsto_one hx)

/-- Radial test limits off one circle point identify the regular part
of the Poisson integral. The other contribution is a nonnegative
multiple of the kernel at that point. -/
theorem exists_diskBoundaryPoissonMeasure_density_add_atom
    {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F (ball 0 1))
    (hPos : ∀ z ∈ ball (0 : ℂ) 1, 0 ≤ (F z).re)
    (p : DiskUnitBoundary) {D : ℝ → ℝ} (hD : Integrable D diskAngleMeasure)
    (hTests : ∀ P : C(DiskUnitBoundary, ℝ), (∀ᶠ q in 𝓝 p, P q = 0) →
      Tendsto (fun r : ℝ => ∫ θ, ((F (circleMap 0 r θ)).re / (2 * Real.pi)) *
        P (diskAnglePoint θ) ∂diskAngleMeasure) (𝓝[<] (1 : ℝ))
        (𝓝 (∫ θ, (D θ / (2 * Real.pi)) * P (diskAnglePoint θ) ∂diskAngleMeasure))) :
    ∃ a : ℝ, 0 ≤ a ∧ ∀ w ∈ ball (0 : ℂ) 1,
      (F w).re = (∫ θ, (D θ / (2 * Real.pi)) * diskBoundaryPoissonKernel w (diskAnglePoint θ)
        ∂diskAngleMeasure) + a * diskBoundaryPoissonKernel w p := by
  obtain ⟨μ, _, hPoisson, hWeak⟩ := exists_diskBoundaryPoissonMeasure_of_test_limits hF hPos
  let ν : Measure DiskUnitBoundary := μ
  let a := ν.real {p}
  refine ⟨a, ENNReal.toReal_nonneg, ?_⟩
  intro w hw
  let P : C(DiskUnitBoundary, ℝ) := ⟨diskBoundaryPoissonKernel w, continuous_diskBoundaryPoissonKernel hw⟩
  let G (θ : ℝ) := (D θ / (2 * Real.pi)) * P (diskAnglePoint θ)
  have hP : Integrable P ν := P.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hG : Integrable G diskAngleMeasure := by
    have hScaled := hD.div_const (2 * Real.pi)
    refine (hScaled.norm.mul_const ‖P‖).mono'
      (hScaled.aestronglyMeasurable.mul
        (P.continuous.comp continuous_diskAnglePoint).aestronglyMeasurable) ?_
    exact ae_of_all _ fun θ => by
      change ‖(D θ / (2 * Real.pi)) * P (diskAnglePoint θ)‖ ≤ ‖D θ / (2 * Real.pi)‖ * ‖P‖
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (P.norm_coe_le_norm _) (norm_nonneg _)
  have hCut (n : ℕ) : (∫ q, P q * diskBoundaryCutoff p n q ∂ν) =
      ∫ θ, G θ * diskBoundaryCutoff p n (diskAnglePoint θ) ∂diskAngleMeasure := by
    let T := P * diskBoundaryCutoff p n
    have hT : ∀ᶠ q in 𝓝 p, T q = 0 := by
      filter_upwards [diskBoundaryCutoff_eventually_zero p n] with q hq
      change P q * diskBoundaryCutoff p n q = 0
      rw [hq, mul_zero]
    refine (hWeak T _ (hTests T hT)).trans ?_
    apply integral_congr_ae
    exact ae_of_all _ fun θ => (mul_assoc _ _ _).symm
  have hFrom := tendsto_integral_mul_diskBoundaryCutoff hP measurable_id p
  have hTo := tendsto_integral_mul_diskBoundaryCutoff hG continuous_diskAnglePoint.measurable p
  have hEq := tendsto_nhds_unique hFrom (hTo.congr fun n => (hCut n).symm)
  change (∫ q in ({p} : Set DiskUnitBoundary)ᶜ, P q ∂ν) =
    ∫ θ in (diskAnglePoint ⁻¹' {p})ᶜ, G θ ∂diskAngleMeasure at hEq
  let _ : NullSingletonClass diskAngleMeasure := by
    unfold diskAngleMeasure
    infer_instance
  have hNull : diskAngleMeasure (diskAnglePoint ⁻¹' {p}) = 0 := by
    apply Set.Countable.measure_zero
    refine ((countable_singleton (p : ℂ)).preimage_circleMap 0 one_ne_zero).mono ?_
    intro θ hθ
    exact congrArg Subtype.val (mem_singleton_iff.mp hθ)
  rw [setIntegral_compl (measurableSet_singleton p) hP, integral_singleton, smul_eq_mul,
    setIntegral_compl (continuous_diskAnglePoint.measurable (measurableSet_singleton p)) hG,
    setIntegral_measure_zero _ hNull, sub_zero] at hEq
  rw [← hPoisson w hw]
  exact sub_eq_iff_eq_add.mp hEq

end
end MeyerGeneralProblem
