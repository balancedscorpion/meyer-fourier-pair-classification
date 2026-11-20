module

public import Mathlib.Analysis.Complex.JensenFormula
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Topology.Algebra.InfiniteSum.Real

@[expose] public section

/-!
# The disk Blaschke condition from Jensen's formula

A uniform radial half-moment controls the total zero weight, counting
each zero with its analytic multiplicity.
-/

namespace MeyerGeneralProblem

noncomputable section

open Filter Function MeromorphicOn Metric Set
open scoped Topology

private theorem divisor_apply_eq_analyticOrderNatAt {F : ℂ → ℂ} {U : Set ℂ}
    (hF : AnalyticOnNhd ℂ F U) {z : ℂ} (hz : z ∈ U) :
    divisor F U z = (analyticOrderNatAt F z : ℤ) := by
  rw [AnalyticOnNhd.divisor_apply hF hz, analyticOrderNatAt]
  cases analyticOrderAt F z <;> rfl

private theorem circleAverage_log_norm_le_twice {F : ℂ → ℂ} {r M : ℝ}
    (hF : AnalyticOnNhd ℂ F (closedBall 0 |r|))
    (hHalf : Real.circleAverage (fun z => Real.sqrt ‖F z‖) 0 r ≤ M) :
    Real.circleAverage (fun z => Real.log ‖F z‖) 0 r ≤ 2 * M := by
  have hC := (hF.mono sphere_subset_closedBall).continuousOn
  have hI : CircleIntegrable (fun z => 2 * Real.sqrt ‖F z‖) 0 r :=
    (continuousOn_const.mul (Real.continuous_sqrt.comp_continuousOn hC.norm)).circleIntegrable'
  calc
    _ ≤ Real.circleAverage (fun z => 2 * Real.sqrt ‖F z‖) 0 r := by
      apply Real.circleAverage_mono (hF.mono sphere_subset_closedBall).meromorphicOn.circleIntegrable_log_norm hI
      intro z _
      have h := Real.log_le_rpow_div (norm_nonneg (F z)) (by norm_num : (0 : ℝ) < 1 / 2)
      rw [← Real.sqrt_eq_rpow] at h
      linarith only [h]
    _ = 2 * Real.circleAverage (fun z => Real.sqrt ‖F z‖) 0 r := by
      change Real.circleAverage (fun z => (2 : ℝ) • Real.sqrt ‖F z‖) 0 r = _
      rw [Real.circleAverage_fun_smul, smul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left hHalf (by norm_num)

private theorem finite_zero_log_sum_le_of_halfMoment {F : ℂ → ℂ} {r M : ℝ}
    (hr : 0 < r) (hF : AnalyticOnNhd ℂ F (closedBall 0 |r|)) (hF₀ : F 0 ≠ 0)
    (hHalf : Real.circleAverage (fun z => Real.sqrt ‖F z‖) 0 r ≤ M)
    (s : Finset ℂ) (hs : ∀ z ∈ s, ‖z‖ ≤ r) :
    (∑ z ∈ s, (analyticOrderNatAt F z : ℝ) * Real.log (r * ‖z‖⁻¹)) ≤
      2 * M - Real.log ‖F 0‖ := by
  classical
  let D := divisor F (closedBall (0 : ℂ) |r|)
  let J (z : ℂ) := (D z : ℝ) * Real.log (r * ‖z‖⁻¹)
  have hJs : (support J).Finite := (D.finiteSupport (isCompact_closedBall _ _)).subset (by
    intro z hz
    contrapose! hz
    have hz₀ : D z = 0 := notMem_support.mp hz
    simp [J, hz₀])
  let T := s ∪ hJs.toFinset
  have hJT : support J ⊆ T := fun z hz => Finset.mem_union_right s (hJs.mem_toFinset.mpr hz)
  have hJnonneg (z : ℂ) : 0 ≤ J z := by
    by_cases hz : z ∈ closedBall (0 : ℂ) |r|
    · have hNz : ‖z‖ ≤ r := by simpa only [mem_closedBall, dist_zero_right, abs_of_pos hr] using hz
      by_cases h₀ : z = 0
      · simp [J, h₀]
      · have hLog : 0 ≤ Real.log (r * ‖z‖⁻¹) := by
          rw [← div_eq_mul_inv]
          exact Real.log_nonneg ((one_le_div (norm_pos_iff.mpr h₀)).2 hNz)
        exact mul_nonneg (by exact_mod_cast hF.divisor_nonneg z) hLog
    · have h₀ : D z = 0 := D.apply_eq_zero_of_notMem hz
      simp [J, h₀]
  have hEq : Real.circleAverage (fun z => Real.log ‖F z‖) 0 r =
      (∑ᶠ z, J z) + Real.log ‖F 0‖ := by
    rw [hF.circleAverage_log_norm hr.ne' hF₀]
    simp only [zero_sub, norm_neg, J, D]
  have hAvg := circleAverage_log_norm_le_twice hF hHalf
  calc
    _ = ∑ z ∈ s, J z := by
      refine Finset.sum_congr rfl fun z hz => ?_
      have hc : z ∈ closedBall (0 : ℂ) |r| := by
        simpa only [mem_closedBall, dist_zero_right, abs_of_pos hr] using hs z hz
      simp only [J, D, divisor_apply_eq_analyticOrderNatAt hF hc, Int.cast_natCast]
    _ ≤ ∑ z ∈ T, J z := Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
      (fun z _ _ => hJnonneg z)
    _ = ∑ᶠ z, J z := (finsum_eq_finsetSum_of_support_subset _ hJT).symm
    _ ≤ _ := by linarith only [hEq, hAvg]

/-- The disk Blaschke weight with its analytic multiplicity and with
zero weight outside the unit disk. -/
def diskBlaschkeZeroWeight (F : ℂ → ℂ) (z : ℂ) : ℝ :=
  if ‖z‖ < 1 then (analyticOrderNatAt F z : ℝ) * (1 - ‖z‖) else 0

/-- Jensen's formula and the radial half-moment imply the disk
Blaschke condition with all analytic multiplicities. -/
theorem summable_diskBlaschkeZeroWeight_of_circleAverage_sqrt_norm_le {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F (ball 0 1)) (hF₀ : F 0 ≠ 0)
    {M : ℝ} (hHalf : ∀ r : ℝ, 0 < r → r < 1 →
      Real.circleAverage (fun z => Real.sqrt ‖F z‖) 0 r ≤ M) :
    Summable (diskBlaschkeZeroWeight F) := by
  classical
  refine summable_of_sum_le (c := 2 * M - Real.log ‖F 0‖) ?_ ?_
  · intro z
    by_cases hz : ‖z‖ < 1
    · simp [diskBlaschkeZeroWeight, hz]
    · simp [diskBlaschkeZeroWeight, hz]
  intro T
  let s := T.filter (fun z => ‖z‖ < 1)
  have hs (z : ℂ) (hz : z ∈ s) : ‖z‖ < 1 := (Finset.mem_filter.mp hz).2
  have hEventually : ∀ᶠ r : ℝ in 𝓝[<] (1 : ℝ),
      (∑ z ∈ s, (analyticOrderNatAt F z : ℝ) * Real.log (r * ‖z‖⁻¹)) ≤
        2 * M - Real.log ‖F 0‖ := by
    have hR : ∀ᶠ r : ℝ in 𝓝[<] (1 : ℝ), 0 < r ∧ r < 1 := by
      filter_upwards [mem_nhdsWithin_of_mem_nhds (eventually_gt_nhds (zero_lt_one : (0 : ℝ) < 1)),
        self_mem_nhdsWithin (s := Iio (1 : ℝ))] with r hr hr₁
      exact ⟨hr, hr₁⟩
    have hAll : ∀ᶠ r : ℝ in 𝓝[<] (1 : ℝ), ∀ z ∈ s, ‖z‖ ≤ r :=
      (eventually_all_finset s).2 fun z hz => by
        have hNear : ∀ᶠ r : ℝ in 𝓝[<] (1 : ℝ), ‖z‖ < r :=
          mem_nhdsWithin_of_mem_nhds (eventually_gt_nhds (hs z hz))
        exact hNear.mono fun _ hu => hu.le
    filter_upwards [hR, hAll] with r hr hsr
    have hSub : closedBall (0 : ℂ) |r| ⊆ ball 0 1 := by
      rw [abs_of_pos hr.1]
      exact closedBall_subset_ball hr.2
    exact finite_zero_log_sum_le_of_halfMoment hr.1 (hF.analyticOnNhd isOpen_ball |>.mono hSub)
      hF₀ (hHalf r hr.1 hr.2) s hsr
  have hLimit : Tendsto (fun r : ℝ =>
      ∑ z ∈ s, (analyticOrderNatAt F z : ℝ) * Real.log (r * ‖z‖⁻¹))
      (𝓝[<] (1 : ℝ))
      (𝓝 (∑ z ∈ s, (analyticOrderNatAt F z : ℝ) * Real.log ‖z‖⁻¹)) := by
    refine tendsto_finsetSum s fun z _ => ?_
    by_cases hz : z = 0
    · simp [hz]
    have hPos : 0 < ‖z‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr hz)
    have hCont : ContinuousAt (fun r : ℝ => Real.log (r * ‖z‖⁻¹)) 1 :=
      (continuous_id.mul continuous_const).continuousAt.log (by simpa using hPos.ne')
    have h := (continuousAt_const.mul hCont :
      ContinuousAt (fun r : ℝ => (analyticOrderNatAt F z : ℝ) * Real.log (r * ‖z‖⁻¹)) 1)
    have hT : Tendsto (fun r : ℝ => (analyticOrderNatAt F z : ℝ) * Real.log (r * ‖z‖⁻¹))
        (𝓝[<] (1 : ℝ)) (𝓝 ((analyticOrderNatAt F z : ℝ) * Real.log (1 * ‖z‖⁻¹))) :=
      h.continuousWithinAt
    simpa only [one_mul] using hT
  have hUpper := le_of_tendsto hLimit hEventually
  have hCenter : analyticOrderNatAt F 0 = 0 := by
    rw [analyticOrderNatAt, (hF.analyticOnNhd isOpen_ball 0 (mem_ball_self zero_lt_one)).analyticOrderAt_eq_zero.mpr hF₀]
    rfl
  calc
    _ = ∑ z ∈ s, (analyticOrderNatAt F z : ℝ) * (1 - ‖z‖) := by
      rw [Finset.sum_filter]
      rfl
    _ ≤ ∑ z ∈ s, (analyticOrderNatAt F z : ℝ) * Real.log ‖z‖⁻¹ := by
      refine Finset.sum_le_sum fun z _ => ?_
      by_cases hz : z = 0
      · simp [hz, hCenter]
      · refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
        rw [Real.log_inv]
        have h := Real.log_le_sub_one_of_pos (norm_pos_iff.mpr hz)
        linarith only [h]
    _ ≤ _ := hUpper

end
end MeyerGeneralProblem
