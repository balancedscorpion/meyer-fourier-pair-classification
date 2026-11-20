module

public import MeyerGeneralProblem.Distribution.DiskPositivePoissonRepresentation
public import MeyerGeneralProblem.Distribution.FourierLaplaceHeatLimit

@[expose] public section

/-!
# Boundary uniqueness on an angular interval

Jensen's radial bound gives a uniformly finite negative logarithmic
moment for a bounded holomorphic function with nonzero center value.
Fatou's lemma rules out vanishing radial limits on an angular interval.
-/

namespace MeyerGeneralProblem

noncomputable section

open Filter MeasureTheory Metric Set
open scoped ENNReal Topology

/-- A bounded holomorphic function with nonzero center value cannot
have zero radial limits on an angular interval of positive length. -/
theorem not_radial_zero_on_interval_of_bounded_diskFunction
    {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F (ball 0 1)) (hF₀ : F 0 ≠ 0)
    {M : ℝ} (hBound : ∀ z ∈ ball (0 : ℂ) 1, ‖F z‖ ≤ M)
    {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 2 * Real.pi) (hab : a < b)
    (hVanish : ∀ θ ∈ Ioo a b, Tendsto (fun r : ℝ => F (circleMap 0 r θ))
      (𝓝[<] (1 : ℝ)) (𝓝 0)) : False := by
  obtain ⟨ρ, hρ₀, hρ₁, hρ⟩ := exists_innerDiskRadialSequence
  let r (n : ℕ) := (ρ n + 1) / 2
  have hr₀ (n : ℕ) : 0 < r n := by dsimp [r]; linarith only [hρ₀ n]
  have hr₁ (n : ℕ) : r n < 1 := by dsimp [r]; linarith only [hρ₁ n]
  have hr : Tendsto r atTop (𝓝 (1 : ℝ)) := by
    simpa only [r, show ((1 : ℝ) + 1) / 2 = 1 by norm_num] using (hρ.add_const 1).div_const 2
  have hrLeft : Tendsto r atTop (𝓝[<] (1 : ℝ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within r hr (Eventually.of_forall hr₁)
  let U := ball (0 : ℂ) 1
  have hAt : (0 : ℂ) ∈ U := mem_ball_self zero_lt_one
  have hA : AnalyticOnNhd ℂ F U := hF.analyticOnNhd isOpen_ball
  have hConnected : IsConnected U := ⟨⟨0, hAt⟩, (convex_ball (0 : ℂ) 1).isPreconnected⟩
  let Z := (F ⁻¹' {(0 : ℂ)}) ∩ U
  have hDisc : IsDiscrete Z := by
    apply isDiscrete_of_codiscreteWithin
    rw [← preimage_compl]
    exact hA.preimage_zero_mem_codiscreteWithin hF₀ hAt hConnected
  have hCount : Z.Countable := by
    let _ : DiscreteTopology Z := isDiscrete_iff_discreteTopology.mp hDisc
    exact TopologicalSpace.separableSpace_iff_countable.mp inferInstance
  have hIn (n : ℕ) (θ : ℝ) : circleMap 0 (r n) θ ∈ U := by
    change circleMap (0 : ℂ) (r n) θ ∈ ball 0 1
    rw [mem_ball_zero_iff, norm_circleMap_zero, abs_of_pos (hr₀ n)]
    exact hr₁ n
  let _ : NullSingletonClass diskAngleMeasure := by
    unfold diskAngleMeasure
    infer_instance
  have hAvoid : ∀ᵐ θ ∂diskAngleMeasure, ∀ n, F (circleMap 0 (r n) θ) ≠ 0 := by
    rw [ae_all_iff]
    intro n
    simp only [ae_iff, not_not]
    apply Set.Countable.measure_zero
    refine (hCount.preimage_circleMap 0 (hr₀ n).ne').mono ?_
    intro θ hθ
    change F (circleMap 0 (r n) θ) = 0 at hθ
    change circleMap 0 (r n) θ ∈ Z
    exact ⟨hθ, hIn n θ⟩
  let N (z : ℂ) := Real.posLog ‖F z‖⁻¹
  let G (n : ℕ) (θ : ℝ) := ENNReal.ofReal (N (circleMap 0 (r n) θ))
  have hG (n : ℕ) : Measurable (G n) := by
    have hC : Continuous (fun θ : ℝ => F (circleMap 0 (r n) θ)) :=
      hF.continuousOn.comp_continuous (continuous_circleMap 0 _) (hIn n)
    exact ENNReal.measurable_ofReal.comp
      (measurable_const.max (Real.measurable_log.comp hC.norm.measurable.inv))
  let C := 2 * Real.sqrt M - Real.log ‖F 0‖
  have hGInt (n : ℕ) : (∫⁻ θ, G n θ ∂diskAngleMeasure) ≤ ENNReal.ofReal (2 * Real.pi * C) := by
    have hSphere : sphere (0 : ℂ) |r n| ⊆ U := by
      rw [abs_of_pos (hr₀ n)]
      exact sphere_subset_closedBall.trans (closedBall_subset_ball (hr₁ n))
    have hHalf : Real.circleAverage (fun z => Real.sqrt ‖F z‖) 0 (r n) ≤ Real.sqrt M := by
      have hI : CircleIntegrable (fun z => Real.sqrt ‖F z‖) 0 (r n) :=
        (Real.continuous_sqrt.comp_continuousOn (hF.continuousOn.mono hSphere).norm).circleIntegrable'
      calc
        _ ≤ Real.circleAverage (fun _ : ℂ => Real.sqrt M) 0 (r n) :=
          Real.circleAverage_mono hI (circleIntegrable_const _ _ _) fun z hz =>
            Real.sqrt_le_sqrt (hBound z (hSphere hz))
        _ = _ := by rw [Real.circleAverage_const]
    have hJ : Real.circleAverage N 0 (r n) ≤ C :=
      circleAverage_neg_log_norm_le_of_circleAverage_sqrt_norm_le hF
        (norm_pos_iff.mpr hF₀) le_rfl (hr₀ n) (hr₁ n) hHalf
    have hMero := (hA.mono hSphere).meromorphicOn
    have hI : CircleIntegrable N 0 (r n) := by
      simpa only [N, Pi.inv_apply, norm_inv] using hMero.inv.circleIntegrable_posLog_norm
    have hInt : Integrable (fun θ => N (circleMap 0 (r n) θ)) diskAngleMeasure :=
      hI.1.mono_set Ioo_subset_Ioc_self
    have hAngle : (∫ θ, N (circleMap 0 (r n) θ) ∂diskAngleMeasure) =
        2 * Real.pi * Real.circleAverage N 0 (r n) := by
      change (∫ θ in Ioo 0 (2 * Real.pi), N (circleMap 0 (r n) θ)) =
        (2 * Real.pi) * ((2 * Real.pi)⁻¹ * ∫ θ in 0..2 * Real.pi, N (circleMap 0 (r n) θ))
      rw [intervalIntegral.integral_of_le Real.two_pi_pos.le, integral_Ioc_eq_integral_Ioo,
        ← mul_assoc, mul_inv_cancel₀ Real.two_pi_pos.ne', one_mul]
    change (∫⁻ θ, ENNReal.ofReal (N (circleMap 0 (r n) θ)) ∂diskAngleMeasure) ≤ _
    rw [← ofReal_integral_eq_lintegral_ofReal hInt (ae_of_all _ fun _ => Real.posLog_nonneg), hAngle]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hJ Real.two_pi_pos.le)
  have hFinite : ∀ᵐ θ ∂diskAngleMeasure, liminf (fun n => G n θ) atTop < ⊤ := by
    refine ae_lt_top (Measurable.liminf hG) ?_
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      ((lintegral_liminf_le hG).trans (liminf_le_of_frequently_le' (.of_forall hGInt)))
  have hOut : ∀ᵐ θ ∂diskAngleMeasure, θ ∉ Ioo a b := by
    filter_upwards [hAvoid, hFinite] with θ hθ hFin hmem
    have hVal := (hVanish θ hmem).comp hrLeft
    have hNorm : Tendsto (fun n => ‖F (circleMap 0 (r n) θ)‖) atTop (𝓝 (0 : ℝ)) := by
      simpa only [Function.comp_apply, norm_zero] using hVal.norm
    have hPos : Tendsto (fun n => ‖F (circleMap 0 (r n) θ)‖) atTop (𝓝[>] (0 : ℝ)) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hNorm
        (Eventually.of_forall fun n => norm_pos_iff.mpr (hθ n))
    have hLog := Real.tendsto_log_atTop.comp (tendsto_inv_nhdsGT_zero.comp hPos)
    have hNeg : Tendsto (fun n => N (circleMap 0 (r n) θ)) atTop atTop :=
      tendsto_atTop_mono (fun n => le_max_right _ _) hLog
    have hTop : Tendsto (fun n => G n θ) atTop (𝓝 ⊤) := ENNReal.tendsto_ofReal_atTop.comp hNeg
    exact hFin.ne hTop.liminf_eq
  simp only [ae_iff, not_not] at hOut
  have hPos : 0 < diskAngleMeasure (Ioo a b) := by
    rw [diskAngleMeasure, Measure.restrict_apply measurableSet_Ioo,
      inter_eq_left.mpr (Ioo_subset_Ioo ha hb), Real.volume_Ioo]
    exact ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)
  exact hPos.ne' hOut

end
end MeyerGeneralProblem
