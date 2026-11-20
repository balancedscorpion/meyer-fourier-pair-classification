module

public import MeyerGeneralProblem.Distribution.BlaschkeBoundaryJumps

@[expose] public section

/-!
# Uniform sign alternation for the heated positive ray

The weighted logarithmic tail allows a conjugate-controlled endpoint
in every sufficiently large fractional window. Two windows give a
phase gain with the full gap slope up to an arbitrarily small loss.
-/

namespace MeyerGeneralProblem

noncomputable section

open Filter MeasureTheory Metric Set
open scoped FourierTransform Topology

private theorem weightedBoundaryConjugate_eq_compact_add_tail
    {u u₀ u₁ : ℝ → ℝ} {x : ℝ}
    (hu : Integrable (fun y : ℝ => u y / (1 + y ^ 2)))
    (hu₀ : Integrable (fun y : ℝ => u₀ y / (1 + y ^ 2)))
    (hu₁ : Integrable (fun y : ℝ => u₁ y / (1 + y ^ 2)))
    (hDiff : DifferentiableAt ℝ u x) (hDiff₀ : DifferentiableAt ℝ u₀ x)
    (hDiff₁ : DifferentiableAt ℝ u₁ x) (hx : u₀ x = 0)
    (hSplit : (fun y => u y - u₀ y) = u₁) :
    weightedDiskHerglotzBoundaryConjugate u x =
      (weightedDiskHerglotzIntegral u₀ (cayleyBoundaryPoint x)).im +
        weightedDiskHerglotzBoundaryConjugate u₁ x := by
  have hLim := tendsto_im_weightedDiskHerglotzIntegral_radial_of_differentiableAt hu hDiff
  have hLim₀ := tendsto_im_weightedDiskHerglotzIntegral_radial_of_differentiableAt hu₀ hDiff₀
  have hLim₁ := tendsto_im_weightedDiskHerglotzIntegral_radial_of_differentiableAt hu₁ hDiff₁
  have hAt : weightedDiskHerglotzBoundaryConjugate u₀ x =
      (weightedDiskHerglotzIntegral u₀ (cayleyBoundaryPoint x)).im := by
    simp only [weightedDiskHerglotzBoundaryConjugate, hx, sub_zero]
  rw [hAt] at hLim₀
  refine tendsto_nhds_unique hLim ((hLim₀.add hLim₁).congr' ?_)
  filter_upwards [eventually_mul_cayleyBoundaryPoint_mem_ball x] with t ht
  let w := (t : ℂ) * cayleyBoundaryPoint x
  have he := weightedDiskHerglotzIntegral_sub hu hu₀ (mem_ball_zero_iff.mp ht)
  rw [hSplit] at he
  have hi := congrArg Complex.im he
  simp only [Complex.sub_im] at hi
  change (weightedDiskHerglotzIntegral u₀ w).im + (weightedDiskHerglotzIntegral u₁ w).im =
    (weightedDiskHerglotzIntegral u w).im
  linarith only [hi]

/-- For every sufficiently small heat time there is an endpoint with
controlled conjugate value in every sufficiently large fractional
window. The radius threshold and additive bound are independent of
the heat time. -/
theorem exists_eventually_heat_conjugate_forward_endpoint
    {f : ℝ → ℝ} (hf : Integrable f) (hfCont : Continuous f) (hf₀ : f ≠ 0)
    {ε δ : ℝ} (hε : 0 < ε) (hε₁ : ε < 1) (hδ : 0 < δ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
      let T := heatFourierLaplace t f 0
      let v := weightedDiskHerglotzBoundaryConjugate (fun x : ℝ => Real.log ‖T (x : ℂ)‖)
      ∀ r ≥ R₀, ∃ x ∈ Ioo ((1 - ε) * r) r, T (x : ℂ) ≠ 0 ∧ |v x| ≤ A + δ * r := by
  obtain ⟨ρ, hρ₀, hρ₁, hρ⟩ := exists_innerDiskRadialSequence
  have hSmall : 0 < ε * δ / 8 := by positivity
  obtain ⟨R, hR, hTail⟩ := exists_eventually_angular_heat_log_tail_radial_limit
    hf hfCont hf₀ hSmall ρ hρ₁ hρ
  obtain ⟨M, hTotal⟩ := exists_eventually_integral_weighted_abs_log_heatFourierLaplace_le hf hfCont hf₀
  obtain ⟨z, d, hd, hCenter⟩ := exists_eventually_norm_heatFourierLaplace_lower_bound hf hfCont hf₀
    (s := 0) le_rfl (by simp) (y := 1) zero_lt_one
  let A := (2 * R + R⁻¹) * max M 0 / Real.pi
  let R₀ := max 1 (2 * R / (1 - ε))
  have hε' : 0 < 1 - ε := sub_pos.mpr hε₁
  refine ⟨A, by dsimp [A]; positivity, R₀, le_max_left _ _, ?_⟩
  have hTime : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  filter_upwards [hTime, hTail, hTotal, hCenter] with t ht hT hM hN
  obtain ⟨hU₁, hMass₁, v, hv, hvAt, hLim⟩ := hT
  let T := heatFourierLaplace t f 0
  let u (x : ℝ) := Real.log ‖T (x : ℂ)‖
  let S := {x : ℝ | R ≤ |x|}
  let u₁ := S.indicator u
  let u₀ (x : ℝ) := u x - u₁ x
  have hDiff := differentiable_heatFourierLaplace hf ht 0
  have hNonzero : ∃ w, T w ≠ 0 :=
    ⟨(z : ℂ) + (1 : ℂ) * Complex.I, norm_pos_iff.mp (hd.trans_le hN)⟩
  have hUMeas : Measurable u :=
    Real.measurable_log.comp ((hDiff.continuous.comp Complex.continuous_ofReal).norm.measurable)
  change Integrable (fun x : ℝ => |u x| / (1 + x ^ 2)) ∧
    (∫ x : ℝ, |u x| / (1 + x ^ 2)) ≤ M at hM
  have hNorm (x : ℝ) : ‖u x / (1 + x ^ 2)‖ = |u x| / (1 + x ^ 2) := by
    rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (by positivity : 0 ≤ 1 + x ^ 2)]
  have hu : Integrable (fun x : ℝ => u x / (1 + x ^ 2)) := by
    refine hM.1.mono' (hUMeas.div (measurable_const.add (measurable_id.pow_const _))).aestronglyMeasurable ?_
    exact ae_of_all _ fun x => (hNorm x).le
  have hU₀ : Integrable (fun x : ℝ => u₀ x / (1 + x ^ 2)) := by
    have he := hu.sub hU₁
    change Integrable (fun x : ℝ => u x / (1 + x ^ 2) - u₁ x / (1 + x ^ 2)) at he
    simpa only [← sub_div, u₀] using he
  have hTailAt (x : ℝ) (hx : R ≤ |x|) : u₁ x = u x := indicator_of_mem (show x ∈ S from hx) u
  have hCompact (x : ℝ) (hx : R ≤ |x|) : u₀ x = 0 := by simp only [u₀, hTailAt x hx, sub_self]
  have hSupp : ∀ᵐ x : ℝ, |x| ≤ R ∨ u₀ x = 0 := ae_of_all _ fun x =>
    (le_total |x| R).imp_right (hCompact x)
  have hMass₀ : (∫ x : ℝ, ‖u₀ x / (1 + x ^ 2)‖) ≤ M := by
    refine (integral_mono_ae hU₀.norm hM.1 ?_).trans hM.2
    refine ae_of_all _ fun x => ?_
    change ‖u₀ x / (1 + x ^ 2)‖ ≤ |u x| / (1 + x ^ 2)
    by_cases hx : R ≤ |x|
    · rw [hCompact x hx, zero_div, norm_zero]
      positivity
    · have h₀ : u₀ x = u x := by
        dsimp only [u₀, u₁]
        rw [indicator_of_notMem (show x ∉ S from hx), sub_zero]
      rw [h₀, hNorm]
  let E := {x : ℝ | T (x : ℂ) = 0}
  have hCount : E.Countable :=
    (countable_complex_zeros_of_entire_nonzero hDiff hNonzero).preimage Complex.ofReal_injective
  let _ : NullSingletonClass cauchyBoundaryMeasure := by
    unfold cauchyBoundaryMeasure
    infer_instance
  have hE : cauchyBoundaryMeasure E = 0 := hCount.measure_zero _
  change ∀ r ≥ R₀, ∃ x ∈ Ioo ((1 - ε) * r) r, T (x : ℂ) ≠ 0 ∧
    |weightedDiskHerglotzBoundaryConjugate u x| ≤ A + δ * r
  intro r hr
  have hr₁ : 1 ≤ r := (le_max_left _ _).trans hr
  have hWin : 2 * R ≤ (1 - ε) * r := by
    simpa only [mul_comm r (1 - ε)] using
      (div_le_iff₀ hε').mp ((le_max_right _ _).trans hr)
  obtain ⟨x, hx, hxE, hxBound⟩ := exists_fractional_window_of_small_weightedDiskHerglotz_tail
    hU₀ hU₁ hv ρ hρ₀ hρ₁ hLim hE hR hε hε₁.le hδ hr₁ hWin hSupp hMass₁
  have hxR : R < x := (by linarith only [hR] : R < 2 * R).trans (hWin.trans_lt hx.1)
  have hNear₁ : u₁ =ᶠ[𝓝 x] u := by
    filter_upwards [Ioi_mem_nhds hxR] with y hy
    exact hTailAt y ((show R < y from hy).le.trans (le_abs_self y))
  have hNear₀ : u₀ =ᶠ[𝓝 x] (fun _ => 0) := by
    filter_upwards [hNear₁] with y hy
    simp only [u₀, hy, sub_self]
  have hUdiff : DifferentiableAt ℝ u x := by
    have hTdiff : DifferentiableAt ℝ (fun y : ℝ => T (y : ℂ)) x :=
      ((hDiff (x : ℂ)).restrictScalars ℝ).comp x Complex.ofRealCLM.differentiableAt
    exact (hTdiff.norm ℂ hxE).log (norm_ne_zero_iff.mpr hxE)
  have hSplit : (fun y => u y - u₀ y) = u₁ := by
    funext y
    exact sub_sub_cancel (u y) (u₁ y)
  have hV := weightedBoundaryConjugate_eq_compact_add_tail hu hU₀ hU₁ hUdiff
    ((differentiableAt_const (0 : ℝ)).congr_of_eventuallyEq hNear₀)
    (hUdiff.congr_of_eventuallyEq hNear₁) hNear₀.eq_of_nhds hSplit
  refine ⟨x, hx, hxE, ?_⟩
  rw [hV, ← hvAt]
  refine hxBound.trans (add_le_add ?_ le_rfl)
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (hMass₀.trans (le_max_left _ _)) (by positivity)) Real.pi_pos.le

/-- The heated density has at least any strictly subcritical rate of
alternations on the positive ray. The radius threshold and the
positive proportional left endpoint are uniform for small heat times. -/
theorem exists_eventually_heatSignAlternations_positive_ray_of_gap
    {f : ℝ → ℝ} (hf : Integrable f) (hfCont : Continuous f) (hf₀ : f ≠ 0)
    {s : ℝ} (hs : 0 < s)
    (hGap : EqOn (𝓕 (fun x : ℝ => (f x : ℂ))) 0 (Ioo (-s) s))
    {c : ℝ} (hc : c < 2 * s) :
    ∃ κ : ℝ, 0 < κ ∧ ∃ R₁ : ℝ, ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
      ∀ r ≥ R₁, ∃ n : ℕ, c * r ≤ (n : ℝ) ∧
        HasSignAlternations (realGaussianSmoothing t f) (Icc (κ * r) r) n := by
  obtain ⟨d, hd, hds⟩ := exists_between (max_lt (show (0 : ℝ) < 2 * s by positivity) hc)
  have hdPos : 0 < d := (le_max_left _ _).trans_lt hd
  have hcd : c < d := (le_max_right _ _).trans_lt hd
  let loss := 2 * s - d
  have hLoss : 0 < loss := sub_pos.mpr hds
  let ε := loss / (8 * s)
  let δ := loss * Real.pi / 8
  let κ := (1 - ε) * ε
  let μ := loss * Real.pi / 4
  have hε : 0 < ε := div_pos hLoss (by positivity)
  have hεQuarter : ε < 1 / 4 :=
    (div_lt_iff₀ (by positivity : 0 < 8 * s)).mpr (by dsimp [loss]; linarith only [hdPos])
  have hε₁ : ε < 1 := by linarith only [hεQuarter]
  have hδ : 0 < δ := div_pos (mul_pos hLoss Real.pi_pos) (by norm_num)
  have hκ : 0 < κ := mul_pos (sub_pos.mpr hε₁) hε
  have hμ : 0 < μ := div_pos (mul_pos hLoss Real.pi_pos) (by norm_num)
  obtain ⟨A, _, R₀, hR₀, hEndpoints⟩ :=
    exists_eventually_heat_conjugate_forward_endpoint hf hfCont hf₀ hε hε₁ hδ
  obtain ⟨b, hb, hHeat⟩ := exists_eventually_heatSignAlternations_of_boundary_conjugate hf hfCont hf₀ hs.le hGap
  let R₁ := max (R₀ / ε) ((2 * A + 2 * Real.pi + 1) / μ)
  refine ⟨κ, hκ, R₁, ?_⟩
  filter_upwards [hEndpoints, hHeat] with t hEnd hAlt
  let T := heatFourierLaplace t f 0
  let v := weightedDiskHerglotzBoundaryConjugate (fun x : ℝ => Real.log ‖T (x : ℂ)‖)
  change ∀ r ≥ R₁, ∃ n : ℕ, c * r ≤ (n : ℝ) ∧
    HasSignAlternations (realGaussianSmoothing t f) (Icc (κ * r) r) n
  intro r hr
  have hR₀ε : R₀ ≤ ε * r := by
    rw [mul_comm]
    exact (div_le_iff₀ hε).mp ((le_max_left _ _).trans hr)
  have hrPos : 0 < r := (div_pos (zero_lt_one.trans_le hR₀) hε).trans_le ((le_max_left _ _).trans hr)
  have hεr : ε * r ≤ r := mul_le_of_le_one_left hrPos.le hε₁.le
  have hR₀r : R₀ ≤ r := hR₀ε.trans hεr
  obtain ⟨l, hl, hTl, hVl⟩ := hEnd (ε * r) hR₀ε
  obtain ⟨q, hq, hTq, hVq⟩ := hEnd r hR₀r
  have hWidth : (1 - 2 * ε) * r < q - l := by
    linarith only [hl.2, hq.1]
  have hWidthNonneg : 0 ≤ (1 - 2 * ε) * r :=
    mul_nonneg (by linarith only [hεQuarter]) hrPos.le
  have hlq : l < q := sub_pos.mp (hWidthNonneg.trans_lt hWidth)
  have hGain : (2 * Real.pi * s) * ((1 - 2 * ε) * r) ≤ (2 * Real.pi * b) * (q - l) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hb (by positivity)) hWidth.le hWidthNonneg
      (mul_nonneg (by positivity) (hs.le.trans hb))
  have hConj : -(2 * A + 2 * δ * r) ≤ v q - v l := by
    have hRight : -(A + δ * r) ≤ v q := (abs_le.mp hVq).1
    have hLeft : v l ≤ A + δ * (ε * r) := (abs_le.mp hVl).2
    linarith only [hRight, hLeft, mul_le_mul_of_nonneg_left hεr hδ.le]
  have hεId : 8 * s * ε = loss := by
    dsimp only [ε]
    field_simp [hs.ne']
  have hδId : 8 * δ = loss * Real.pi := by
    dsimp only [δ]
    ring
  have hBudget : (2 * Real.pi * s) * ((1 - 2 * ε) * r) - 2 * δ * r =
      d * r * Real.pi + μ * r := calc
    _ = (2 * s * Real.pi - (8 * s * ε) * Real.pi / 2 - (8 * δ) / 4) * r := by ring
    _ = _ := by
      rw [hεId, hδId]
      dsimp only [μ, loss]
      ring
  have hMargin : 2 * A + 2 * Real.pi + 1 ≤ r * μ :=
    (div_le_iff₀ hμ).mp ((le_max_right _ _).trans hr)
  let n := ⌈d * r⌉₊
  have hN : ((n : ℝ) + 1) * Real.pi < (d * r + 2) * Real.pi := by
    apply mul_lt_mul_of_pos_right _ Real.pi_pos
    have hdN := Nat.ceil_lt_add_one (mul_nonneg hdPos.le hrPos.le)
    change (n : ℝ) < d * r + 1 at hdN
    linarith only [hdN]
  have hInc : ((n : ℝ) + 1) * Real.pi < (2 * Real.pi * b) * (q - l) + (v q - v l) :=
    hN.trans (by linarith only [hGain, hConj, hBudget, hMargin])
  have hSign := hAlt hlq hTl hTq (n := n) hInc
  have hLeft : κ * r ≤ l := by
    change (1 - ε) * ε * r ≤ l
    rw [mul_assoc]
    exact hl.1.le
  refine ⟨n, (mul_le_mul_of_nonneg_right hcd.le hrPos.le).trans (Nat.le_ceil _), ?_⟩
  exact hSign.mono (Icc_subset_Icc hLeft hq.2.le)

end
end MeyerGeneralProblem
