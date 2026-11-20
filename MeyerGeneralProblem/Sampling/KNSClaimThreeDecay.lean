module

public import MeyerGeneralProblem.Sampling.KNSOpenSector
public import MeyerGeneralProblem.Sampling.KNSMovingZeroCounts
public import MeyerGeneralProblem.Sampling.KNSLocalJensen

@[expose] public section

/-!
# One-sided scaled Claim 3 from actual eventual-gap zeros

A strictly interior moving disk supplies the analytic neighborhood and actual
boundary growth needed by local Jensen. The selected zeros and logarithmic
lower bound are constructed from the whole eventual-gap sequence. Independent
gap and zero cutoffs affect only the starting center, not the negative rate.
This does not yet produce the square-root/Phragmén–Lindelöf growth hypothesis.
-/

noncomputable section

open Set Filter
open scoped BigOperators

namespace MeyerGeneralProblem

private theorem selectedZeroProduct_eq_exp_neg_log_sum
    {r x : ℝ} (hr : 0 < r) (Z : Finset ℝ) (hne : ∀ y ∈ Z, y ≠ x) :
    (∏ y ∈ Z, |x - y| / r) =
      Real.exp (-(∑ y ∈ Z, Real.log (r / |y - x|))) := by
  rw [← Finset.sum_neg_distrib, Real.exp_sum]
  apply Finset.prod_congr rfl
  intro y hy
  have hd : 0 < |y - x| := abs_pos.mpr (sub_ne_zero.mpr (hne y hy))
  rw [Real.exp_neg, Real.exp_log (div_pos hr hd), inv_div, abs_sub_comm x y]

/-- Actual right-half-plane analyticity, eventual sector growth and actual
eventual-gap zeros imply a one-sided exponential bound with strictly negative
rate. The two independent exceptional prefixes and the radial growth threshold
enter only the starting center. No moving count/log certificate, sector
principle, symmetry or optimal-rate attainment is assumed. -/
theorem exists_eventual_exp_decay_of_sectorGrowth_eventualGapZeros
    {H : ℂ → ℂ} {z : ℕ → ℝ} {ell d a α s M Rg : ℝ}
    (hell : 0 < ell) (hd0 : 0 < d) (hdell : d < ell⁻¹)
    (ha0 : 0 ≤ a) (had : a < d)
    (hα0 : 0 < α) (hαhalf : α < Real.pi / 2)
    (hs0 : 0 < s) (hs1 : s < 1)
    (hsSector : s * (Real.sin α + Real.cos α) < Real.sin α)
    (hM : 1 ≤ M) (hRg : 0 ≤ Rg)
    (hAnalytic : AnalyticOnNhd ℂ H {w : ℂ | 0 < w.re})
    (hGrowth : ∀ w ∈ knsOpenSector α, Rg ≤ ‖w‖ →
      ‖H w‖ ≤ M * Real.exp (a * Real.pi * |w.im|))
    (hzmono : StrictMono z) (hztop : Tendsto z atTop atTop)
    (Ngap Nzero : ℕ)
    (hgap : ∀ n ≥ Ngap, z (n + 1) - z n ≤ ell)
    (hzero : ∀ n ≥ Nzero, H (z n : ℂ) = 0) :
    let r0 := (ell⁻¹ - d)⁻¹
    ∃ X0 > (0 : ℝ), ∀ (x : ℝ), x ≥ X0 →
      ‖H (x : ℂ)‖ ≤ M * Real.exp (2 * d * r0) *
        Real.exp (-2 * (d - a) * s * x) := by
  classical
  dsimp only
  have hrate : 0 < 2 * (d - a) * s :=
    mul_pos (mul_pos (by norm_num) (sub_pos.mpr had)) hs0
  obtain ⟨Xc, hXc, hselect⟩ :=
    exists_movingOpenZeroFinset_log_sum_ge_of_eventual_gap
      hzmono hztop hell hd0 hdell hs0 hs1 (max Ngap Nzero)
      (fun n hn => hgap n ((le_max_left _ _).trans hn))
  have h1s : 0 < 1 - s := sub_pos.mpr hs1
  let X0 : ℝ := Xc + Rg / (1 - s)
  have hquot : 0 ≤ Rg / (1 - s) := div_nonneg hRg h1s.le
  have hX0 : 0 < X0 := add_pos_of_pos_of_nonneg hXc hquot
  refine ⟨X0, hX0, ?_⟩
  intro x hx
  have hx0 : 0 < x := hX0.trans_le hx
  have hxC : Xc ≤ x := by dsimp [X0] at hx; linarith
  have hxRg : Rg ≤ (1 - s) * x := by
    have hdiv : Rg / (1 - s) ≤ x := by dsimp [X0] at hx; linarith
    have := (div_le_iff₀ h1s).mp hdiv
    nlinarith
  by_cases hxzero : H (x : ℂ) = 0
  · rw [hxzero, norm_zero]
    exact mul_nonneg (mul_nonneg (by linarith) (Real.exp_pos _).le) (Real.exp_pos _).le
  obtain ⟨Z, hrR, hZ, hlog⟩ := hselect x hxC
  have hr : 0 < s * x := mul_pos hs0 hx0
  have hlocal : AnalyticOnNhd ℂ H (Metric.closedBall (x : ℂ) (s * x)) :=
    hAnalytic.mono (closedBall_realCenter_subset_rightHalfPlane hx0 hs1)
  have hboundary : ∀ w ∈ Metric.sphere (x : ℂ) (s * x),
      ‖H w‖ ≤ M * Real.exp (a * Real.pi * |w.im|) := by
    intro w hw
    have hdisk : w ∈ Metric.closedBall (x : ℂ) (s * x) :=
      Metric.sphere_subset_closedBall hw
    exact hGrowth w
      (closedBall_realCenter_subset_knsOpenSector hα0 hαhalf hx0 hsSector hdisk)
      (hxRg.trans (realCenter_closedBall_norm_lower_bound hdisk))
  have hzeros : ∀ y ∈ Z, H (y : ℂ) = 0 := by
    intro y hy
    obtain ⟨n, hn, rfl, hinner, hne⟩ := (hZ y).mp hy
    exact hzero n ((le_max_right _ _).trans hn)
  have hinside : ∀ y ∈ Z, |y - x| < s * x := by
    intro y hy
    obtain ⟨n, hn, heq, hinner, hne⟩ := (hZ y).mp hy
    exact hinner
  have hne : ∀ y ∈ Z, y ≠ x := by
    intro y hy
    obtain ⟨n, hn, heq, hinner, hne⟩ := (hZ y).mp hy
    exact hne
  have hJ := norm_center_le_sectorGrowth_mul_selectedZeroProduct hr ha0 hM
    hlocal hboundary Z hzeros hinside
  rw [selectedZeroProduct_eq_exp_neg_log_sum hr Z hne] at hJ
  have hprod := Real.exp_le_exp.mpr (neg_le_neg hlog)
  have hfactor : 0 ≤ M * Real.exp (2 * a * (s * x)) :=
    mul_nonneg (by linarith) (Real.exp_pos _).le
  have hbound := hJ.trans (mul_le_mul_of_nonneg_left hprod hfactor)
  calc
    ‖H (x : ℂ)‖ ≤ M * Real.exp (2 * a * (s * x)) *
        Real.exp (-(2 * d * (s * x - (ell⁻¹ - d)⁻¹))) := hbound
    _ = M * Real.exp (2 * d * (ell⁻¹ - d)⁻¹) *
        Real.exp (-2 * (d - a) * s * x) := by
      simp only [mul_assoc, ← Real.exp_add]
      congr 2
      ring

end MeyerGeneralProblem
