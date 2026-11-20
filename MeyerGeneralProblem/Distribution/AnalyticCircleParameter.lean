module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.Topology.UniformSpace.HeineCantor

@[expose] public section

/-!
# Analytic dependence of a circle integral on a complex parameter

A jointly continuous parameter derivative on a fixed boundary circle
is uniformly bounded on each compact parameter disk. This allows
differentiation under the actual circle integral.
-/

namespace MeyerGeneralProblem

noncomputable section

open Complex Filter MeasureTheory Metric Set
open scoped Topology Interval

/-- Integrating over a fixed circle preserves continuity in a parameter
when the integrand is jointly continuous on that circle. -/
theorem circleIntegral_continuousOn_of_continuous_parameter
    {E : Type*} [TopologicalSpace E] [FirstCountableTopology E]
    (D : Set E) (c : ℂ) (r : ℝ) (hr : 0 ≤ r) (F : E → ℂ → ℂ)
    (hF : ContinuousOn (fun v : E × ℂ => F v.1 v.2) (D ×ˢ sphere c r)) :
    ContinuousOn (fun u => ∮ w in C(c, r), F u w) D := by
  intro u hu
  have hunif : TendstoUniformlyOn F (F u) (𝓝[D] u) (sphere c r) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    obtain ⟨V, hV, hdist⟩ := (isCompact_sphere c r).mem_uniformity_of_prod
      (f := F) hF hu (dist_mem_uniformity hε)
    filter_upwards [hV] with y hy
    intro w hw
    rw [dist_comm]
    exact hdist y hy w hw
  apply hunif.tendsto_circleIntegral_of_continuousOn hr
  filter_upwards [self_mem_nhdsWithin] with u hu
  exact hF.comp (continuous_const.prodMk continuous_id).continuousOn
    (fun w hw => ⟨hu, hw⟩)

set_option maxHeartbeats 750000 in
/-- A circle integral depends analytically on a scalar complex parameter
when the integrand and its parameter derivative are jointly continuous
on the parameter region times the circle. -/
theorem circleIntegral_analyticOnNhd_of_continuous_parameter_derivative
    (U : Set ℂ) (hU : IsOpen U) (c : ℂ) (r : ℝ) (hr : 0 < r)
    (f f' : ℂ → ℂ → ℂ)
    (hf : ContinuousOn (fun y : ℂ × ℂ => f y.1 y.2) (U ×ˢ sphere c r))
    (hf' : ContinuousOn (fun y : ℂ × ℂ => f' y.1 y.2) (U ×ˢ sphere c r))
    (hder : ∀ x ∈ U, ∀ z ∈ sphere c r, HasDerivAt (fun y => f y z) (f' x z) x) :
    AnalyticOnNhd ℂ (fun x => ∮ z in C(c, r), f x z) U := by
  apply DifferentiableOn.analyticOnNhd _ hU
  intro x hx
  let A := uIcc (0 : ℝ) (2 * Real.pi)
  let γ := circleMap c r
  let τ (t : ℝ) := circleMap 0 r t * Complex.I
  let F (x : ℂ) (t : ℝ) := τ t * f x (γ t)
  let G (x : ℂ) (t : ℝ) := τ t * f' x (γ t)
  have hγ : Continuous γ := continuous_circleMap _ _
  have hτ : Continuous τ := (continuous_circleMap _ _).mul continuous_const
  have hγimage (t : ℝ) : γ t ∈ sphere c r := by
    rw [← abs_of_pos hr, ← range_circleMap]
    exact mem_range_self t
  have hmap : MapsTo (fun v : ℂ × ℝ => (v.1, γ v.2)) (U ×ˢ A) (U ×ˢ sphere c r) :=
    fun v hv => ⟨hv.1, hγimage _⟩
  have hc : ContinuousOn (fun v : ℂ × ℝ => F v.1 v.2) (U ×ˢ A) :=
    (hτ.comp continuous_snd).continuousOn.mul
      (hf.comp (continuous_fst.prodMk (hγ.comp continuous_snd)).continuousOn hmap)
  have hc' : ContinuousOn (fun v : ℂ × ℝ => G v.1 v.2) (U ×ˢ A) :=
    (hτ.comp continuous_snd).continuousOn.mul
      (hf'.comp (continuous_fst.prodMk (hγ.comp continuous_snd)).continuousOn hmap)
  have hcont_section (y : ℂ) : Continuous (fun t : ℝ => (y, t)) :=
    continuous_const.prodMk continuous_id
  have hmap_section (y : ℂ) (hy : y ∈ U) : MapsTo (fun t : ℝ => (y, t)) A (U ×ˢ A) :=
    fun _ ht => ⟨hy, ht⟩
  have hFint (y : ℂ) (hy : y ∈ U) : IntervalIntegrable (F y) volume 0 (2 * Real.pi) :=
    (hc.comp (hcont_section y).continuousOn (hmap_section y hy)).intervalIntegrable
  have hGint : IntervalIntegrable (G x) volume 0 (2 * Real.pi) :=
    (hc'.comp (hcont_section x).continuousOn (hmap_section x hx)).intervalIntegrable
  obtain ⟨ρ, hρ, hsub⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx)
  let R := ρ / 2
  have hR : 0 < R := by dsimp [R]; positivity
  have hRρ : R < ρ := by dsimp [R]; linarith
  have hclosed : closedBall x R ⊆ U := closedBall_subset_ball hRρ |>.trans hsub
  have hsmall : ball x R ⊆ U := ball_subset_closedBall.trans hclosed
  have hCompact : IsCompact (closedBall x R ×ˢ A) :=
    (isCompact_closedBall x R).prod (by dsimp [A]; exact isCompact_uIcc)
  have hcG : ContinuousOn (fun v : ℂ × ℝ => G v.1 v.2) (closedBall x R ×ˢ A) :=
    hc'.mono (Set.prod_mono hclosed Subset.rfl)
  obtain ⟨C, hC⟩ := hCompact.exists_bound_of_continuousOn hcG
  have hFmeas : ∀ᶠ y in 𝓝 x, AEStronglyMeasurable (F y)
      (volume.restrict (uIoc 0 (2 * Real.pi))) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact (intervalIntegrable_iff.mp (hFint y hy)).aestronglyMeasurable
  have hGmeas : AEStronglyMeasurable (G x) (volume.restrict (uIoc 0 (2 * Real.pi))) :=
    (intervalIntegrable_iff.mp hGint).aestronglyMeasurable
  have hbound : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ uIoc 0 (2 * Real.pi) →
      ∀ y ∈ ball x R, ‖G y t‖ ≤ C := ae_of_all _ fun t ht y hy =>
    hC (y, t) ⟨ball_subset_closedBall hy, uIoc_subset_uIcc ht⟩
  have hdiff : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ uIoc 0 (2 * Real.pi) →
      ∀ y ∈ ball x R, HasDerivAt (fun z => F z t) (G y t) y :=
    ae_of_all _ fun t _ y hy => (hder y (hsmall hy) (γ t) (hγimage t)).const_mul (τ t)
  have hInt := (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (ball_mem_nhds x hR) hFmeas (hFint x hx) hGmeas hbound intervalIntegrable_const hdiff).2
  simpa only [circleIntegral, deriv_circleMap, smul_eq_mul, F, τ, γ] using
    hInt.differentiableAt.differentiableWithinAt (s := U)

end

end MeyerGeneralProblem
