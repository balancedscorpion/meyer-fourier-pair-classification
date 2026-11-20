module

public import MeyerGeneralProblem.Distribution.GaussianHeatEquation

@[expose] public section

/-!
# Initial values for Gaussian heat flow

At a continuity point, the local bounded part of an integrable density
converges to the initial value. The separated integrable remainder
contributes a joint zero limit.
-/

namespace MeyerGeneralProblem

noncomputable section

open Filter MeasureTheory Set
open scoped Topology

/-- Gaussian smoothing of an integrable density converges to its value
at every continuity point, jointly in positive time and position. -/
theorem tendsto_realGaussianSmoothing_initial_of_integrable
    {f : ℝ → ℝ} (hf : Integrable f volume) (y : ℝ) (hy : ContinuousAt f y) :
    Tendsto (fun p : ℝ × ℝ => realGaussianSmoothing p.1 f p.2)
      (𝓝[Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)] (0, y)) (𝓝 (f y)) := by
  have hLocal : ∀ᶠ x in 𝓝 y, f x ∈ Metric.ball (f y) 1 :=
    hy.tendsto.eventually (Metric.ball_mem_nhds _ zero_lt_one)
  obtain ⟨δ, hδ, hBall⟩ := Metric.mem_nhds_iff.mp hLocal
  let B := Metric.ball y δ
  let g := B.indicator f
  let h := Bᶜ.indicator f
  have hM : MeasurableSet B := Metric.isOpen_ball.measurableSet
  have hg : Integrable g := hf.indicator hM
  have hh : Integrable h := hf.indicator hM.compl
  have hgy : g y = f y := indicator_of_mem (Metric.mem_ball_self hδ) _
  have hgc : ContinuousAt g y := by
    apply hy.congr_of_eventuallyEq
    filter_upwards [Metric.ball_mem_nhds y hδ] with x hx
    exact indicator_of_mem hx _
  have hBound (x : ℝ) : ‖g x‖ ≤ ‖f y‖ + 1 := by
    by_cases hx : x ∈ B
    · have hDiff : ‖f x - f y‖ < 1 := by
        simpa only [mem_ofPred_eq, Metric.mem_ball, dist_eq_norm] using hBall hx
      rw [show g x = f x from indicator_of_mem hx _]
      calc
        ‖f x‖ = ‖(f x - f y) + f y‖ := by rw [sub_add_cancel]
        _ ≤ ‖f x - f y‖ + ‖f y‖ := norm_add_le _ _
        _ ≤ _ := by linarith
    · rw [show g x = 0 from indicator_of_notMem hx _, norm_zero]
      positivity
  have hTail : ∀ᵐ x : ℝ ∂volume, |x - y| < δ → h x = 0 := by
    filter_upwards with x hx
    exact indicator_of_notMem (show x ∉ Bᶜ from fun hn =>
      hn (by simpa only [B, Metric.mem_ball, Real.dist_eq] using hx)) _
  have hAdd (x : ℝ) : f x = g x + h x := by
    by_cases hx : x ∈ B
    · rw [show g x = f x from indicator_of_mem hx _,
        show h x = 0 from indicator_of_notMem (show x ∉ Bᶜ from fun hn => hn hx) _, add_zero]
    · rw [show g x = 0 from indicator_of_notMem hx _,
        show h x = f x from indicator_of_mem (show x ∈ Bᶜ from hx) _, zero_add]
  have hG := tendsto_realGaussianSmoothing_initial_of_bounded_integrable hg hBound y hgc
  rw [hgy] at hG
  have hH := tendsto_realGaussianSmoothing_zero_of_ae_zero_near hh hδ y hTail
  have hSum := hG.add hH
  rw [add_zero] at hSum
  refine hSum.congr' ?_
  filter_upwards [self_mem_nhdsWithin (s := Ioi (0 : ℝ) ×ˢ (univ : Set ℝ))] with p hp
  rw [← realGaussianSmoothing_fun_add hg hh hp.1, ← funext hAdd]

end
end MeyerGeneralProblem
