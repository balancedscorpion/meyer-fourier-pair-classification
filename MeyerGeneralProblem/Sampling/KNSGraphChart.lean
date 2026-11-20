module

public import MeyerGeneralProblem.Sampling.KNSGraphSmoothApproximation
public import MeyerGeneralProblem.Sampling.SignedSquareChartBounds
public import MeyerGeneralProblem.Sampling.SignedSquareFiniteChart
public import MeyerGeneralProblem.Sampling.L2LimitBound

@[expose] public section

/-!
# Actual bounded cutoff charts of every KNS graph input

Explicit Gaussian graph approximation, finite classical derivative identities
and quantitative Fatou passage identify the actual chart of every graph input.
The constant is fixed before the vector, ray sign and derivative index. This
is not yet original-prefix sampling, coercivity, deformation or the phase diagram.
-/

namespace MeyerGeneralProblem.KNSGraphChart
noncomputable section
open MeasureTheory Filter KNSGraphRegularization KNSGraphSmoothApproximation
open scoped ContDiff Topology
/-- The actual signed-square cutoff chart of every original graph input has
all permitted classical derivatives in L2 with one fixed same-order graph
bound. The constant is chosen before the input, sign and derivative index. -/
theorem exists_graph_chart_bound (q k : ℕ) (hq : q+1≤k) {R : ℝ} (hR : 2≤R) :
    ∃ C > 0, ∀ v : KNSGraphSpace k, ∀ ε : ℝ, ε^2=1 →
      ContDiff ℝ q (signedSquareCutoffChart k R ε (KNSGraphSpace.representative k v)) ∧
      ∀ j≤q, ∃ hJ : MemLp (iteratedDeriv j
        (signedSquareCutoffChart k R ε (KNSGraphSpace.representative k v))) 2,
        ‖hJ.toLp‖^2 ≤ C*‖v‖^2 := by
  obtain ⟨C, hC, hc⟩ := SignedSquareSmoothGraphBounds.exists_smooth_chart_graph_bound k hR
  refine ⟨C, hC, ?_⟩
  intro v ε hε
  have hk : 1≤k := by omega
  have hr : 1<R := by linarith
  have hrep := SignedSquareFiniteChart.representative_contDiff hq v
  have hchart := SignedSquareFiniteChart.cutoff_contDiff k q hr ε hrep
  refine ⟨hchart, ?_⟩
  intro j hj
  let U : ℕ → ℝ → ℂ := fun N => iteratedDeriv j
    (signedSquareCutoffChart k R ε
      (KNSGraphSpace.representative k (gaussianRegularized N v)))
  have hUN (N : ℕ) : ∃ hJ : MemLp (U N) 2,
      ‖hJ.toLp‖^2 ≤ C*‖gaussianRegularized N v‖^2 := by
    obtain ⟨hJ, hbJ⟩ := hc ε hε
      (KNSGraphSpace.representative k (gaussianRegularized N v))
      (gaussianRegularized_smooth N v) (regularized_memLp hk N v)
      (regularized_weight_memLp hk N v) (regularized_iteratedDeriv_memLp N v k)
      j (by omega)
    rw [ofSmooth_regularized_eq hk] at hbJ
    exact ⟨hJ, hbJ⟩
  have hU : ∀ N, MemLp (U N) 2 := fun N => (hUN N).choose
  have hUn : ∀ N, ‖(hU N).toLp‖^2 ≤ C*‖gaussianRegularized N v‖^2 :=
    fun N => (hUN N).choose_spec
  have hlim : ∀ᵐ x, Tendsto (fun N => U N x) atTop
      (𝓝 (iteratedDeriv j
        (signedSquareCutoffChart k R ε (KNSGraphSpace.representative k v)) x)) := by
    filter_upwards [] with x
    exact SignedSquareFiniteChart.cutoff_derivative_tendsto k q hr ε hrep
      (fun N => (gaussianRegularized_smooth N v).of_le (by simp))
      (fun i hi y => regularized_iteratedDeriv_tendsto v i (by omega) y) j hj x
  exact L2LimitBound.exists_memLp_sq_le_of_tendsto hU
    (hchart.continuous_iteratedDeriv j (by exact_mod_cast hj)).aestronglyMeasurable
    hC.le (norm_nonneg v) (fun _ => norm_nonneg _)
    (gaussianRegularized_tendsto v).norm hUn hlim
end
end MeyerGeneralProblem.KNSGraphChart
