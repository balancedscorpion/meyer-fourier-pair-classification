module

public import MeyerGeneralProblem.Sampling.KNSGraphRegularization
public import MeyerGeneralProblem.Sampling.KNSGraphSpaceSmooth

@[expose] public section

/-!
# Actual smooth graph approximants and finite derivative limits

Every Gaussian-regularized representative has all actual derivatives in L2,
and its production smooth lift is exactly the regularized graph. Original
representative derivatives converge pointwise strictly below the graph order.
There is no classical top-derivative assumption on an arbitrary graph input.
-/

namespace MeyerGeneralProblem.KNSGraphSmoothApproximation
noncomputable section
open MeyerGeneralProblem MeasureTheory GaussianDamping KNSGraphRegularization
open scoped FourierTransform Topology ContDiff

/-- Every Gaussian-damped L2 input has all actual polynomial L2 moments. -/
theorem damped_power_memLp (N : ℕ) (q : KNSL2) (j : ℕ) :
    MemLp (fun x : ℝ => (x : ℂ)^j * (gaussianCutoff N x * q x)) 2 := by
  have h := mulSchwartz_memLp
    (SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => (x : ℂ)^j) (gaussianCutoff N)) q
  convert h using 1
  funext x
  simp only [SchwartzMap.smulLeftCLM_apply_apply (by fun_prop :
    (fun x : ℝ => (x : ℂ)^j).HasTemperateGrowth), smul_eq_mul]
  ring

/-- Every actual classical derivative of the regularized representative lies in L2.
No top classical derivative premise is imposed on the original graph input. -/
theorem regularized_iteratedDeriv_memLp {k : ℕ} (N : ℕ) (v : KNSGraphSpace k) (j : ℕ) :
    MemLp (iteratedDeriv j (KNSGraphSpace.representative k (gaussianRegularized N v))) 2 := by
  let G : ℝ → ℂ := fun x => gaussianCutoff N x * KNSGraphSpace.frequency k v x
  have hm : ∀ i ≤ j, Integrable (fun x : ℝ => x^i • G x) :=
    fun i _hi => damped_integrable_moment N (KNSGraphSpace.frequency k v) i
  have hM := memLp_fourierDerivativeData_of_physical_power j
    (damped_power_memLp N (KNSGraphSpace.frequency k v) j)
  obtain ⟨hD, _⟩ := memLp_iteratedDeriv_fourier_of_integrable_moments_le hm le_rfl hM
  have hneg := (hD.comp_measurePreserving
    (Measure.measurePreserving_neg (volume : Measure ℝ))).const_smul ((-1 : ℝ)^j)
  rw [representative_gaussianRegularized]
  have he : (𝓕⁻ G : ℝ → ℂ) = fun x => (𝓕 G : ℝ → ℂ) (-x) := by
    funext x
    exact Real.fourierInv_eq_fourier_neg G x
  change MemLp (iteratedDeriv j (𝓕⁻ G)) 2
  rw [he]
  convert hneg using 1
  funext x
  exact iteratedDeriv_comp_neg j (𝓕 G : ℝ → ℂ) x

/-- The regularized representative has the actual physical L2 membership. -/
theorem regularized_memLp {k : ℕ} (hk : 1 ≤ k) (N : ℕ) (v : KNSGraphSpace k) :
    MemLp (KNSGraphSpace.representative k (gaussianRegularized N v)) 2 :=
  (memLp_congr_ae (KNSGraphSpace.representative_ae hk _)).mpr (Lp.memLp _)

/-- Its original kth physical power weight is L2, from the proved same-order graph. -/
theorem regularized_weight_memLp {k : ℕ} (hk : 1 ≤ k) (N : ℕ) (v : KNSGraphSpace k) :
    MemLp (fun x : ℝ => (x : ℂ)^k *
      KNSGraphSpace.representative k (gaussianRegularized N v) x) 2 := by
  apply (memLp_congr_ae ?_).mpr (KNSGraphSpace.memLp_physicalWeight (gaussianRegularized N v))
  filter_upwards [KNSGraphSpace.representative_ae hk (gaussianRegularized N v)] with x hx
  rw [hx]

/-- The production smooth adapter is exactly the actual regularized graph element,
not merely a graph with a comparable norm. -/
theorem ofSmooth_regularized_eq {k : ℕ} (hk : 1 ≤ k) (N : ℕ) (v : KNSGraphSpace k) :
    KNSGraphSpace.ofSmooth k (gaussianRegularized_smooth N v)
      (regularized_memLp hk N v) (regularized_weight_memLp hk N v)
      (regularized_iteratedDeriv_memLp N v k) = gaussianRegularized N v := by
  apply KNSGraphSpace.physical_injective k
  rw [KNSGraphSpace.physical_ofSmooth]
  apply Lp.ext
  exact (regularized_memLp hk N v).coeFn_toLp.trans
    (KNSGraphSpace.representative_ae hk (gaussianRegularized N v))

/-- In particular the production smooth graph norm is the same original graph norm. -/
theorem norm_ofSmooth_regularized {k : ℕ} (hk : 1 ≤ k) (N : ℕ) (v : KNSGraphSpace k) :
    ‖KNSGraphSpace.ofSmooth k (gaussianRegularized_smooth N v)
      (regularized_memLp hk N v) (regularized_weight_memLp hk N v)
      (regularized_iteratedDeriv_memLp N v k)‖ = ‖gaussianRegularized N v‖ := by
  rw [ofSmooth_regularized_eq hk]

end
end MeyerGeneralProblem.KNSGraphSmoothApproximation

namespace MeyerGeneralProblem.KNSGraphSmoothApproximation
noncomputable section
open MeyerGeneralProblem MeasureTheory GaussianDamping KNSGraphRegularization Filter
open scoped FourierTransform Topology ContDiff

/-- Gaussian damping converges inside the genuine Fourier integral of each L1 input. -/
theorem fourier_gaussian_tendsto {G : ℝ → ℂ} (hG : Integrable G) (x : ℝ) :
    Tendsto (fun N => (𝓕 (fun ξ => gaussianCutoff N ξ * G ξ) : ℝ → ℂ) x)
      atTop (𝓝 ((𝓕 G : ℝ → ℂ) x)) := by
  have hN (N : ℕ) : Integrable (fun ξ => gaussianCutoff N ξ * G ξ) := by
    apply hG.norm.mono'
      ((gaussianCutoff N).continuous.aestronglyMeasurable.mul hG.aestronglyMeasurable)
    filter_upwards [] with ξ
    rw [Pi.mul_apply, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (gaussianCutoff_norm_le_one N ξ)
  simp only [Real.fourier_eq]
  apply tendsto_integral_of_dominated_convergence (fun ξ => ‖G ξ‖)
    (fun N => ((Real.fourierIntegral_convergent_iff x).mpr (hN N)).aestronglyMeasurable) hG.norm
  · intro N
    filter_upwards [] with ξ
    rw [Circle.norm_smul, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (gaussianCutoff_norm_le_one N ξ)
  · filter_upwards [] with ξ
    simpa only [one_mul] using ((gaussianCutoff_tendsto ξ).mul_const (G ξ)).const_smul
      (Real.fourierChar (-inner ℝ ξ x))

/-- The original frequency coordinate has every integrable moment strictly below k. -/
theorem frequency_moment_integrable {k : ℕ} (v : KNSGraphSpace k) (j : ℕ) (hj : j < k) :
    Integrable (fun ξ : ℝ => ξ^j • KNSGraphSpace.frequency k v ξ) := by
  apply integrable_real_moment_of_fourierSobolev (Lp.memLp _)
    (memLp_fourierDerivativeData_of_physical_power k
      ((memLp_congr_ae (KNSGraphSpace.frequencyWeight_ae v)).mpr (Lp.memLp _))) hj

/-- Actual original representative derivatives below the graph order have the
reflected Fourier-integral formula with the genuine (-1)^j factor. -/
theorem representative_iteratedDeriv_formula {k : ℕ} (v : KNSGraphSpace k)
    (j : ℕ) (hj : j < k) (x : ℝ) :
    iteratedDeriv j (KNSGraphSpace.representative k v) x =
      (-1 : ℝ)^j • (𝓕 (fourierDerivativeData j
        (KNSGraphSpace.frequency k v : ℝ → ℂ)) : ℝ → ℂ) (-x) := by
  change iteratedDeriv j (fun y => (𝓕 (KNSGraphSpace.frequency k v : ℝ → ℂ)) (-y)) x = _
  rw [iteratedDeriv_comp_neg]
  have hm : ∀ i ≤ j, Integrable (fun ξ : ℝ => ξ^i • KNSGraphSpace.frequency k v ξ) :=
    fun i hi => frequency_moment_integrable v i (by omega)
  rw [iteratedDeriv_fourier_of_integrable_moments_le hm le_rfl]

/-- The actual regularized derivatives have the same formula with Gaussian damping. -/
theorem regularized_iteratedDeriv_formula {k : ℕ} (N : ℕ) (v : KNSGraphSpace k)
    (j : ℕ) (x : ℝ) :
    iteratedDeriv j (KNSGraphSpace.representative k (gaussianRegularized N v)) x =
      (-1 : ℝ)^j • (𝓕 (fun ξ => gaussianCutoff N ξ *
        fourierDerivativeData j (KNSGraphSpace.frequency k v : ℝ → ℂ) ξ) : ℝ → ℂ) (-x) := by
  rw [representative_gaussianRegularized]
  let G : ℝ → ℂ := fun ξ => gaussianCutoff N ξ * KNSGraphSpace.frequency k v ξ
  have he : (𝓕⁻ G : ℝ → ℂ) = fun y => (𝓕 G : ℝ → ℂ) (-y) := by
    funext y
    exact Real.fourierInv_eq_fourier_neg G y
  change iteratedDeriv j (𝓕⁻ G) x = _
  rw [he, iteratedDeriv_comp_neg]
  have hm : ∀ i ≤ j, Integrable (fun ξ : ℝ => ξ^i • G ξ) :=
    fun i _hi => damped_integrable_moment N (KNSGraphSpace.frequency k v) i
  rw [iteratedDeriv_fourier_of_integrable_moments_le hm le_rfl]
  have hfun : fourierDerivativeData j G = fun ξ => gaussianCutoff N ξ *
      fourierDerivativeData j (KNSGraphSpace.frequency k v : ℝ → ℂ) ξ := by
    funext ξ
    simp only [fourierDerivativeData, G]
    ring
  rw [hfun]

/-- Gaussian regularization converges pointwise in every actual classical
derivative strictly below the original graph order, on both real rays. -/
theorem regularized_iteratedDeriv_tendsto {k : ℕ} (v : KNSGraphSpace k)
    (j : ℕ) (hj : j < k) (x : ℝ) :
    Tendsto (fun N => iteratedDeriv j
      (KNSGraphSpace.representative k (gaussianRegularized N v)) x) atTop
        (𝓝 (iteratedDeriv j (KNSGraphSpace.representative k v) x)) := by
  have hi := integrable_fourierDerivativeData_of_moment j (frequency_moment_integrable v j hj)
  have ht := (fourier_gaussian_tendsto hi (-x)).const_smul ((-1 : ℝ)^j)
  simpa only [regularized_iteratedDeriv_formula,
    representative_iteratedDeriv_formula v j hj x] using ht

end
end MeyerGeneralProblem.KNSGraphSmoothApproximation
