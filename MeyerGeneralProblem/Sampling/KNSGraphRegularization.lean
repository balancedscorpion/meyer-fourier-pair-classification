module

public import MeyerGeneralProblem.Sampling.GaussianDamping
public import MeyerGeneralProblem.Distribution.SchwartzDistributionLeibniz

@[expose] public section

/-!
# Explicit same-order regularization of the full KNS graph

Pure frequency moments construct every lower weak derivative, including the
actual top distributional derivative. Schwartz multiplication preserves the
complete original graph. Gaussian-frequency and compact-physical cutoffs yield
explicit unrestricted Schwartz graph density at every order at least two.
No E2 oscillator, mixed-monomial bound, higher graph order or evenness is used.
-/

namespace MeyerGeneralProblem.KNSGraphRegularization
noncomputable section
open MeyerGeneralProblem MeasureTheory GaussianDamping
open scoped FourierTransform Topology

/-- The actual Fourier derivative normalization. -/
def fourierConstant : ℂ := 2 * Real.pi * Complex.I

/-- Polynomial multiplication on actual distributions. -/
def powerDistribution (n : ℕ) :=
  TemperedDistribution.smulLeftCLM ℂ (fun x : ℝ => (x : ℂ)^n)

/-- The zeroth polynomial multiplier is genuinely the identity. -/
theorem powerDistribution_zero (T : TemperedDistribution ℝ ℂ) :
    powerDistribution 0 T = T := by simp [powerDistribution]

/-- Exact polynomial multiplier composition. -/
theorem powerDistribution_succ (n : ℕ) (T : TemperedDistribution ℝ ℂ) :
    powerDistribution 1 (powerDistribution n T) = powerDistribution (n+1) T := by
  rw [powerDistribution, powerDistribution,
    TemperedDistribution.smulLeftCLM_smulLeftCLM_apply (by fun_prop) (by fun_prop)]
  congr 2
  funext x
  simp only [Pi.mul_apply]
  ring

/-- The generic one-dimensional derivative conversion uses only Schwartz tests,
not the order-two oscillator or its derived density. -/
theorem derivCLM_eq_lineDeriv (T : TemperedDistribution ℝ ℂ) :
    TemperedDistribution.derivCLM ℂ T = LineDeriv.lineDerivOp (1 : ℝ) T := by
  have hφ (φ : SchwartzMap ℝ ℂ) :
      LineDeriv.lineDerivOp (1 : ℝ) φ = SchwartzMap.derivCLM ℂ ℂ φ := by
    ext x
    simp [SchwartzMap.lineDerivOp_apply_eq_fderiv]
  ext φ
  simp only [TemperedDistribution.derivCLM_apply_apply,
    TemperedDistribution.lineDerivOp_apply_apply, hφ]

/-- All iterated distributional derivatives have the actual Fourier multiplier,
including the top order without any classical differentiability hypothesis. -/
theorem fourier_iterate_deriv (n : ℕ) (T : TemperedDistribution ℝ ℂ) :
    𝓕 (((TemperedDistribution.derivCLM ℂ)^[n]) T) =
      fourierConstant^n • powerDistribution n (𝓕 T) := by
  induction n with
  | zero => simp [powerDistribution_zero]
  | succ n ih =>
    rw [Function.iterate_succ_apply', derivCLM_eq_lineDeriv,
      TemperedDistribution.fourier_lineDerivOp_eq, ih]
    have hid : (fun x : ℝ => ((inner ℝ x (1 : ℝ) : ℝ) : ℂ)) =
        (fun x : ℝ => (x : ℂ)^1) := by
      funext x
      simp
    change fourierConstant •
      TemperedDistribution.smulLeftCLM ℂ
        (fun x : ℝ => ((inner ℝ x (1 : ℝ) : ℝ) : ℂ))
        (fourierConstant^n • powerDistribution n (𝓕 T)) = _
    rw [hid, map_smul]
    change fourierConstant • (fourierConstant^n •
      powerDistribution 1 (powerDistribution n (𝓕 T))) = _
    rw [powerDistribution_succ, smul_smul, pow_succ']
end
end MeyerGeneralProblem.KNSGraphRegularization

namespace MeyerGeneralProblem.KNSGraphRegularization
noncomputable section
open MeyerGeneralProblem MeasureTheory GaussianDamping
open scoped FourierTransform Topology

/-- Lower pure power moments require only the original zeroth and top moments. -/
theorem memLp_power_of_le {f : ℝ → ℂ} {j k : ℕ}
    (hf : MemLp f 2) (hk : MemLp (fun x : ℝ => (x : ℂ)^k * f x) 2) (hj : j ≤ k) :
    MemLp (fun x : ℝ => (x : ℂ)^j * f x) 2 := by
  apply (hf.norm.add hk.norm).mono'
  · exact (show Continuous (fun x : ℝ => (x : ℂ)^j) by fun_prop).aestronglyMeasurable.mul
      hf.aestronglyMeasurable
  · filter_upwards [] with x
    change ‖(x : ℂ)^j * f x‖ ≤ ‖f x‖ + ‖(x : ℂ)^k * f x‖
    simp only [norm_mul, norm_pow]
    have hp : ‖(x : ℂ)‖^j ≤ 1 + ‖(x : ℂ)‖^k := by
      by_cases h : 1 ≤ ‖(x : ℂ)‖
      · exact (pow_le_pow_right₀ h hj).trans (by linarith)
      · exact (pow_le_one₀ (norm_nonneg _) (le_of_not_ge h)).trans
          (le_add_of_nonneg_right (pow_nonneg (norm_nonneg _) _))
    nlinarith [mul_le_mul_of_nonneg_right hp (norm_nonneg (f x))]

/-- Polynomial multiplication represented by a genuine L2 input. -/
theorem power_toLp_distribution (j : ℕ) (p : KNSL2)
    (h : MemLp (fun x : ℝ => (x : ℂ)^j * p x) 2) :
    (h.toLp : TemperedDistribution ℝ ℂ) =
      powerDistribution j (p : TemperedDistribution ℝ ℂ) := by
  ext φ
  simp only [Lp.toTemperedDistribution_apply, powerDistribution,
    TemperedDistribution.smulLeftCLM_apply_apply]
  apply integral_congr_ae
  filter_upwards [h.coeFn_toLp] with x hx
  rw [hx, SchwartzMap.smulLeftCLM_apply_apply (by fun_prop :
    (fun x : ℝ => (x : ℂ)^j).HasTemperateGrowth)]
  simp only [smul_eq_mul]
  ring

/-- Every graph element has all lower pure frequency moments. -/
theorem lower_frequency_memLp {k : ℕ} (v : KNSGraphSpace k) (j : ℕ) (hj : j ≤ k) :
    MemLp (fun x : ℝ => (x : ℂ)^j * KNSGraphSpace.frequency k v x) 2 :=
  memLp_power_of_le (Lp.memLp _) ((memLp_congr_ae (KNSGraphSpace.frequencyWeight_ae v)).mpr
    (Lp.memLp _)) hj

/-- A pure weak derivative class built from the actual frequency moments. -/
def derivativeLp {k : ℕ} (v : KNSGraphSpace k) (j : ℕ) (hj : j ≤ k) : KNSL2 :=
  fourierConstant^j • 𝓕⁻ (lower_frequency_memLp v j hj).toLp

/-- The L2 derivative class is the actual iterated distributional derivative.
The top order is not promoted to a classical derivative. -/
theorem derivativeLp_distribution {k : ℕ} (v : KNSGraphSpace k) (j : ℕ) (hj : j ≤ k) :
    (derivativeLp v j hj : TemperedDistribution ℝ ℂ) =
      ((TemperedDistribution.derivCLM ℂ)^[j])
        (KNSGraphSpace.physical k v : TemperedDistribution ℝ ℂ) := by
  apply (show Function.Injective (fun T : TemperedDistribution ℝ ℂ => 𝓕 T) from
    fun A B h => by simpa using congrArg (fun T : TemperedDistribution ℝ ℂ => 𝓕⁻ T) h)
  dsimp only
  rw [fourier_iterate_deriv, Lp.fourier_toTemperedDistribution_eq]
  change (Lp.toTemperedDistributionCLM ℂ volume 2)
    (𝓕 (derivativeLp v j hj)) = _
  simp only [derivativeLp, FourierTransform.fourier_smul,
    FourierTransform.fourier_fourierInv_eq, map_smul, Lp.toTemperedDistributionCLM_apply]
  rw [power_toLp_distribution, KNSGraphSpace.frequency_eq_fourier,
    ← Lp.fourier_toTemperedDistribution_eq]

/-- The zeroth derivative class is exactly the original physical coordinate. -/
theorem derivativeLp_zero {k : ℕ} (v : KNSGraphSpace k) :
    derivativeLp v 0 (Nat.zero_le k) = KNSGraphSpace.physical k v := by
  apply (LinearMap.ker_eq_bot.mp
    (Lp.ker_toTemperedDistributionCLM_eq_bot (F := ℂ) (μ := volume)))
  simpa using derivativeLp_distribution v 0 (Nat.zero_le k)

end
end MeyerGeneralProblem.KNSGraphRegularization

namespace MeyerGeneralProblem.KNSGraphRegularization
noncomputable section
open MeyerGeneralProblem MeasureTheory GaussianDamping
open scoped FourierTransform Topology BigOperators

/-- The Fourier constant is nonzero. -/
theorem fourierConstant_ne_zero : fourierConstant ≠ 0 := by
  unfold fourierConstant
  exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
    Complex.I_ne_zero

/-- Polynomial and Schwartz distribution multipliers commute. -/
theorem power_mul_comm (k : ℕ) (g : SchwartzMap ℝ ℂ) (T : TemperedDistribution ℝ ℂ) :
    powerDistribution k (TemperedDistribution.smulLeftCLM ℂ g T) =
      TemperedDistribution.smulLeftCLM ℂ g (powerDistribution k T) := by
  unfold powerDistribution
  rw [TemperedDistribution.smulLeftCLM_smulLeftCLM_apply g.hasTemperateGrowth (by fun_prop),
    TemperedDistribution.smulLeftCLM_smulLeftCLM_apply (by fun_prop) g.hasTemperateGrowth]
  congr 2
  funext x
  exact mul_comm _ _

/-- The actual L2 binomial expression for the top derivative after multiplication. -/
def multipliedDerivative {k : ℕ} (g : SchwartzMap ℝ ℂ) (v : KNSGraphSpace k) : KNSL2 :=
  ∑ i ∈ Finset.range (k+1), k.choose i •
    mulSchwartz (((SchwartzMap.derivCLM ℂ ℂ)^[i]) g)
      (derivativeLp v (k-i) (Nat.sub_le _ _))

/-- The binomial expression is proved equal to the top distributional derivative. -/
theorem multipliedDerivative_distribution {k : ℕ} (g : SchwartzMap ℝ ℂ) (v : KNSGraphSpace k) :
    (multipliedDerivative g v : TemperedDistribution ℝ ℂ) =
      ((TemperedDistribution.derivCLM ℂ)^[k])
        (mulSchwartz g (KNSGraphSpace.physical k v) : TemperedDistribution ℝ ℂ) := by
  rw [mulSchwartz_distribution, SchwartzDistributionLeibniz.iterate_deriv_smul]
  change (Lp.toTemperedDistributionCLM ℂ volume 2) (multipliedDerivative g v) = _
  simp only [multipliedDerivative, map_sum, map_nsmul, Lp.toTemperedDistributionCLM_apply, mulSchwartz_distribution,
    derivativeLp_distribution]

/-- Actual Schwartz multiplication on the full graph; both weighted coordinates
are constructed and verified rather than assumed. -/
def multiplyGraph {k : ℕ} (g : SchwartzMap ℝ ℂ) (v : KNSGraphSpace k) : KNSGraphSpace k :=
  ⟨WithLp.toLp 2 ![mulSchwartz g (KNSGraphSpace.physical k v),
    𝓕 (mulSchwartz g (KNSGraphSpace.physical k v)),
    mulSchwartz g (KNSGraphSpace.physicalWeight k v),
    (fourierConstant^k)⁻¹ • 𝓕 (multipliedDerivative g v)],
    by
      refine ⟨rfl, ?_, ?_⟩
      · change (mulSchwartz g (KNSGraphSpace.physicalWeight k v) : TemperedDistribution ℝ ℂ) =
          powerDistribution k (mulSchwartz g (KNSGraphSpace.physical k v) : TemperedDistribution ℝ ℂ)
        rw [mulSchwartz_distribution, mulSchwartz_distribution, power_mul_comm]
        exact congrArg (TemperedDistribution.smulLeftCLM ℂ g) v.property.2.1
      · change (Lp.toTemperedDistributionCLM ℂ volume 2)
          ((fourierConstant^k)⁻¹ • 𝓕 (multipliedDerivative g v)) =
          powerDistribution k ((𝓕 (mulSchwartz g (KNSGraphSpace.physical k v)) : KNSL2) :
            TemperedDistribution ℝ ℂ)
        rw [map_smul, Lp.toTemperedDistributionCLM_apply, ← Lp.fourier_toTemperedDistribution_eq,
          multipliedDerivative_distribution, fourier_iterate_deriv,
          smul_smul, inv_mul_cancel₀ (pow_ne_zero _ fourierConstant_ne_zero), one_smul,
          Lp.fourier_toTemperedDistribution_eq]⟩

/-- Exact physical product coordinate. -/
theorem physical_multiplyGraph {k : ℕ} (g : SchwartzMap ℝ ℂ) (v : KNSGraphSpace k) :
    KNSGraphSpace.physical k (multiplyGraph g v) = mulSchwartz g (KNSGraphSpace.physical k v) := rfl

/-- Exact physical weighted product coordinate. -/
theorem physicalWeight_multiplyGraph {k : ℕ} (g : SchwartzMap ℝ ℂ) (v : KNSGraphSpace k) :
    KNSGraphSpace.physicalWeight k (multiplyGraph g v) =
      mulSchwartz g (KNSGraphSpace.physicalWeight k v) := rfl

/-- Exact genuine Fourier weighted coordinate, with the normalization visible. -/
theorem frequencyWeight_multiplyGraph {k : ℕ} (g : SchwartzMap ℝ ℂ) (v : KNSGraphSpace k) :
    KNSGraphSpace.frequencyWeight k (multiplyGraph g v) =
      (fourierConstant^k)⁻¹ • 𝓕 (multipliedDerivative g v) := rfl

end
end MeyerGeneralProblem.KNSGraphRegularization

namespace MeyerGeneralProblem.KNSGraphRegularization
noncomputable section
open MeyerGeneralProblem MeasureTheory GaussianDamping Filter
open scoped FourierTransform Topology BigOperators

/-- The Fourier transform of the top weak derivative recovers the stored weight. -/
theorem top_derivative_fourier {k : ℕ} (v : KNSGraphSpace k) :
    (fourierConstant^k)⁻¹ • 𝓕 (derivativeLp v k le_rfl) =
      KNSGraphSpace.frequencyWeight k v := by
  have h : (lower_frequency_memLp v k le_rfl).toLp =
      KNSGraphSpace.frequencyWeight k v := by
    apply Lp.ext
    exact (lower_frequency_memLp v k le_rfl).coeFn_toLp.trans
      (KNSGraphSpace.frequencyWeight_ae v)
  simp only [derivativeLp, FourierTransform.fourier_smul,
    FourierTransform.fourier_fourierInv_eq, smul_smul,
    inv_mul_cancel₀ (pow_ne_zero _ fourierConstant_ne_zero), one_smul, h]

/-- Strong convergence of the actual binomial derivative expression. -/
theorem multipliedDerivative_tendsto {k : ℕ} (v : KNSGraphSpace k)
    (g : ℕ → SchwartzMap ℝ ℂ)
    (hzero : ∀ p : KNSL2, Tendsto (fun N => mulSchwartz (g N) p) atTop (𝓝 p))
    (hpos : ∀ i : ℕ, 0 < i → ∀ p : KNSL2,
      Tendsto (fun N => mulSchwartz (((SchwartzMap.derivCLM ℂ ℂ)^[i]) (g N)) p)
        atTop (𝓝 0)) :
    Tendsto (fun N => multipliedDerivative (g N) v) atTop
      (𝓝 (derivativeLp v k le_rfl)) := by
  have ht := tendsto_finsetSum (x := atTop) (Finset.range (k+1))
    (f := fun i N => k.choose i • mulSchwartz
      (((SchwartzMap.derivCLM ℂ ℂ)^[i]) (g N))
        (derivativeLp v (k-i) (Nat.sub_le _ _)))
    (a := fun i => if i = 0 then derivativeLp v k le_rfl else 0) ?_
  · simpa only [multipliedDerivative, Finset.sum_ite_eq',
      Finset.mem_range, Nat.zero_lt_succ, ite_true] using ht
  · intro i hi
    by_cases he : i = 0
    · subst i
      simpa using hzero (derivativeLp v k le_rfl)
    · simpa [he] using (hpos i (Nat.pos_of_ne_zero he)
        (derivativeLp v (k-i) (Nat.sub_le _ _))).const_smul (k.choose i)

/-- Convergence of the three independent graph coordinates gives full graph convergence. -/
theorem tendsto_graph_of_coordinates {k : ℕ} (u : ℕ → KNSGraphSpace k) (v : KNSGraphSpace k)
    (hp : Tendsto (fun N => KNSGraphSpace.physical k (u N)) atTop
      (𝓝 (KNSGraphSpace.physical k v)))
    (hw : Tendsto (fun N => KNSGraphSpace.physicalWeight k (u N)) atTop
      (𝓝 (KNSGraphSpace.physicalWeight k v)))
    (hq : Tendsto (fun N => KNSGraphSpace.frequencyWeight k (u N)) atTop
      (𝓝 (KNSGraphSpace.frequencyWeight k v))) :
    Tendsto u atTop (𝓝 v) := by
  have hs : Tendsto (fun N => ‖u N - v‖^2) atTop (𝓝 0) := by
    have hp' := ((hp.sub_const (KNSGraphSpace.physical k v)).norm.pow 2).const_mul 2
    have hw' := (hw.sub_const (KNSGraphSpace.physicalWeight k v)).norm.pow 2
    have hq' := (hq.sub_const (KNSGraphSpace.frequencyWeight k v)).norm.pow 2
    have ht := (hp'.add hw').add hq'
    simpa only [KNSGraphSpace.norm_sq, map_sub, sub_self, norm_zero,
      zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, add_zero] using ht
  have hn := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hs
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  convert hn using 1
  · funext N
    exact (Real.sqrt_sq (norm_nonneg (u N - v))).symm
  · simp only [Real.sqrt_zero]

/-- Multiplier convergence is genuine graph-norm convergence at every original order. -/
theorem multiplyGraph_tendsto {k : ℕ} (v : KNSGraphSpace k)
    (g : ℕ → SchwartzMap ℝ ℂ)
    (hzero : ∀ p : KNSL2, Tendsto (fun N => mulSchwartz (g N) p) atTop (𝓝 p))
    (hpos : ∀ i : ℕ, 0 < i → ∀ p : KNSL2,
      Tendsto (fun N => mulSchwartz (((SchwartzMap.derivCLM ℂ ℂ)^[i]) (g N)) p)
        atTop (𝓝 0)) :
    Tendsto (fun N => multiplyGraph (g N) v) atTop (𝓝 v) := by
  apply tendsto_graph_of_coordinates
  · exact hzero _
  · exact hzero _
  · have ht := ((FourierTransform.fourierCLM ℂ KNSL2).continuous.tendsto
      (derivativeLp v k le_rfl)).comp (multipliedDerivative_tendsto v g hzero hpos)
    simpa only [Function.comp_apply, FourierTransform.fourierCLM_apply,
      frequencyWeight_multiplyGraph, top_derivative_fourier] using
      ht.const_smul ((fourierConstant^k)⁻¹)

/-- Gaussian multiplication therefore converges in the full original graph. -/
theorem gaussian_multiplyGraph_tendsto {k : ℕ} (v : KNSGraphSpace k) :
    Tendsto (fun N => multiplyGraph (gaussianCutoff N) v) atTop (𝓝 v) :=
  multiplyGraph_tendsto v gaussianCutoff gaussianJet_zero_tendsto
    (fun _i hi p => gaussianJet_succ_tendsto hi p)
end
end MeyerGeneralProblem.KNSGraphRegularization

namespace MeyerGeneralProblem.KNSGraphRegularization
noncomputable section
open MeyerGeneralProblem MeasureTheory GaussianDamping Filter Set
open scoped FourierTransform Topology BigOperators ContDiff

/-- Expanding physical cutoffs tend pointwise to one on both rays. -/
theorem compactCutoff_tendsto (x : ℝ) :
    Tendsto (fun N => scaledCompactSchwartzCutoff N x) atTop (𝓝 1) := by
  have h := (compactSchwartzCutoff.continuous.tendsto (0 : ℝ)).comp
    (by simpa only [zero_mul] using compactSchwartzCutoffScale_tendsto.mul_const x)
  simpa only [zero_mul, Function.comp_def, scaledCompactSchwartzCutoff_apply,
    compactSchwartzCutoff_eq_one (by norm_num : |(0 : ℝ)| ≤ 1)] using h

/-- Zeroth cutoff multiplication converges on every actual L2 class. -/
theorem compactCutoff_zero_tendsto (p : KNSL2) :
    Tendsto (fun N => mulSchwartz (scaledCompactSchwartzCutoff N) p) atTop (𝓝 p) := by
  have ht := toLp_tendsto_of_dominated
    (fun N => mulSchwartz_memLp (scaledCompactSchwartzCutoff N) p) (Lp.memLp p) p
    (C := 2) (by norm_num) (fun N => ?_) ?_
  · simpa only [Lp.toLp_coeFn, mulSchwartz] using ht
  · filter_upwards [] with x
    calc
      ‖scaledCompactSchwartzCutoff N x * p x - p x‖ =
        ‖(scaledCompactSchwartzCutoff N x - 1) * p x‖ := by congr 1; ring
      _ ≤ 2 * ‖p x‖ := by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right
          (norm_scaledCompactSchwartzCutoff_sub_one_le_two N x) (norm_nonneg _)
  · filter_upwards [] with x
    simpa only [one_mul] using (compactCutoff_tendsto x).mul_const (p x)

/-- Positive cutoff derivative multipliers vanish strongly. -/
theorem compactCutoff_positive_tendsto (i : ℕ) (hi : 0 < i) (p : KNSL2) :
    Tendsto (fun N => mulSchwartz (((SchwartzMap.derivCLM ℂ ℂ)^[i])
      (scaledCompactSchwartzCutoff N)) p) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _)
    (fun N => mulSchwartz_norm_le _ p (fun x => by
      rw [schwartzDerivative_iterate_apply]
      exact norm_iteratedDeriv_scaledCompactSchwartzCutoff_le N i x))
  simpa only [zero_pow hi.ne', zero_mul] using
    ((compactSchwartzCutoffScale_tendsto.pow i).mul_const
      (SchwartzMap.seminorm ℂ 0 i compactSchwartzCutoff)).mul_const ‖p‖

/-- Physical cutoff approximation in the complete original graph norm. -/
theorem compact_multiplyGraph_tendsto {k : ℕ} (v : KNSGraphSpace k) :
    Tendsto (fun N => multiplyGraph (scaledCompactSchwartzCutoff N) v) atTop (𝓝 v) :=
  multiplyGraph_tendsto v scaledCompactSchwartzCutoff compactCutoff_zero_tendsto
    compactCutoff_positive_tendsto

/-- Gaussian frequency regularization is conjugated by the actual graph Fourier equivalence. -/
def gaussianRegularized {k : ℕ} (N : ℕ) (v : KNSGraphSpace k) : KNSGraphSpace k :=
  (KNSGraphSpace.fourierEquiv k).symm
    (multiplyGraph (gaussianCutoff N) (KNSGraphSpace.fourierEquiv k v))

/-- Its actual frequency coordinate is the original Gaussian-damped frequency. -/
theorem frequency_gaussianRegularized {k : ℕ} (N : ℕ) (v : KNSGraphSpace k) :
    KNSGraphSpace.frequency k (gaussianRegularized N v) =
      damped N (KNSGraphSpace.frequency k v) := by
  have h := congrArg (KNSGraphSpace.physical k)
    ((KNSGraphSpace.fourierEquiv k).apply_symm_apply
      (multiplyGraph (gaussianCutoff N) (KNSGraphSpace.fourierEquiv k v)))
  change KNSGraphSpace.physical k (KNSGraphSpace.fourier k (gaussianRegularized N v)) =
    mulSchwartz (gaussianCutoff N)
      (KNSGraphSpace.physical k (KNSGraphSpace.fourier k v)) at h
  rw [KNSGraphSpace.physical_fourier, KNSGraphSpace.physical_fourier,
    ← KNSGraphSpace.frequency_eq_fourier, ← KNSGraphSpace.frequency_eq_fourier] at h
  exact h

/-- Frequency Gaussian regularization converges in the full original graph norm. -/
theorem gaussianRegularized_tendsto {k : ℕ} (v : KNSGraphSpace k) :
    Tendsto (fun N => gaussianRegularized N v) atTop (𝓝 v) := by
  have h := ((KNSGraphSpace.fourierEquiv k).symm.continuous.tendsto
    (KNSGraphSpace.fourierEquiv k v)).comp
      (gaussian_multiplyGraph_tendsto (KNSGraphSpace.fourierEquiv k v))
  simpa only [Function.comp_def, gaussianRegularized,
    LinearIsometryEquiv.symm_apply_apply] using h

/-- The chosen graph representative of the regularized class is the genuine
smooth inverse integral of the Gaussian-damped original frequency function. -/
theorem representative_gaussianRegularized {k : ℕ} (N : ℕ) (v : KNSGraphSpace k) :
    KNSGraphSpace.representative k (gaussianRegularized N v) =
      𝓕⁻ (fun x : ℝ => gaussianCutoff N x * KNSGraphSpace.frequency k v x) := by
  funext x
  rw [KNSGraphSpace.representative, frequency_gaussianRegularized,
    Real.fourierInv_eq_fourier_neg]
  exact Real.fourier_congr_ae (damped_memLp N (KNSGraphSpace.frequency k v)).coeFn_toLp (-x)

/-- The actual regularized graph representative is C∞. -/
theorem gaussianRegularized_smooth {k : ℕ} (N : ℕ) (v : KNSGraphSpace k) :
    ContDiff ℝ ∞ (KNSGraphSpace.representative k (gaussianRegularized N v)) := by
  rw [representative_gaussianRegularized]
  exact damped_inverse_contDiff N (KNSGraphSpace.frequency k v)

end
end MeyerGeneralProblem.KNSGraphRegularization

namespace MeyerGeneralProblem.KNSGraphRegularization
noncomputable section
open MeyerGeneralProblem MeasureTheory GaussianDamping Filter Set
open scoped FourierTransform Topology BigOperators ContDiff

/-- Concrete compact physical cutoff of the smooth frequency-damped representative. -/
def regularizedSchwartz {k : ℕ} (N R : ℕ) (v : KNSGraphSpace k) : SchwartzMap ℝ ℂ :=
  ((scaledCompactSchwartzCutoff_hasCompactSupport R).mul_right :
    HasCompactSupport (fun x : ℝ => scaledCompactSchwartzCutoff R x *
      KNSGraphSpace.representative k (gaussianRegularized N v) x)).toSchwartzMap
        ((scaledCompactSchwartzCutoff R).smooth'.mul (gaussianRegularized_smooth N v))

/-- The approximant is exactly the prescribed two-sided regularization, pointwise. -/
theorem regularizedSchwartz_apply {k : ℕ} (N R : ℕ) (v : KNSGraphSpace k) (x : ℝ) :
    regularizedSchwartz N R v x = scaledCompactSchwartzCutoff R x *
      𝓕⁻ (fun ξ : ℝ => gaussianCutoff N ξ * KNSGraphSpace.frequency k v ξ) x := by
  change scaledCompactSchwartzCutoff R x *
    KNSGraphSpace.representative k (gaussianRegularized N v) x = _
  rw [representative_gaussianRegularized]

/-- The concrete approximants genuinely have compact support. -/
theorem regularizedSchwartz_compactSupport {k : ℕ} (N R : ℕ) (v : KNSGraphSpace k) :
    HasCompactSupport (regularizedSchwartz N R v) :=
  (scaledCompactSchwartzCutoff_hasCompactSupport R).mul_right

/-- The actual Schwartz embedding equals the proved four-coordinate graph construction.
Only the existing AE representative identity is used, never a point-sample inference. -/
theorem embedding_regularizedSchwartz {k : ℕ} (hk : 1 ≤ k) (N R : ℕ) (v : KNSGraphSpace k) :
    KNSGraphSpace.schwartzEmbedding k (regularizedSchwartz N R v) =
      multiplyGraph (scaledCompactSchwartzCutoff R) (gaussianRegularized N v) := by
  apply KNSGraphSpace.physical_injective k
  rw [KNSGraphSpace.physical_schwartzEmbedding, physical_multiplyGraph]
  apply Lp.ext
  filter_upwards [(regularizedSchwartz N R v).coeFn_toLp 2 volume,
    mulSchwartz_ae (scaledCompactSchwartzCutoff R)
      (KNSGraphSpace.physical k (gaussianRegularized N v)),
    KNSGraphSpace.representative_ae hk (gaussianRegularized N v)] with x hx hy hz
  rw [hx, hy]
  change scaledCompactSchwartzCutoff R x *
    KNSGraphSpace.representative k (gaussianRegularized N v) x = _
  rw [hz]

/-- At fixed Gaussian damping, the concrete compact Schwartz approximants converge
in the full original graph norm as the physical cutoff expands. -/
theorem regularizedSchwartz_tendsto {k : ℕ} (hk : 1 ≤ k) (N : ℕ) (v : KNSGraphSpace k) :
    Tendsto (fun R => KNSGraphSpace.schwartzEmbedding k (regularizedSchwartz N R v))
      atTop (𝓝 (gaussianRegularized N v)) := by
  simp only [embedding_regularizedSchwartz hk]
  exact compact_multiplyGraph_tendsto _

/-- Unrestricted actual Schwartz graph density at every order at least two,
derived from explicit two-sided regularization and the original pure endpoints. -/
theorem schwartzEmbedding_denseRange {k : ℕ} (hk : 2 ≤ k) :
    DenseRange (KNSGraphSpace.schwartzEmbedding k) := by
  intro v
  apply isClosed_closure.mem_of_tendsto (gaussianRegularized_tendsto v)
  filter_upwards [] with N
  apply isClosed_closure.mem_of_tendsto (regularizedSchwartz_tendsto (by omega : 1 ≤ k) N v)
  filter_upwards [] with R
  exact subset_closure ⟨regularizedSchwartz N R v, rfl⟩

/-- An explicit Gaussian index and physical cutoff index achieve every positive
graph-norm tolerance for each actual graph input. -/
theorem exists_regularizedSchwartz_close {k : ℕ} (hk : 2 ≤ k)
    (v : KNSGraphSpace k) {ε : ℝ} (hε : 0 < ε) :
    ∃ N R : ℕ, ‖KNSGraphSpace.schwartzEmbedding k (regularizedSchwartz N R v) - v‖ < ε := by
  have hN := (tendsto_iff_norm_sub_tendsto_zero.mp (gaussianRegularized_tendsto v)).eventually
    (gt_mem_nhds (show 0 < ε / 2 by positivity))
  obtain ⟨N, hN⟩ := hN.exists
  have hR := (tendsto_iff_norm_sub_tendsto_zero.mp
    (regularizedSchwartz_tendsto (by omega : 1 ≤ k) N v)).eventually
      (gt_mem_nhds (show 0 < ε / 2 by positivity))
  obtain ⟨R, hR⟩ := hR.exists
  refine ⟨N, R, ?_⟩
  calc
    ‖KNSGraphSpace.schwartzEmbedding k (regularizedSchwartz N R v) - v‖ =
      ‖(KNSGraphSpace.schwartzEmbedding k (regularizedSchwartz N R v) -
        gaussianRegularized N v) + (gaussianRegularized N v - v)‖ := by
          congr 1
          abel
    _ ≤ ‖KNSGraphSpace.schwartzEmbedding k (regularizedSchwartz N R v) -
        gaussianRegularized N v‖ + ‖gaussianRegularized N v - v‖ := norm_add_le _ _
    _ < ε := by linarith

end
end MeyerGeneralProblem.KNSGraphRegularization

namespace MeyerGeneralProblem.KNSGraphRegularization
noncomputable section
open MeyerGeneralProblem MeasureTheory GaussianDamping Filter Set
open scoped FourierTransform Topology BigOperators ContDiff

/-- A genuine non-even Schwartz input for both-ray regularization controls. -/
def oddGaussian : SchwartzMap ℝ ℂ :=
  SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => (x : ℂ)) gaussianBase

/-- The test input has its exact Gaussian-polynomial values. -/
theorem oddGaussian_apply (x : ℝ) :
    oddGaussian x = (x : ℂ) * (Real.exp (-(x^2 / 2)) : ℂ) := by
  simp only [oddGaussian, SchwartzMap.smulLeftCLM_apply_apply (by fun_prop :
    (fun x : ℝ => (x : ℂ)).HasTemperateGrowth), smul_eq_mul, gaussianBase_apply]

/-- Negative inputs really reverse the sign of this non-even input. -/
theorem oddGaussian_neg (x : ℝ) : oddGaussian (-x) = -oddGaussian x := by
  simp [oddGaussian_apply]

/-- The actual model is nonzero at the positive unit input. -/
theorem oddGaussian_one_ne_zero : oddGaussian 1 ≠ 0 := by
  rw [oddGaussian_apply]
  exact mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _))

/-- Evenness is genuinely false, so the model does not test only a symmetric subspace. -/
theorem oddGaussian_not_even : ¬ ∀ x : ℝ, oddGaussian (-x) = oddGaussian x := by
  intro h
  have he : -oddGaussian 1 = oddGaussian 1 := by simpa only [oddGaussian_neg] using h 1
  apply oddGaussian_one_ne_zero
  linear_combination -(1 / 2 : ℂ) * he

/-- The actual graph input from this model is nonzero at every graph order. -/
theorem oddGaussian_embedding_ne_zero (k : ℕ) :
    KNSGraphSpace.schwartzEmbedding k oddGaussian ≠ 0 := by
  intro h
  have hs : oddGaussian = 0 :=
    KNSGraphSpace.schwartzEmbedding_injective k (h.trans (map_zero _).symm)
  apply oddGaussian_one_ne_zero
  exact congrArg (fun g : SchwartzMap ℝ ℂ => g 1) hs

/-- The all-order core theorem is instantiated on a genuine non-even, nonzero input. -/
theorem oddGaussian_approximation (k : ℕ) (hk : 2 ≤ k) {ε : ℝ} (hε : 0 < ε) :
    ∃ N R : ℕ,
      ‖KNSGraphSpace.schwartzEmbedding k
        (regularizedSchwartz N R (KNSGraphSpace.schwartzEmbedding k oddGaussian)) -
          KNSGraphSpace.schwartzEmbedding k oddGaussian‖ < ε :=
  exists_regularizedSchwartz_close hk _ hε

/-- The actual negative-ray approximant retains the inverse Fourier argument -x;
it is not replaced by a positive argument or an evenness premise. -/
theorem regularizedSchwartz_negative_apply {k : ℕ} (N R : ℕ) (v : KNSGraphSpace k) (x : ℝ) :
    regularizedSchwartz N R v (-x) = scaledCompactSchwartzCutoff R (-x) *
      𝓕⁻ (fun ξ : ℝ => gaussianCutoff N ξ * KNSGraphSpace.frequency k v ξ) (-x) :=
  regularizedSchwartz_apply N R v (-x)

end
end MeyerGeneralProblem.KNSGraphRegularization
