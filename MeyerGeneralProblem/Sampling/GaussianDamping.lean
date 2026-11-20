module

public import MeyerGeneralProblem.Sampling.KNSGraphRepresentative
public import MeyerGeneralProblem.Hermite.CutoffNorm
public import MeyerGeneralProblem.Distribution.CompactSchwartzDensity
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section

/-!
# Actual Gaussian and Schwartz multiplication on L2

Explicit positive Gaussian parameters tend to zero. Genuine L2 dominated
convergence, multiplier jets and integrable damped moments provide smoothing.
This module does not assume or assert graph density.
-/

namespace MeyerGeneralProblem.GaussianDamping

noncomputable section
open MeyerGeneralProblem MeasureTheory Filter Set
open scoped FourierTransform Topology ContDiff

/-- The unnormalised Gaussian is recovered from the public Hermite zero. -/
def gaussianBase : SchwartzMap ℝ ℂ :=
  Real.sqrt (Real.sqrt Real.pi) •
    (TauCeti.hermiteSchwartzMap 0).postcompCLM Complex.ofRealCLM

/-- Exact real Gaussian values, including both signs of the argument. -/
theorem gaussianBase_apply (x : ℝ) :
    gaussianBase x = (Real.exp (-(x ^ 2 / 2)) : ℂ) := by
  have hc : Real.sqrt (Real.sqrt Real.pi) ≠ 0 := by positivity
  simp only [gaussianBase, smul_apply, SchwartzMap.postcompCLM_apply,
    Complex.ofRealCLM_apply, TauCeti.hermiteSchwartzMap_apply,
    TauCeti.hermiteFunction_zero, Complex.real_smul, ← Complex.ofReal_mul]
  congr 1
  field_simp

/-- The same expanding scale already used by the actual compact cutoffs. -/
def gaussianCutoff (N : ℕ) : SchwartzMap ℝ ℂ :=
  SchwartzMap.compCLM ℂ
    (by fun_prop : (fun x : ℝ => compactSchwartzCutoffScale N * x).HasTemperateGrowth)
    (by
      refine ⟨1, (N : ℝ) + 1, fun x => ?_⟩
      have hc := compactSchwartzCutoffScale_pos N
      simp only [pow_one, Real.norm_eq_abs, abs_mul, abs_of_pos hc]
      have he : ((N : ℝ) + 1) * compactSchwartzCutoffScale N = 1 := by
        unfold compactSchwartzCutoffScale
        field_simp
      nlinarith [abs_nonneg x]) gaussianBase

/-- These are precisely positive Gaussian damping parameters. -/
def dampingParameter (N : ℕ) : ℝ := compactSchwartzCutoffScale N ^ 2 / 2

/-- Every actual damping parameter is positive. -/
theorem dampingParameter_pos (N : ℕ) : 0 < dampingParameter N := by
  unfold dampingParameter
  exact div_pos (sq_pos_of_pos (compactSchwartzCutoffScale_pos N)) (by norm_num)

/-- The multiplier is the stated Gaussian, not an assigned surrogate. -/
theorem gaussianCutoff_apply (N : ℕ) (x : ℝ) :
    gaussianCutoff N x = (Real.exp (-dampingParameter N * x ^ 2) : ℂ) := by
  change gaussianBase (compactSchwartzCutoffScale N * x) = _
  rw [gaussianBase_apply]
  congr 2
  unfold dampingParameter
  ring

/-- Gaussian multiplication is a pointwise contraction. -/
theorem gaussianCutoff_norm_le_one (N : ℕ) (x : ℝ) : ‖gaussianCutoff N x‖ ≤ 1 := by
  rw [gaussianCutoff_apply, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_one_iff.mpr
  nlinarith [dampingParameter_pos N, sq_nonneg x]

/-- The actual parameters tend to zero. -/
theorem dampingParameter_tendsto : Tendsto dampingParameter atTop (𝓝 0) := by
  change Tendsto (fun N => compactSchwartzCutoffScale N ^ 2 / 2) atTop (𝓝 0)
  simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_div] using
    (compactSchwartzCutoffScale_tendsto.pow 2).div_const 2

/-- On every real input, including negative inputs, damping tends to one. -/
theorem gaussianCutoff_tendsto (x : ℝ) :
    Tendsto (fun N => gaussianCutoff N x) atTop (𝓝 1) := by
  simp only [gaussianCutoff_apply]
  have ht : Tendsto (fun N => Real.exp (-dampingParameter N * x ^ 2)) atTop (𝓝 1) := by
    have hz : Tendsto (fun N => -dampingParameter N * x ^ 2) atTop (𝓝 0) := by
      simpa only [neg_zero, zero_mul] using dampingParameter_tendsto.neg.mul_const (x ^ 2)
    simpa only [Real.exp_zero, Function.comp_def] using (Real.continuous_exp.tendsto (0 : ℝ)).comp hz
  exact (Complex.continuous_ofReal.tendsto (1 : ℝ)).comp ht

/-- Exact derivatives of the dilated Gaussian Schwartz multiplier. -/
theorem gaussianCutoff_iteratedDeriv (N i : ℕ) (x : ℝ) :
    iteratedDeriv i (gaussianCutoff N) x = compactSchwartzCutoffScale N ^ i •
      iteratedDeriv i gaussianBase (compactSchwartzCutoffScale N * x) := by
  exact congrFun (iteratedDeriv_comp_const_smul (gaussianBase.smooth i)
    (compactSchwartzCutoffScale N)) x

/-- Uniform derivative bounds retain the small scaling factor. -/
theorem gaussianCutoff_iteratedDeriv_bound (N i : ℕ) (x : ℝ) :
    ‖iteratedDeriv i (gaussianCutoff N) x‖ ≤ compactSchwartzCutoffScale N ^ i *
      SchwartzMap.seminorm ℂ 0 i gaussianBase := by
  rw [gaussianCutoff_iteratedDeriv, norm_smul, Real.norm_eq_abs, abs_pow,
    abs_of_pos (compactSchwartzCutoffScale_pos N)]
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg (compactSchwartzCutoffScale_pos N).le i)
  simpa only [pow_zero, one_mul] using
    SchwartzMap.le_seminorm' ℂ 0 i gaussianBase (compactSchwartzCutoffScale N * x)

/-- Every positive-order derivative tends pointwise to zero. -/
theorem gaussianCutoff_iteratedDeriv_tendsto {i : ℕ} (hi : 0 < i) (x : ℝ) :
    Tendsto (fun N => iteratedDeriv i (gaussianCutoff N) x) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) (fun N => gaussianCutoff_iteratedDeriv_bound N i x)
  simpa [zero_pow hi.ne'] using
    (compactSchwartzCutoffScale_tendsto.pow i).mul_const (SchwartzMap.seminorm ℂ 0 i gaussianBase)

/-- Damping of a genuine L2 representative remains in L2. -/
theorem damped_memLp (N : ℕ) (q : KNSL2) :
    MemLp (fun x : ℝ => gaussianCutoff N x * q x) 2 := by
  apply (Lp.memLp q).of_le_mul (c := 1)
    ((gaussianCutoff N).continuous.aestronglyMeasurable.mul (Lp.memLp q).aestronglyMeasurable)
  filter_upwards [] with x
  change ‖gaussianCutoff N x * q x‖ ≤ 1 * ‖q x‖
  simpa only [norm_mul, one_mul] using
    mul_le_mul_of_nonneg_right (gaussianCutoff_norm_le_one N x) (norm_nonneg (q x))

/-- The actual frequency-damped L2 class. -/
def damped (N : ℕ) (q : KNSL2) : KNSL2 := (damped_memLp N q).toLp

/-- Damping is a contraction on the genuine L2 class. -/
theorem damped_norm_le (N : ℕ) (q : KNSL2) : ‖damped N q‖ ≤ ‖q‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [(damped_memLp N q).coeFn_toLp] with x hx
  change ‖((damped_memLp N q).toLp : KNSL2) x‖ ≤ ‖q x‖
  rw [hx, norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (gaussianCutoff_norm_le_one N x)


/-- L2 dominated convergence with an actual fixed L2 majorant. -/
theorem toLp_tendsto_of_dominated {F : ℕ → ℝ → ℂ} {f : ℝ → ℂ}
    (hF : ∀ n, MemLp (F n) 2) (hf : MemLp f 2) (q : KNSL2) {C : ℝ} (_hC : 0 ≤ C)
    (hbound : ∀ n, ∀ᵐ x, ‖F n x - f x‖ ≤ C * ‖q x‖)
    (hlim : ∀ᵐ x, Tendsto (fun n => F n x) atTop (𝓝 (f x))) :
    Tendsto (fun n => (hF n).toLp) atTop (𝓝 hf.toLp) := by
  have hsq : Tendsto (fun n => ∫ x : ℝ, ‖F n x - f x‖ ^ 2) atTop (𝓝 0) := by
    have hb : Integrable (fun x : ℝ => C ^ 2 * ‖q x‖ ^ 2) :=
      (integrable_norm_sq_of_memLp_complex (Lp.memLp q)).const_mul _
    have h := tendsto_integral_of_dominated_convergence
      (fun x : ℝ => C ^ 2 * ‖q x‖ ^ 2)
      (fun n => ((hF n).sub hf).aestronglyMeasurable.norm.pow 2) hb
      (fun n => ?_) (f := fun _ : ℝ => (0 : ℝ)) ?_
    · simpa only [Pi.pow_apply, Pi.sub_apply, integral_zero] using h
    · filter_upwards [hbound n] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      calc
        ‖F n x - f x‖ ^ 2 ≤ (C * ‖q x‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hx _
        _ = _ := mul_pow _ _ _
    · filter_upwards [hlim] with x hx
      simpa only [Pi.pow_apply, Pi.sub_apply, sub_self, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using
        (hx.sub_const (f x)).norm.pow 2
  have hs : Tendsto (fun n => ‖(hF n).toLp - hf.toLp‖ ^ 2) atTop (𝓝 0) := by
    convert hsq using 1
    ext n
    change ‖((hF n).sub hf).toLp‖ ^ 2 = _
    exact (integral_norm_sq_eq_toLp_norm_sq_complex ((hF n).sub hf)).symm
  have hn := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hs
  have ht : Tendsto (fun n => ‖(hF n).toLp - hf.toLp‖) atTop (𝓝 0) := by
    convert hn using 1
    · funext n
      exact (Real.sqrt_sq (norm_nonneg ((hF n).toLp - hf.toLp))).symm
    · simp only [Real.sqrt_zero]
  exact tendsto_iff_norm_sub_tendsto_zero.mpr ht

/-- Strong L2 damping convergence holds for every actual L2 input. -/
theorem damped_tendsto (q : KNSL2) : Tendsto (fun N => damped N q) atTop (𝓝 q) := by
  have ht := toLp_tendsto_of_dominated (fun N => damped_memLp N q) (Lp.memLp q) q
    (C := 2) (by norm_num) (fun N => ?_) ?_
  · simpa only [Lp.toLp_coeFn, damped] using ht
  · filter_upwards [] with x
    calc
      ‖gaussianCutoff N x * q x - q x‖ ≤ ‖gaussianCutoff N x * q x‖ + ‖q x‖ :=
        norm_sub_le _ _
      _ ≤ 2 * ‖q x‖ := by
        rw [norm_mul]
        nlinarith [mul_le_mul_of_nonneg_right (gaussianCutoff_norm_le_one N x) (norm_nonneg (q x))]
  · filter_upwards [] with x
    simpa only [one_mul] using (gaussianCutoff_tendsto x).mul_const (q x)

/-- Gaussian damping supplies every integrable moment of rough L2 data. -/
theorem damped_integrable_moment (N : ℕ) (q : KNSL2) (j : ℕ) :
    Integrable (fun x : ℝ => x ^ j • (gaussianCutoff N x * q x)) := by
  let P : SchwartzMap ℝ ℂ := SchwartzMap.smulLeftCLM ℂ
    (fun x : ℝ => (x : ℂ) ^ j) (gaussianCutoff N)
  have h := (P.memLp 2 volume).integrable_mul (Lp.memLp q)
  convert h using 1
  ext x
  simp only [Pi.mul_apply, P, SchwartzMap.smulLeftCLM_apply_apply (by fun_prop :
    (fun x : ℝ => (x : ℂ) ^ j).HasTemperateGrowth), smul_eq_mul,
    Complex.real_smul, Complex.ofReal_pow]
  ring

/-- The genuine inverse Fourier integral of damped data is smooth. -/
theorem damped_inverse_contDiff (N : ℕ) (q : KNSL2) :
    ContDiff ℝ ∞ (𝓕⁻ (fun x : ℝ => gaussianCutoff N x * q x)) := by
  rw [Real.fourierInv_eq_fourier_comp_neg, contDiff_infty]
  intro j
  apply contDiff_fourier_of_integrable_moments_le
  intro i hi
  have h := (damped_integrable_moment N q i).comp_neg
  apply (h.smul ((-1 : ℝ) ^ i)).congr
  filter_upwards [] with x
  change (-1 : ℝ) ^ i • ((-x) ^ i • (gaussianCutoff N (-x) * q (-x))) =
    x ^ i • (gaussianCutoff N (-x) * q (-x))
  simp only [smul_smul, ← mul_pow, neg_one_mul, neg_neg]


/-- Actual multiplication of any L2 input by a Schwartz function. -/
theorem mulSchwartz_memLp (g : SchwartzMap ℝ ℂ) (q : KNSL2) :
    MemLp (fun x : ℝ => g x * q x) 2 := by
  apply (Lp.memLp q).of_le_mul (c := SchwartzMap.seminorm ℂ 0 0 g)
    (g.continuous.aestronglyMeasurable.mul (Lp.memLp q).aestronglyMeasurable)
  filter_upwards [] with x
  change ‖g x * q x‖ ≤ _
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  simpa only [pow_zero, iteratedDeriv_zero, one_mul] using SchwartzMap.le_seminorm' ℂ 0 0 g x

/-- The L2 product is built from proved membership. -/
def mulSchwartz (g : SchwartzMap ℝ ℂ) (q : KNSL2) : KNSL2 :=
  (mulSchwartz_memLp g q).toLp

/-- The actual multiplication representative holds almost everywhere. -/
theorem mulSchwartz_ae (g : SchwartzMap ℝ ℂ) (q : KNSL2) :
    (mulSchwartz g q : ℝ → ℂ) =ᵐ[volume] fun x => g x * q x :=
  (mulSchwartz_memLp g q).coeFn_toLp

/-- Uniform multiplier bounds yield the corresponding genuine L2 bound. -/
theorem mulSchwartz_norm_le (g : SchwartzMap ℝ ℂ) (q : KNSL2)
    {C : ℝ} (hC : ∀ x, ‖g x‖ ≤ C) :
    ‖mulSchwartz g q‖ ≤ C * ‖q‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [mulSchwartz_ae g q] with x hx
  rw [hx, norm_mul]
  exact mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _)

/-- Multiplication agrees with the actual distributional multiplication. -/
theorem mulSchwartz_distribution (g : SchwartzMap ℝ ℂ) (q : KNSL2) :
    (mulSchwartz g q : TemperedDistribution ℝ ℂ) =
      TemperedDistribution.smulLeftCLM ℂ g (q : TemperedDistribution ℝ ℂ) := by
  ext φ
  simp only [Lp.toTemperedDistribution_apply, TemperedDistribution.smulLeftCLM_apply_apply]
  apply integral_congr_ae
  filter_upwards [mulSchwartz_ae g q] with x hx
  rw [hx, SchwartzMap.smulLeftCLM_apply_apply g.hasTemperateGrowth]
  simp only [smul_eq_mul]
  ring

/-- The derivative jet is the actual iterated Schwartz derivative. -/
def gaussianJet (N i : ℕ) : SchwartzMap ℝ ℂ :=
  ((SchwartzMap.derivCLM ℂ ℂ)^[i]) (gaussianCutoff N)

/-- The jet evaluates to the actual classical derivative. -/
theorem gaussianJet_apply (N i : ℕ) (x : ℝ) :
    gaussianJet N i x = iteratedDeriv i (gaussianCutoff N) x :=
  schwartzDerivative_iterate_apply i (gaussianCutoff N) x

/-- The zeroth jet multiplier converges strongly to the identity. -/
theorem gaussianJet_zero_tendsto (q : KNSL2) :
    Tendsto (fun N => mulSchwartz (gaussianJet N 0) q) atTop (𝓝 q) := by
  exact damped_tendsto q

/-- Every positive jet multiplier vanishes strongly on each actual L2 input. -/
theorem gaussianJet_succ_tendsto {i : ℕ} (hi : 0 < i) (q : KNSL2) :
    Tendsto (fun N => mulSchwartz (gaussianJet N i) q) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _)
    (fun N => mulSchwartz_norm_le (gaussianJet N i) q (fun x => by
      rw [gaussianJet_apply]
      exact gaussianCutoff_iteratedDeriv_bound N i x))
  simpa only [zero_pow hi.ne', zero_mul] using
    ((compactSchwartzCutoffScale_tendsto.pow i).mul_const
      (SchwartzMap.seminorm ℂ 0 i gaussianBase)).mul_const ‖q‖

end
end MeyerGeneralProblem.GaussianDamping
