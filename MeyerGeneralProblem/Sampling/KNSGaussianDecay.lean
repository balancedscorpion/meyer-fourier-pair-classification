module

public import MeyerGeneralProblem.Sampling.KNSStageBFactorial

@[expose] public section

/-!
# Gaussian weighted square integrability from the actual KNS bootstrap

The positive exponent is fixed by the reciprocal-gap margin alone. The
exponential series is interchanged with the nonnegative integral exactly;
the finitely many low moments need only be finite, not uniformly bounded.
-/

namespace MeyerGeneralProblem

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal FourierTransform ContDiff Topology

/-- A Gaussian exponent determined before the carrier exceptions and the
function, using the already proved factorial base. -/
def knsGaussianParameter (ρ : ℝ) : ℝ := 1/(2*knsStageBFactorialBase ρ)

/-- The chosen Gaussian exponent is positive and leaves exactly a factor
one-half in the exponential moment series. -/
theorem knsGaussianParameter_properties {ρ : ℝ} (hρ : 0 < ρ) (hρhalf : ρ < 1/2) :
    0 < knsGaussianParameter ρ ∧
      knsGaussianParameter ρ*knsStageBFactorialBase ρ = 1/2 := by
  have hC := knsStageBFactorialBase_pos hρ hρhalf
  constructor
  · exact div_pos (by norm_num) (mul_pos (by norm_num) hC)
  · dsimp only [knsGaussianParameter]
    field_simp

/-- Exact nonnegative exponential-series interchange for Gaussian square
energy. No finiteness of the energy or moments is needed for this identity. -/
theorem lintegral_knsGaussian_eq_tsum {a : ℝ} (ha : 0 ≤ a) {f : ℝ → ℂ}
    (hf : Continuous f) :
    (∫⁻ x, ENNReal.ofReal (Real.exp (a*x^2))*ENNReal.ofReal (‖f x‖^2)) =
      ∑' n : ℕ, ENNReal.ofReal (a^n/(n.factorial : ℝ))*knsPowerEnergy n f := by
  have hseries (x : ℝ) : ENNReal.ofReal (Real.exp (a*x^2)) =
      ∑' n : ℕ, ENNReal.ofReal (a^n/(n.factorial : ℝ))*ENNReal.ofReal (x^(2*n)) := by
    have hs : HasSum (fun n : ℕ => (a*x^2)^n/(n.factorial : ℝ)) (Real.exp (a*x^2)) := by
      simpa only [Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp (a*x^2)
    rw [← hs.tsum_eq,ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hs.summable]
    apply tsum_congr
    intro n
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ a^n/(n.factorial : ℝ))]
    congr 1
    rw [mul_pow,← pow_mul]
    ring
  simp_rw [hseries,← ENNReal.tsum_mul_right]
  rw [lintegral_tsum]
  · apply tsum_congr
    intro n
    simp only [mul_assoc,lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,knsPowerEnergy]
  · intro n
    exact ((measurable_const.mul ((measurable_id.pow_const (2*n)).ennreal_ofReal)).mul
      (hf.norm.pow 2).measurable.ennreal_ofReal).aemeasurable

/-- Eventual factorial control yields actual Gaussian square integrability
whenever the exponent times the factorial base is below one. Finite low
moments are retained explicitly and need no uniform bound. -/
theorem integrable_knsGaussian_of_eventual_factorialMoments
    {a C M : ℝ} (ha : 0 ≤ a) (hC : 0 ≤ C) (hac : a*C < 1)
    {f : ℝ → ℂ} (hf : Continuous f)
    (hm : ∀ n : ℕ, Integrable (fun x => x^(2*n)*‖f x‖^2))
    (hbound : ∃ n0 : ℕ, ∀ n ≥ n0,
      (∫ x, x^(2*n)*‖f x‖^2) ≤ C^n*(n.factorial : ℝ)*M) :
    Integrable (fun x => Real.exp (a*x^2)*‖f x‖^2) := by
  let c : ℕ → ℝ := fun n => a^n/(n.factorial : ℝ)*(∫ x, x^(2*n)*‖f x‖^2)
  have hc (n : ℕ) : 0 ≤ c n := by
    dsimp only [c]
    apply mul_nonneg (by positivity)
    exact integral_nonneg (fun x => mul_nonneg
      (show 0 ≤ x^(2*n) by rw [pow_mul]; positivity) (sq_nonneg _))
  have hsum : Summable c := by
    apply ((summable_geometric_of_lt_one (mul_nonneg ha hC) hac).mul_right M).of_norm_bounded_eventually_nat
    obtain ⟨n0,hn0⟩ := hbound
    filter_upwards [eventually_ge_atTop n0] with n hn
    rw [Real.norm_of_nonneg (hc n)]
    have h := mul_le_mul_of_nonneg_left (hn0 n hn)
      (by positivity : 0 ≤ a^n/(n.factorial : ℝ))
    change c n ≤ (a*C)^n*M
    convert! h using 1
    rw [mul_pow]
    have hnfac : (n.factorial : ℝ) ≠ 0 := by positivity
    field_simp
  apply (lintegral_ofReal_ne_top_iff_integrable
    ((Real.continuous_exp.comp (continuous_const.mul (continuous_id.pow 2))).mul
      (hf.norm.pow 2)).aestronglyMeasurable
    (Eventually.of_forall (fun x => mul_nonneg (Real.exp_pos _).le (sq_nonneg _)))).mp
  change (∫⁻ x, ENNReal.ofReal (Real.exp (a*x^2)*‖f x‖^2)) ≠ ⊤
  simp_rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
  rw [lintegral_knsGaussian_eq_tsum ha hf]
  have he : (∑' n : ℕ, ENNReal.ofReal (a^n/(n.factorial : ℝ))*knsPowerEnergy n f) =
      ENNReal.ofReal (∑' n : ℕ, c n) := by
    rw [ENNReal.ofReal_tsum_of_nonneg hc hsum]
    apply tsum_congr
    intro n
    rw [knsPowerEnergy_eq_ofReal_integral n (hm n),← ENNReal.ofReal_mul (by positivity)]
  rw [he]
  exact ENNReal.ofReal_ne_top

/-- Actual reciprocal-gap Fourier pairs have Gaussian weighted square
integrability on both sides. The positive exponent depends only on rho;
independent finite zero and gap exceptions remain allowed. Only the two
second moments are inputs: Stage A and Stage B supply the other moments. -/
theorem knsGaussianDecay_of_reciprocal_gaps
    {ρ : ℝ} (hρ : 0 < ρ) (hρhalf : ρ < 1/2)
    (Λ M : TwoSidedCarrier) (F J G L : Finset ℤ)
    (hgapΛ : ∀ j : ℤ, j ∉ J → max |Λ j| |Λ (j+1)| * (Λ (j+1)-Λ j) ≤ ρ)
    (hgapM : ∀ j : ℤ, j ∉ L → max |M j| |M (j+1)| * (M (j+1)-M j) ≤ ρ)
    {f : ℝ → ℂ} (hf : ContDiff ℝ 1 f) (hF : ContDiff ℝ 1 (𝓕 f))
    (hf1 : Integrable f) (hF1 : Integrable (𝓕 f)) (hf2 : MemLp f 2)
    (hx2 : Integrable (fun x => x^2*‖f x‖^2))
    (hξ2 : Integrable (fun ξ => ξ^2*‖𝓕 f ξ‖^2))
    (hzΛ : ∀ j : ℤ, j ∉ F → f (Λ j) = 0)
    (hzM : ∀ j : ℤ, j ∉ G → 𝓕 f (M j) = 0) :
    Integrable (fun x => Real.exp (knsGaussianParameter ρ*x^2)*‖f x‖^2) ∧
      Integrable (fun ξ => Real.exp (knsGaussianParameter ρ*ξ^2)*‖𝓕 f ξ‖^2) := by
  have hC := knsStageBFactorialBase_pos hρ hρhalf
  obtain ⟨ha,haC⟩ := knsGaussianParameter_properties hρ hρhalf
  have hac : knsGaussianParameter ρ*knsStageBFactorialBase ρ < 1 := by
    rw [haC]
    norm_num
  have hσ := (knsStageB_parameters hρ hρhalf).2.1
  have hgΛ : ∀ j : ℤ, j ∉ J →
      max |Λ j| |Λ (j+1)| * (Λ (j+1)-Λ j) ≤ (2*knsStageBSigma ρ)⁻¹ := by
    simpa only [knsStageBSigma_reciprocal hρ] using hgapΛ
  have hgM : ∀ j : ℤ, j ∉ L →
      max |M j| |M (j+1)| * (M (j+1)-M j) ≤ (2*knsStageBSigma ρ)⁻¹ := by
    simpa only [knsStageBSigma_reciprocal hρ] using hgapM
  have hm := knsStageA_all_squareMoments Λ M F J G L hσ hgΛ hgM
    hf hF hf1 hF1 hf2 hx2 hξ2 hzΛ hzM
  obtain ⟨n0,_,hfact⟩ := knsStageB_eventual_factorialMoments hρ hρhalf Λ M F J G L hgapΛ hgapM
  have hpair := hfact f hf hF hf1 hF1 hf2 hx2 hξ2 hzΛ hzM
  constructor
  · apply integrable_knsGaussian_of_eventual_factorialMoments ha.le hC.le hac
      hf.continuous (fun n => (hm n).1)
    refine ⟨n0,fun n hn => ?_⟩
    have hy : 0 ≤ ∫ ξ, ξ^(2*n)*‖𝓕 f ξ‖^2 := integral_nonneg (fun ξ => mul_nonneg
      (show 0 ≤ ξ^(2*n) by rw [pow_mul]; positivity) (sq_nonneg _))
    exact (le_add_of_nonneg_right hy).trans (hpair n hn)
  · apply integrable_knsGaussian_of_eventual_factorialMoments ha.le hC.le hac
      hF.continuous (fun n => (hm n).2)
    refine ⟨n0,fun n hn => ?_⟩
    have hx : 0 ≤ ∫ x, x^(2*n)*‖f x‖^2 := integral_nonneg (fun x => mul_nonneg
      (show 0 ≤ x^(2*n) by rw [pow_mul]; positivity) (sq_nonneg _))
    exact (le_add_of_nonneg_left hx).trans (hpair n hn)

end

end MeyerGeneralProblem
