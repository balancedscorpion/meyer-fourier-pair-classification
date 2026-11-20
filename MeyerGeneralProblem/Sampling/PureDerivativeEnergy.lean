module

public import MeyerGeneralProblem.Sampling.SignedSquareSpectralTransfer

@[expose] public section

/-!
# Quantitative pure endpoint derivative energy

Every lower pure derivative energy is at most mass plus top derivative energy.
The angular Fourier normalization and actual continuous representative are
identified before differentiation. No mixed estimate or graph core is assumed.
-/

namespace MeyerGeneralProblem.PureDerivativeEnergy

noncomputable section
open MeasureTheory
open scoped ContDiff FourierTransform

/-- Each lower angular multiplier energy is bounded by the zeroth and top
energies, with coefficient one independent of both derivative indices. -/
theorem lower_multiplier_norm_sq_le {G : ℝ → ℂ} {j k : ℕ}
    (hG : MemLp G 2) (hK : MemLp (fourierDerivativeData k G) 2) (hjk : j ≤ k) :
    ‖(memLp_fourierDerivativeData_of_le hG hK hjk).toLp‖^2 ≤
      ‖hG.toLp‖^2 + ‖hK.toLp‖^2 := by
  have hJ := memLp_fourierDerivativeData_of_le hG hK hjk
  have hp (t : ℝ) : ‖fourierDerivativeData j G t‖^2 ≤
      ‖G t‖^2 + ‖fourierDerivativeData k G t‖^2 := by
    have he (n : ℕ) : ‖fourierDerivativeData n G t‖ =
        ‖-2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)‖^n * ‖G t‖ := by
      rw [fourierDerivativeData, norm_mul, norm_pow]
    by_cases ht : 1 ≤ ‖-2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)‖
    · have hb : ‖fourierDerivativeData j G t‖ ≤ ‖fourierDerivativeData k G t‖ := by
        rw [he j, he k]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ ht hjk) (norm_nonneg _)
      nlinarith [norm_nonneg (fourierDerivativeData j G t),
        norm_nonneg (fourierDerivativeData k G t), sq_nonneg ‖G t‖]
    · have hb : ‖fourierDerivativeData j G t‖ ≤ ‖G t‖ := by
        rw [he j]
        simpa only [one_mul] using mul_le_mul_of_nonneg_right
          (pow_le_one₀ (norm_nonneg _) (le_of_not_ge ht) (n := j)) (norm_nonneg (G t))
      nlinarith [norm_nonneg (fourierDerivativeData j G t), norm_nonneg (G t),
        sq_nonneg ‖fourierDerivativeData k G t‖]
  have hi := integral_mono (integrable_norm_sq_of_memLp_complex hJ)
    ((integrable_norm_sq_of_memLp_complex hG).add
      (integrable_norm_sq_of_memLp_complex hK)) hp
  simp only [Pi.add_apply] at hi
  rw [integral_add (integrable_norm_sq_of_memLp_complex hG)
      (integrable_norm_sq_of_memLp_complex hK),
    integral_norm_sq_eq_toLp_norm_sq_complex hJ,
    integral_norm_sq_eq_toLp_norm_sq_complex hG,
    integral_norm_sq_eq_toLp_norm_sq_complex hK] at hi
  exact hi

/-- All actual lower classical derivatives have one same-order energy
bound from only smoothness, L2 mass and the actual top derivative in L2. -/
theorem exists_lower_derivative_norm_sq_le {f : ℝ → ℂ} (k : ℕ)
    (hf : ContDiff ℝ ∞ f) (hF : MemLp f 2) (hD : MemLp (iteratedDeriv k f) 2)
    (j : ℕ) (hj : j ≤ k) :
    ∃ hJ : MemLp (iteratedDeriv j f) 2,
      ‖hJ.toLp‖^2 ≤ ‖hF.toLp‖^2 + ‖hD.toLp‖^2 := by
  by_cases heq : j = k
  · subst j
    exact ⟨hD, by nlinarith [sq_nonneg ‖hF.toLp‖]⟩
  have hk : 1 ≤ k := by omega
  obtain ⟨hK, _, hnK⟩ := memLp_fourierDerivativeData_of_top_classical_derivative k hf hF hD
  let G : Lp ℂ 2 volume := 𝓕⁻ hF.toLp
  have hM := memLp_fourierDerivativeData_of_le (Lp.memLp G) hK hj
  have hm : ∀ i ≤ j, Integrable (fun t : ℝ => t^i • G t) :=
    fun i hi => integrable_real_moment_of_fourierSobolev (Lp.memLp G) hK (by omega)
  obtain ⟨hJ, hnJ⟩ := memLp_iteratedDeriv_fourier_of_integrable_moments_le hm le_rfl hM
  have hrep : (𝓕 (G : ℝ → ℂ) : ℝ → ℂ) = f :=
    fourierIntegral_inverse_L2_eq_of_fourierSobolev hf.continuous hF hk hK
  have hJf : MemLp (iteratedDeriv j f) 2 := by rwa [hrep] at hJ
  have heJ : hJf.toLp = hJ.toLp := by
    apply MemLp.toLp_congr
    rw [hrep]
  refine ⟨hJf, ?_⟩
  rw [heJ, hnJ]
  have hb := lower_multiplier_norm_sq_le (Lp.memLp G) hK hj
  have hnG : ‖(Lp.memLp G).toLp‖ = ‖hF.toLp‖ := by
    rw [Lp.toLp_coeFn]
    dsimp only [G]
    rw [← Lp.norm_fourier_eq (𝓕⁻ hF.toLp), FourierTransform.fourier_fourierInv_eq]
  rwa [hnG, hnK] at hb

end
end MeyerGeneralProblem.PureDerivativeEnergy
