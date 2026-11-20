module

public import MeyerGeneralProblem.Sampling.BeurlingBiorthogonal
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

@[expose] public section

/-!
# Finite interpolation duality on the actual Fourier window

Uniform Bessel bounds for genuine supported interpolation kernels imply the
reciprocal lower Riesz bound for finite exponential sums. The constants do not
depend on the finite dimension.
-/

namespace MeyerGeneralProblem

open MeasureTheory ComplexConjugate

noncomputable section

/-- A Bessel biorthogonal family forces a reciprocal lower bound for the
original family, in any complex inner product space. -/
theorem finite_lowerBound_of_biorthogonal_bessel
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {n : ℕ} (v y : Fin n → H) {B : ℝ} (hB : 0 < B)
    (hbio : ∀ i j, inner ℂ (y i) (v j) = if i = j then 1 else 0)
    (hupper : ∀ c : Fin n → ℂ, ‖∑ i, c i • y i‖ ^ 2 ≤ B * ∑ i, ‖c i‖ ^ 2)
    (c : Fin n → ℂ) :
    B⁻¹ * ∑ i, ‖c i‖ ^ 2 ≤ ‖∑ i, c i • v i‖ ^ 2 := by
  classical
  let E : ℝ := ∑ i, ‖c i‖ ^ 2
  have hE : 0 ≤ E := Finset.sum_nonneg (fun i hi => sq_nonneg _)
  have hip : inner ℂ (∑ i, c i • y i) (∑ i, c i • v i) = (E : ℂ) := by
    simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right, hbio]
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true, E, Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [mul_comm, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  have hcs := norm_inner_le_norm (𝕜 := ℂ) (∑ i, c i • y i) (∑ i, c i • v i)
  rw [hip, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hE] at hcs
  have hsq : E ^ 2 ≤ B * E * ‖∑ i, c i • v i‖ ^ 2 := by
    calc
      E ^ 2 ≤ (‖∑ i, c i • y i‖ * ‖∑ i, c i • v i‖) ^ 2 :=
        (sq_le_sq₀ hE (by positivity)).2 hcs
      _ = ‖∑ i, c i • y i‖ ^ 2 * ‖∑ i, c i • v i‖ ^ 2 := mul_pow _ _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right (hupper c) (sq_nonneg _)
  by_cases hzero : E = 0
  · change B⁻¹ * E ≤ _
    rw [hzero, mul_zero]
    positivity
  · have hpos : 0 < E := lt_of_le_of_ne hE (Ne.symm hzero)
    have hbound : E ≤ B * ‖∑ i, c i • v i‖ ^ 2 := by nlinarith
    change B⁻¹ * E ≤ _
    rw [← div_eq_inv_mul]
    exact (div_le_iff₀ hB).2 (by simpa only [mul_comm] using hbound)

/-- Supported Schwartz interpolation kernels with a common Bessel synthesis
bound yield the actual finite-window exponential lower bound. -/
theorem finite_fourierWindow_lowerBound_of_schwartz_bessel
    {n : ℕ} (s : Fin n → ℝ) {a B : ℝ} (hB : 0 < B)
    (v : Fin n → SchwartzMap ℝ ℂ)
    (hsupp : ∀ i, Function.support (v i) ⊆ Set.Icc (-a) a)
    (hfourier : ∀ i j, FourierTransform.fourier (v i : ℝ → ℂ) (s j) =
      if i = j then 1 else 0)
    (hupper : ∀ c : Fin n → ℂ,
      (∫ t : ℝ, ‖(∑ i, c i • v i : SchwartzMap ℝ ℂ) t‖ ^ 2) ≤
        B * ∑ i, ‖c i‖ ^ 2)
    (c : Fin n → ℂ) :
    B⁻¹ * ∑ i, ‖c i‖ ^ 2 ≤
      ∫ t : ℝ in Set.Icc (-a) a, ‖gramFourierPolynomial s c t‖ ^ 2 := by
  classical
  let hyv (i : Fin n) : MemLp (v i : ℝ → ℂ) 2 (volume.restrict (Set.Icc (-a) a)) :=
    ((v i).memLp 2).restrict (Set.Icc (-a) a)
  let y : Fin n → FourierWindowSpace a := fun i => (hyv i).toLp (v i)
  have hyae (i : Fin n) : (y i : ℝ → ℂ) =ᵐ[volume.restrict (Set.Icc (-a) a)]
      (v i : ℝ → ℂ) := by
    exact (hyv i).coeFn_toLp
  have hpair (i j : Fin n) : inner ℂ (fourierWindowVector a (s j)) (y i) =
      FourierTransform.fourier (v i : ℝ → ℂ) (s j) := by
    rw [L2.inner_def, fourier_eq_integral_gramPhase]
    calc
      _ = ∫ t : ℝ in Set.Icc (-a) a, gramPhase (-(s j)) t * v i t := by
        apply integral_congr_ae
        filter_upwards [fourierWindowVector_coeFn a (s j), hyae i] with t ht hy
        rw [ht, hy]
        simp only [RCLike.inner_apply, gramPhase_neg_left, mul_comm]
      _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero (fun t ht => by
        have hz : v i t = 0 := not_not.mp (fun h => ht (hsupp i h))
        rw [hz, mul_zero])
  have hbio (i j : Fin n) : inner ℂ (y i) (fourierWindowVector a (s j)) =
      if i = j then 1 else 0 := by
    rw [← inner_conj_symm, hpair, hfourier]
    split_ifs <;> simp
  have henergy (d : Fin n → ℂ) : ‖∑ i, d i • y i‖ ^ 2 =
      ∫ t : ℝ, ‖(∑ i, d i • v i : SchwartzMap ℝ ℂ) t‖ ^ 2 := by
    rw [fourierWindowSpace_norm_sq]
    calc
      _ = ∫ t : ℝ in Set.Icc (-a) a,
          ‖(∑ i, d i • v i : SchwartzMap ℝ ℂ) t‖ ^ 2 := by
        apply integral_congr_ae
        have hterms (i : Fin n) :
            (d i • y i : FourierWindowSpace a) =ᵐ[volume.restrict (Set.Icc (-a) a)]
              fun t => d i * v i t := by
          filter_upwards [Lp.coeFn_smul (d i) (y i), hyae i] with t ht hy
          simp only [ht, Pi.smul_apply, smul_eq_mul, hy]
        filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun i => d i • y i),
          Filter.eventually_all.2 hterms] with t ht hterms
        simp only [ht, Finset.sum_apply, hterms, sum_apply, smul_apply, smul_eq_mul]
      _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero (fun t ht => by
        have hz (i : Fin n) : v i t = 0 := not_not.mp (fun h => ht (hsupp i h))
        simp only [sum_apply, smul_apply, hz,
          smul_zero, Finset.sum_const_zero, norm_zero, zero_pow (by norm_num : 2 ≠ 0)])
  have hbound := finite_lowerBound_of_biorthogonal_bessel
    (fun i => fourierWindowVector a (s i)) y hB hbio
    (fun d => by rw [henergy]; exact hupper d) c
  simpa only [fourierWindowVector_sum_norm_sq] using hbound

end

end MeyerGeneralProblem
