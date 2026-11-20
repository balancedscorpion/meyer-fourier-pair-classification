module

public import MeyerGeneralProblem.Sampling.BeurlingSmoothing
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

@[expose] public section

/-!
# Compact positive Fourier smoothing on a prescribed frequency band

A sufficiently narrow nonnegative unit-mass bump has Fourier transform close
to one on the entire prescribed band. Its smooth autocorrelation therefore
has a strictly positive Fourier floor, not just a prescribed value at zero.
All transforms are the actual negative-`2π` Fourier transform.
-/

namespace MeyerGeneralProblem

noncomputable section

open MeasureTheory
open scoped SchwartzMap FourierTransform ContDiff ComplexConjugate

/-- The actual Fourier phase is Lipschitz at time zero with its exact frequency scale. -/
theorem norm_gramPhase_sub_one_le (w t : ℝ) :
    ‖gramPhase w t - 1‖ ≤ 2 * Real.pi * |w| * |t| := by
  have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := 2 * Real.pi * w * t)
  simpa only [gramPhase, mul_comm Complex.I, Real.norm_eq_abs, abs_mul,
    abs_of_pos Real.pi_pos, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)] using h

/-- A nonnegative unit-mass function supported near zero has an actual
Fourier transform uniformly close to one on bounded frequency intervals. -/
theorem norm_fourier_sub_one_le_of_nonnegative_mass
    {h : ℝ → ℝ} (hh : Continuous h) (hhc : HasCompactSupport h)
    (hpos : ∀ t, 0 ≤ h t) (hmass : ∫ t : ℝ, h t = 1)
    {ρ : ℝ} (_hρ : 0 ≤ ρ) (hs : Function.support h ⊆ Set.Icc (-ρ) ρ)
    (w : ℝ) :
    ‖FourierTransform.fourier (fun t => (h t : ℂ)) w - 1‖ ≤
      2 * Real.pi * |w| * ρ := by
  have hint : Integrable h := hh.integrable_of_hasCompactSupport hhc
  have hhc' : HasCompactSupport (fun t => (h t : ℂ)) :=
    hhc.comp_left (g := Complex.ofReal) (by simp)
  have hcont : Continuous (fun t => (gramPhase (-w) t - 1) * (h t : ℂ)) := by
    unfold gramPhase
    fun_prop
  have hsupport : HasCompactSupport (fun t => (gramPhase (-w) t - 1) * (h t : ℂ)) := by
    apply HasCompactSupport.of_support_subset_isCompact hhc.isCompact
    intro t ht
    apply subset_closure
    intro hz
    exact ht (by simp [hz])
  have hfi : Integrable (fun t => gramPhase (-w) t * (h t : ℂ)) := by
    exact (show Continuous (fun t => gramPhase (-w) t * (h t : ℂ)) by
      unfold gramPhase; fun_prop).integrable_of_hasCompactSupport
        hhc'.mul_left
  have heq : FourierTransform.fourier (fun t => (h t : ℂ)) w - 1 =
      ∫ t : ℝ, (gramPhase (-w) t - 1) * (h t : ℂ) := by
    have hmassC : (∫ t : ℝ, (h t : ℂ)) = 1 := by
      rw [integral_complex_ofReal, hmass]; norm_num
    calc
      _ = (∫ t : ℝ, gramPhase (-w) t * (h t : ℂ)) - ∫ t : ℝ, (h t : ℂ) := by
        rw [hmassC, fourier_eq_integral_gramPhase]
      _ = ∫ t : ℝ, gramPhase (-w) t * (h t : ℂ) - (h t : ℂ) :=
        (integral_sub hfi hint.ofReal).symm
      _ = _ := by
        congr 1
        funext t
        ring
  rw [heq]
  calc
    _ ≤ ∫ t : ℝ, ‖(gramPhase (-w) t - 1) * (h t : ℂ)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t : ℝ, (2 * Real.pi * |w| * ρ) * h t := by
      apply integral_mono (hcont.integrable_of_hasCompactSupport hsupport).norm
        (hint.const_mul _)
      intro t
      dsimp only
      by_cases ht : h t = 0
      · simp [ht]
      · have habs := abs_le.mpr (hs ht)
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hpos t)]
        exact mul_le_mul_of_nonneg_right
          ((norm_gramPhase_sub_one_le (-w) t).trans (by rw [abs_neg]; gcongr)) (hpos t)
    _ = _ := by rw [integral_const_mul, hmass, mul_one]

/-- Every support budget and finite frequency band permit an actual compact
Schwartz smoother with Fourier value one at zero, nonnegative Fourier
transform everywhere, and a uniform quarter-unit floor on the whole band. -/
theorem exists_compact_positive_fourier_band_smoothing
    {r D : ℝ} (hr : 0 < r) (hD : 0 ≤ D) :
    ∃ G : SchwartzMap ℝ ℂ,
      Function.support G ⊆ Set.Icc (-r) r ∧
      FourierTransform.fourier (G : ℝ → ℂ) 0 = 1 ∧
      (∀ w : ℝ, ∃ z : ℝ, 0 ≤ z ∧ FourierTransform.fourier (G : ℝ → ℂ) w = z) ∧
      (∀ w : ℝ, |w| ≤ D → (1 / 4 : ℝ) ≤
        (FourierTransform.fourier (G : ℝ → ℂ) w).re) := by
  let ρ := min (r / 2) (1 / (4 * Real.pi * (D + 1)))
  have hρ : 0 < ρ := lt_min (by positivity) (by positivity)
  have hρr : ρ + ρ ≤ r := by have := min_le_left (r / 2) (1 / (4 * Real.pi * (D + 1))); dsimp [ρ]; linarith
  have hρD : 4 * Real.pi * (D + 1) * ρ ≤ 1 := by
    have h : ρ ≤ 1 / (4 * Real.pi * (D + 1)) := min_le_right _ _
    simpa only [mul_comm] using
      (le_div_iff₀ (by positivity : 0 < 4 * Real.pi * (D + 1))).mp h
  let b : ContDiffBump (0 : ℝ) := ⟨ρ / 2, ρ, by positivity, by linarith⟩
  let h : ℝ → ℂ := fun t => (b.normed volume t : ℂ)
  have hh : Integrable h := b.integrable_normed.ofReal
  have hhsm : ContDiff ℝ ∞ h := Complex.ofRealCLM.contDiff.comp b.contDiff_normed
  have hbs : Function.support (b.normed volume) ⊆ Set.Icc (-ρ) ρ := by
    intro t ht
    rw [b.support_normed_eq] at ht
    have habs : |t| < ρ := by simpa [Metric.mem_ball, Real.dist_eq, b] using ht
    exact ⟨(abs_lt.mp habs).1.le, (abs_lt.mp habs).2.le⟩
  have hhs : Function.support h ⊆ Set.Icc (-ρ) ρ := by
    intro t ht
    exact hbs (by simpa only [Function.mem_support, h, ne_eq, Complex.ofReal_eq_zero] using ht)
  have href : (fun t => conj (h (-t))) = h := by
    funext t
    simp only [h, Complex.conj_ofReal, b.normed_neg]
  obtain ⟨G, hG, hGs⟩ := exists_schwartz_fourierKernelConvolution hh hhs hhs hhsm
  have hfourier (w : ℝ) : FourierTransform.fourier (G : ℝ → ℂ) w =
      (‖FourierTransform.fourier h w‖ ^ 2 : ℝ) := by
    rw [hG, fourier_fourierKernelConvolution hh hh]
    conv_lhs => rhs; rw [← href, fourier_conj_reflect]
    simpa only [Complex.ofReal_pow] using Complex.mul_conj' (FourierTransform.fourier h w)
  refine ⟨G, ?_, ?_, fun w => ⟨_, sq_nonneg _, hfourier w⟩, ?_⟩
  · intro t ht
    have ht' := hGs ht
    exact ⟨by linarith [ht'.1], by linarith [ht'.2]⟩
  · have hz : FourierTransform.fourier h 0 = 1 := by
      rw [fourier_eq_integral_gramPhase]
      simp only [neg_zero, gramPhase_zero_left, one_mul, h]
      rw [integral_complex_ofReal, b.integral_normed]
      norm_num
    rw [hfourier, hz]
    norm_num
  · intro w hw
    have hclose := norm_fourier_sub_one_le_of_nonnegative_mass b.continuous_normed
      b.hasCompactSupport_normed (fun t => b.nonneg_normed t) b.integral_normed hρ.le hbs w
    change ‖FourierTransform.fourier h w - 1‖ ≤ _ at hclose
    have hscale : 2 * Real.pi * |w| * ρ ≤ 1 / 2 := by
      have hle : 2 * Real.pi * |w| * ρ ≤ 2 * Real.pi * (D + 1) * ρ := by
        gcongr
        linarith
      nlinarith
    have hnorm : (1 / 2 : ℝ) ≤ ‖FourierTransform.fourier h w‖ := by
      have htriangle := norm_sub_le (FourierTransform.fourier h w)
        (FourierTransform.fourier h w - 1)
      simp only [sub_sub_cancel, norm_one] at htriangle
      linarith
    rw [hfourier, Complex.ofReal_re]
    nlinarith

/-- A positive Fourier floor on a slightly larger band gives one bound for
every genuine reciprocal derivative through a fixed order on the inner band.
There is no assumed derivative bound or inverse node gap. -/
theorem exists_uniform_reciprocal_fourier_derivative_bound
    (G : SchwartzMap ℝ ℂ) {D : ℝ} (_hD : 0 ≤ D)
    (hfloor : ∀ w : ℝ, |w| ≤ D + 1 → (1 / 4 : ℝ) ≤
      (FourierTransform.fourier (G : ℝ → ℂ) w).re) (q : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ j ≤ q, ∀ w : ℝ, |w| ≤ D →
      ‖iteratedDeriv j (fun t : ℝ =>
        (FourierTransform.fourier (G : ℝ → ℂ) t)⁻¹) w‖ ≤ C := by
  let f : ℝ → ℂ := fun t => (FourierTransform.fourier (G : ℝ → ℂ) t)⁻¹
  let U := Set.Ioo (-(D + 1)) (D + 1)
  have hne (w : ℝ) (hw : w ∈ U) : FourierTransform.fourier (G : ℝ → ℂ) w ≠ 0 := by
    have hf := hfloor w (abs_le.mpr ⟨hw.1.le, hw.2.le⟩)
    intro hz
    rw [hz, Complex.zero_re] at hf
    norm_num at hf
  have hsmooth : ContDiffOn ℝ q f U :=
    ((𝓕 G).smooth q).contDiffOn.inv hne
  have hcont (j : Fin (q + 1)) : ContinuousOn (iteratedDeriv j f) (Set.Icc (-D) D) := by
    have hwithin := hsmooth.continuousOn_iteratedDerivWithin
      (show (j:ℕ) ≤ (q:ℕ∞ω) by exact_mod_cast (show (j:ℕ) ≤ q by omega))
      isOpen_Ioo.uniqueDiffOn
    have heq : Set.EqOn (iteratedDerivWithin j f U) (iteratedDeriv j f) U := by
      intro w hw
      exact iteratedDerivWithin_eq_iteratedDeriv isOpen_Ioo.uniqueDiffOn
        (((hsmooth w hw).contDiffAt (isOpen_Ioo.mem_nhds hw)).of_le
          (by exact_mod_cast (show (j:ℕ) ≤ q by omega))) hw
    exact (hwithin.congr heq.symm).mono (by intro w hw; exact ⟨by linarith [hw.1], by linarith [hw.2]⟩)
  choose C hC using fun j : Fin (q + 1) =>
    isCompact_Icc.exists_bound_of_continuousOn (hcont j)
  let B := 1 + ∑ j : Fin (q + 1), |C j|
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨B, hB, ?_⟩
  intro j hj w hw
  let jj : Fin (q + 1) := ⟨j, by omega⟩
  have hsingle : |C jj| ≤ ∑ k : Fin (q + 1), |C k| :=
    Finset.single_le_sum (f := fun k => |C k|) (fun k hk => abs_nonneg _) (Finset.mem_univ jj)
  exact (hC jj w (abs_le.mp hw)).trans ((le_abs_self _).trans (by dsimp [B]; linarith))

/-- One actual smoother works for every finite derivative order: its band
floor and all reciprocal derivative bounds are constructed, not hypotheses. -/
theorem exists_compact_positive_fourier_smoothing_with_reciprocal_bounds
    {r D : ℝ} (hr : 0 < r) (hD : 0 ≤ D) :
    ∃ G : SchwartzMap ℝ ℂ,
      Function.support G ⊆ Set.Icc (-r) r ∧
      FourierTransform.fourier (G : ℝ → ℂ) 0 = 1 ∧
      (∀ w : ℝ, ∃ z : ℝ, 0 ≤ z ∧ FourierTransform.fourier (G : ℝ → ℂ) w = z) ∧
      (∀ w : ℝ, |w| ≤ D → (1 / 4 : ℝ) ≤
        (FourierTransform.fourier (G : ℝ → ℂ) w).re) ∧
      (∀ q : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ j ≤ q, ∀ w : ℝ, |w| ≤ D →
        ‖iteratedDeriv j (fun t : ℝ =>
          (FourierTransform.fourier (G : ℝ → ℂ) t)⁻¹) w‖ ≤ C) := by
  obtain ⟨G, hGs, hG0, hGpos, hfloor⟩ :=
    exists_compact_positive_fourier_band_smoothing hr (show 0 ≤ D + 1 by linarith)
  exact ⟨G, hGs, hG0, hGpos, fun w hw => hfloor w (by linarith),
    fun q => exists_uniform_reciprocal_fourier_derivative_bound G hD hfloor q⟩

end

end MeyerGeneralProblem
