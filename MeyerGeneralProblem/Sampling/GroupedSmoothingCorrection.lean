module

public import MeyerGeneralProblem.Sampling.GroupedFourierSmoothing
public import MeyerGeneralProblem.Sampling.GroupedFiniteFloor
public import MeyerGeneralProblem.Sampling.GroupedFiniteKernels
public import MeyerGeneralProblem.Interpolation.UniformNewtonBounds
public import MeyerGeneralProblem.Interpolation.GroupedSubdata
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.Calculus.ContDiff.Polynomial

@[expose] public section

/-!
# Smooth reciprocal correction of grouped Fourier data

A globally smooth regularized reciprocal agrees with the true complex inverse
on the positive Fourier band. This permits genuine global HG differentiation
without incorrectly assuming that the Fourier transform is nonzero outside
the interpolation band.
-/

namespace MeyerGeneralProblem

noncomputable section

open MeasureTheory
open scoped ComplexConjugate FourierTransform ContDiff

/-- A strictly positive smooth denominator equal to the squared norm away
from a small neighborhood of zero. -/
def groupedReciprocalDenominator (z : ℂ) : ℝ :=
  Complex.normSq z + Real.smoothTransition (1 - 32 * Complex.normSq z)

/-- The actual global smooth inverse correction; it agrees with inversion
where the real part is at least one quarter. -/
def groupedSmoothReciprocal (z : ℂ) : ℂ :=
  conj z * ((groupedReciprocalDenominator z)⁻¹ : ℝ)

/-- The regularized denominator never vanishes, including at complex zero. -/
theorem groupedReciprocalDenominator_pos (z : ℂ) : 0 < groupedReciprocalDenominator z := by
  by_cases hz : z = 0
  · subst z
    simp [groupedReciprocalDenominator]
  · have hn : 0 < Complex.normSq z := Complex.normSq_pos.mpr hz
    have ht := Real.smoothTransition.nonneg (1 - 32 * Complex.normSq z)
    dsimp [groupedReciprocalDenominator]
    linarith

/-- The denominator is globally smooth as a real function on the complex plane. -/
theorem contDiff_groupedReciprocalDenominator : ContDiff ℝ ∞ groupedReciprocalDenominator := by
  have hn : ContDiff ℝ ∞ (fun z : ℂ => Complex.normSq z) := by
    simp only [Complex.normSq_apply]
    exact (Complex.reCLM.contDiff.mul Complex.reCLM.contDiff).add
      (Complex.imCLM.contDiff.mul Complex.imCLM.contDiff)
  exact hn.add (Real.smoothTransition.contDiff.comp (contDiff_const.sub (contDiff_const.mul hn)))

/-- The correction is globally smooth; no global nonvanishing of its input
Fourier transform will be needed. -/
theorem contDiff_groupedSmoothReciprocal : ContDiff ℝ ∞ groupedSmoothReciprocal := by
  exact Complex.conjCLE.contDiff.mul
    (Complex.ofRealCLM.contDiff.comp (contDiff_groupedReciprocalDenominator.inv
      (fun z => (groupedReciprocalDenominator_pos z).ne')))

/-- On the entire positive band the correction is exactly the complex inverse. -/
theorem groupedSmoothReciprocal_eq_inv {z : ℂ} (hz : (1/4:ℝ) ≤ z.re) :
    groupedSmoothReciprocal z = z⁻¹ := by
  have hn := Complex.re_sq_le_normSq z
  have ht : 1 - 32 * Complex.normSq z ≤ 0 := by nlinarith
  simp only [groupedSmoothReciprocal, groupedReciprocalDenominator,
    Real.smoothTransition.zero_of_nonpos ht, add_zero, Complex.inv_def]

/-- The constructed correction composed with any actual Schwartz Fourier
transform is globally smooth, even if that transform has zeros elsewhere. -/
theorem contDiff_groupedFourierReciprocal (G : SchwartzMap ℝ ℂ) :
    ContDiff ℝ ∞ (fun t : ℝ => groupedSmoothReciprocal (FourierTransform.fourier (G : ℝ → ℂ) t)) :=
  contDiff_groupedSmoothReciprocal.comp ((𝓕 G).smooth (⊤ : ℕ∞))

/-- All derivatives through a prescribed order of the genuine smooth
correction have a common compact-band bound. -/
theorem exists_uniform_groupedFourierReciprocal_derivative_bound
    (G : SchwartzMap ℝ ℂ) (D : ℝ) (q : ℕ) :
    ∃ M : ℝ, 0 < M ∧ ∀ j ≤ q, ∀ x : ℝ, |x| ≤ D →
      ‖iteratedDeriv j (fun t : ℝ => groupedSmoothReciprocal
        (FourierTransform.fourier (G : ℝ → ℂ) t)) x‖ ≤ M := by
  let R : ℝ → ℂ := fun t => groupedSmoothReciprocal
    (FourierTransform.fourier (G : ℝ → ℂ) t)
  have hs : ContDiff ℝ ∞ R := contDiff_groupedFourierReciprocal G
  choose C hC using fun j : Fin (q + 1) =>
    (isCompact_Icc : IsCompact (Set.Icc (-D) D)).exists_bound_of_continuousOn
      ((hs.of_le (by simp : (j : ℕ∞ω) ≤ ∞)).continuous_iteratedDeriv' j).continuousOn
  let M := 1 + ∑ j : Fin (q + 1), |C j|
  refine ⟨M, by dsimp [M]; positivity, ?_⟩
  intro j hj x hx
  let jj : Fin (q + 1) := ⟨j, by omega⟩
  have hsingle : |C jj| ≤ ∑ k : Fin (q + 1), |C k| :=
    Finset.single_le_sum (fun k _ => abs_nonneg (C k)) (Finset.mem_univ jj)
  exact (hC jj x (abs_le.mp hx)).trans ((le_abs_self _).trans (by dsimp [M]; linarith))

/-- A genuine Leibniz bound for a corrected polynomial: the constant is
independent of the cluster length, internal gaps and prescribed data. -/
theorem exists_uniform_correctedNewton_derivative_bound
    (G : SchwartzMap ℝ ℂ) (q : ℕ) {D : ℝ} (hD : 0 ≤ D) :
    ∃ C : ℝ, 0 < C ∧ ∀ n ≤ q, ∀ (nodes : ℕ → ℂ) (data : Fin n → ℂ),
      (∀ i < n, ‖nodes i‖ ≤ D) → ∀ j ≤ q, ∀ x ∈ Set.Icc (-D) D,
        ‖iteratedDeriv j (fun t : ℝ =>
          (confluentNewtonInterpolant nodes data : Polynomial ℂ).eval (t : ℂ) *
            groupedSmoothReciprocal (FourierTransform.fourier (G : ℝ → ℂ) t)) x‖ ≤
          C * ∑ i, ‖data i‖ := by
  obtain ⟨M, hM, hbound⟩ := exists_uniform_groupedFourierReciprocal_derivative_bound G D q
  let N := boundedClusterNewtonBound q D
  have hN : 0 ≤ N := boundedClusterNewtonBound_nonneg q hD
  refine ⟨2 ^ q * (N + 1) * M, by positivity, ?_⟩
  intro n hn nodes data hnodes j hj x hx
  let P : ℝ → ℂ := fun t =>
    (confluentNewtonInterpolant nodes data : Polynomial ℂ).eval (t : ℂ)
  let R : ℝ → ℂ := fun t => groupedSmoothReciprocal
    (FourierTransform.fourier (G : ℝ → ℂ) t)
  have hP : ContDiff ℝ ∞ P := by
    have hp := (confluentNewtonInterpolant nodes data : Polynomial ℂ).contDiff_aeval (𝕜 := ℂ) ∞
    exact (hp.restrict_scalars ℝ).comp Complex.ofRealCLM.contDiff
  have hR : ContDiff ℝ ∞ R := contDiff_groupedFourierReciprocal G
  change ‖iteratedDeriv j (fun t => P t * R t) x‖ ≤ _
  rw [iteratedDeriv_fun_mul ((hP.of_le (by simp)).contDiffAt)
    ((hR.of_le (by simp)).contDiffAt)]
  calc
    _ ≤ ∑ i ∈ Finset.range (j + 1),
        (j.choose i : ℝ) * (N * ∑ k, ‖data k‖) * M := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum ?_)
      intro i hi
      rw [norm_mul, norm_mul, Complex.norm_natCast]
      gcongr
      · exact norm_iteratedDeriv_confluentNewtonInterpolant_le_of_length_le
          hn nodes data i hD hnodes hx
      · exact hbound (j-i) (by omega) x (abs_le.mpr hx)
    _ = (2:ℝ) ^ j * (N * ∑ k, ‖data k‖) * M := by
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      congr 2
      exact_mod_cast Nat.sum_range_choose j
    _ ≤ (2:ℝ)^q * ((N+1) * ∑ k, ‖data k‖) * M := by
      have hpow : (2:ℝ)^j ≤ 2^q := pow_le_pow_right₀ (by norm_num) hj
      gcongr
      linarith
    _ = _ := by ring

/-- The genuine globally smooth corrected interpolating function. -/
def groupedCorrectedNewtonFunction {n : ℕ} (G : SchwartzMap ℝ ℂ)
    (nodes : Fin n → ℝ) (data : Fin n → ℂ) (t : ℝ) : ℂ :=
  (confluentNewtonInterpolant (fun i => (finiteNodeSequence nodes i : ℂ)) data :
      Polynomial ℂ).eval (t : ℂ) *
    groupedSmoothReciprocal (FourierTransform.fourier (G : ℝ → ℂ) t)

/-- Hermite--Genocchi gives one bound on all actual corrected initial data,
including confluent configurations, with no inverse node gap. -/
theorem exists_uniform_correctedNewton_data_bound
    (G : SchwartzMap ℝ ℂ) (q : ℕ) {D : ℝ} (hD : 0 ≤ D) :
    ∃ C : ℝ, 0 < C ∧ ∀ n ≤ q, ∀ (nodes : Fin n → ℝ),
      (∀ i, |nodes i| ≤ D) → ∀ (data : Fin n → ℂ) (j : Fin n),
        ‖analyticDividedDifference (finiteNodeSequence nodes) j
          (groupedCorrectedNewtonFunction G nodes data)‖ ≤ C * ∑ i, ‖data i‖ := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_correctedNewton_derivative_bound G q hD
  refine ⟨C, hC, ?_⟩
  intro n hn nodes hnodes data j
  have hp := (confluentNewtonInterpolant (fun i => (finiteNodeSequence nodes i : ℂ))
    data : Polynomial ℂ).contDiff_aeval (𝕜 := ℂ) ∞
  have hs : ContDiff ℝ ∞ (groupedCorrectedNewtonFunction G nodes data) :=
    ((hp.restrict_scalars ℝ).comp Complex.ofRealCLM.contDiff).mul
      (contDiff_groupedFourierReciprocal G)
  have hh := norm_analyticDividedDifference_le_of_contDiff (finiteNodeSequence nodes) j
    (hs.of_le (by simp)) (L := -D) (U := D) (M := C * ∑ i, ‖data i‖)
    (by
      intro i hi
      have hin : i < n := hi.trans_lt j.isLt
      simpa only [finiteNodeSequence, dite_eq_left hin, Set.mem_Icc] using abs_le.mp (hnodes ⟨i, hin⟩))
    (by
      intro x hx
      exact hbound n hn (fun i => (finiteNodeSequence nodes i : ℂ)) data
        (by
          intro i hi
          simpa only [finiteNodeSequence, dite_eq_left hi, Complex.norm_real,
            Real.norm_eq_abs] using hnodes ⟨i, hi⟩)
        j (j.isLt.le.trans hn) x hx)
  exact hh.trans (div_le_self (by positivity)
    (by exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos (j : ℕ))))

/-- On the positive Fourier band the correction really cancels the smoother,
leaving the original interpolating polynomial, not a scalar-at-zero surrogate. -/
theorem groupedCorrectedNewtonFunction_mul_fourier {n : ℕ} (G : SchwartzMap ℝ ℂ)
    (nodes : Fin n → ℝ) (data : Fin n → ℂ) {t : ℝ}
    (hfloor : (1/4:ℝ) ≤ (FourierTransform.fourier (G : ℝ → ℂ) t).re) :
    groupedCorrectedNewtonFunction G nodes data t *
        FourierTransform.fourier (G : ℝ → ℂ) t =
      (confluentNewtonInterpolant (fun i => (finiteNodeSequence nodes i : ℂ)) data :
        Polynomial ℂ).eval (t : ℂ) := by
  have hne : FourierTransform.fourier (G : ℝ → ℂ) t ≠ 0 := by
    intro hz
    rw [hz, Complex.zero_re] at hfloor
    norm_num at hfloor
  rw [groupedCorrectedNewtonFunction, groupedSmoothReciprocal_eq_inv hfloor,
    mul_assoc, inv_mul_cancel₀ hne, mul_one]

/-- The correction is expressed in coordinates relative to the actual cluster
anchor, so its bound has no dependence on the anchor's absolute position. -/
def groupedCenteredCorrectedData {n : ℕ} (G : SchwartzMap ℝ ℂ)
    (nodes : Fin n → ℝ) (anchor : ℝ) (data : Fin n → ℂ) (j : Fin n) : ℂ :=
  analyticDividedDifference (finiteNodeSequence (fun i => nodes i - anchor)) j
    (groupedCorrectedNewtonFunction G (fun i => nodes i - anchor) data)

/-- A single constant bounds the actual centered corrected data for all
bounded clusters and all locations, including colliding node configurations. -/
theorem exists_uniform_centeredCorrectedData_bound
    (G : SchwartzMap ℝ ℂ) (q : ℕ) {D : ℝ} (hD : 0 ≤ D) :
    ∃ C : ℝ, 0 < C ∧ ∀ n ≤ q, ∀ (nodes : Fin n → ℝ) (anchor : ℝ),
      (∀ i, |nodes i - anchor| ≤ D) → ∀ (data : Fin n → ℂ) (j : Fin n),
        ‖groupedCenteredCorrectedData G nodes anchor data j‖ ≤ C * ∑ i, ‖data i‖ := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_correctedNewton_data_bound G q hD
  exact ⟨C, hC, fun n hn nodes anchor hnodes data j =>
    hbound n hn (fun i => nodes i - anchor) hnodes data j⟩

/-- Realizing the corrected data and multiplying by the shifted smoother
restores every original Newton coordinate exactly. Distinctness is used only
for the nodal-value identities, never for a gap estimate. -/
theorem initialData_mul_shifted_fourier_eq_of_correctedData
    {n : ℕ} (G : SchwartzMap ℝ ℂ) (nodes : Fin n → ℝ)
    (hnodes : Function.Injective nodes) (anchor : ℝ) (data : Fin n → ℂ)
    (f : ℝ → ℂ)
    (hf : ∀ j : Fin n, analyticDividedDifference (finiteNodeSequence nodes) j f =
      groupedCenteredCorrectedData G nodes anchor data j)
    (hfloor : ∀ i, (1/4:ℝ) ≤
      (FourierTransform.fourier (G : ℝ → ℂ) (nodes i - anchor)).re) (j : Fin n) :
    analyticDividedDifference (finiteNodeSequence nodes) j
      (fun t => f t * FourierTransform.fourier (G : ℝ → ℂ) (t-anchor)) = data j := by
  let centered : Fin n → ℝ := fun i => nodes i - anchor
  have hc : Function.Injective centered := by
    intro i k h
    apply hnodes
    dsimp [centered] at h
    linarith
  let P : Polynomial ℂ :=
    confluentNewtonInterpolant (fun i => (finiteNodeSequence centered i : ℂ)) data
  have hvalues (i : Fin n) : f (nodes i) =
      groupedCorrectedNewtonFunction G centered data (centered i) := by
    have hv := values_eq_of_initialData_eq centered hc (fun t => f (t+anchor))
      (groupedCorrectedNewtonFunction G centered data) (by
        intro k
        rw [analyticDividedDifference_finite_recenter nodes k f anchor]
        exact hf k) i
    simpa only [centered, sub_add_cancel] using hv
  have hproduct (i : Fin n) :
      f (nodes i) * FourierTransform.fourier (G : ℝ → ℂ) (nodes i-anchor) =
        P.eval (nodes i-anchor : ℂ) := by
    rw [hvalues i]
    simpa only [P, centered, Complex.ofReal_sub] using
      groupedCorrectedNewtonFunction_mul_fourier G centered data (hfloor i)
  rw [initialData_eq_of_values_eq nodes hnodes _ (fun t => P.eval (t-anchor : ℂ))
    hproduct j]
  have hshift := analyticDividedDifference_finite_recenter nodes j
    (fun t : ℝ => P.eval (t-anchor : ℂ)) anchor
  simp only [Complex.ofReal_add, add_sub_cancel_right] at hshift
  rw [← hshift, analyticDividedDifference_polynomial_eval]
  exact polynomialDividedDifference_confluentNewtonInterpolant
    (fun i => (finiteNodeSequence centered i : ℂ)) data j

end

end MeyerGeneralProblem
