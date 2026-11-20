module

public import MeyerGeneralProblem.Sampling.KNSQuadraticEntire

@[expose] public section

/-!
# Pointwise Gaussian decay for actual Fourier pairs

An outward half-interval converts Gaussian square mass and a Lipschitz
bound into pointwise decay. The Lipschitz bound on the Fourier side is
derived from the actual differentiated integral, not assumed as extra
regularity of the Fourier pair.
-/

namespace MeyerGeneralProblem

noncomputable section

open MeasureTheory Set Filter
open scoped Topology FourierTransform ContDiff NNReal

/-- Gaussian square mass controls the point value through an outward
half-interval, retaining the exact cubic bound and constant eight. -/
theorem norm_cube_mul_exp_le_of_lipschitz_gaussian
    {a : ℝ} (ha : 0 < a) {A : ℝ≥0} (hA : 0 < A) {f : ℝ → ℂ}
    (hLip : LipschitzWith A f)
    (hgauss : Integrable (fun t => Real.exp (a*t^2)*‖f t‖^2)) (x : ℝ) :
    ‖f x‖^3*Real.exp (a*x^2) ≤
      8*(A : ℝ)*(∫ t, Real.exp (a*t^2)*‖f t‖^2) := by
  have hAr : 0 < (A : ℝ) := hA
  let δ : ℝ := ‖f x‖/(2*(A : ℝ))
  let l : ℝ := if 0 ≤ x then x else x-δ
  let u : ℝ := if 0 ≤ x then x+δ else x
  have hδ : 0 ≤ δ := by dsimp only [δ]; positivity
  have hwidth : u-l=δ := by dsimp only [u,l]; split_ifs <;> ring
  have hgeom (t : ℝ) (ht : t ∈ Icc l u) : |t-x| ≤ δ ∧ x^2 ≤ t^2 := by
    by_cases hx : 0 ≤ x
    · simp only [l,u,hx,↓reduceIte,mem_Icc] at ht
      rw [abs_of_nonneg (by linarith : 0 ≤ t-x)]
      constructor <;> nlinarith
    · simp only [l,u,hx,↓reduceIte,mem_Icc] at ht
      rw [abs_of_nonpos (by linarith : t-x ≤ 0)]
      constructor <;> nlinarith
  have hnorm (t : ℝ) (ht : t ∈ Icc l u) : ‖f x‖/2 ≤ ‖f t‖ := by
    have hg := (hgeom t ht).1
    have hl := hLip.norm_sub_le t x
    rw [Real.norm_eq_abs] at hl
    have hn := norm_le_norm_add_norm_sub (f t) (f x)
    have hd : (A : ℝ)*δ=‖f x‖/2 := by dsimp only [δ]; field_simp
    have hh := mul_le_mul_of_nonneg_left hg A.coe_nonneg
    nlinarith
  let c : ℝ := Real.exp (a*x^2)*(‖f x‖/2)^2
  have hpoint (t : ℝ) (ht : t ∈ Icc l u) : c ≤ Real.exp (a*t^2)*‖f t‖^2 := by
    have he : Real.exp (a*x^2) ≤ Real.exp (a*t^2) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_left (hgeom t ht).2 ha.le
    dsimp only [c]
    gcongr
    exact hnorm t ht
  have hs := setIntegral_mono_on
    (show IntegrableOn (fun _ : ℝ => c) (Icc l u) from continuous_const.integrableOn_Icc)
    hgauss.integrableOn measurableSet_Icc hpoint
  rw [setIntegral_const,Real.volume_real_Icc,hwidth,max_eq_left hδ,smul_eq_mul] at hs
  have hglobal := setIntegral_le_integral (s := Icc l u) hgauss
    (Eventually.of_forall (fun t => mul_nonneg (Real.exp_pos _).le (sq_nonneg _)))
  have hmass := hs.trans hglobal
  have heq : 8*(A : ℝ)*(δ*c)=‖f x‖^3*Real.exp (a*x^2) := by
    dsimp only [δ,c]
    field_simp
    ring
  have h := mul_le_mul_of_nonneg_left hmass (by positivity : 0 ≤ 8*(A : ℝ))
  rwa [heq] at h

/-- Pointwise Gaussian decay at one-third of the square-weight exponent.
The displayed finite constant may depend on the function and Lipschitz
bound; these low-order quantities do not affect the exponent. -/
theorem norm_le_gaussian_of_lipschitz_gaussian
    {a : ℝ} (ha : 0 < a) {A : ℝ≥0} (hA : 0 < A) {f : ℝ → ℂ}
    (hLip : LipschitzWith A f)
    (hgauss : Integrable (fun t => Real.exp (a*t^2)*‖f t‖^2)) (x : ℝ) :
    ‖f x‖ ≤ (1+8*(A : ℝ)*(∫ t, Real.exp (a*t^2)*‖f t‖^2))*
      Real.exp (-(a/3)*x^2) := by
  let M : ℝ := 8*(A : ℝ)*(∫ t, Real.exp (a*t^2)*‖f t‖^2)
  have hM : 0 ≤ M := mul_nonneg (by positivity)
    (integral_nonneg (fun t => mul_nonneg (Real.exp_pos _).le (sq_nonneg _)))
  let r : ℝ := ‖f x‖*Real.exp (a*x^2/3)
  have hr : 0 ≤ r := by dsimp only [r]; positivity
  have hc : r^3 ≤ M := by
    have he : Real.exp (a*x^2/3)^3=Real.exp (a*x^2) := by
      rw [← Real.exp_nat_mul]
      congr 1
      norm_num
      ring
    dsimp only [r]
    rw [mul_pow,he]
    exact norm_cube_mul_exp_le_of_lipschitz_gaussian ha hA hLip hgauss x
  have hrM : r ≤ 1+M := by
    by_cases hr1 : r ≤ 1
    · linarith
    · have hsq : r ≤ r^2 := by nlinarith
      have hcube : r ≤ r^3 := by nlinarith
      linarith
  have h := mul_le_mul_of_nonneg_right hrM (Real.exp_pos (-(a/3)*x^2)).le
  have he : Real.exp (a*x^2/3)*Real.exp (-(a/3)*x^2)=1 := by
    rw [← Real.exp_add]
    have hzero : a*x^2/3+(-(a/3)*x^2)=0 := by ring
    rw [hzero,Real.exp_zero]
  dsimp only [r] at h
  rw [mul_assoc,he,mul_one] at h
  exact h

/-- Gaussian square integrability gives a genuine positive Lipschitz
constant for the classical Fourier transform. The proof bounds the actual
derivative integral by an integrable linear-exponential weight. -/
theorem exists_pos_lipschitzWith_fourier_of_gaussian
    {a : ℝ} (ha : 0 < a) {f : ℝ → ℂ} (hf : AEStronglyMeasurable f volume)
    (hgauss : Integrable (fun t => Real.exp (a*t^2)*‖f t‖^2)) :
    ∃ A : ℝ≥0, 0 < A ∧ LipschitzWith A (𝓕 f) := by
  let J : ℝ → ℝ → ℂ := fun z x =>
    (Complex.exp (((-2*Real.pi*x : ℝ) : ℂ)*Complex.I*(z : ℂ))*
      (((-2*Real.pi*x : ℝ) : ℂ)*Complex.I))*f x
  let B : ℝ := (2*Real.pi)*(∫ x, ‖f x‖*Real.exp |x|)
  have hB : 0 ≤ B := mul_nonneg (by positivity)
    (integral_nonneg (fun x => mul_nonneg (norm_nonneg _) (Real.exp_pos _).le))
  have hw : Integrable (fun x => ‖f x‖*Real.exp |x|) := by
    simpa only [one_mul] using integrable_norm_mul_exp_abs_of_gaussian ha hf hgauss 1
  have hpoint (z x : ℝ) : ‖J z x‖ ≤ (2*Real.pi)*(‖f x‖*Real.exp |x|) := by
    have hphase : ‖Complex.exp (((-2*Real.pi*x : ℝ) : ℂ)*Complex.I*(z : ℂ))‖ = 1 := by
      rw [norm_knsFourierLaplace_phase]
      simp
    have hc : ‖(((-2*Real.pi*x : ℝ) : ℂ)*Complex.I)‖ = 2*Real.pi*|x| := by
      simp [Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
    have hx : |x| ≤ Real.exp |x| := by linarith [Real.add_one_le_exp |x|]
    dsimp only [J]
    rw [norm_mul,norm_mul,hphase,hc,one_mul]
    calc
      _ = (2*Real.pi)*(‖f x‖*|x|) := by ring
      _ ≤ _ := by gcongr
  have hJi (z : ℝ) : Integrable (J z) := by
    apply (hw.const_mul (2*Real.pi)).mono'
      ((show Continuous (fun x : ℝ =>
        Complex.exp (((-2*Real.pi*x : ℝ) : ℂ)*Complex.I*(z : ℂ))*
          (((-2*Real.pi*x : ℝ) : ℂ)*Complex.I)) by
            fun_prop).aestronglyMeasurable.mul hf)
    exact Eventually.of_forall (hpoint z)
  have hd (z : ℝ) : HasDerivAt (𝓕 f) (∫ x, J z x) z := by
    simpa only [bandFourierExtension_ofReal,J] using
      (hasDerivAt_knsFourierLaplace ha hf hgauss (z : ℂ)).comp_ofReal
  have hn (z : ℝ) : ‖deriv (𝓕 f) z‖ ≤ B := by
    rw [(hd z).deriv]
    have h := (norm_integral_le_integral_norm _).trans
      (integral_mono (hJi z).norm (hw.const_mul (2*Real.pi)) (hpoint z))
    rw [integral_const_mul] at h
    exact h
  let A : ℝ≥0 := ⟨1+B,by linarith⟩
  have hA : 0 < A := by change (0 : ℝ) < 1+B; linarith
  refine ⟨A,hA,lipschitzWith_of_nnnorm_deriv_le (fun z => (hd z).differentiableAt) ?_⟩
  intro z
  have h : ‖deriv (𝓕 f) z‖ ≤ (A : ℝ) := by change _ ≤ 1+B; linarith [hn z]
  exact_mod_cast h

/-- An actual continuous Fourier pair with Gaussian square integrability
on both sides has pointwise Gaussian decay on both sides. Fourier inversion
transfers the proved Lipschitz bound back to the original function by
reflection; no global Schwartz assumption is required. -/
theorem exists_pointwise_gaussian_of_gaussian_fourier_pair
    {a : ℝ} (ha : 0 < a) {f : ℝ → ℂ} (hf : Continuous f)
    (hgauss : Integrable (fun t => Real.exp (a*t^2)*‖f t‖^2))
    (hFgauss : Integrable (fun t => Real.exp (a*t^2)*‖𝓕 f t‖^2)) :
    ∃ C > 0, ∀ x : ℝ,
      ‖f x‖ ≤ C*Real.exp (-(a/3)*x^2) ∧
        ‖𝓕 f x‖ ≤ C*Real.exp (-(a/3)*x^2) := by
  have hf1 := integrable_of_gaussian_square ha hf.aestronglyMeasurable hgauss
  have hF : Continuous (𝓕 f : ℝ → ℂ) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hf1
  have hF1 := integrable_of_gaussian_square ha hF.aestronglyMeasurable hFgauss
  obtain ⟨A,hA,hLipF⟩ := exists_pos_lipschitzWith_fourier_of_gaussian ha hf.aestronglyMeasurable hgauss
  obtain ⟨B,hB,hLipFF⟩ := exists_pos_lipschitzWith_fourier_of_gaussian ha hF.aestronglyMeasurable hFgauss
  have hLip : LipschitzWith B f := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have h := hLipFF.dist_le_mul (-x) (-y)
    simpa only [kns_fourier_fourier_eq_reflection hf hf1 hF1,neg_neg,dist_neg_neg] using h
  let E := ∫ t, Real.exp (a*t^2)*‖f t‖^2
  let D := ∫ t, Real.exp (a*t^2)*‖𝓕 f t‖^2
  have hE : 0 ≤ E := integral_nonneg (fun t => mul_nonneg (Real.exp_pos _).le (sq_nonneg _))
  have hD : 0 ≤ D := integral_nonneg (fun t => mul_nonneg (Real.exp_pos _).le (sq_nonneg _))
  let C : ℝ := 1+8*(B : ℝ)*E+8*(A : ℝ)*D
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C,hC,fun x => ⟨?_,?_⟩⟩
  · apply (norm_le_gaussian_of_lipschitz_gaussian ha hB hLip hgauss x).trans
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    dsimp only [C,E]
    have h := mul_nonneg (by positivity : 0 ≤ 8*(A : ℝ)) hD
    linarith
  · apply (norm_le_gaussian_of_lipschitz_gaussian ha hA hLipF hFgauss x).trans
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    dsimp only [C,D]
    have h := mul_nonneg (by positivity : 0 ≤ 8*(B : ℝ)) hE
    linarith

/-- The actual cofinite reciprocal-gap Fourier pair has pointwise Gaussian
decay on both sides at an exponent determined only by rho. C1, L1, L2 and
the original second moments suffice; higher moments, Gaussian mass, and
Lipschitz constants are all obtained from the proved bootstrap. -/
theorem knsPointwiseGaussian_of_reciprocal_gaps
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
    ∃ C > 0, ∀ x : ℝ,
      ‖f x‖ ≤ C*Real.exp (-(knsGaussianParameter ρ/3)*x^2) ∧
        ‖𝓕 f x‖ ≤ C*Real.exp (-(knsGaussianParameter ρ/3)*x^2) := by
  obtain ⟨hg,hFg⟩ := knsGaussianDecay_of_reciprocal_gaps hρ hρhalf Λ M F J G L
    hgapΛ hgapM hf hF hf1 hF1 hf2 hx2 hξ2 hzΛ hzM
  exact exists_pointwise_gaussian_of_gaussian_fourier_pair
    (knsGaussianParameter_properties hρ hρhalf).1 hf.continuous hg hFg

end

end MeyerGeneralProblem
