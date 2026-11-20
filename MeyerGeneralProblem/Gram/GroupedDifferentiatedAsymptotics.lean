module

public import MeyerGeneralProblem.Gram.GroupedNormalizerBounds
public import MeyerGeneralProblem.Gram.HermiteUniversalUniform
public import MeyerGeneralProblem.Gram.UniversalDecay
public import Mathlib.Analysis.Fourier.FourierTransformDeriv
public import Mathlib.Analysis.Calculus.Taylor

@[expose] public section

/-!
# Differentiated same-side Hermite estimates

The interpolation route of Theorem F, Lemmas 5.3–5.4, is implemented using
actual Taylor remainders and independently proved higher derivatives.
Uniform derivative boundedness is not identified with derivative smallness.
All ray estimates remain away from the signed-square origin.
-/

namespace MeyerGeneralProblem

noncomputable section

open Filter
open MeasureTheory
open scoped Topology

/-- A complex-valued one-step Landau estimate, obtained from the actual
first-order Taylor polynomial with bounded second derivative. -/
theorem grouped_norm_deriv_le_value_secondDerivative
    (f : ℝ → ℂ) (x h A B : ℝ) (hh : 0 < h)
    (hf : ∀ z ∈ Set.Icc x (x+h), ContDiffAt ℝ 2 f z)
    (hval : ∀ z ∈ Set.Icc x (x+h), ‖f z‖ ≤ A)
    (hsecond : ∀ z ∈ Set.Icc x (x+h), ‖iteratedDeriv 2 f z‖ ≤ B) :
    ‖deriv f x‖ ≤ 2*A/h+B*h := by
  have hx : x ∈ Set.Icc x (x+h) := ⟨le_rfl, by linarith⟩
  have hx' : x+h ∈ Set.Icc x (x+h) := ⟨by linarith, le_rfl⟩
  have huniq := uniqueDiffOn_Icc (show x < x+h by linarith)
  have ht := taylor_mean_remainder_bound (n := 1) (f := f) (C := B)
    (show x ≤ x+h by linarith) (fun z hz => (hf z hz).contDiffWithinAt) hx'
    (fun z hz => by
      rw [iteratedDerivWithin_eq_iteratedDeriv huniq (hf z hz) hz]
      exact hsecond z hz)
  have hpoly : taylorWithinEval f 1 (Set.Icc x (x+h)) x (x+h) = f x + h • deriv f x := by
    rw [show (1:ℕ)=0+1 by rfl, taylorWithinEval_succ]
    rw [iteratedDerivWithin_eq_iteratedDeriv huniq ((hf x hx).of_le (by norm_num)) hx]
    simp
  rw [hpoly] at ht
  norm_num only [add_sub_cancel_left, Nat.reduceAdd, Nat.factorial_one, Nat.cast_one, div_one] at ht
  have hv : ‖f (x+h)-f x‖ ≤ 2*A := by
    exact (norm_sub_le _ _).trans (by linarith [hval x hx, hval (x+h) hx'])
  have hid : h • deriv f x = (f (x+h)-f x) - (f (x+h)-(f x+h • deriv f x)) := by abel
  have hd : h*‖deriv f x‖ ≤ 2*A+B*h^2 := by
    calc
      _ = ‖h • deriv f x‖ := by rw [norm_smul, Real.norm_of_nonneg hh.le]
      _ = _ := congrArg norm hid
      _ ≤ ‖f (x+h)-f x‖ + ‖f (x+h)-(f x+h • deriv f x)‖ := norm_sub_le _ _
      _ ≤ _ := add_le_add hv ht
  calc
    _ ≤ (2*A+B*h^2)/h := (le_div_iff₀ hh).mpr (by simpa only [mul_comm] using hd)
    _ = _ := by field_simp

/-- Optimized one-step interpolation: an exponentially small function
with an independently bounded second derivative has a decaying derivative. -/
theorem grouped_norm_deriv_le_exponential_of_secondDerivative
    (f : ℝ → ℂ) (x A B c D : ℝ) (hc : 0 ≤ c) (hD : 0 ≤ D)
    (hf : ∀ z ∈ Set.Icc x (x+1), ContDiffAt ℝ 2 f z)
    (hval : ∀ z ∈ Set.Icc x (x+1), ‖f z‖ ≤ A*Real.exp (-c*D))
    (hsecond : ∀ z ∈ Set.Icc x (x+1), ‖iteratedDeriv 2 f z‖ ≤ B) :
    ‖deriv f x‖ ≤ (2*A+B)*Real.exp (-c*D/2) := by
  let h := Real.exp (-c*D/2)
  have hh : 0 < h := Real.exp_pos _
  have hh1 : h ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [mul_nonneg hc hD])
  have hsub : Set.Icc x (x+h) ⊆ Set.Icc x (x+1) := by
    intro z hz
    exact ⟨hz.1, by linarith [hz.2]⟩
  have heq : Real.exp (-c*D) = h^2 := by
    dsimp [h]
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hb := grouped_norm_deriv_le_value_secondDerivative f x h (A*Real.exp (-c*D)) B hh
    (fun z hz => hf z (hsub hz)) (fun z hz => hval z (hsub hz))
    (fun z hz => hsecond z (hsub hz))
  refine hb.trans_eq ?_
  rw [heq]
  change 2*(A*h^2)/h+B*h = (2*A+B)*h
  field_simp

/-- Exact derivative-norm invariance under either real sign. -/
theorem grouped_norm_iteratedDeriv_comp_sign
    (f : ℝ → ℂ) (i : ℕ) (ε x : ℝ) (hε : ε^2=1) :
    ‖iteratedDeriv i (fun z => f (ε*z)) x‖ = ‖iteratedDeriv i f (ε*x)‖ := by
  rcases sq_eq_one_iff.mp hε with rfl | rfl
  · simp
  · simp only [neg_one_mul, iteratedDeriv_comp_neg, norm_smul, norm_pow,
      norm_neg, norm_one, one_pow, one_mul]

/-- The actual normalized kernel parameterized by positive magnitudes;
the two signs still select the physical rays. -/
def groupedMagnitudeNormalizedKernel (m : ℕ) (hm : 1 ≤ m) (ε η r t : ℝ) : ℂ :=
  normalizedHermiteGramKernel m hm (ε*Real.sqrt r) (η*Real.sqrt t)

theorem groupedSignedSquareRayPoint_sign_mul (ε r : ℝ) (hε : ε^2=1) :
    groupedSignedSquareRayPoint ε (ε*r) = ε*Real.sqrt r := by
  unfold groupedSignedSquareRayPoint
  rw [← mul_assoc, ← pow_two, hε, one_mul]

theorem groupedMagnitudeNormalizedKernel_eq_ray
    (m : ℕ) (hm : 1 ≤ m) (ε η r t : ℝ) (hε : ε^2=1) (hη : η^2=1) :
    groupedMagnitudeNormalizedKernel m hm ε η r t =
      normalizedHermiteGramKernel m hm (groupedSignedSquareRayPoint ε (ε*r))
        (groupedSignedSquareRayPoint η (η*t)) := by
  rw [groupedSignedSquareRayPoint_sign_mul ε r hε,
    groupedSignedSquareRayPoint_sign_mul η t hη]
  rfl

theorem norm_groupedMagnitudeNormalizedKernel_le_exponential
    (m : ℕ) (hm : 1 ≤ m) (ε η r t : ℝ) (hε : ε^2=1) (hη : η^2=1)
    (hr : 0 ≤ r) (ht : 0 ≤ t) :
    ‖groupedMagnitudeNormalizedKernel m hm ε η r t‖ ≤
      hermiteNormalizedGramGaussianConstant m * Real.exp (-(Real.pi/2)*|η*t-ε*r|) := by
  rw [groupedMagnitudeNormalizedKernel_eq_ray m hm ε η r t hε hη]
  have hr' : 0 ≤ ε*(ε*r) := by nlinarith [hε]
  have ht' : 0 ≤ η*(η*t) := by nlinarith [hη]
  have h := norm_normalizedHermiteGramKernel_le_signedSquare m hm
    (groupedSignedSquareRayPoint ε (ε*r)) (groupedSignedSquareRayPoint η (η*t))
  rwa [signedSquare_groupedSignedSquareRayPoint hε hr',
    signedSquare_groupedSignedSquareRayPoint hη ht'] at h

theorem contDiffAt_groupedMagnitudeNormalizedKernel_left
    (q m : ℕ) (hm : groupedHermiteDifferentiationOrder q ≤ m)
    (ε η r t : ℝ) (hε : ε^2=1) (_hη : η^2=1) (hr : 0 < r) :
    ContDiffAt ℝ q (fun z => groupedMagnitudeNormalizedKernel m
      (by have := (le_max_left _ _).trans hm; omega) ε η z t) r := by
  have hp : 1 ≤ m := by have := (le_max_left _ _).trans hm; omega
  have hr' : 0 < ε*(ε*r) := by nlinarith [hε]
  have hnorm := contDiffAt_inv_groupedHermiteRayNormalizer m hp q ε (ε*r) hε hr'
  have hraw := contDiffAt_hermiteResolventKernel_ray_left q m hm ε (ε*r) (η*Real.sqrt t) hr'
  have h := (hnorm.smul (hraw.const_smul ‖hermitePointMass m hp (η*Real.sqrt t)‖⁻¹)).comp r
    (contDiffAt_const.mul contDiffAt_id)
  have heq : (fun z => groupedMagnitudeNormalizedKernel m hp ε η z t) =
      (fun z => (groupedHermiteRayNormalizer m hp ε (ε*z))⁻¹ •
        (‖hermitePointMass m hp (η*Real.sqrt t)‖⁻¹ •
          hermiteResolventKernel m (groupedSignedSquareRayPoint ε (ε*z)) (η*Real.sqrt t))) := by
    funext z
    rw [← normalizedHermiteGramKernel_ray_eq_smul,
      groupedSignedSquareRayPoint_sign_mul ε z hε]
    rfl
  rw [heq]
  exact h

theorem norm_iteratedDeriv_groupedMagnitudeNormalizedKernel_left
    (m : ℕ) (hm : 1 ≤ m) (i : ℕ) (ε η r t : ℝ) (hε : ε^2=1) (hη : η^2=1) :
    ‖iteratedDeriv i (fun z => groupedMagnitudeNormalizedKernel m hm ε η z t) r‖ =
      ‖iteratedDeriv i (fun z => normalizedHermiteGramKernel m hm
        (groupedSignedSquareRayPoint ε z) (groupedSignedSquareRayPoint η (η*t))) (ε*r)‖ := by
  simp_rw [groupedMagnitudeNormalizedKernel_eq_ray m hm ε η _ _ hε hη]
  exact grouped_norm_iteratedDeriv_comp_sign (fun z => normalizedHermiteGramKernel m hm
    (groupedSignedSquareRayPoint ε z) (groupedSignedSquareRayPoint η (η*t))) i ε r hε

/-- Genuine first differentiated off-diagonal decay of the actual
normalized same-order Hermite kernel, on all physical ray pairs. -/
theorem exists_norm_deriv_groupedMagnitudeNormalizedKernel_left_le_exponential
    (m : ℕ) (hm : groupedHermiteDifferentiationOrder 2 ≤ m) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε η : ℝ, ε^2=1 → η^2=1 → ∀ r t : ℝ,
      1 ≤ r → 1 ≤ t →
      ‖deriv (fun z => groupedMagnitudeNormalizedKernel m
        (by have := (le_max_left _ _).trans hm; omega) ε η z t) r‖ ≤
        C*Real.exp (-(Real.pi/4)*|η*t-ε*r|) := by
  have hp : 1 ≤ m := by have := (le_max_left _ _).trans hm; omega
  obtain ⟨B,hB,hbound⟩ := exists_uniform_normalizedHermiteGramKernel_signedSquareRay_derivative_bound 2 m hm
  let A := hermiteNormalizedGramGaussianConstant m * Real.exp (Real.pi/2)
  have hA : 0 < A := mul_pos (hermiteNormalizedGramGaussianConstant_pos hp) (Real.exp_pos _)
  refine ⟨2*A+B, by positivity, ?_⟩
  intro ε η hε hη r t hr ht
  have heps : |ε|=1 := by nlinarith [sq_abs ε, abs_nonneg ε]
  have hlocal (z : ℝ) (hz : z ∈ Set.Icc r (r+1)) :
      |η*t-ε*r|-1 ≤ |η*t-ε*z| := by
    have hd : |z-r| ≤ 1 := (abs_le).mpr ⟨by linarith [hz.1], by linarith [hz.2]⟩
    have htriangle := abs_add_le (η*t-ε*z) (ε*(z-r))
    rw [show (η*t-ε*z)+(ε*(z-r))=η*t-ε*r by ring,
      abs_mul, heps, one_mul] at htriangle
    linarith
  have h := grouped_norm_deriv_le_exponential_of_secondDerivative
    (fun z => groupedMagnitudeNormalizedKernel m hp ε η z t) r A B (Real.pi/2) |η*t-ε*r|
    (by positivity) (abs_nonneg _)
    (fun z hz => contDiffAt_groupedMagnitudeNormalizedKernel_left 2 m hm ε η z t hε hη (by linarith [hz.1]))
    (fun z hz => ?_) (fun z hz => ?_)
  · convert h using 1
    congr 2
    ring
  · refine (norm_groupedMagnitudeNormalizedKernel_le_exponential m hp ε η z t hε hη
      (by linarith [hz.1]) (by linarith)).trans ?_
    dsimp [A]
    rw [mul_assoc, ← Real.exp_add]
    apply mul_le_mul_of_nonneg_left _ (hermiteNormalizedGramGaussianConstant_pos hp).le
    apply Real.exp_le_exp.mpr
    have hπ := Real.pi_pos
    nlinarith [hlocal z hz]
  · rw [norm_iteratedDeriv_groupedMagnitudeNormalizedKernel_left m hp 2 ε η z t hε hη]
    have hraw := hbound 2 0 (by omega) (by omega) ε η hε hη (ε*z) (η*t)
      (by nlinarith [hz.1, hε]) (by nlinarith [hη])
    simpa only [iteratedDeriv_zero] using hraw

/-- A concrete polynomial-moment bound for the actual rational Fourier
density. The cofinal range is sufficient for the grouped derivative route. -/
theorem grouped_abs_pow_mul_rawGramDensity_le (m k : ℕ) (hk : k+2 ≤ 2*m) (z : ℝ) :
    |z|^k*rawGramDensity m z ≤ rawGramDensity 1 z := by
  let b : ℝ := (1+4*z^2)⁻¹
  have hb0 : 0 ≤ b := by dsimp [b]; positivity
  have hb1 : b ≤ 1 := (inv_le_one₀ (by positivity)).mpr (by nlinarith [sq_nonneg z])
  have hz : |z| * b ≤ 1 := by
    simpa only [b, norm_mul, Real.norm_eq_abs, abs_inv,
      abs_of_pos (by positivity : 0 < 1+4*z^2)] using norm_mul_inverseQuadratic_le_one z
  simp only [rawGramDensity_eq_inv_pow]
  change |z|^k*b^(2*m) ≤ b^2
  have hsplit : 2*m=k+(2*m-k) := by omega
  rw [hsplit, pow_add, ← mul_assoc, ← mul_pow]
  calc
    _ ≤ 1*b^(2*m-k) := mul_le_mul_of_nonneg_right (pow_le_one₀ (by positivity) hz) (by positivity)
    _ ≤ b^2 := by simpa only [one_mul] using pow_le_pow_of_le_one hb0 hb1 (show 2 ≤ 2*m-k by omega)

theorem integrable_grouped_abs_pow_mul_rawGramDensity (m k : ℕ) (hk : k+2 ≤ 2*m) :
    Integrable (fun z : ℝ => |z|^k*rawGramDensity m z) := by
  apply (integrable_rawGramDensity (m := 1) (by omega)).mono'
  · apply Continuous.aestronglyMeasurable
    simp_rw [rawGramDensity_eq_inv_pow]
    fun_prop (disch := intro z; positivity)
  · filter_upwards with z
    rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg (abs_nonneg z) _) (rawGramDensity_nonneg m z))]
    exact grouped_abs_pow_mul_rawGramDensity_le m k hk z

theorem integrable_grouped_abs_pow_mul_gramDensity (m k : ℕ) (hk : k+2 ≤ 2*m) :
    Integrable (fun z : ℝ => |z|^k*gramDensity m z) := by
  have h := (integrable_grouped_abs_pow_mul_rawGramDensity m k hk).const_mul (2*gramNormalization m)
  convert h using 1
  funext z
  unfold gramDensity
  ring

theorem integrable_grouped_pow_smul_complexGramDensity (m k : ℕ) (hk : k+2 ≤ 2*m) :
    Integrable (fun z : ℝ => z^k • (gramDensity m z : ℂ)) := by
  have hp : 1 ≤ m := by omega
  apply (integrable_grouped_abs_pow_mul_gramDensity m k hk).mono'
  · apply Continuous.aestronglyMeasurable
    unfold gramDensity
    simp_rw [rawGramDensity_eq_inv_pow]
    fun_prop (disch := intro z; positivity)
  · filter_upwards with z
    simp only [norm_smul, norm_pow, Real.norm_eq_abs, Complex.norm_real,
      abs_of_nonneg (gramDensity_nonneg hp z)]
    exact le_rfl

/-- Finite-order smoothness of the actual universal Fourier kernel, from
proved rational-density moments rather than a smoothness assumption. -/
theorem contDiff_grouped_universalGramKernel (m q : ℕ) (hq : q+2 ≤ 2*m) :
    ContDiff ℝ q (universalGramKernel m) := by
  have hp : 1 ≤ m := by omega
  have h := Real.contDiff_fourier (N := (q:ℕ∞)) (f := fun z : ℝ => (gramDensity m z : ℂ))
    (fun k hk => by
      have hk' : k ≤ q := by exact_mod_cast hk
      simpa only [Real.norm_eq_abs, Complex.norm_real, abs_of_nonneg (gramDensity_nonneg hp _)]
        using integrable_grouped_abs_pow_mul_gramDensity m k (by omega))
  have heq : universalGramKernel m = fun t =>
      FourierTransform.fourier (fun z : ℝ => (gramDensity m z : ℂ)) (-t) :=
    funext universalGramKernel_eq_fourier
  rw [heq]
  exact_mod_cast h.comp contDiff_neg

/-- Integrable Fourier derivative density at an arbitrary admissible order. -/
theorem integrable_grouped_universalDerivativeDensity (m k : ℕ) (hk : k+2 ≤ 2*m) :
    Integrable (fun z : ℝ => (-2*Real.pi*Complex.I*z)^k • (gramDensity m z : ℂ)) := by
  have h := (integrable_grouped_pow_smul_complexGramDensity m k hk).smul
    ((-2*Real.pi*Complex.I)^k)
  convert h using 1
  funext z
  simp only [Pi.smul_apply, mul_pow, mul_smul, ← Complex.ofReal_pow, Complex.real_smul]
  rfl

/-- An actual integral bound for the universal kernel's derivative. -/
def groupedUniversalDerivativeBound (m k : ℕ) : ℝ :=
  ∫ z : ℝ, ‖(-2*Real.pi*Complex.I*z)^k • (gramDensity m z : ℂ)‖

theorem groupedUniversalDerivativeBound_nonneg (m k : ℕ) :
    0 ≤ groupedUniversalDerivativeBound m k := integral_nonneg (fun _ => norm_nonneg _)

theorem norm_iteratedDeriv_universalGramKernel_le_groupedBound
    (m k : ℕ) (hk : k+2 ≤ 2*m) (x : ℝ) :
    ‖iteratedDeriv k (universalGramKernel m) x‖ ≤ groupedUniversalDerivativeBound m k := by
  have heq : universalGramKernel m = fun t =>
      FourierTransform.fourier (fun z : ℝ => (gramDensity m z : ℂ)) (-t) :=
    funext universalGramKernel_eq_fourier
  rw [heq, iteratedDeriv_comp_neg, norm_smul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  rw [Real.iteratedDeriv_fourier (N := (k:ℕ∞)) (fun n hn => by
    have hn' : n ≤ k := by exact_mod_cast hn
    exact integrable_grouped_pow_smul_complexGramDensity m n (by omega)) (by exact_mod_cast le_rfl)]
  exact VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _

/-- Uniform vanishing on every bounded displacement band, away from the
origin in both positive magnitude coordinates. -/
def GroupedVanishesOnMagnitudeBands (F : ℝ → ℝ → ℂ) : Prop :=
  ∀ L ≥ 0, ∀ δ > 0, ∃ T ≥ 1, ∀ r t : ℝ,
    T ≤ r → T ≤ t → |t-r| ≤ L → ‖F r t‖ ≤ δ

/-- Taylor interpolation transfers uniform bandwise smallness to the
first derivative, provided the second derivative is genuinely bounded. -/
theorem GroupedVanishesOnMagnitudeBands.deriv_left
    {F : ℝ → ℝ → ℂ} (hF : GroupedVanishesOnMagnitudeBands F)
    (hreg : ∀ r t : ℝ, 1 ≤ r → 1 ≤ t → ContDiffAt ℝ 2 (fun z => F z t) r)
    (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ r t : ℝ, 1 ≤ r → 1 ≤ t →
      ‖iteratedDeriv 2 (fun z => F z t) r‖ ≤ B) :
    GroupedVanishesOnMagnitudeBands (fun r t => deriv (fun z => F z t) r) := by
  intro L hL δ hδ
  let h := min 1 (δ/(4*(B+1)))
  have hh : 0 < h := lt_min (by norm_num) (by positivity)
  have hh1 : h ≤ 1 := min_le_left _ _
  have hhδ : h ≤ δ/(4*(B+1)) := min_le_right _ _
  have hBh : B*h ≤ δ/4 := by
    have hh' : h*(4*(B+1)) ≤ δ := (le_div_iff₀ (by positivity)).mp hhδ
    nlinarith
  obtain ⟨T,hT,hsmall⟩ := hF (L+1) (by linarith) (δ*h/8) (by positivity)
  refine ⟨T,hT,?_⟩
  intro r t hr ht hrt
  have hlocal (z : ℝ) (hz : z ∈ Set.Icc r (r+h)) : |t-z| ≤ L+1 := by
    have hz' : |r-z| ≤ 1 := abs_le.mpr ⟨by linarith [hz.2], by linarith [hz.1]⟩
    have htri := abs_add_le (t-r) (r-z)
    rw [show (t-r)+(r-z)=t-z by ring] at htri
    linarith
  have hres := grouped_norm_deriv_le_value_secondDerivative (fun z => F z t) r h (δ*h/8) B hh
    (fun z hz => hreg z t (hT.trans (hr.trans hz.1)) (hT.trans ht))
    (fun z hz => hsmall z t (hr.trans hz.1) ht (hlocal z hz))
    (fun z hz => hbound z t (hT.trans (hr.trans hz.1)) (hT.trans ht))
  have hquot : 2*(δ*h/8)/h=δ/4 := by field_simp; norm_num
  rw [hquot] at hres
  linarith

/-- The actual normalized same-side remainder, without a formal
asymptotic surrogate or a changed physical Hermite order. -/
def groupedMagnitudeHermiteRemainder (m : ℕ) (hm : 1 ≤ m) (ε r t : ℝ) : ℂ :=
  groupedMagnitudeNormalizedKernel m hm ε ε r t - universalGramKernel m (ε*(t-r))

theorem groupedMagnitudeHermiteRemainder_vanishesOnBands
    (m : ℕ) (hm : 1 ≤ m) (ε : ℝ) (hε : ε^2=1) :
    GroupedVanishesOnMagnitudeBands (groupedMagnitudeHermiteRemainder m hm ε) := by
  intro L hL δ hδ
  obtain ⟨T,hT,hsmall⟩ := hermiteUniversalUniformOnBand m hm L hL δ hδ
  refine ⟨max 1 T, le_max_left _ _, ?_⟩
  intro r t hr ht hrt
  have hr0 : 0 ≤ r := by have := (le_max_left 1 T).trans hr; linarith
  have ht0 : 0 ≤ t := by have := (le_max_left 1 T).trans ht; linarith
  have hx : signedSquare (ε*Real.sqrt r)=ε*r := by
    rw [← groupedSignedSquareRayPoint_sign_mul ε r hε]
    exact signedSquare_groupedSignedSquareRayPoint hε (by nlinarith [hε])
  have hy : signedSquare (ε*Real.sqrt t)=ε*t := by
    rw [← groupedSignedSquareRayPoint_sign_mul ε t hε]
    exact signedSquare_groupedSignedSquareRayPoint hε (by nlinarith [hε])
  have heps : |ε|=1 := by nlinarith [sq_abs ε, abs_nonneg ε]
  have h := hsmall (ε*Real.sqrt r) (ε*Real.sqrt t)
  rw [hx,hy,abs_mul,abs_mul,heps,one_mul,one_mul,abs_of_nonneg hr0,
    abs_of_nonneg ht0, ← mul_sub, abs_mul, heps,one_mul] at h
  exact h ((le_max_right 1 T).trans hr) ((le_max_right 1 T).trans ht) hrt

theorem contDiffAt_groupedMagnitudeHermiteRemainder_left
    (q m : ℕ) (hm : groupedHermiteDifferentiationOrder q ≤ m)
    (ε r t : ℝ) (hε : ε^2=1) (hr : 0 < r) :
    ContDiffAt ℝ q (fun z => groupedMagnitudeHermiteRemainder m
      (by have := (le_max_left _ _).trans hm; omega) ε z t) r := by
  have hq : q+2 ≤ m := (le_max_left _ _).trans hm
  exact (contDiffAt_groupedMagnitudeNormalizedKernel_left q m hm ε ε r t hε hε hr).sub
    ((contDiff_grouped_universalGramKernel m q (by omega)).contDiffAt.comp r
      (contDiffAt_const.mul (contDiffAt_const.sub contDiffAt_id)))

theorem norm_iteratedDeriv_grouped_universalMagnitude_left
    (m i : ℕ) (ε r t : ℝ) (hε : ε^2=1) :
    ‖iteratedDeriv i (fun z => universalGramKernel m (ε*(t-z))) r‖ =
      ‖iteratedDeriv i (universalGramKernel m) (ε*(t-r))‖ := by
  change ‖iteratedDeriv i (fun z => (fun v => universalGramKernel m (ε*v)) (t-z)) r‖ = _
  rw [congrFun (iteratedDeriv_comp_const_sub i (fun v : ℝ => universalGramKernel m (ε*v)) t) r,
    norm_smul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  exact grouped_norm_iteratedDeriv_comp_sign (universalGramKernel m) i ε (t-r) hε

theorem exists_norm_iteratedDeriv_groupedMagnitudeHermiteRemainder_left_le
    (q m i : ℕ) (hm : groupedHermiteDifferentiationOrder q ≤ m) (hi : i ≤ q) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ ε : ℝ, ε^2=1 → ∀ r t : ℝ, 1 ≤ r → 1 ≤ t →
      ‖iteratedDeriv i (fun z => groupedMagnitudeHermiteRemainder m
        (by have := (le_max_left _ _).trans hm; omega) ε z t) r‖ ≤ B := by
  have hq : q+2 ≤ m := (le_max_left _ _).trans hm
  have hp : 1 ≤ m := by omega
  obtain ⟨C,hC,hbound⟩ := exists_uniform_normalizedHermiteGramKernel_signedSquareRay_derivative_bound q m hm
  refine ⟨C+groupedUniversalDerivativeBound m i, by positivity [groupedUniversalDerivativeBound_nonneg m i], ?_⟩
  intro ε hε r t hr ht
  have hregK := (contDiffAt_groupedMagnitudeNormalizedKernel_left q m hm ε ε r t hε hε
    (by linarith)).of_le (show (i:WithTop ℕ∞) ≤ q by exact_mod_cast hi)
  have hregU : ContDiffAt ℝ i (fun z => universalGramKernel m (ε*(t-z))) r :=
    (contDiff_grouped_universalGramKernel m i (by omega)).contDiffAt.comp r
      (contDiffAt_const.mul (contDiffAt_const.sub contDiffAt_id))
  unfold groupedMagnitudeHermiteRemainder
  change ‖iteratedDeriv i ((fun z => groupedMagnitudeNormalizedKernel m hp ε ε z t) -
    (fun z => universalGramKernel m (ε*(t-z)))) r‖ ≤ _
  rw [iteratedDeriv_sub hregK hregU]
  refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_iteratedDeriv_groupedMagnitudeNormalizedKernel_left m hp i ε ε r t hε hε]
    simpa only [iteratedDeriv_zero] using
      hbound i 0 hi (by omega) ε ε hε hε (ε*r) (ε*t) (by nlinarith [hε]) (by nlinarith [hε])
  · rw [norm_iteratedDeriv_grouped_universalMagnitude_left m i ε r t hε]
    exact norm_iteratedDeriv_universalGramKernel_le_groupedBound m i (by omega) _

/-- Genuine first differentiated asymptotic remainder: on each bounded
signed-square displacement band it tends uniformly to zero on either
physical same-side ray. The proof uses actual Taylor remainders and
independently dominated second derivatives, not differentiation of a
value-level limit. -/
theorem groupedMagnitudeHermiteRemainder_deriv_left_vanishesOnBands
    (m : ℕ) (hm : groupedHermiteDifferentiationOrder 2 ≤ m)
    (ε : ℝ) (hε : ε^2=1) :
    GroupedVanishesOnMagnitudeBands (fun r t => deriv (fun z =>
      groupedMagnitudeHermiteRemainder m (by have := (le_max_left _ _).trans hm; omega) ε z t) r) := by
  obtain ⟨B,hB,hbound⟩ := exists_norm_iteratedDeriv_groupedMagnitudeHermiteRemainder_left_le 2 m 2 hm le_rfl
  exact (groupedMagnitudeHermiteRemainder_vanishesOnBands m _ ε hε).deriv_left
    (fun r t hr _ht => contDiffAt_groupedMagnitudeHermiteRemainder_left 2 m hm ε r t hε (by linarith))
    B hB (hbound ε hε)

/-- Iterating genuine derivatives adds their orders, without smoothness
or a formal-jet convention. -/
theorem grouped_iteratedDeriv_iteratedDeriv (a b : ℕ) (f : ℝ → ℂ) :
    iteratedDeriv a (iteratedDeriv b f) = iteratedDeriv (a+b) f := by
  simp only [iteratedDeriv_eq_iterate, Function.iterate_add_apply]

/-- Local smoothness left after taking an actual iterated derivative. -/
theorem grouped_contDiffAt_iteratedDeriv (f : ℝ → ℂ) (q i : ℕ) (r : ℝ)
    (hf : ContDiffAt ℝ (q+i) f r) :
    ContDiffAt ℝ q (iteratedDeriv i f) r := by
  induction i generalizing q with
  | zero => simpa using hf
  | succ i ih =>
    rw [iteratedDeriv_succ]
    have h : ContDiffAt ℝ (q+1) (iteratedDeriv i f) r :=
      ih (q+1) (by simpa only [Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm] using hf)
    exact h.derivWithin (by norm_cast)

/-- Arbitrarily many applications of the proved one-step interpolation
lemma; the one additional derivative is used for the Taylor remainder. -/
theorem GroupedVanishesOnMagnitudeBands.iteratedDeriv_left
    {F : ℝ → ℝ → ℂ} (hF : GroupedVanishesOnMagnitudeBands F) (q : ℕ)
    (hreg : ∀ r t : ℝ, 1 ≤ r → 1 ≤ t → ContDiffAt ℝ (q+1) (fun z => F z t) r)
    (hbound : ∀ k ≤ q+1, ∃ B : ℝ, 0 ≤ B ∧ ∀ r t : ℝ, 1 ≤ r → 1 ≤ t →
      ‖iteratedDeriv k (fun z => F z t) r‖ ≤ B) :
    ∀ i ≤ q, GroupedVanishesOnMagnitudeBands (fun r t => iteratedDeriv i (fun z => F z t) r) := by
  intro i
  induction i with
  | zero => intro _; simpa only [iteratedDeriv_zero] using hF
  | succ i ih =>
    intro hi
    have hsmall := ih (by omega)
    obtain ⟨B,hB,hb⟩ := hbound (i+2) (by omega)
    have hstep := hsmall.deriv_left (fun r t hr ht =>
      grouped_contDiffAt_iteratedDeriv (fun z => F z t) 2 i r
        ((hreg r t hr ht).of_le (by exact_mod_cast (show 2+i ≤ q+1 by omega)))) B hB
      (fun r t hr ht => by
        rw [grouped_iteratedDeriv_iteratedDeriv]
        simpa only [Nat.add_comm] using hb r t hr ht)
    simpa only [iteratedDeriv_succ] using hstep

/-- Every fixed left derivative of the actual same-side remainder is
uniformly small on bounded displacement bands. The physical order is
unchanged and the sufficient cofinal cutoff is stated explicitly. -/
theorem groupedMagnitudeHermiteRemainder_iteratedDeriv_left_vanishesOnBands
    (q m i : ℕ) (hm : groupedHermiteDifferentiationOrder (q+1) ≤ m) (hi : i ≤ q)
    (ε : ℝ) (hε : ε^2=1) :
    GroupedVanishesOnMagnitudeBands (fun r t => iteratedDeriv i (fun z =>
      groupedMagnitudeHermiteRemainder m (by have := (le_max_left _ _).trans hm; omega) ε z t) r) := by
  apply (groupedMagnitudeHermiteRemainder_vanishesOnBands m _ ε hε).iteratedDeriv_left q
    (fun r t hr _ht => contDiffAt_groupedMagnitudeHermiteRemainder_left (q+1) m hm ε r t hε (by linarith))
    ?_ i hi
  intro k hk
  obtain ⟨B,hB,hbound⟩ := exists_norm_iteratedDeriv_groupedMagnitudeHermiteRemainder_left_le (q+1) m k hm hk
  exact ⟨B,hB,hbound ε hε⟩

/-- Swapping magnitude coordinates preserves the exact bandwise limit. -/
theorem GroupedVanishesOnMagnitudeBands.swap
    {F : ℝ → ℝ → ℂ} (hF : GroupedVanishesOnMagnitudeBands F) :
    GroupedVanishesOnMagnitudeBands (fun r t => F t r) := by
  intro L hL δ hδ
  obtain ⟨T,hT,hsmall⟩ := hF L hL δ hδ
  exact ⟨T,hT,fun r t hr ht hrt => hsmall t r ht hr (by simpa only [abs_sub_comm] using hrt)⟩

theorem GroupedVanishesOnMagnitudeBands.iteratedDeriv_right
    {F : ℝ → ℝ → ℂ} (hF : GroupedVanishesOnMagnitudeBands F) (q : ℕ)
    (hreg : ∀ r t : ℝ, 1 ≤ r → 1 ≤ t → ContDiffAt ℝ (q+1) (F r) t)
    (hbound : ∀ k ≤ q+1, ∃ B : ℝ, 0 ≤ B ∧ ∀ r t : ℝ, 1 ≤ r → 1 ≤ t →
      ‖iteratedDeriv k (F r) t‖ ≤ B) :
    ∀ j ≤ q, GroupedVanishesOnMagnitudeBands (fun r t => iteratedDeriv j (F r) t) := by
  intro j hj
  have h := hF.swap.iteratedDeriv_left q (fun r t hr ht => hreg t r ht hr)
    (fun k hk => by
      obtain ⟨B,hB,hb⟩ := hbound k hk
      exact ⟨B,hB,fun r t hr ht => hb t r ht hr⟩) j hj
  exact h.swap

/-- Exact signed-coordinate derivative identity. -/
theorem grouped_iteratedDeriv_comp_sign (f : ℝ → ℂ) (i : ℕ) (ε x : ℝ) (hε : ε^2=1) :
    iteratedDeriv i (fun z => f (ε*z)) x = ε^i • iteratedDeriv i f (ε*x) := by
  rcases sq_eq_one_iff.mp hε with rfl | rfl
  · simp
  · simp only [neg_one_mul, iteratedDeriv_comp_neg]

theorem iteratedDeriv_groupedMagnitudeNormalizedKernel_left
    (m : ℕ) (hm : 1 ≤ m) (i : ℕ) (ε η r t : ℝ) (hε : ε^2=1) (hη : η^2=1) :
    iteratedDeriv i (fun z => groupedMagnitudeNormalizedKernel m hm ε η z t) r =
      ε^i • iteratedDeriv i (fun z => normalizedHermiteGramKernel m hm
        (groupedSignedSquareRayPoint ε z) (groupedSignedSquareRayPoint η (η*t))) (ε*r) := by
  simp_rw [groupedMagnitudeNormalizedKernel_eq_ray m hm ε η _ _ hε hη]
  exact grouped_iteratedDeriv_comp_sign (fun z => normalizedHermiteGramKernel m hm
    (groupedSignedSquareRayPoint ε z) (groupedSignedSquareRayPoint η (η*t))) i ε r hε

theorem norm_iteratedDeriv_iteratedDeriv_groupedMagnitudeNormalizedKernel
    (m : ℕ) (hm : 1 ≤ m) (i j : ℕ) (ε η r t : ℝ) (hε : ε^2=1) (hη : η^2=1) :
    ‖iteratedDeriv j (fun v => iteratedDeriv i
      (fun u => groupedMagnitudeNormalizedKernel m hm ε η u v) r) t‖ =
      ‖iteratedDeriv j (fun v => iteratedDeriv i (fun u => normalizedHermiteGramKernel m hm
        (groupedSignedSquareRayPoint ε u) (groupedSignedSquareRayPoint η v)) (ε*r)) (η*t)‖ := by
  simp_rw [iteratedDeriv_groupedMagnitudeNormalizedKernel_left m hm i ε η r _ hε hη]
  rw [iteratedDeriv_fun_const_smul_field, norm_smul, norm_pow]
  have heps : ‖ε‖=1 := by rw [Real.norm_eq_abs]; nlinarith [sq_abs ε, abs_nonneg ε]
  rw [heps,one_pow,one_mul]
  exact grouped_norm_iteratedDeriv_comp_sign (fun v => iteratedDeriv i
    (fun u => normalizedHermiteGramKernel m hm (groupedSignedSquareRayPoint ε u)
      (groupedSignedSquareRayPoint η v)) (ε*r)) j η t hη

theorem contDiffAt_iteratedDeriv_normalizedHermiteGramKernel_ray_right
    (q m i : ℕ) (hm : groupedHermiteDifferentiationOrder q ≤ m) (hi : i ≤ q)
    (ε η s t : ℝ) (hε : ε^2=1) (hη : η^2=1) (hs : 0 < ε*s) (ht : 0 < η*t) :
    ContDiffAt ℝ q (fun v => iteratedDeriv i (fun u => normalizedHermiteGramKernel m
      (by have := (le_max_left _ _).trans hm; omega)
      (groupedSignedSquareRayPoint ε u) (groupedSignedSquareRayPoint η v)) s) t := by
  have hp : 1 ≤ m := by have := (le_max_left _ _).trans hm; omega
  simp_rw [iteratedDeriv_normalizedHermiteGramKernel_ray_left q m i hm hi ε s _ hε hs]
  apply ContDiffAt.sum
  intro a _ha
  apply ContDiffAt.const_smul
  exact (contDiffAt_inv_groupedHermiteRayNormalizer m hp q η t hη ht).smul
    (contDiffAt_iteratedDeriv_hermiteResolventKernel_ray_right q m (i-a) hm
      (by omega) ε η s t hs ht)

theorem contDiffAt_iteratedDeriv_groupedMagnitudeNormalizedKernel_right
    (q m i : ℕ) (hm : groupedHermiteDifferentiationOrder q ≤ m) (hi : i ≤ q)
    (ε η r t : ℝ) (hε : ε^2=1) (hη : η^2=1) (hr : 0 < r) (ht : 0 < t) :
    ContDiffAt ℝ q (fun v => iteratedDeriv i (fun u => groupedMagnitudeNormalizedKernel m
      (by have := (le_max_left _ _).trans hm; omega) ε η u v) r) t := by
  simp_rw [iteratedDeriv_groupedMagnitudeNormalizedKernel_left m _ i ε η r _ hε hη]
  apply ContDiffAt.const_smul (c := ε^i)
  exact (contDiffAt_iteratedDeriv_normalizedHermiteGramKernel_ray_right q m i hm hi ε η
    (ε*r) (η*t) hε hη (by nlinarith [hε]) (by nlinarith [hη])).comp t
      (contDiffAt_const.mul contDiffAt_id)

theorem contDiffAt_iteratedDeriv_grouped_universalMagnitude_right
    (m q i : ℕ) (hi : q+i+2 ≤ 2*m) (ε r t : ℝ) (hε : ε^2=1) :
    ContDiffAt ℝ q (fun v => iteratedDeriv i (fun u => universalGramKernel m (ε*(v-u))) r) t := by
  have hreg (x : ℝ) : ContDiffAt ℝ q (iteratedDeriv i (universalGramKernel m)) x :=
    grouped_contDiffAt_iteratedDeriv _ q i x (contDiff_grouped_universalGramKernel m (q+i) hi).contDiffAt
  rcases sq_eq_one_iff.mp hε with rfl | rfl
  · simp only [one_mul, iteratedDeriv_comp_const_sub]
    exact ((hreg (t-r)).comp t (contDiffAt_id.sub contDiffAt_const)).const_smul ((-1:ℝ)^i)
  · simp only [neg_one_mul, neg_sub, iteratedDeriv_comp_sub_const]
    exact (hreg (r-t)).comp t (contDiffAt_const.sub contDiffAt_id)

theorem norm_iteratedDeriv_iteratedDeriv_grouped_universalMagnitude
    (m i j : ℕ) (ε r t : ℝ) (hε : ε^2=1) :
    ‖iteratedDeriv j (fun v => iteratedDeriv i (fun u => universalGramKernel m (ε*(v-u))) r) t‖ =
      ‖iteratedDeriv (j+i) (universalGramKernel m) (ε*(t-r))‖ := by
  rcases sq_eq_one_iff.mp hε with rfl | rfl
  · simp only [one_mul, iteratedDeriv_comp_const_sub, iteratedDeriv_fun_const_smul_field,
      iteratedDeriv_comp_sub_const, grouped_iteratedDeriv_iteratedDeriv,
      norm_smul, norm_pow, norm_neg, norm_one, one_pow]
  · simp only [neg_one_mul, neg_sub, iteratedDeriv_comp_sub_const, iteratedDeriv_comp_const_sub,
      grouped_iteratedDeriv_iteratedDeriv, norm_smul, norm_pow, norm_neg, norm_one, one_pow, one_mul]

theorem iteratedDeriv_groupedMagnitudeHermiteRemainder_left_eq
    (q m i : ℕ) (hm : groupedHermiteDifferentiationOrder q ≤ m) (hi : i ≤ q)
    (ε r t : ℝ) (hε : ε^2=1) (hr : 0 < r) :
    iteratedDeriv i (fun z => groupedMagnitudeHermiteRemainder m
      (by have := (le_max_left _ _).trans hm; omega) ε z t) r =
      iteratedDeriv i (fun z => groupedMagnitudeNormalizedKernel m
        (by have := (le_max_left _ _).trans hm; omega) ε ε z t) r -
      iteratedDeriv i (fun z => universalGramKernel m (ε*(t-z))) r := by
  have hq : q+2 ≤ m := (le_max_left _ _).trans hm
  have hK := (contDiffAt_groupedMagnitudeNormalizedKernel_left q m hm ε ε r t hε hε hr).of_le
    (show (i:WithTop ℕ∞) ≤ q by exact_mod_cast hi)
  have hU : ContDiffAt ℝ i (fun z => universalGramKernel m (ε*(t-z))) r :=
    (contDiff_grouped_universalGramKernel m i (by omega)).contDiffAt.comp r
      (contDiffAt_const.mul (contDiffAt_const.sub contDiffAt_id))
  exact iteratedDeriv_sub hK hU

theorem contDiffAt_iteratedDeriv_groupedMagnitudeHermiteRemainder_right
    (q m i : ℕ) (hm : groupedHermiteDifferentiationOrder q ≤ m) (hi : i ≤ q)
    (ε r t : ℝ) (hε : ε^2=1) (hr : 0 < r) (ht : 0 < t) :
    ContDiffAt ℝ q (fun v => iteratedDeriv i (fun u => groupedMagnitudeHermiteRemainder m
      (by have := (le_max_left _ _).trans hm; omega) ε u v) r) t := by
  have hq : q+2 ≤ m := (le_max_left _ _).trans hm
  simp_rw [iteratedDeriv_groupedMagnitudeHermiteRemainder_left_eq q m i hm hi ε r _ hε hr]
  exact (contDiffAt_iteratedDeriv_groupedMagnitudeNormalizedKernel_right q m i hm hi ε ε r t hε hε hr ht).sub
    (contDiffAt_iteratedDeriv_grouped_universalMagnitude_right m q i (by omega) ε r t hε)

theorem exists_norm_iteratedDeriv_iteratedDeriv_groupedMagnitudeHermiteRemainder_le
    (q m i j : ℕ) (hm : groupedHermiteDifferentiationOrder q ≤ m) (hi : i ≤ q) (hj : j ≤ q) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ ε : ℝ, ε^2=1 → ∀ r t : ℝ, 1 ≤ r → 1 ≤ t →
      ‖iteratedDeriv j (fun v => iteratedDeriv i (fun u => groupedMagnitudeHermiteRemainder m
        (by have := (le_max_left _ _).trans hm; omega) ε u v) r) t‖ ≤ B := by
  have hq : q+2 ≤ m := (le_max_left _ _).trans hm
  have hp : 1 ≤ m := by omega
  obtain ⟨C,hC,hbound⟩ := exists_uniform_normalizedHermiteGramKernel_signedSquareRay_derivative_bound q m hm
  refine ⟨C+groupedUniversalDerivativeBound m (j+i),
    add_nonneg hC.le (groupedUniversalDerivativeBound_nonneg m _), ?_⟩
  intro ε hε r t hr ht
  simp_rw [iteratedDeriv_groupedMagnitudeHermiteRemainder_left_eq q m i hm hi ε r _ hε (by linarith)]
  have hK := (contDiffAt_iteratedDeriv_groupedMagnitudeNormalizedKernel_right q m i hm hi ε ε r t hε hε
    (by linarith) (by linarith)).of_le (show (j:WithTop ℕ∞) ≤ q by exact_mod_cast hj)
  have hU := contDiffAt_iteratedDeriv_grouped_universalMagnitude_right m j i (by omega) ε r t hε
  change ‖iteratedDeriv j ((fun v => iteratedDeriv i
    (fun u => groupedMagnitudeNormalizedKernel m hp ε ε u v) r) -
    (fun v => iteratedDeriv i (fun u => universalGramKernel m (ε*(v-u))) r)) t‖ ≤ _
  rw [iteratedDeriv_sub hK hU]
  refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_iteratedDeriv_iteratedDeriv_groupedMagnitudeNormalizedKernel m hp i j ε ε r t hε hε]
    exact hbound i j hi hj ε ε hε hε (ε*r) (ε*t) (by nlinarith [hε]) (by nlinarith [hε])
  · rw [norm_iteratedDeriv_iteratedDeriv_grouped_universalMagnitude m i j ε r t hε]
    exact norm_iteratedDeriv_universalGramKernel_le_groupedBound m (j+i) (by omega) _

/-- Arbitrary fixed mixed derivatives of the actual same-side
Hermite-minus-universal remainder converge uniformly to zero on every
bounded signed-square displacement band. This is the near-diagonal
differentiated remainder, with a proved cofinal cutoff and no gap factor. -/
theorem groupedMagnitudeHermiteRemainder_mixedDeriv_vanishesOnBands
    (q m i j : ℕ) (hm : groupedHermiteDifferentiationOrder (q+1) ≤ m)
    (hi : i ≤ q) (hj : j ≤ q) (ε : ℝ) (hε : ε^2=1) :
    GroupedVanishesOnMagnitudeBands (fun r t => iteratedDeriv j (fun v => iteratedDeriv i (fun u =>
      groupedMagnitudeHermiteRemainder m (by have := (le_max_left _ _).trans hm; omega) ε u v) r) t) := by
  have hleft := groupedMagnitudeHermiteRemainder_iteratedDeriv_left_vanishesOnBands q m i hm hi ε hε
  apply hleft.iteratedDeriv_right q
    (fun r t hr ht => contDiffAt_iteratedDeriv_groupedMagnitudeHermiteRemainder_right (q+1) m i hm
      (by omega) ε r t hε (by linarith) (by linarith)) ?_ j hj
  intro k hk
  obtain ⟨B,hB,hbound⟩ := exists_norm_iteratedDeriv_iteratedDeriv_groupedMagnitudeHermiteRemainder_le
    (q+1) m i k hm (by omega) hk
  exact ⟨B,hB,hbound ε hε⟩

/-- A positive exponential rate uniform over the four physical ray
pairs in positive magnitude coordinates. -/
def GroupedUniformRayExponentialDecay (F : ℝ → ℝ → ℝ → ℝ → ℂ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧ ∀ ε η : ℝ, ε^2=1 → η^2=1 →
    ∀ r t : ℝ, 1 ≤ r → 1 ≤ t → ‖F ε η r t‖ ≤ C*Real.exp (-c*|η*t-ε*r|)

/-- An exponentially localized actual function retains a positive
exponential rate after differentiation. The rate loss is explicit in
the proof and comes from Taylor interpolation, not a differentiated limit. -/
theorem GroupedUniformRayExponentialDecay.deriv_left
    {F : ℝ → ℝ → ℝ → ℝ → ℂ} (hF : GroupedUniformRayExponentialDecay F)
    (hreg : ∀ ε η : ℝ, ε^2=1 → η^2=1 → ∀ r t : ℝ, 1 ≤ r → 1 ≤ t →
      ContDiffAt ℝ 2 (fun z => F ε η z t) r)
    (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ ε η : ℝ, ε^2=1 → η^2=1 → ∀ r t : ℝ, 1 ≤ r → 1 ≤ t →
      ‖iteratedDeriv 2 (fun z => F ε η z t) r‖ ≤ B) :
    GroupedUniformRayExponentialDecay (fun ε η r t => deriv (fun z => F ε η z t) r) := by
  obtain ⟨A,hA,c,hc,hdec⟩ := hF
  refine ⟨2*(A*Real.exp c)+B, by positivity, c/2, by positivity, ?_⟩
  intro ε η hε hη r t hr ht
  have heps : |ε|=1 := by nlinarith [sq_abs ε, abs_nonneg ε]
  have hd (z : ℝ) (hz : z ∈ Set.Icc r (r+1)) : |η*t-ε*r|-1 ≤ |η*t-ε*z| := by
    have hlocal : |z-r| ≤ 1 := abs_le.mpr ⟨by linarith [hz.1], by linarith [hz.2]⟩
    have htri := abs_add_le (η*t-ε*z) (ε*(z-r))
    rw [show (η*t-ε*z)+ε*(z-r)=η*t-ε*r by ring,abs_mul,heps,one_mul] at htri
    linarith
  have h := grouped_norm_deriv_le_exponential_of_secondDerivative
    (fun z => F ε η z t) r (A*Real.exp c) B c |η*t-ε*r| hc.le (abs_nonneg _)
    (fun z hz => hreg ε η hε hη z t (hr.trans hz.1) ht)
    (fun z hz => ?_) (fun z hz => hbound ε η hε hη z t (hr.trans hz.1) ht)
  · convert h using 1
    congr 2
    ring
  · refine (hdec ε η hε hη z t (hr.trans hz.1) ht).trans ?_
    rw [mul_assoc, ← Real.exp_add]
    apply mul_le_mul_of_nonneg_left _ hA.le
    exact Real.exp_le_exp.mpr (by nlinarith [hd z hz])

theorem GroupedUniformRayExponentialDecay.iteratedDeriv_left
    {F : ℝ → ℝ → ℝ → ℝ → ℂ} (hF : GroupedUniformRayExponentialDecay F) (q : ℕ)
    (hreg : ∀ ε η : ℝ, ε^2=1 → η^2=1 → ∀ r t : ℝ, 1 ≤ r → 1 ≤ t →
      ContDiffAt ℝ (q+1) (fun z => F ε η z t) r)
    (hbound : ∀ k ≤ q+1, ∃ B : ℝ, 0 ≤ B ∧ ∀ ε η : ℝ, ε^2=1 → η^2=1 →
      ∀ r t : ℝ, 1 ≤ r → 1 ≤ t → ‖iteratedDeriv k (fun z => F ε η z t) r‖ ≤ B) :
    ∀ i ≤ q, GroupedUniformRayExponentialDecay
      (fun ε η r t => iteratedDeriv i (fun z => F ε η z t) r) := by
  intro i
  induction i with
  | zero => intro _; simpa only [iteratedDeriv_zero] using hF
  | succ i ih =>
    intro hi
    obtain ⟨B,hB,hb⟩ := hbound (i+2) (by omega)
    have h := (ih (by omega)).deriv_left (fun ε η hε hη r t hr ht =>
      grouped_contDiffAt_iteratedDeriv (fun z => F ε η z t) 2 i r
        ((hreg ε η hε hη r t hr ht).of_le (by exact_mod_cast (show 2+i ≤ q+1 by omega)))) B hB
      (fun ε η hε hη r t hr ht => by
        rw [grouped_iteratedDeriv_iteratedDeriv]
        simpa only [Nat.add_comm] using hb ε η hε hη r t hr ht)
    simpa only [iteratedDeriv_succ] using h

theorem GroupedUniformRayExponentialDecay.swap
    {F : ℝ → ℝ → ℝ → ℝ → ℂ} (hF : GroupedUniformRayExponentialDecay F) :
    GroupedUniformRayExponentialDecay (fun ε η r t => F η ε t r) := by
  obtain ⟨C,hC,c,hc,h⟩ := hF
  exact ⟨C,hC,c,hc,fun ε η hε hη r t hr ht => by
    simpa only [abs_sub_comm] using h η ε hη hε t r ht hr⟩

theorem GroupedUniformRayExponentialDecay.iteratedDeriv_right
    {F : ℝ → ℝ → ℝ → ℝ → ℂ} (hF : GroupedUniformRayExponentialDecay F) (q : ℕ)
    (hreg : ∀ ε η : ℝ, ε^2=1 → η^2=1 → ∀ r t : ℝ, 1 ≤ r → 1 ≤ t →
      ContDiffAt ℝ (q+1) (F ε η r) t)
    (hbound : ∀ k ≤ q+1, ∃ B : ℝ, 0 ≤ B ∧ ∀ ε η : ℝ, ε^2=1 → η^2=1 →
      ∀ r t : ℝ, 1 ≤ r → 1 ≤ t → ‖iteratedDeriv k (F ε η r) t‖ ≤ B) :
    ∀ j ≤ q, GroupedUniformRayExponentialDecay
      (fun ε η r t => iteratedDeriv j (F ε η r) t) := by
  intro j hj
  have h := hF.swap.iteratedDeriv_left q (fun ε η hε hη r t hr ht => hreg η ε hη hε t r ht hr)
    (fun k hk => by
      obtain ⟨B,hB,hb⟩ := hbound k hk
      exact ⟨B,hB,fun ε η hε hη r t hr ht => hb η ε hη hε t r ht hr⟩) j hj
  exact h.swap

/-- Actual normalized mixed derivatives have a strictly positive
off-diagonal exponential rate, uniform over all four ray pairs. No
derivative is inferred from the value-level asymptotic theorem. -/
theorem groupedMagnitudeNormalizedKernel_mixedDeriv_exponentialDecay
    (q m i j : ℕ) (hm : groupedHermiteDifferentiationOrder (q+1) ≤ m)
    (hi : i ≤ q) (hj : j ≤ q) :
    GroupedUniformRayExponentialDecay (fun ε η r t => iteratedDeriv j (fun v => iteratedDeriv i
      (fun u => groupedMagnitudeNormalizedKernel m
        (by have := (le_max_left _ _).trans hm; omega) ε η u v) r) t) := by
  have hp : 1 ≤ m := by have := (le_max_left _ _).trans hm; omega
  have hzero : GroupedUniformRayExponentialDecay (groupedMagnitudeNormalizedKernel m hp) :=
    ⟨hermiteNormalizedGramGaussianConstant m, hermiteNormalizedGramGaussianConstant_pos hp,
      Real.pi/2, by positivity, fun ε η hε hη r t hr ht =>
        norm_groupedMagnitudeNormalizedKernel_le_exponential m hp ε η r t hε hη (by linarith) (by linarith)⟩
  obtain ⟨B,hB,hbound⟩ := exists_uniform_normalizedHermiteGramKernel_signedSquareRay_derivative_bound (q+1) m hm
  have hall (a b : ℕ) (ha : a ≤ q+1) (hb : b ≤ q+1) (ε η : ℝ) (hε : ε^2=1) (hη : η^2=1)
      (r t : ℝ) (hr : 1 ≤ r) (ht : 1 ≤ t) :
      ‖iteratedDeriv b (fun v => iteratedDeriv a
        (fun u => groupedMagnitudeNormalizedKernel m hp ε η u v) r) t‖ ≤ B := by
    rw [norm_iteratedDeriv_iteratedDeriv_groupedMagnitudeNormalizedKernel m hp a b ε η r t hε hη]
    exact hbound a b ha hb ε η hε hη (ε*r) (η*t) (by nlinarith [hε]) (by nlinarith [hη])
  have hleft := hzero.iteratedDeriv_left q
    (fun ε η hε hη r t hr _ht => contDiffAt_groupedMagnitudeNormalizedKernel_left (q+1) m hm ε η r t
      hε hη (by linarith))
    (fun k hk => ⟨B,hB.le,fun ε η hε hη r t hr ht => by
      simpa only [iteratedDeriv_zero] using hall k 0 hk (by omega) ε η hε hη r t hr ht⟩) i hi
  exact hleft.iteratedDeriv_right q
    (fun ε η hε hη r t hr ht => contDiffAt_iteratedDeriv_groupedMagnitudeNormalizedKernel_right
      (q+1) m i hm (by omega) ε η r t hε hη (by linarith) (by linarith))
    (fun k hk => ⟨B,hB.le,hall i k (by omega) hk⟩) j hj

theorem mixedDeriv_groupedMagnitudeHermiteRemainder_eq
    (q m i j : ℕ) (hm : groupedHermiteDifferentiationOrder q ≤ m) (hi : i ≤ q) (hj : j ≤ q)
    (ε r t : ℝ) (hε : ε^2=1) (hr : 0 < r) (ht : 0 < t) :
    iteratedDeriv j (fun v => iteratedDeriv i (fun u => groupedMagnitudeHermiteRemainder m
      (by have := (le_max_left _ _).trans hm; omega) ε u v) r) t =
      iteratedDeriv j (fun v => iteratedDeriv i (fun u => groupedMagnitudeNormalizedKernel m
        (by have := (le_max_left _ _).trans hm; omega) ε ε u v) r) t -
      iteratedDeriv j (fun v => iteratedDeriv i (fun u => universalGramKernel m (ε*(v-u))) r) t := by
  have hq : q+2 ≤ m := (le_max_left _ _).trans hm
  simp_rw [iteratedDeriv_groupedMagnitudeHermiteRemainder_left_eq q m i hm hi ε r _ hε hr]
  exact iteratedDeriv_sub
    ((contDiffAt_iteratedDeriv_groupedMagnitudeNormalizedKernel_right q m i hm hi ε ε r t hε hε hr ht).of_le
      (by exact_mod_cast hj))
    (contDiffAt_iteratedDeriv_grouped_universalMagnitude_right m j i (by omega) ε r t hε)

/-- The universal model inherits a genuine mixed-derivative exponential
bound from the proved differentiated limit and the independently proved
Hermite decay. This is a limit of derivatives, not a derivative of a limit. -/
theorem exists_norm_iteratedDeriv_universalGramKernel_le_exponential_grouped
    (q m i j : ℕ) (hm : groupedHermiteDifferentiationOrder (q+1) ≤ m)
    (hi : i ≤ q) (hj : j ≤ q) :
    ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧ ∀ ε : ℝ, ε^2=1 → ∀ d : ℝ,
      ‖iteratedDeriv (j+i) (universalGramKernel m) (ε*d)‖ ≤ C*Real.exp (-c*|d|) := by
  have hp : 1 ≤ m := by have := (le_max_left _ _).trans hm; omega
  obtain ⟨C,hC,c,hc,hdec⟩ := groupedMagnitudeNormalizedKernel_mixedDeriv_exponentialDecay q m i j hm hi hj
  refine ⟨C,hC,c,hc,?_⟩
  intro ε hε d
  have heps : |ε|=1 := by nlinarith [sq_abs ε, abs_nonneg ε]
  have hlim := groupedMagnitudeHermiteRemainder_mixedDeriv_vanishesOnBands q m i j hm hi hj ε hε
  by_contra hbad
  have hgap : 0 < (‖iteratedDeriv (j+i) (universalGramKernel m) (ε*d)‖ - C*Real.exp (-c*|d|))/2 := by
    push Not at hbad
    linarith
  obtain ⟨T,hT,hsmall⟩ := hlim |d| (abs_nonneg d) _ hgap
  let r := T+|d|
  let t := r+d
  have hrT : T ≤ r := by dsimp [r]; linarith [abs_nonneg d]
  have htT : T ≤ t := by dsimp [t,r]; linarith [neg_abs_le d]
  have htr : t-r=d := by dsimp [t]; ring
  have hd : |ε*t-ε*r|=|d| := by rw [← mul_sub,htr,abs_mul,heps,one_mul]
  have hk := hdec ε ε hε hε r t (hT.trans hrT) (hT.trans htT)
  rw [hd] at hk
  have hr := hsmall r t hrT htT (by rw [htr])
  dsimp only at hr hk
  rw [mixedDeriv_groupedMagnitudeHermiteRemainder_eq (q+1) m i j hm (by omega) (by omega)
    ε r t hε (by linarith) (by linarith)] at hr
  have hnorm := norm_sub_le
    (iteratedDeriv j (fun v => iteratedDeriv i (fun u => groupedMagnitudeNormalizedKernel m hp ε ε u v) r) t)
    (iteratedDeriv j (fun v => iteratedDeriv i (fun u => groupedMagnitudeNormalizedKernel m hp ε ε u v) r) t -
      iteratedDeriv j (fun v => iteratedDeriv i (fun u => universalGramKernel m (ε*(v-u))) r) t)
  rw [sub_sub_cancel, norm_iteratedDeriv_iteratedDeriv_grouped_universalMagnitude m i j ε r t hε, htr] at hnorm
  linarith

/-- Same-side far-diagonal differentiated remainder bound. Together
with `groupedMagnitudeHermiteRemainder_mixedDeriv_vanishesOnBands`, it
provides the analytic near/far split for the grouped comparison; the
Schur matrix assembly itself is a separate obligation. -/
theorem exists_norm_mixedDeriv_groupedMagnitudeHermiteRemainder_le_exponential
    (q m i j : ℕ) (hm : groupedHermiteDifferentiationOrder (q+1) ≤ m)
    (hi : i ≤ q) (hj : j ≤ q) :
    ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧ ∀ ε : ℝ, ε^2=1 → ∀ r t : ℝ,
      1 ≤ r → 1 ≤ t →
      ‖iteratedDeriv j (fun v => iteratedDeriv i (fun u => groupedMagnitudeHermiteRemainder m
        (by have := (le_max_left _ _).trans hm; omega) ε u v) r) t‖ ≤ C*Real.exp (-c*|t-r|) := by
  obtain ⟨A,hA,a,ha,hactual⟩ := groupedMagnitudeNormalizedKernel_mixedDeriv_exponentialDecay q m i j hm hi hj
  obtain ⟨B,hB,b,hb,hmodel⟩ := exists_norm_iteratedDeriv_universalGramKernel_le_exponential_grouped q m i j hm hi hj
  refine ⟨A+B,by positivity,min a b,lt_min ha hb,?_⟩
  intro ε hε r t hr ht
  rw [mixedDeriv_groupedMagnitudeHermiteRemainder_eq (q+1) m i j hm (by omega) (by omega) ε r t hε
    (by linarith) (by linarith)]
  have hεabs : |ε|=1 := by nlinarith [sq_abs ε, abs_nonneg ε]
  have hK := hactual ε ε hε hε r t hr ht
  rw [← mul_sub,abs_mul,hεabs,one_mul] at hK
  have hU : ‖iteratedDeriv j (fun v => iteratedDeriv i (fun u => universalGramKernel m (ε*(v-u))) r) t‖ ≤
      B*Real.exp (-b*|t-r|) := by
    rw [norm_iteratedDeriv_iteratedDeriv_grouped_universalMagnitude m i j ε r t hε]
    exact hmodel ε hε _
  refine (norm_sub_le _ _).trans ((add_le_add hK hU).trans ?_)
  rw [add_mul]
  apply add_le_add
  · apply mul_le_mul_of_nonneg_left _ hA.le
    apply Real.exp_le_exp.mpr
    nlinarith [min_le_left a b,abs_nonneg (t-r)]
  · apply mul_le_mul_of_nonneg_left _ hB.le
    apply Real.exp_le_exp.mpr
    nlinarith [min_le_right a b,abs_nonneg (t-r)]

/-- The genuine same-side normalized remainder in the signed-square
coordinates used by the grouped divided differences. -/
def groupedSignedSquareHermiteRemainder (m : ℕ) (hm : 1 ≤ m) (ε s t : ℝ) : ℂ :=
  normalizedHermiteGramKernel m hm (groupedSignedSquareRayPoint ε s)
    (groupedSignedSquareRayPoint ε t) - universalGramKernel m (t-s)

theorem groupedMagnitudeHermiteRemainder_eq_signedSquare
    (m : ℕ) (hm : 1 ≤ m) (ε r t : ℝ) (hε : ε^2=1) :
    groupedMagnitudeHermiteRemainder m hm ε r t =
      groupedSignedSquareHermiteRemainder m hm ε (ε*r) (ε*t) := by
  unfold groupedMagnitudeHermiteRemainder groupedSignedSquareHermiteRemainder
  rw [groupedMagnitudeNormalizedKernel_eq_ray m hm ε ε r t hε hε, mul_sub]

theorem grouped_norm_mixedDeriv_comp_signs
    (F : ℝ → ℝ → ℂ) (i j : ℕ) (ε η r t : ℝ) (hε : ε^2=1) (hη : η^2=1) :
    ‖iteratedDeriv j (fun v => iteratedDeriv i (fun u => F (ε*u) (η*v)) r) t‖ =
      ‖iteratedDeriv j (fun v => iteratedDeriv i (fun u => F u v) (ε*r)) (η*t)‖ := by
  have heq (v : ℝ) : iteratedDeriv i (fun u => F (ε*u) (η*v)) r =
      ε^i • iteratedDeriv i (fun u => F u (η*v)) (ε*r) :=
    grouped_iteratedDeriv_comp_sign (fun u => F u (η*v)) i ε r hε
  simp_rw [heq]
  rw [iteratedDeriv_fun_const_smul_field,norm_smul,norm_pow]
  have heps : ‖ε‖=1 := by rw [Real.norm_eq_abs]; nlinarith [sq_abs ε,abs_nonneg ε]
  rw [heps,one_pow,one_mul]
  exact grouped_norm_iteratedDeriv_comp_sign (fun v => iteratedDeriv i (fun u => F u v) (ε*r)) j η t hη

theorem norm_mixedDeriv_groupedMagnitudeHermiteRemainder_eq_signedSquare
    (m : ℕ) (hm : 1 ≤ m) (i j : ℕ) (ε r t : ℝ) (hε : ε^2=1) :
    ‖iteratedDeriv j (fun v => iteratedDeriv i (fun u => groupedMagnitudeHermiteRemainder m hm ε u v) r) t‖ =
      ‖iteratedDeriv j (fun v => iteratedDeriv i
        (fun u => groupedSignedSquareHermiteRemainder m hm ε u v) (ε*r)) (ε*t)‖ := by
  simp_rw [groupedMagnitudeHermiteRemainder_eq_signedSquare m hm ε _ _ hε]
  exact grouped_norm_mixedDeriv_comp_signs (groupedSignedSquareHermiteRemainder m hm ε) i j ε ε r t hε hε

/-- Signed-square near-diagonal differentiated remainder, on either
physical ray and for arbitrary fixed grouped derivative orders. -/
theorem groupedSignedSquareHermiteRemainder_mixedDeriv_vanishesOnBands
    (q m i j : ℕ) (hm : groupedHermiteDifferentiationOrder (q+1) ≤ m)
    (hi : i ≤ q) (hj : j ≤ q) (ε : ℝ) (hε : ε^2=1) :
    ∀ L ≥ 0, ∀ δ > 0, ∃ T ≥ 1, ∀ s t : ℝ,
      T ≤ ε*s → T ≤ ε*t → |t-s| ≤ L →
      ‖iteratedDeriv j (fun v => iteratedDeriv i (fun u => groupedSignedSquareHermiteRemainder m
        (by have := (le_max_left _ _).trans hm; omega) ε u v) s) t‖ ≤ δ := by
  intro L hL δ hδ
  obtain ⟨T,hT,h⟩ := groupedMagnitudeHermiteRemainder_mixedDeriv_vanishesOnBands q m i j hm hi hj ε hε L hL δ hδ
  refine ⟨T,hT,?_⟩
  intro s t hs ht hst
  have heps : |ε|=1 := by nlinarith [sq_abs ε,abs_nonneg ε]
  have hres := h (ε*s) (ε*t) hs ht (by rwa [← mul_sub,abs_mul,heps,one_mul])
  dsimp only at hres
  rw [norm_mixedDeriv_groupedMagnitudeHermiteRemainder_eq_signedSquare m _ i j ε (ε*s) (ε*t) hε,
    ← mul_assoc,← pow_two,hε,one_mul,← mul_assoc,← pow_two,hε,one_mul] at hres
  exact hres

/-- Signed-square far-diagonal differentiated remainder, with constants
uniform over both same-side physical rays and independent of node gaps. -/
theorem exists_norm_mixedDeriv_groupedSignedSquareHermiteRemainder_le_exponential
    (q m i j : ℕ) (hm : groupedHermiteDifferentiationOrder (q+1) ≤ m)
    (hi : i ≤ q) (hj : j ≤ q) :
    ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧ ∀ ε : ℝ, ε^2=1 → ∀ s t : ℝ,
      1 ≤ ε*s → 1 ≤ ε*t →
      ‖iteratedDeriv j (fun v => iteratedDeriv i (fun u => groupedSignedSquareHermiteRemainder m
        (by have := (le_max_left _ _).trans hm; omega) ε u v) s) t‖ ≤ C*Real.exp (-c*|t-s|) := by
  obtain ⟨C,hC,c,hc,h⟩ := exists_norm_mixedDeriv_groupedMagnitudeHermiteRemainder_le_exponential q m i j hm hi hj
  refine ⟨C,hC,c,hc,?_⟩
  intro ε hε s t hs ht
  have heps : |ε|=1 := by nlinarith [sq_abs ε,abs_nonneg ε]
  have hres := h ε hε (ε*s) (ε*t) hs ht
  rw [norm_mixedDeriv_groupedMagnitudeHermiteRemainder_eq_signedSquare m _ i j ε (ε*s) (ε*t) hε,
    ← mul_assoc,← pow_two,hε,one_mul,← mul_assoc,← pow_two,hε,one_mul,
    ← mul_sub,abs_mul,heps,one_mul] at hres
  exact hres

end

end MeyerGeneralProblem
