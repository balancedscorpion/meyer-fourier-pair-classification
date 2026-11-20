module

public import MeyerGeneralProblem.Distribution.BroadCauchyPairing
public import MeyerGeneralProblem.Distribution.CombScaling
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Fourier.Convolution

@[expose] public section

/-!
# Convolution of a compact frequency record with the inverse cutoff

The derivatives pass through the integral against the integrable
frequency record. Separation from its support gives quantitative
decay for the expanding inverse Fourier cutoff.
-/

namespace MeyerGeneralProblem

noncomputable section

open Filter MeasureTheory Set
open scoped Convolution FourierTransform Topology

private theorem integrable_mul_iteratedDeriv_sub (f : ℝ → ℂ) (hf : Integrable f)
    (g : SchwartzMap ℝ ℂ) (j : ℕ) (x : ℝ) :
    Integrable (fun t => f t * iteratedDeriv j (g : ℝ → ℂ) (x - t)) := by
  have hg := (g.smooth j).continuous_iteratedDeriv' j
  refine (hf.norm.mul_const (SchwartzMap.seminorm ℂ 0 j g)).mono'
    (hf.aestronglyMeasurable.mul (hg.comp (continuous_const.sub continuous_id)).aestronglyMeasurable) ?_
  filter_upwards with t
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (by
    simpa only [pow_zero, one_mul] using SchwartzMap.le_seminorm' ℂ 0 j g (x - t)) (norm_nonneg _)

private theorem hasDerivAt_integral_mul_iteratedDeriv_sub (f : ℝ → ℂ) (hf : Integrable f)
    (g : SchwartzMap ℝ ℂ) (j : ℕ) (x : ℝ) :
    HasDerivAt (fun y => ∫ t, f t * iteratedDeriv j (g : ℝ → ℂ) (y - t))
      (∫ t, f t * iteratedDeriv (j + 1) (g : ℝ → ℂ) (x - t)) x := by
  let F (y t : ℝ) := f t * iteratedDeriv j (g : ℝ → ℂ) (y - t)
  let F' (y t : ℝ) := f t * iteratedDeriv (j + 1) (g : ℝ → ℂ) (y - t)
  have hF (y : ℝ) : Integrable (F y) := integrable_mul_iteratedDeriv_sub f hf g j y
  have hF' (y : ℝ) : Integrable (F' y) := integrable_mul_iteratedDeriv_sub f hf g (j + 1) y
  let C := SchwartzMap.seminorm ℂ 0 (j + 1) g
  have hbound (t y : ℝ) : ‖F' y t‖ ≤ ‖f t‖ * C := by
    change ‖f t * iteratedDeriv (j + 1) (g : ℝ → ℂ) (y - t)‖ ≤ _
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (by
      simpa only [pow_zero, one_mul] using SchwartzMap.le_seminorm' ℂ 0 (j + 1) g (y - t)) (norm_nonneg _)
  have hderiv (t y : ℝ) : HasDerivAt (fun x => F x t) (F' y t) y := by
    have h : HasDerivAt (iteratedDeriv j (g : ℝ → ℂ))
        (iteratedDeriv (j + 1) (g : ℝ → ℂ) (y - t)) (y - t) := by
      rw [iteratedDeriv_succ]
      exact ((g.smooth (j + 1)).differentiable_iteratedDeriv' j (y - t)).hasDerivAt
    have h' : HasDerivAt (fun x : ℝ => x - t) 1 y := (hasDerivAt_id' y).sub_const t
    simpa only [F, F', Function.comp_apply, one_smul] using (h.scomp y h').const_mul (f t)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (show (univ : Set ℝ) ∈ 𝓝 x from univ_mem)
    (Eventually.of_forall fun y => (hF y).aestronglyMeasurable) (hF x)
    (hF' x).aestronglyMeasurable
    (Eventually.of_forall fun t y _ => hbound t y) (hf.norm.mul_const C)
    (Eventually.of_forall fun t y _ => hderiv t y)).2

theorem iteratedDeriv_integral_schwartz_translate (f : ℝ → ℂ) (hf : Integrable f)
    (g : SchwartzMap ℝ ℂ) (j : ℕ) :
    iteratedDeriv j (fun x => ∫ t, f t * g (x - t)) =
      fun x => ∫ t, f t * iteratedDeriv j (g : ℝ → ℂ) (x - t) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [iteratedDeriv_succ, ih]
    exact funext fun x => (hasDerivAt_integral_mul_iteratedDeriv_sub f hf g j x).deriv

private theorem continuous_integral_schwartz_translate (f : ℝ → ℂ) (hf : Integrable f)
    (g : SchwartzMap ℝ ℂ) : Continuous (fun x => ∫ t, f t * g (x - t)) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  exact (hasDerivAt_integral_mul_iteratedDeriv_sub f hf g 0 x).continuousAt

/-- The inverse Fourier cutoff retains the exact reciprocal dilation
and its positive Jacobian. -/
theorem fourierInv_scaledCompactSchwartzCutoff (N : ℕ) (x : ℝ) :
    (𝓕⁻ (scaledCompactSchwartzCutoff N) : SchwartzMap ℝ ℂ) x =
      ((N : ℝ) + 1) • (𝓕⁻ compactSchwartzCutoff : SchwartzMap ℝ ℂ) (((N : ℝ) + 1) * x) := by
  let a := compactSchwartzCutoffScale N
  have ha : 0 < a := compactSchwartzCutoffScale_pos N
  have he : scaledCompactSchwartzCutoff N = combSchwartzDilation a ha.ne' compactSchwartzCutoff := by
    ext t
    rw [scaledCompactSchwartzCutoff_apply, combSchwartzDilation_apply]
  rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq_fourier_neg, he, ← SchwartzMap.fourier_coe,
    fourier_combSchwartzDilation, mul_neg, SchwartzMap.fourier_coe, ← Real.fourierInv_eq_fourier_neg,
    ← SchwartzMap.fourierInv_coe, abs_of_pos (inv_pos.mpr ha)]
  simp only [a, compactSchwartzCutoffScale, inv_inv]

private theorem norm_iteratedDeriv_fourierInv_scaledCutoff (N j : ℕ) (x : ℝ) :
    ‖iteratedDeriv j (𝓕⁻ (scaledCompactSchwartzCutoff N) : SchwartzMap ℝ ℂ) x‖ =
      ((N : ℝ) + 1) ^ (j + 1) *
        ‖iteratedDeriv j (𝓕⁻ compactSchwartzCutoff : SchwartzMap ℝ ℂ) (((N : ℝ) + 1) * x)‖ := by
  let R := (N : ℝ) + 1
  let g : SchwartzMap ℝ ℂ := 𝓕⁻ compactSchwartzCutoff
  have hR : 0 ≤ R := by dsimp [R]; positivity
  rw [show ((𝓕⁻ (scaledCompactSchwartzCutoff N) : SchwartzMap ℝ ℂ) : ℝ → ℂ) =
    R • (fun t : ℝ => g (R * t)) from funext (fourierInv_scaledCompactSchwartzCutoff N)]
  rw [iteratedDeriv_const_smul_field, iteratedDeriv_comp_const_smul (g.smooth j)]
  change ‖R • (R ^ j • iteratedDeriv j (g : ℝ → ℂ) (R * x))‖ = _
  simp only [norm_smul, norm_pow, Real.norm_eq_abs, abs_of_nonneg hR, pow_succ]
  ring

private theorem weighted_norm_iteratedDeriv_fourierInv_scaledCutoff_le
    (a b : ℝ) (hb : 0 ≤ b) (hab : b < a) (k j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (x y : ℝ), a ≤ |x| → |y| ≤ b →
      |x| ^ k * ‖iteratedDeriv j (𝓕⁻ (scaledCompactSchwartzCutoff N) : SchwartzMap ℝ ℂ) (x - y)‖ ≤
        C * compactSchwartzCutoffScale N := by
  let d := a - b
  have hd : 0 < d := sub_pos.mpr hab
  let A := 1 + b * d⁻¹
  have hA : 0 ≤ A := by dsimp [A]; positivity
  let g : SchwartzMap ℝ ℂ := 𝓕⁻ compactSchwartzCutoff
  let D := SchwartzMap.seminorm ℂ (k + (j + 2)) j g
  let C := A ^ k * d⁻¹ ^ (j + 2) * D
  refine ⟨C, by dsimp only [C]; positivity, fun N x y hx hy => ?_⟩
  let R := (N : ℝ) + 1
  have hR : 0 < R := by dsimp [R]; positivity
  have hR₁ : 1 ≤ R := le_add_of_nonneg_left (Nat.cast_nonneg N)
  let u := R * (x - y)
  have htriangle : |x| ≤ |x - y| + |y| := by
    calc
      |x| = |(x - y) + y| := by rw [sub_add_cancel]
      _ ≤ _ := abs_add_le _ _
  have hsep : d ≤ |x - y| := by dsimp [d]; linarith
  have hui : |u| = R * |x - y| := by rw [show u = _ from rfl, abs_mul, abs_of_pos hR]
  have hdR : R ≤ d⁻¹ * |u| := by
    rw [hui, ← mul_assoc, mul_comm d⁻¹ R, mul_assoc]
    exact le_mul_of_one_le_right hR.le (one_le_inv_mul₀ hd |>.mpr hsep)
  have hxu : |x| ≤ A * |u| := by
    have hh : b ≤ b * d⁻¹ * |x - y| := by
      rw [mul_assoc]
      exact le_mul_of_one_le_right hb (one_le_inv_mul₀ hd |>.mpr hsep)
    have hx' : |x| ≤ A * |x - y| := by dsimp [A]; linarith
    exact hx'.trans (mul_le_mul_of_nonneg_left
      (by rw [hui]; exact le_mul_of_one_le_left (abs_nonneg _) hR₁) hA)
  rw [norm_iteratedDeriv_fourierInv_scaledCutoff]
  change |x| ^ k * (R ^ (j + 1) * ‖iteratedDeriv j (g : ℝ → ℂ) u‖) ≤ C * R⁻¹
  rw [← div_eq_mul_inv]
  apply (le_div_iff₀ hR).mpr
  calc
    _ = (|x| ^ k * R ^ (j + 2)) * ‖iteratedDeriv j (g : ℝ → ℂ) u‖ := by rw [pow_succ R (j + 1)]; ring
    _ ≤ ((A * |u|) ^ k * (d⁻¹ * |u|) ^ (j + 2)) * ‖iteratedDeriv j (g : ℝ → ℂ) u‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul
        (pow_le_pow_left₀ (abs_nonneg _) hxu _) (pow_le_pow_left₀ hR.le hdR _) (by positivity) (by positivity))
        (norm_nonneg _)
    _ = A ^ k * d⁻¹ ^ (j + 2) * (|u| ^ (k + (j + 2)) * ‖iteratedDeriv j (g : ℝ → ℂ) u‖) := by
      rw [mul_pow, mul_pow, pow_add]
      ring
    _ ≤ C := mul_le_mul_of_nonneg_left (SchwartzMap.le_seminorm' ℂ _ _ _ _) (by positivity)

private theorem norm_integral_schwartz_translate_le_of_separatedSupport
    (L : ℝ → ℂ) (hL : Integrable L) (a b : ℝ) (hb : 0 ≤ b) (hab : b < a)
    (hz : ∀ y : ℝ, b < |y| → L y = 0) (k j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (x : ℝ), a ≤ |x| →
      |x| ^ k * ‖∫ y, L y * iteratedDeriv j
          (𝓕⁻ (scaledCompactSchwartzCutoff N) : SchwartzMap ℝ ℂ) (x - y)‖ ≤
        C * compactSchwartzCutoffScale N := by
  obtain ⟨D, hD, hCut⟩ := weighted_norm_iteratedDeriv_fourierInv_scaledCutoff_le a b hb hab k j
  let A := ∫ y, ‖L y‖
  have hA : 0 ≤ A := integral_nonneg fun _ => norm_nonneg _
  refine ⟨A * D, mul_nonneg hA hD, fun N x hx => ?_⟩
  let g : SchwartzMap ℝ ℂ := 𝓕⁻ (scaledCompactSchwartzCutoff N)
  have hlocal (y : ℝ) : ‖|x| ^ k • (L y * iteratedDeriv j (g : ℝ → ℂ) (x - y))‖ ≤
      ‖L y‖ * (D * compactSchwartzCutoffScale N) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity), norm_mul]
    by_cases hy : |y| ≤ b
    · rw [mul_left_comm]
      exact mul_le_mul_of_nonneg_left (hCut N x y hx hy) (norm_nonneg _)
    · rw [hz y (lt_of_not_ge hy), norm_zero, zero_mul, mul_zero, zero_mul]
  rw [← norm_smul_of_nonneg (show 0 ≤ |x| ^ k by positivity), ← integral_smul]
  have hh := norm_integral_le_of_norm_le
    (hL.norm.mul_const (D * compactSchwartzCutoffScale N)) (Eventually.of_forall hlocal)
  exact hh.trans_eq (by rw [integral_mul_const]; dsimp only [A]; ring)

/-- A Schwartz function whose Fourier transform is the product of the
fixed Schwartz cutoff and the Fourier transform of an integrable
function is the convolution with the exact inverse cutoff. -/
theorem eq_integral_translate_of_fourier_eq_mul (L : ℝ → ℂ) (hL : Integrable L)
    (χ g : SchwartzMap ℝ ℂ)
    (he : ∀ ξ : ℝ, (𝓕 g : SchwartzMap ℝ ℂ) ξ = (𝓕 L) ξ * χ ξ) (x : ℝ) :
    g x = ∫ t, L t * (𝓕⁻ χ : SchwartzMap ℝ ℂ) (x - t) := by
  let h : SchwartzMap ℝ ℂ := 𝓕⁻ χ
  let f : ℝ → ℂ := L ⋆[ContinuousLinearMap.mul ℂ ℂ] (h : ℝ → ℂ)
  have hcont : Continuous f := continuous_integral_schwartz_translate L hL h
  have hint : Integrable f := hL.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) h.integrable
  have hF : 𝓕 f = (𝓕 g : SchwartzMap ℝ ℂ) := by
    funext ξ
    rw [he, show f = _ from rfl, Real.fourier_mul_convolution_eq hL h.integrable, ← SchwartzMap.fourier_coe]
    change _ * (𝓕 (𝓕⁻ χ) : SchwartzMap ℝ ℂ) ξ = _
    rw [FourierTransform.fourier_fourierInv_eq]
  have hiF : Integrable (𝓕 f) := hF ▸ (𝓕 g : SchwartzMap ℝ ℂ).integrable
  have hInv := hcont.fourierInv_fourier_eq hint hiF
  rw [hF, ← SchwartzMap.fourierInv_coe, FourierTransform.fourierInv_fourier_eq] at hInv
  exact congrFun hInv x

theorem hasTemperateGrowth_one_sub_schwartz (χ : SchwartzMap ℝ ℂ) :
    (fun x => 1 - χ x).HasTemperateGrowth :=
  (Function.HasTemperateGrowth.const (1 : ℂ)).sub χ.hasTemperateGrowth

theorem norm_iteratedDeriv_one_sub_schwartz_le (χ : SchwartzMap ℝ ℂ) (i : ℕ) (x : ℝ) :
    ‖iteratedDeriv i (fun x => 1 - χ x) x‖ ≤ 1 + SchwartzMap.seminorm ℂ 0 i χ := by
  have hc : ContDiffAt ℝ i (fun _ : ℝ => (1 : ℂ)) x := contDiffAt_const
  have hs : ‖iteratedDeriv i (χ : ℝ → ℂ) x‖ ≤ SchwartzMap.seminorm ℂ 0 i χ := by
    simpa only [pow_zero, one_mul] using SchwartzMap.le_seminorm' ℂ 0 i χ x
  have hconst : ‖iteratedDeriv i (fun _ : ℝ => (1 : ℂ)) x‖ ≤ 1 := by
    by_cases hi : i = 0 <;> simp [iteratedDeriv_const, hi]
  rw [iteratedDeriv_fun_sub hc (χ.smooth i).contDiffAt]
  exact (norm_sub_le _ _).trans (add_le_add hconst hs)

private theorem masked_inverseCutoffConvolution_seminorm_le
    (L : ℝ → ℂ) (hL : Integrable L) (a b : ℝ) (hb : 0 ≤ b) (hab : b < a)
    (hLz : ∀ y : ℝ, b < |y| → L y = 0)
    (χ : SchwartzMap ℝ ℂ) (hχ : ∀ x : ℝ, |x| < a → χ x = 1)
    (g : ℕ → SchwartzMap ℝ ℂ)
    (hg : ∀ (N : ℕ) (x : ℝ), g N x =
      ∫ t, L t * (𝓕⁻ (scaledCompactSchwartzCutoff N) : SchwartzMap ℝ ℂ) (x - t))
    (k j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N,
      SchwartzMap.seminorm ℂ k j (SchwartzMap.smulLeftCLM ℂ (fun x => 1 - χ x) (g N)) ≤
        C * compactSchwartzCutoffScale N := by
  have hnorm (i : ℕ) := norm_integral_schwartz_translate_le_of_separatedSupport L hL a b hb hab hLz k i
  choose D hD hDval using hnorm
  let B (i : ℕ) := (j.choose i : ℝ) * (1 + SchwartzMap.seminorm ℂ 0 i χ) * D (j - i)
  let C := ∑ i ∈ Finset.range (j + 1), B i
  have hC : 0 ≤ C := Finset.sum_nonneg fun i _ =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (by positivity)) (hD _)
  refine ⟨C, hC, fun N => SchwartzMap.seminorm_le_bound' ℂ k j _
    (mul_nonneg hC (compactSchwartzCutoffScale_pos N).le) ?_⟩
  intro x
  let θ (t : ℝ) := 1 - χ t
  have hfun : (SchwartzMap.smulLeftCLM ℂ θ (g N) : ℝ → ℂ) =
      θ * (g N : ℝ → ℂ) := by
    funext t
    rw [SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_one_sub_schwartz χ)]
    rfl
  change |x| ^ k * ‖iteratedDeriv j (SchwartzMap.smulLeftCLM ℂ θ (g N) : ℝ → ℂ) x‖ ≤ _
  rw [hfun]
  by_cases hx : |x| < a
  · have he : θ * (g N : ℝ → ℂ) =ᶠ[𝓝 x] (fun _ => 0) := by
      filter_upwards [(isOpen_lt continuous_abs continuous_const).mem_nhds hx] with y hy
      simp only [Pi.mul_apply, θ, hχ y hy, sub_self, zero_mul]
    rw [he.iteratedDeriv_eq j]
    simp only [iteratedDeriv_const, ite_self, norm_zero, mul_zero]
    exact mul_nonneg hC (compactSchwartzCutoffScale_pos N).le
  · have hθ : ContDiffAt ℝ j θ x := contDiffAt_const.sub (χ.smooth j).contDiffAt
    rw [iteratedDeriv_mul hθ ((g N).smooth j).contDiffAt]
    refine (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)).trans ?_
    rw [Finset.mul_sum, show C = ∑ i ∈ Finset.range (j + 1), B i from rfl, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i hi
    have hN : (g N : ℝ → ℂ) =
        fun x => ∫ t, L t * (𝓕⁻ (scaledCompactSchwartzCutoff N) : SchwartzMap ℝ ℂ) (x - t) :=
      funext (hg N)
    have hsub : |x| ^ k * ‖iteratedDeriv (j - i) (g N : ℝ → ℂ) x‖ ≤
        D (j - i) * compactSchwartzCutoffScale N := by
      rw [hN, iteratedDeriv_integral_schwartz_translate L hL]
      exact hDval (j - i) N x (le_of_not_gt hx)
    simp only [norm_mul, norm_natCast]
    calc
      _ = (j.choose i : ℝ) * ‖iteratedDeriv i θ x‖ *
          (|x| ^ k * ‖iteratedDeriv (j - i) (g N : ℝ → ℂ) x‖) := by ring
      _ ≤ (j.choose i : ℝ) * (1 + SchwartzMap.seminorm ℂ 0 i χ) *
          (D (j - i) * compactSchwartzCutoffScale N) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (norm_iteratedDeriv_one_sub_schwartz_le χ i x)
          (Nat.cast_nonneg _)) hsub (by positivity) (by positivity)
      _ = _ := by dsimp only [B]; ring

/-- Once the fixed mask vanishes on a neighborhood of the compact
frequency support, the expanding cutoff's contribution from that
support tends to zero in the full Schwartz topology. -/
theorem tendsto_masked_inverseCutoffConvolution
    (L : ℝ → ℂ) (hL : Integrable L) (a b : ℝ) (hb : 0 ≤ b) (hab : b < a)
    (hLz : ∀ y : ℝ, b < |y| → L y = 0)
    (χ : SchwartzMap ℝ ℂ) (hχ : ∀ x : ℝ, |x| < a → χ x = 1)
    (g : ℕ → SchwartzMap ℝ ℂ)
    (hg : ∀ (N : ℕ) (x : ℝ), g N x =
      ∫ t, L t * (𝓕⁻ (scaledCompactSchwartzCutoff N) : SchwartzMap ℝ ℂ) (x - t)) :
    Tendsto (fun N => SchwartzMap.smulLeftCLM ℂ (fun x => 1 - χ x) (g N)) atTop (𝓝 0) := by
  rw [(schwartz_withSeminorms ℂ ℝ ℂ).tendsto_nhds_atTop]
  rintro ⟨k, j⟩ ε hε
  obtain ⟨C, _, hC⟩ := masked_inverseCutoffConvolution_seminorm_le L hL a b hb hab hLz χ hχ g hg k j
  have ht : Tendsto (fun N => C * compactSchwartzCutoffScale N) atTop (𝓝 0) := by
    simpa only [mul_zero] using compactSchwartzCutoffScale_tendsto.const_mul C
  obtain ⟨K, hK⟩ := eventually_atTop.mp (ht.eventually_lt_const hε)
  refine ⟨K, fun N hN => ?_⟩
  simpa only [schwartzSeminormFamily, sub_zero] using (hC N).trans_lt (hK N hN)

end

end MeyerGeneralProblem
