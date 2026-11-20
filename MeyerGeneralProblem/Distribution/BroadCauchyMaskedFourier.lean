module

public import MeyerGeneralProblem.Distribution.BroadCauchySmoothFrequency
public import Mathlib.Analysis.Real.Pi.Bounds

@[expose] public section

/-!
# The broad Cauchy pairing across the original spectral gap

The half-line formula splits into a smooth Schwartz part and an
integrable compact part near zero. The expanding cutoff converges
on the smooth part. The compact part has Schwartz decay after applying
the mask, since its support has positive distance from the mask.
-/

namespace MeyerGeneralProblem

noncomputable section

open Filter MeasureTheory Metric Set
open scoped FourierTransform Topology

private theorem compactSchwartzCutoff_eq_zero {x : ℝ} (hx : 2 ≤ |x|) :
    compactSchwartzCutoff x = 0 := by
  rw [compactSchwartzCutoff_apply, compactSchwartzCutoffBump.zero_of_le_dist]
  · norm_num
  · simpa only [Real.dist_eq, sub_zero, compactSchwartzCutoffBump] using hx

private theorem fourier_add_of_integrable (f g : ℝ → ℂ) (hf : Integrable f) (hg : Integrable g)
    (ξ : ℝ) : 𝓕 (f + g) ξ = 𝓕 f ξ + 𝓕 g ξ := by
  rw [Real.fourier_eq, Real.fourier_eq, Real.fourier_eq]
  simp only [Pi.add_apply, smul_add]
  exact integral_add
    (by simpa only [Real.inner_apply, mul_comm ξ] using (Real.fourierIntegral_convergent_iff ξ).mpr hf)
    (by simpa only [Real.inner_apply, mul_comm ξ] using (Real.fourierIntegral_convergent_iff ξ).mpr hg)

/-- The inverse Fourier transforms of the original compact tests, after
removing a fixed central neighborhood, converge in every Schwartz
seminorm to the masked exact half-line formula. -/
theorem exists_tendsto_masked_fourierInv_broadCauchySchwartzCut
    (n : ℕ) (z : ℂ) (hz : z.im ≠ 0) (a : ℝ) (ha : 0 < a)
    (χ : SchwartzMap ℝ ℂ) (hχ : ∀ x : ℝ, |x| < a → χ x = 1) :
    ∃ H : SchwartzMap ℝ ℂ, (∀ x : ℝ, H x = (1 - χ x) * broadCauchyFrequency n z x) ∧
      Tendsto (fun N : ℕ => SchwartzMap.smulLeftCLM ℂ (fun x => 1 - χ x)
        (𝓕⁻ (broadCauchySchwartzCut (n + 1) z hz N))) atTop (𝓝 H) := by
  let b := a / 2
  have hb : 0 ≤ b := (half_pos ha).le
  have hba : b < a := half_lt_self ha
  let c := 4 / a
  have hc : 0 < c := div_pos (by norm_num) ha
  let ψ := combSchwartzDilation c hc.ne' compactSchwartzCutoff
  have hψ₁ : ∀ᶠ x in 𝓝 (0 : ℝ), ψ x = 1 := by
    filter_upwards [ball_mem_nhds (0 : ℝ) (show 0 < a / 4 by positivity)] with x hx
    have hx' : |x| < a / 4 := by simpa only [mem_ball, Real.dist_eq, sub_zero] using hx
    rw [show ψ x = compactSchwartzCutoff (c * x) from combSchwartzDilation_apply _ _ _ _]
    apply compactSchwartzCutoff_eq_one
    rw [abs_mul, abs_of_pos hc, show c = 4 / a from rfl, div_mul_eq_mul_div]
    exact (div_le_iff₀ ha).mpr (by linarith)
  have hψ₀ (x : ℝ) (hx : b < |x|) : ψ x = 0 := by
    rw [show ψ x = compactSchwartzCutoff (c * x) from combSchwartzDilation_apply _ _ _ _]
    apply compactSchwartzCutoff_eq_zero
    rw [abs_mul, abs_of_pos hc, show c = 4 / a from rfl, div_mul_eq_mul_div]
    apply (le_div_iff₀ ha).mpr
    dsimp [b] at hx
    linarith
  let G := broadCauchyFrequency n z
  obtain ⟨H, hH⟩ := exists_maskedCauchyFrequencySchwartz ψ hψ₁ n z hz
  let L (x : ℝ) := ψ x * G x
  have hL : Integrable L := by
    exact (integrable_broadCauchyFrequency n z hz).bdd_mul
      ψ.continuous.aestronglyMeasurable
      (Eventually.of_forall fun x => SchwartzMap.norm_le_seminorm ℂ ψ x)
  have hLz (x : ℝ) (hx : b < |x|) : L x = 0 := by
    simp only [L, hψ₀ x hx, zero_mul]
  have hdecomp : L + (H : ℝ → ℂ) = G := by
    funext x
    change ψ x * G x + H x = G x
    rw [hH x]
    change ψ x * G x + (1 - ψ x) * G x = G x
    ring
  have hdecF (x : ℝ) : 𝓕 L x + (𝓕 H : SchwartzMap ℝ ℂ) x = broadCauchyKernel (n + 1) z x := by
    rw [SchwartzMap.fourier_coe, ← fourier_add_of_integrable L (H : ℝ → ℂ) hL H.integrable x,
      hdecomp]
    exact congrFun (fourier_broadCauchyFrequency n z hz) x
  let F (N : ℕ) := broadCauchySchwartzCut (n + 1) z hz N
  let J (N : ℕ) := compactSchwartzApproximation N (𝓕 H)
  let g (N : ℕ) : SchwartzMap ℝ ℂ := 𝓕⁻ (F N - J N)
  have hG (N : ℕ) (x : ℝ) : g N x =
      ∫ t, L t * (𝓕⁻ (scaledCompactSchwartzCutoff N) : SchwartzMap ℝ ℂ) (x - t) := by
    refine eq_integral_translate_of_fourier_eq_mul L hL (scaledCompactSchwartzCutoff N) (g N)
      (fun ξ => ?_) x
    change (𝓕 (𝓕⁻ (F N - J N)) : SchwartzMap ℝ ℂ) ξ = _
    rw [FourierTransform.fourier_fourierInv_eq]
    change F N ξ - J N ξ = _
    dsimp only [F, J]
    rw [broadCauchySchwartzCut_apply, compactSchwartzApproximation_apply, ← hdecF]
    ring
  let M := SchwartzMap.smulLeftCLM ℂ (fun x => 1 - χ x)
  have hTail := tendsto_masked_inverseCutoffConvolution L hL a b hb hba hLz χ hχ g hG
  have hMain : Tendsto (fun N : ℕ => M (𝓕⁻ (J N))) atTop (𝓝 (M H)) := by
    let I := FourierTransform.fourierInvCLM ℂ (SchwartzMap ℝ ℂ)
    have ht := (M.continuous.tendsto (I (𝓕 H))).comp
      ((I.continuous.tendsto (𝓕 H)).comp (compactSchwartzApproximation_tendsto (𝓕 H)))
    change Tendsto (fun N => M (𝓕⁻ (J N))) atTop (𝓝 (M (𝓕⁻ (𝓕 H)))) at ht
    rwa [FourierTransform.fourierInv_fourier_eq] at ht
  refine ⟨M H, fun x => ?_, ?_⟩
  · change SchwartzMap.smulLeftCLM ℂ (fun x => 1 - χ x) H x = _
    rw [SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_one_sub_schwartz χ),
      smul_eq_mul, hH x]
    by_cases hx : |x| < a
    · rw [hχ x hx, sub_self, zero_mul, zero_mul]
    · rw [hψ₀ x (hba.trans_le (le_of_not_gt hx)), sub_zero, one_mul]
  · have ht : Tendsto (fun N => M (𝓕⁻ (J N)) + M (g N)) atTop (𝓝 (M H)) := by
      simpa only [add_zero] using hMain.add hTail
    refine ht.congr' (Eventually.of_forall fun N => ?_)
    change M (𝓕⁻ (J N)) + M (𝓕⁻ (F N - J N)) = M (𝓕⁻ (F N))
    rw [← map_add]
    congr 1
    let I := FourierTransform.fourierInvCLM ℂ (SchwartzMap ℝ ℂ)
    change I (J N) + I (F N - J N) = I (F N)
    rw [← map_add]
    congr 1
    abel

/-- The original Cauchy pairing can be evaluated directly on the masked
Schwartz frequency test when the Fourier distribution has a genuine gap. -/
theorem exists_broadCauchyPairing_eq_gapTest
    (U : TemperedDistribution ℝ ℂ) (q n : ℕ) (hU : HasSchwartzOrderBound U q) (hm : q < n + 1)
    (z : ℂ) (hz : z.im ≠ 0) (a r : ℝ) (ha : 0 < a)
    (hgap : ∀ f : SchwartzMap ℝ ℂ, HasCompactSupport (f : ℝ → ℂ) →
      tsupport (f : ℝ → ℂ) ⊆ Ioo (-r) r → (𝓕 U) f = 0)
    (χ : SchwartzMap ℝ ℂ) (hχ : ∀ x : ℝ, |x| < a → χ x = 1)
    (hχc : HasCompactSupport (χ : ℝ → ℂ)) (hχs : tsupport (χ : ℝ → ℂ) ⊆ Ioo (-r) r) :
    ∃ H : SchwartzMap ℝ ℂ, (∀ x : ℝ, H x = (1 - χ x) * broadCauchyFrequency n z x) ∧
      broadCauchyPairing U q (n + 1) hU hm z hz = (𝓕 U) H := by
  obtain ⟨H, hH, hlim⟩ := exists_tendsto_masked_fourierInv_broadCauchySchwartzCut n z hz a ha χ hχ
  let F (N : ℕ) := broadCauchySchwartzCut (n + 1) z hz N
  let η : TemperedDistribution ℝ ℂ := 𝓕 U
  let A := SchwartzMap.smulLeftCLM ℂ χ
  let B := SchwartzMap.smulLeftCLM ℂ (fun x => 1 - χ x)
  have he (N : ℕ) : U (F N) = η (B (𝓕⁻ (F N))) := by
    let f : SchwartzMap ℝ ℂ := 𝓕⁻ (F N)
    have hbase : η f = U (F N) := by
      change (𝓕 U) (𝓕⁻ (F N) : SchwartzMap ℝ ℂ) = _
      rw [TemperedDistribution.fourier_apply, FourierTransform.fourier_fourierInv_eq]
    have hA : (A f : ℝ → ℂ) = fun x => χ x * f x := by
      funext x
      exact SchwartzMap.smulLeftCLM_apply_apply χ.hasTemperateGrowth f x
    have hAc : HasCompactSupport (A f : ℝ → ℂ) := by
      rw [hA]
      exact hχc.mul_right
    have hAs : tsupport (A f : ℝ → ℂ) ⊆ Ioo (-r) r := by
      rw [hA]
      exact tsupport_mul_subset_left.trans hχs
    have hSplit : f = A f + B f := by
      ext x
      change f x = A f x + B f x
      rw [show A f x = χ x * f x from congrFun hA x]
      change f x = χ x * f x + SchwartzMap.smulLeftCLM ℂ (fun x => 1 - χ x) f x
      rw [SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_one_sub_schwartz χ), smul_eq_mul]
      ring
    rw [← hbase]
    calc
      η f = η (A f + B f) := congrArg (fun g : SchwartzMap ℝ ℂ => η g) hSplit
      _ = η (B f) := by rw [map_add, hgap (A f) hAc hAs, zero_add]
  have hη := (η.continuous.tendsto H).comp hlim
  have hUlim := tendsto_broadCauchyPairing U q (n + 1) hU hm z hz
  refine ⟨H, hH, tendsto_nhds_unique hUlim ?_⟩
  exact hη.congr' (Eventually.of_forall fun N => (he N).symm)

/-- An actual centered gap supplies one compact mask for all off-real
poles, with any prescribed inner and outer radii within the gap. -/
theorem exists_broadCauchyPairing_eq_centeredGapTest
    (U : TemperedDistribution ℝ ℂ) (q n : ℕ) (hU : HasSchwartzOrderBound U q) (hm : q < n + 1)
    (a₀ a₁ a : ℝ) (h₀ : 0 < a₀) (h₀₁ : a₀ < a₁) (h₁ : a₁ < a)
    (hgap : ∀ f : SchwartzMap ℝ ℂ, HasCompactSupport (f : ℝ → ℂ) →
      tsupport (f : ℝ → ℂ) ⊆ Ioo (-a) a → (𝓕 U) f = 0) :
    ∃ χ : SchwartzMap ℝ ℂ, (∀ x : ℝ, |x| ≤ a₀ → χ x = 1) ∧
      (∀ x : ℝ, a₁ ≤ |x| → χ x = 0) ∧ (∀ x : ℝ, ‖χ x‖ ≤ 1) ∧
      ∀ (z : ℂ) (hz : z.im ≠ 0), ∃ H : SchwartzMap ℝ ℂ,
        (∀ x : ℝ, H x = (1 - χ x) * broadCauchyFrequency n z x) ∧
        broadCauchyPairing U q (n + 1) hU hm z hz = (𝓕 U) H := by
  let b : ContDiffBump (0 : ℝ) := ⟨a₀, a₁, h₀, h₀₁⟩
  let f : ℝ → ℂ := Complex.ofRealCLM ∘ b
  have hf : HasCompactSupport f := b.hasCompactSupport.comp_left (show ((0 : ℝ) : ℂ) = 0 by norm_num)
  let χ := hf.toSchwartzMap (Complex.ofRealCLM.contDiff.comp b.contDiff)
  have hχ (x : ℝ) (hx : |x| ≤ a₀) : χ x = 1 := by
    change (b x : ℂ) = 1
    rw [b.one_of_mem_closedBall (mem_closedBall.mpr (by simpa only [Real.dist_eq, sub_zero] using hx))]
    norm_num
  have hz (x : ℝ) (hx : a₁ ≤ |x|) : χ x = 0 := by
    change (b x : ℂ) = 0
    rw [b.zero_of_le_dist (by simpa only [Real.dist_eq, sub_zero] using hx)]
    norm_num
  have hcs : tsupport (χ : ℝ → ℂ) ⊆ closedBall (0 : ℝ) a₁ := by
    refine closure_minimal (fun x hx => ?_) isClosed_closedBall
    by_contra h
    have hdist : a₁ < dist x 0 := lt_of_not_ge (fun hh => h (mem_closedBall.mpr hh))
    exact hx (hz x (by simpa only [Real.dist_eq, sub_zero] using hdist.le))
  have hgapSupport : tsupport (χ : ℝ → ℂ) ⊆ Ioo (-a) a := by
    intro x hx
    have hx' : |x| ≤ a₁ := by simpa only [mem_closedBall, Real.dist_eq, sub_zero] using hcs hx
    exact abs_lt.mp (hx'.trans_lt h₁)
  refine ⟨χ, hχ, hz, fun x => ?_, fun z hz' => ?_⟩
  · change ‖(b x : ℂ)‖ ≤ 1
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg b.nonneg]
    exact b.le_one
  · exact exists_broadCauchyPairing_eq_gapTest U q n hU hm z hz' a₀ a h₀ hgap χ
      (fun x hx => hχ x hx.le) hf hgapSupport

/-- A genuine centered gap bounds both vertical values of the original
Cauchy pairing at the exact exponential rate from any inner gap radius. -/
theorem exists_norm_broadCauchyPairings_vertical_le
    (U : TemperedDistribution ℝ ℂ) (q n : ℕ) (hU : HasSchwartzOrderBound U q) (hm : q < n + 1)
    (a₀ a₁ a : ℝ) (h₀ : 0 < a₀) (h₀₁ : a₀ < a₁) (h₁ : a₁ < a)
    (hgap : ∀ f : SchwartzMap ℝ ℂ, HasCompactSupport (f : ℝ → ℂ) →
      tsupport (f : ℝ → ℂ) ⊆ Ioo (-a) a → (𝓕 U) f = 0) :
    ∃ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (y : ℝ), 1 ≤ y →
      ∀ (hp : (((y : ℂ) * Complex.I).im) ≠ 0) (hn : ((-((y : ℂ) * Complex.I)).im) ≠ 0),
        ‖broadCauchyPairing U q (n + 1) hU hm ((y : ℂ) * Complex.I) hp‖ +
          ‖broadCauchyPairing U q (n + 1) hU hm (-((y : ℂ) * Complex.I)) hn‖ ≤
        C * (2 * Real.pi * y) ^ k * Real.exp (-(2 * Real.pi * y) * a₀) := by
  obtain ⟨χ, hχ, _, _, hPair⟩ :=
    exists_broadCauchyPairing_eq_centeredGapTest U q n hU hm a₀ a₁ a h₀ h₀₁ h₁ hgap
  let η : TemperedDistribution ℝ ℂ := 𝓕 U
  obtain ⟨k, _, D, hD, hη⟩ := exists_hasSchwartzOrderBound η
  let I : Finset (ℕ × ℕ) := Finset.Iic (k, k)
  have htest (i : I) := seminorm_maskedCauchyFrequency_vertical_le
    χ a₀ h₀ (fun x hx => hχ x hx.le) n i.val.1 i.val.2
  choose B hB hTest using htest
  let A := ∑ i : I, B i
  have hA : 0 ≤ A := Finset.sum_nonneg fun i _ => hB i
  refine ⟨k, 2 * D * A, by positivity, fun y hy hp hn => ?_⟩
  let z : ℂ := (y : ℂ) * Complex.I
  obtain ⟨P, hP, hPaction⟩ := hPair z hp
  obtain ⟨N, hN, hNaction⟩ := hPair (-z) hn
  let s := 2 * Real.pi * y
  have hs : 1 ≤ s := by
    dsimp only [s]
    nlinarith [Real.pi_gt_three, mul_nonneg (sub_nonneg.mpr hy) (Real.pi_pos.le)]
  let W := s ^ k * Real.exp (-s * a₀)
  have hW : 0 ≤ W := by dsimp only [W]; positivity
  have hboth (i : I) : SchwartzMap.seminorm ℂ i.val.1 i.val.2 P +
      SchwartzMap.seminorm ℂ i.val.1 i.val.2 N ≤ A * W := by
    have hi : i.val.2 ≤ k := (Finset.mem_Iic.mp i.property).2
    have hbA : B i ≤ A := Finset.single_le_sum (fun i' _ => hB i') (Finset.mem_univ i)
    calc
      _ ≤ B i * s ^ i.val.2 * Real.exp (-s * a₀) := hTest i y hy P N hP hN
      _ ≤ A * s ^ k * Real.exp (-s * a₀) := mul_le_mul_of_nonneg_right
        (mul_le_mul hbA (pow_le_pow_right₀ hs hi) (by positivity) hA) (Real.exp_pos _).le
      _ = _ := by dsimp only [W]; ring
  have hsup (g : SchwartzMap ℝ ℂ)
      (hg : ∀ i : I, SchwartzMap.seminorm ℂ i.val.1 i.val.2 g ≤ A * W) :
      ‖η g‖ ≤ D * (A * W) := by
    apply (hη g).trans
    apply mul_le_mul_of_nonneg_left _ hD
    refine Seminorm.finset_sup_apply_le (mul_nonneg hA hW) fun i hi => ?_
    exact hg ⟨i, hi⟩
  have hPnorm := hsup P fun i => (le_add_of_nonneg_right (apply_nonneg _ _)).trans (hboth i)
  have hNnorm := hsup N fun i => (le_add_of_nonneg_left (apply_nonneg _ _)).trans (hboth i)
  change ‖broadCauchyPairing U q (n + 1) hU hm z hp‖ +
    ‖broadCauchyPairing U q (n + 1) hU hm (-z) hn‖ ≤ _
  rw [hPaction, hNaction]
  exact (add_le_add hPnorm hNnorm).trans_eq (by dsimp only [W, s]; ring)

end

end MeyerGeneralProblem
