module

public import MeyerGeneralProblem.Distribution.FourierGapKernelPairing
public import MeyerGeneralProblem.Cardinal.Adaptive.NativeTranslations
public import MeyerGeneralProblem.Hermite.Exhaustion
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

/-!
# Representation of the Fourier-gap primitive by a continuous function

A Schwartz kernel pairing is identified with the original Fourier
multiplier by Fubini on scalar Schwartz densities and continuity on the
negative Hermite scale. The cutoff limits then agree on each test.
-/

namespace MeyerGeneralProblem

noncomputable section

open Filter LineDeriv MeasureTheory Set UniformDiscrete
open scoped FourierTransform Topology

/-- The Schwartz test obtained by integrating the reflected translations
of a kernel against the original physical test. -/
def fourierPrimitiveKernelTest (g φ : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  𝓕 (SchwartzMap.smulLeftCLM ℂ (⇑(𝓕 g : SchwartzMap ℝ ℂ)) (𝓕⁻ φ))

theorem fourierPrimitiveKernelTest_apply (g φ : SchwartzMap ℝ ℂ) (t : ℝ) :
    fourierPrimitiveKernelTest g φ t = ∫ x : ℝ, φ x * g (x - t) := by
  let G : SchwartzMap ℝ ℂ := 𝓕 g
  let M := combSchwartzModulation (-t) G
  have hInv : (𝓕⁻ M : SchwartzMap ℝ ℂ) = combSchwartzTranslation (-t) g := by
    change (𝓕⁻ (𝓕 (combSchwartzTranslation (-t) (𝓕⁻ G))) : SchwartzMap ℝ ℂ) = _
    rw [FourierTransform.fourierInv_fourier_eq, show (𝓕⁻ G : SchwartzMap ℝ ℂ) = g from
      FourierTransform.fourierInv_fourier_eq g]
  have h := SchwartzMap.integral_fourierInv_mul_eq φ M
  rw [hInv] at h
  calc
    fourierPrimitiveKernelTest g φ t = ∫ x : ℝ, (𝓕⁻ φ : SchwartzMap ℝ ℂ) x * M x := by
      unfold fourierPrimitiveKernelTest
      rw [SchwartzMap.fourier_coe, Real.fourier_eq]
      apply integral_congr_ae
      filter_upwards with x
      rw [SchwartzMap.smulLeftCLM_apply_apply G.hasTemperateGrowth,
        show M x = combModulationCharacter (-t) x * G x from combSchwartzModulation_apply _ _ _]
      simp only [Real.inner_apply, Circle.smul_def, smul_eq_mul, combModulationCharacter, neg_mul]
      rw [mul_comm x t]
      ac_rfl
    _ = _ := by simpa only [combSchwartzTranslation_apply, sub_eq_add_neg, add_comm] using h

private theorem integral_pairing_schwartz_density
    (h g φ : SchwartzMap ℝ ℂ) :
    (∫ x : ℝ, φ x * ∫ y : ℝ, h y * g (x - y)) =
      ∫ y : ℝ, h y * fourierPrimitiveKernelTest g φ y := by
  let A (x y : ℝ) := φ x * (h y * g (x - y))
  let C := SchwartzMap.seminorm ℂ 0 0 g
  have hp : Integrable (Function.uncurry A) (volume.prod volume) := by
    have hMeas : Continuous (Function.uncurry A) := by
      change Continuous (fun p : ℝ × ℝ => φ p.1 * (h p.2 * g (p.1 - p.2)))
      exact (φ.continuous.comp continuous_fst).mul
        ((h.continuous.comp continuous_snd).mul
          (g.continuous.comp (continuous_fst.sub continuous_snd)))
    have hMajor : Integrable (fun p : ℝ × ℝ => ‖φ p.1‖ * ‖h p.2‖) (volume.prod volume) :=
      φ.integrable.norm.mul_prod h.integrable.norm
    refine (hMajor.mul_const C).mono' hMeas.aestronglyMeasurable (Eventually.of_forall fun p => ?_)
    change ‖φ p.1 * (h p.2 * g (p.1 - p.2))‖ ≤ (‖φ p.1‖ * ‖h p.2‖) * C
    rw [norm_mul, norm_mul, ← mul_assoc]
    exact mul_le_mul_of_nonneg_left (SchwartzMap.norm_le_seminorm ℂ g _) (by positivity)
  calc
    _ = ∫ x : ℝ, ∫ y : ℝ, A x y := by
      apply integral_congr_ae
      filter_upwards with x
      exact (integral_const_mul (φ x) _).symm
    _ = ∫ y : ℝ, ∫ x : ℝ, A x y := integral_integral_swap hp
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with y
      rw [fourierPrimitiveKernelTest_apply, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      dsimp [A]
      ring

private theorem hermiteScaleDistribution_single_apply
    (m n : ℕ) (z : ℂ) (ψ : SchwartzMap ℝ ℂ) :
    hermiteScaleDistribution m (lp.single (2 : ENNReal) n z) ψ =
      ((hermiteScaleWeight (-(m : ℤ)) n : ℂ)⁻¹ * z) *
        ∫ y : ℝ, normalizedHermiteSchwartz n y * ψ y := by
  rw [hermiteScaleDistribution_apply_raw, ← schwartzHermiteCoefficients_apply_integral]
  rw [tsum_eq_single n]
  · simp only [rawHermiteCoefficients, lp.single_apply_self]
  · intro k hk
    have hz : (lp.single (2 : ENNReal) n z : HermiteScale (-(m : ℤ))) k = 0 :=
      lp.single_apply_ne _ _ _ hk
    simp only [rawHermiteCoefficients, hz, mul_zero, zero_mul]

/-- Every polynomial weight times the norm of a Schwartz test is integrable. -/
theorem integrable_one_add_abs_pow_mul_norm_schwartz (φ : SchwartzMap ℝ ℂ) (k : ℕ) :
    Integrable (fun x : ℝ => (1 + |x|) ^ k * ‖φ x‖) := by
  have hEq (x : ℝ) : (1 + |x|) ^ k * ‖φ x‖ =
      ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * (|x| ^ j * ‖φ x‖) := by
    rw [add_comm 1, add_pow, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    simp only [one_pow, mul_one]
    ring
  simp_rw [hEq]
  exact integrable_finsetSum _ fun j _ => by
    simpa only [Real.norm_eq_abs] using
      (φ.integrable_pow_mul volume j).const_mul (k.choose j : ℝ)

private theorem integral_mul_kernelPairing_single
    (m n : ℕ) (z : ℂ) (g φ : SchwartzMap ℝ ℂ) :
    (∫ x : ℝ, φ x * fourierPrimitiveKernelPairing
      (hermiteScaleDistribution m (lp.single (2 : ENNReal) n z)) g x) =
      hermiteScaleDistribution m (lp.single (2 : ENNReal) n z) (fourierPrimitiveKernelTest g φ) := by
  let h := normalizedHermiteSchwartz n
  let C : ℂ := (hermiteScaleWeight (-(m : ℤ)) n : ℂ)⁻¹ * z
  have hAct (x : ℝ) : fourierPrimitiveKernelPairing
      (hermiteScaleDistribution m (lp.single (2 : ENNReal) n z)) g x =
      C * ∫ y : ℝ, h y * g (x - y) := by
    rw [fourierPrimitiveKernelPairing, hermiteScaleDistribution_single_apply]
    simp only [h, C, schwartzReflectionCLM_apply, combSchwartzTranslation_apply, sub_eq_add_neg]
  simp_rw [hAct, mul_left_comm (φ _), integral_const_mul]
  rw [integral_pairing_schwartz_density h g φ, hermiteScaleDistribution_single_apply]

private theorem exists_norm_hermiteScale_kernelPairing_le
    (m : ℕ) (g : SchwartzMap ℝ ℂ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (u : HermiteScale (-(m : ℤ))) (x : ℝ),
      ‖fourierPrimitiveKernelPairing (hermiteScaleDistribution m u) g x‖ ≤
        D * ‖u‖ * (1 + |x|) ^ (2 * m) := by
  obtain ⟨C, hC, ht⟩ := Adaptive.exists_hermite_translation_bound m
  let g₀ := schwartzReflectionCLM g
  refine ⟨C * ‖schwartzToHermiteScale m g₀‖, by positivity, fun u x => ?_⟩
  have hShift : schwartzReflectionCLM (combSchwartzTranslation x g) =
      combSchwartzTranslation (-x) g₀ := by
    ext y
    simp only [g₀, schwartzReflectionCLM_apply, combSchwartzTranslation_apply]
    congr 1
    ring
  rw [fourierPrimitiveKernelPairing, hShift, hermiteScaleDistribution_apply]
  have h := mul_le_mul_of_nonneg_left (ht (-x) g₀) (norm_nonneg u)
  rw [abs_neg] at h
  exact (norm_hermiteScalePairing_le (m : ℤ) u _).trans (h.trans_eq (by ring))

private theorem integral_mul_kernelPairing_eq_action_hermiteScale
    (m : ℕ) (u : HermiteScale (-(m : ℤ))) (g φ : SchwartzMap ℝ ℂ) :
    (∫ x : ℝ, φ x * fourierPrimitiveKernelPairing (hermiteScaleDistribution m u) g x) =
      hermiteScaleDistribution m u (fourierPrimitiveKernelTest g φ) := by
  obtain ⟨D, hD, hK⟩ := exists_norm_hermiteScale_kernelPairing_le m g
  let F (v : HermiteScale (-(m : ℤ))) (x : ℝ) :=
    φ x * fourierPrimitiveKernelPairing (hermiteScaleDistribution m v) g x
  let W (x : ℝ) := (1 + |x|) ^ (2 * m) * ‖φ x‖
  have hW : Integrable W := integrable_one_add_abs_pow_mul_norm_schwartz φ (2 * m)
  have hNorm (v : HermiteScale (-(m : ℤ))) (x : ℝ) : ‖F v x‖ ≤ (D * ‖v‖) * W x := by
    calc
      ‖F v x‖ ≤ ‖φ x‖ * (D * ‖v‖ * (1 + |x|) ^ (2 * m)) := by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hK v x) (norm_nonneg _)
      _ = _ := by dsimp [W]; ring
  have hI (v : HermiteScale (-(m : ℤ))) : Integrable (F v) := by
    have hCont : Continuous (F v) :=
      φ.continuous.mul (continuous_fourierPrimitiveKernelPairing (hermiteScaleDistribution m v) g)
    exact (hW.const_mul (D * ‖v‖)).mono' hCont.aestronglyMeasurable (Eventually.of_forall (hNorm v))
  let A₀ : HermiteScale (-(m : ℤ)) →ₗ[ℂ] ℂ :=
    { toFun := fun v => ∫ x, F v x
      map_add' := fun v w => by
        have he : F (v + w) = fun x => F v x + F w x := by
          funext x
          simp only [F, fourierPrimitiveKernelPairing, ← hermiteScaleDistributionCLM_apply,
            map_add, add_apply, mul_add]
        exact he ▸ integral_add (hI v) (hI w)
      map_smul' := fun c v => by
        have he : F (c • v) = fun x => c * F v x := by
          funext x
          simp only [F, fourierPrimitiveKernelPairing, ← hermiteScaleDistributionCLM_apply,
            map_smul, smul_apply, smul_eq_mul]
          ring
        rw [he, integral_const_mul]
        rfl }
  have hA (v : HermiteScale (-(m : ℤ))) : ‖A₀ v‖ ≤ (D * ∫ x, W x) * ‖v‖ := by
    calc
      ‖A₀ v‖ ≤ ∫ x, (D * ‖v‖) * W x :=
        norm_integral_le_of_norm_le (hW.const_mul _) (Eventually.of_forall (hNorm v))
      _ = _ := by rw [integral_const_mul]; ring
  let A := A₀.mkContinuous _ hA
  let B := (PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) ℂ
    (fourierPrimitiveKernelTest g φ)).comp (hermiteScaleDistributionCLM m)
  have hSingle (n : ℕ) : A (lp.single (2 : ENNReal) n (u n)) =
      B (lp.single (2 : ENNReal) n (u n)) := by
    change (∫ x, F (lp.single (2 : ENNReal) n (u n)) x) =
      hermiteScaleDistribution m (lp.single (2 : ENNReal) n (u n)) (fourierPrimitiveKernelTest g φ)
    exact integral_mul_kernelPairing_single m n (u n) g φ
  have hs := lp.hasSum_single (p := (2 : ENNReal)) (by norm_num) u
  have hSumA := A.hasSum hs
  have hSumB := B.hasSum hs
  change A u = B u
  exact hSumA.unique (by simpa only [Function.comp_def, hSingle] using hSumB)

/-- Integration of the original tempered pairing applies the original
source to the integrated Schwartz test. -/
theorem integral_mul_fourierPrimitiveKernelPairing (T : TemperedDistribution ℝ ℂ)
    (g φ : SchwartzMap ℝ ℂ) :
    (∫ x : ℝ, φ x * fourierPrimitiveKernelPairing T g x) = T (fourierPrimitiveKernelTest g φ) := by
  obtain ⟨m, u, rfl⟩ := exists_hermiteScale_representation T
  exact integral_mul_kernelPairing_eq_action_hermiteScale m u g φ

/-- The kernel pairing represents precisely the inverse Fourier transform
of multiplication of the original Fourier distribution by the kernel symbol. -/
theorem integral_mul_fourierPrimitiveKernelPairing_eq_fourierMultiplier
    (T : TemperedDistribution ℝ ℂ) (g φ : SchwartzMap ℝ ℂ) :
    (∫ x : ℝ, φ x * fourierPrimitiveKernelPairing T g x) =
      (𝓕⁻ (TemperedDistribution.smulLeftCLM ℂ (⇑(𝓕 g : SchwartzMap ℝ ℂ)) (𝓕 T)) :
        TemperedDistribution ℝ ℂ) φ := by
  rw [integral_mul_fourierPrimitiveKernelPairing]
  rfl

private theorem tendsto_integral_mul_of_polynomialWeight
    (φ : SchwartzMap ℝ ℂ) (q : ℕ) (F : ℕ → ℝ → ℂ) (f : ℝ → ℂ)
    (hF : ∀ N, Continuous (F N)) (C : ℝ)
    (hf : ∀ x : ℝ, ‖f x‖ ≤ C * (1 + |x|) ^ q)
    (hConv : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ x : ℝ,
      ‖F N x - f x‖ ≤ ε * (1 + |x|) ^ q) :
    Tendsto (fun N => ∫ x : ℝ, φ x * F N x) atTop (𝓝 (∫ x : ℝ, φ x * f x)) := by
  let W (x : ℝ) := (1 + |x|) ^ q
  have hW (x : ℝ) : 0 < W x := by dsimp [W]; positivity
  have hlim (x : ℝ) : Tendsto (fun N => F N x) atTop (𝓝 (f x)) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hδ := div_pos hε (show 0 < 2 * W x by positivity)
    filter_upwards [hConv (ε / (2 * W x)) hδ] with N hN
    rw [dist_eq_norm]
    have hHalf : ε / (2 * W x) * W x = ε / 2 := by field_simp [(hW x).ne']
    exact (hN x).trans_lt (by change ε / (2 * W x) * W x < ε; rw [hHalf]; exact half_lt_self hε)
  apply tendsto_integral_filter_of_dominated_convergence (bound := fun x => (C + 1) * (W x * ‖φ x‖))
  · exact Eventually.of_forall fun N => ((φ.continuous.mul (hF N))).aestronglyMeasurable
  · filter_upwards [hConv 1 zero_lt_one] with N hN
    exact Eventually.of_forall fun x => by
      have hSum : ‖F N x‖ ≤ (C + 1) * W x := by
        calc
          _ = ‖(F N x - f x) + f x‖ := by rw [sub_add_cancel]
          _ ≤ ‖F N x - f x‖ + ‖f x‖ := norm_add_le _ _
          _ ≤ _ := by
            have hB := add_le_add (hN x) (hf x)
            simpa only [W, add_mul, one_mul, add_comm] using hB
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_left hSum (norm_nonneg _)).trans_eq (by ring)
  · exact (integrable_one_add_abs_pow_mul_norm_schwartz φ q).const_mul (C + 1)
  · exact Eventually.of_forall fun x => tendsto_const_nhds.mul (hlim x)

/-- High powers of the reciprocal gap symbol give a continuous
polynomial-growth representative of the actual inverse Fourier multiplier
on the original tempered source. -/
theorem exists_polynomialGrowth_representation_inverseFourier_power
    (T : TemperedDistribution ℝ ℂ) (a : ℝ → ℂ) (ha : a.HasTemperateGrowth) (r : ℝ)
    (hRecip : ∀ x : ℝ, r ≤ |x| →
      a x = ((2 * (Real.pi : ℂ) * Complex.I) * (x : ℂ))⁻¹) :
    ∃ q : ℕ, ∀ m : ℕ, q + 2 ≤ m →
      ∃ f : ℝ → ℂ, Continuous f ∧ (∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, ‖f x‖ ≤ C * (1 + |x|) ^ q) ∧
        ∀ φ : SchwartzMap ℝ ℂ,
          (𝓕⁻ (TemperedDistribution.smulLeftCLM ℂ (a ^ m) (𝓕 T)) : TemperedDistribution ℝ ℂ) φ =
            ∫ x : ℝ, φ x * f x := by
  obtain ⟨q, hf⟩ := exists_polynomialGrowth_limit_fourierPrimitiveKernelPairing T a ha r hRecip
  refine ⟨q, fun m hm => ?_⟩
  obtain ⟨f, hfCont, ⟨C, hC, hfBound⟩, hConv⟩ := hf m hm
  refine ⟨f, hfCont, ⟨C, hC, hfBound⟩, fun φ => ?_⟩
  let U := TemperedDistribution.smulLeftCLM ℂ (a ^ m) (𝓕 T)
  let g := fourierPrimitiveSchwartzApproximation a m
  let F (N : ℕ) (x : ℝ) := fourierPrimitiveKernelPairing T (g N) x
  have hF := tendsto_integral_mul_of_polynomialWeight φ q F f
    (fun N => continuous_fourierPrimitiveKernelPairing T (g N)) C hfBound hConv
  have hU := tendsto_inverseFourier_cutoff_tempered_apply U φ
  have he (N : ℕ) : (∫ x : ℝ, φ x * F N x) =
      (𝓕⁻ (TemperedDistribution.smulLeftCLM ℂ (⇑(scaledCompactSchwartzCutoff N)) U) :
        TemperedDistribution ℝ ℂ) φ := by
    change (∫ x : ℝ, φ x * fourierPrimitiveKernelPairing T (g N) x) = _
    rw [integral_mul_fourierPrimitiveKernelPairing_eq_fourierMultiplier]
    have hG : (𝓕 (g N) : SchwartzMap ℝ ℂ) =
        SchwartzMap.smulLeftCLM ℂ (a ^ m) (scaledCompactSchwartzCutoff N) :=
      FourierTransform.fourier_fourierInv_eq _
    rw [hG]
    dsimp only [U]
    rw [TemperedDistribution.smulLeftCLM_smulLeftCLM_apply (ha.pow m)
      (scaledCompactSchwartzCutoff N).hasTemperateGrowth]
    have hSymbol : (⇑(SchwartzMap.smulLeftCLM ℂ (a ^ m) (scaledCompactSchwartzCutoff N)) : ℝ → ℂ) =
        (a ^ m) * ⇑(scaledCompactSchwartzCutoff N) := by
      funext x
      exact SchwartzMap.smulLeftCLM_apply_apply (ha.pow m) _ _
    rw [hSymbol]
  change (𝓕⁻ U : TemperedDistribution ℝ ℂ) φ = _
  exact tendsto_nhds_unique hU (hF.congr' (Eventually.of_forall he))

/-- Every sufficiently high distributional primitive of a tempered source
can be chosen with the same centered Fourier gap and represented by a
continuous function of polynomial growth. -/
theorem exists_continuous_polynomialGrowth_primitive_with_centered_gap
    (T : TemperedDistribution ℝ ℂ) (R : ℝ) (hR : 0 < R)
    (hGap : VanishesOnInterval (𝓕 T) R) :
    ∃ q : ℕ, ∀ m : ℕ, q + 2 ≤ m →
      ∃ (V : TemperedDistribution ℝ ℂ) (f : ℝ → ℂ),
        ((lineDerivOp (1 : ℝ))^[m]) V = T ∧ VanishesOnInterval (𝓕 V) R ∧
          Continuous f ∧ (∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, ‖f x‖ ≤ C * (1 + |x|) ^ q) ∧
          (T ≠ 0 → f ≠ 0) ∧ ∀ φ : SchwartzMap ℝ ℂ, V φ = ∫ x : ℝ, φ x * f x := by
  obtain ⟨a, ha, hRecip, hChain⟩ := exists_fourier_symbol_for_centered_gap_primitives R (R / 2)
    (half_pos hR) (half_lt_self hR)
  obtain ⟨V, hBase, hStep, hVGap, hFourier⟩ := hChain T hGap
  obtain ⟨q, hRep⟩ := exists_polynomialGrowth_representation_inverseFourier_power T a ha (R / 2) hRecip
  have hD (m : ℕ) : ((lineDerivOp (1 : ℝ))^[m]) (V m) = T := by
    induction m with
    | zero => exact hBase
    | succ m ih => rw [Function.iterate_succ_apply, hStep, ih]
  refine ⟨q, fun m hm => ?_⟩
  obtain ⟨f, hCont, hBound, hf⟩ := hRep m hm
  have hAction (φ : SchwartzMap ℝ ℂ) : V m φ = ∫ x : ℝ, φ x * f x := by
    have hInv : (𝓕⁻ (𝓕 (V m)) : TemperedDistribution ℝ ℂ) = V m :=
      FourierTransform.fourierInv_fourier_eq _
    rw [← hInv, hFourier]
    exact hf φ
  refine ⟨V m, f, hD m, hVGap m, hCont, hBound, ?_, hAction⟩
  intro hT hfZero
  have hVZero : V m = 0 := by
    ext φ
    rw [hAction, hfZero]
    simp
  have hIterZero (k : ℕ) : ((lineDerivOp (1 : ℝ))^[k]) (0 : TemperedDistribution ℝ ℂ) = 0 := by
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply, lineDerivOp_zero, ih]
  exact hT (by rw [← hD m, hVZero, hIterZero])

end
end MeyerGeneralProblem
