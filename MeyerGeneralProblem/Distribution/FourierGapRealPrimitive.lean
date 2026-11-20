module

public import MeyerGeneralProblem.Distribution.FourierGapPrimitiveRepresentation
public import MeyerGeneralProblem.Sampling.CommonOrderSamplingCokernelBridge

@[expose] public section

/-!
# Real components of a tempered source with a centered Fourier gap

Conjugation reflects Fourier support while preserving value-only atomic
support. A real component of either the original source or its phase
rotation is nonzero, and taking the same component of a primitive
preserves exact differentiation.
-/

namespace MeyerGeneralProblem

noncomputable section

open Filter LineDeriv MeasureTheory Set UniformDiscrete
open scoped ComplexConjugate FourierTransform Topology

/-- Complex conjugation of a tempered distribution acts by conjugating both
the test and the resulting value. -/
def complexConjugateTemperedDistribution (T : TemperedDistribution ℝ ℂ) :
    TemperedDistribution ℝ ℂ where
  toFun φ := conj (T (complexConjugateSchwartz φ))
  map_add' φ ψ := by
    have he : complexConjugateSchwartz (φ + ψ) =
        complexConjugateSchwartz φ + complexConjugateSchwartz ψ := by
      ext x
      simp
    rw [he, map_add, map_add]
  map_smul' c φ := by
    have he : complexConjugateSchwartz (c • φ) = conj c • complexConjugateSchwartz φ := by
      ext x
      simp [smul_eq_mul, map_mul]
    rw [he, map_smul]
    simp only [RingHom.id_apply, smul_eq_mul, map_mul, starRingEnd_self_apply]
  cont := Complex.continuous_conj.comp
    (T.continuous.comp (SchwartzMap.postcompCLM Complex.conjCLE.toContinuousLinearMap).continuous)

@[simp]
theorem complexConjugateTemperedDistribution_apply (T : TemperedDistribution ℝ ℂ)
    (φ : SchwartzMap ℝ ℂ) :
    complexConjugateTemperedDistribution T φ = conj (T (complexConjugateSchwartz φ)) := rfl

private theorem complexConjugateSchwartz_twice (φ : SchwartzMap ℝ ℂ) :
    complexConjugateSchwartz (complexConjugateSchwartz φ) = φ := by
  ext x
  simp

@[simp]
theorem complexConjugateTemperedDistribution_twice (T : TemperedDistribution ℝ ℂ) :
    complexConjugateTemperedDistribution (complexConjugateTemperedDistribution T) = T := by
  ext φ
  simp [complexConjugateSchwartz_twice]

@[simp]
theorem complexConjugateTemperedDistribution_add (T U : TemperedDistribution ℝ ℂ) :
    complexConjugateTemperedDistribution (T + U) =
      complexConjugateTemperedDistribution T + complexConjugateTemperedDistribution U := by
  ext φ
  simp

theorem complexConjugateTemperedDistribution_smul (c : ℂ) (T : TemperedDistribution ℝ ℂ) :
    complexConjugateTemperedDistribution (c • T) = conj c • complexConjugateTemperedDistribution T := by
  ext φ
  simp [smul_eq_mul]

private theorem complexConjugateSchwartz_fourier (φ : SchwartzMap ℝ ℂ) :
    complexConjugateSchwartz (𝓕 φ) = 𝓕 (schwartzReflectionCLM (complexConjugateSchwartz φ)) := by
  have hF : (𝓕 (complexConjugateSchwartz (𝓕 φ)) : SchwartzMap ℝ ℂ) = complexConjugateSchwartz φ := by
    rw [fourier_complexConjugateSchwartz, FourierTransform.fourierInv_fourier_eq]
  have hR (ψ : SchwartzMap ℝ ℂ) :
      (𝓕 (schwartzReflectionCLM ψ) : SchwartzMap ℝ ℂ) = 𝓕⁻ ψ := by
    change _ = schwartzReflectionCLM (𝓕 ψ)
    rw [← schwartz_fourier_sq_eq_reflection ψ, ← schwartz_fourier_sq_eq_reflection (𝓕 ψ)]
  rw [hR, ← hF, FourierTransform.fourierInv_fourier_eq]

/-- Fourier transform and conjugation commute after reflecting the frequency
distribution. -/
theorem fourier_complexConjugateTemperedDistribution (T : TemperedDistribution ℝ ℂ) :
    (𝓕 (complexConjugateTemperedDistribution T) : TemperedDistribution ℝ ℂ) =
      complexConjugateTemperedDistribution (temperedReflectionCLM (𝓕 T)) := by
  ext φ
  simp only [TemperedDistribution.fourier_apply, complexConjugateTemperedDistribution_apply,
    temperedReflectionCLM_apply, complexConjugateSchwartz_fourier]

private theorem tsupport_complexConjugateSchwartz (φ : SchwartzMap ℝ ℂ) :
    tsupport (complexConjugateSchwartz φ : ℝ → ℂ) = tsupport (φ : ℝ → ℂ) := by
  have he : Function.support (complexConjugateSchwartz φ : ℝ → ℂ) =
      Function.support (φ : ℝ → ℂ) := by
    ext x
    simp [Function.mem_support]
  simp only [tsupport, he]

/-- A centered Fourier gap persists under conjugation of the source. -/
theorem vanishesOnInterval_fourier_complexConjugateTemperedDistribution
    {T : TemperedDistribution ℝ ℂ} {R : ℝ} (hT : VanishesOnInterval (𝓕 T) R) :
    VanishesOnInterval (𝓕 (complexConjugateTemperedDistribution T)) R := by
  intro φ hφ hSupp
  rw [fourier_complexConjugateTemperedDistribution, complexConjugateTemperedDistribution_apply,
    temperedReflectionCLM_apply]
  let ψ := complexConjugateSchwartz φ
  have hψ : HasCompactSupport (ψ : ℝ → ℂ) := by
    change IsCompact (tsupport (complexConjugateSchwartz φ : ℝ → ℂ))
    rw [tsupport_complexConjugateSchwartz]
    exact hφ
  have he : (schwartzReflectionCLM ψ : ℝ → ℂ) = (ψ : ℝ → ℂ) ∘ (Homeomorph.neg ℝ) := rfl
  have hComp : HasCompactSupport (schwartzReflectionCLM ψ : ℝ → ℂ) :=
    he.symm ▸ hψ.comp_homeomorph (Homeomorph.neg ℝ)
  have hSub : tsupport (schwartzReflectionCLM ψ : ℝ → ℂ) ⊆ Ioo (-R) R := by
    rw [he, tsupport_comp_eq_preimage]
    intro x hx
    have hx' : -x ∈ tsupport (ψ : ℝ → ℂ) := hx
    change -x ∈ tsupport (complexConjugateSchwartz φ : ℝ → ℂ) at hx'
    rw [tsupport_complexConjugateSchwartz] at hx'
    have hb := hSupp hx'
    exact ⟨by linarith [hb.2], by linarith [hb.1]⟩
  rw [hT _ hComp hSub, map_zero]

/-- Conjugation retains value-only atomic action on the given carrier. -/
theorem AtomicOnCarrier.complexConjugateTemperedDistribution
    {S : LocallyFiniteCarrier} {T : TemperedDistribution ℝ ℂ} (hT : AtomicOnCarrier S T) :
    AtomicOnCarrier S (complexConjugateTemperedDistribution T) := by
  intro φ hφ
  have hC : SchwartzVanishesOn S (complexConjugateSchwartz φ) := by
    intro x hx
    rw [complexConjugateSchwartz_apply, hφ x hx, map_zero]
  rw [complexConjugateTemperedDistribution_apply, hT _ hC, map_zero]

private theorem complexConjugateSchwartz_lineDeriv_one (φ : SchwartzMap ℝ ℂ) :
    complexConjugateSchwartz (lineDerivOp (1 : ℝ) φ) =
      lineDerivOp (1 : ℝ) (complexConjugateSchwartz φ) := by
  have hd (ψ : SchwartzMap ℝ ℂ) : lineDerivOp (1 : ℝ) ψ = SchwartzMap.derivCLM ℂ ℂ ψ := by
    ext x
    simp [SchwartzMap.lineDerivOp_apply_eq_fderiv]
  rw [hd, hd]
  ext x
  simp only [complexConjugateSchwartz_apply, SchwartzMap.derivCLM_apply]
  have h := (Complex.conjCLE.toContinuousLinearMap.hasFDerivAt (x := φ x)).comp_hasDerivAt x
    (φ.hasDerivAt x)
  exact h.deriv.symm

theorem lineDeriv_one_complexConjugateTemperedDistribution (T : TemperedDistribution ℝ ℂ) :
    lineDerivOp (1 : ℝ) (complexConjugateTemperedDistribution T) =
      complexConjugateTemperedDistribution (lineDerivOp (1 : ℝ) T) := by
  ext φ
  have hneg : complexConjugateSchwartz (-lineDerivOp (1 : ℝ) φ) =
      -lineDerivOp (1 : ℝ) (complexConjugateSchwartz φ) := by
    have he := complexConjugateSchwartz_lineDeriv_one φ
    ext x
    simp only [neg_apply, complexConjugateSchwartz_apply, map_neg]
    exact congrArg (fun g : SchwartzMap ℝ ℂ => -g x) he
  simp only [TemperedDistribution.lineDerivOp_apply_apply, complexConjugateTemperedDistribution_apply, hneg]

/-- The real part is again a complex-linear tempered distribution. -/
def realPartTemperedDistribution (T : TemperedDistribution ℝ ℂ) : TemperedDistribution ℝ ℂ :=
  (1 / 2 : ℂ) • (T + complexConjugateTemperedDistribution T)

theorem realPartTemperedDistribution_fixed (T : TemperedDistribution ℝ ℂ) :
    complexConjugateTemperedDistribution (realPartTemperedDistribution T) =
      realPartTemperedDistribution T := by
  have hHalf : conj (1 / 2 : ℂ) = 1 / 2 := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, Complex.conj_ofReal]
  simp only [realPartTemperedDistribution, complexConjugateTemperedDistribution_smul,
    complexConjugateTemperedDistribution_add, complexConjugateTemperedDistribution_twice, hHalf,
    add_comm]

theorem AtomicOnCarrier.realPartTemperedDistribution
    {S : LocallyFiniteCarrier} {T : TemperedDistribution ℝ ℂ} (hT : AtomicOnCarrier S T) :
    AtomicOnCarrier S (realPartTemperedDistribution T) := by
  intro φ hφ
  have hC := hT.complexConjugateTemperedDistribution φ hφ
  change (1 / 2 : ℂ) * (T φ + MeyerGeneralProblem.complexConjugateTemperedDistribution T φ) = 0
  rw [hT φ hφ, hC]
  simp

theorem vanishesOnInterval_fourier_realPartTemperedDistribution
    {T : TemperedDistribution ℝ ℂ} {R : ℝ} (hT : VanishesOnInterval (𝓕 T) R) :
    VanishesOnInterval (𝓕 (realPartTemperedDistribution T)) R := by
  intro φ hφ hSub
  have hC := vanishesOnInterval_fourier_complexConjugateTemperedDistribution hT φ hφ hSub
  simp [realPartTemperedDistribution, hC, hT φ hφ hSub]

theorem lineDeriv_one_realPartTemperedDistribution (T : TemperedDistribution ℝ ℂ) :
    lineDerivOp (1 : ℝ) (realPartTemperedDistribution T) =
      realPartTemperedDistribution (lineDerivOp (1 : ℝ) T) := by
  simp only [realPartTemperedDistribution, lineDerivOp_smul, lineDerivOp_add,
    lineDeriv_one_complexConjugateTemperedDistribution]

/-- A fixed choice of the real or imaginary component suffices to keep a
nonzero source nonzero. -/
theorem exists_realPart_smul_ne_zero {T : TemperedDistribution ℝ ℂ} (hT : T ≠ 0) :
    ∃ c : ℂ, (c = 1 ∨ c = -Complex.I) ∧ realPartTemperedDistribution (c • T) ≠ 0 := by
  by_cases h : realPartTemperedDistribution T = 0
  · have hsum : T + complexConjugateTemperedDistribution T = 0 :=
      (smul_eq_zero.mp h).resolve_left (by norm_num)
    have hc : complexConjugateTemperedDistribution T = -T := eq_neg_of_add_eq_zero_right hsum
    refine ⟨-Complex.I, Or.inr rfl, ?_⟩
    have he : realPartTemperedDistribution ((-Complex.I) • T) = (-Complex.I) • T := by
      rw [realPartTemperedDistribution, complexConjugateTemperedDistribution_smul, hc]
      have hI : conj (-Complex.I) = Complex.I := by simp
      rw [hI]
      ext φ
      change (1 / 2 : ℂ) * ((-Complex.I) * T φ + Complex.I * (-T φ)) = (-Complex.I) * T φ
      ring
    rw [he]
    exact smul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) hT
  · exact ⟨1, Or.inl rfl, by simpa using h⟩

private theorem iterate_lineDeriv_one_realPartTemperedDistribution (m : ℕ)
    (T : TemperedDistribution ℝ ℂ) :
    ((lineDerivOp (1 : ℝ))^[m]) (realPartTemperedDistribution T) =
      realPartTemperedDistribution (((lineDerivOp (1 : ℝ))^[m]) T) := by
  induction m generalizing T with
  | zero => rfl
  | succ m ih =>
    simp only [Function.iterate_succ_apply, lineDeriv_one_realPartTemperedDistribution, ih]

/-- An integral representative of a tempered distribution gives the
pointwise real part as representative of its real component. -/
theorem realPartTemperedDistribution_apply_of_integral
    (V : TemperedDistribution ℝ ℂ) (f : ℝ → ℂ) (hf : Continuous f)
    (q : ℕ) (C : ℝ) (hBound : ∀ x : ℝ, ‖f x‖ ≤ C * (1 + |x|) ^ q)
    (hRep : ∀ φ : SchwartzMap ℝ ℂ, V φ = ∫ x : ℝ, φ x * f x)
    (φ : SchwartzMap ℝ ℂ) :
    realPartTemperedDistribution V φ = ∫ x : ℝ, φ x * ((f x).re : ℂ) := by
  have hW := (integrable_one_add_abs_pow_mul_norm_schwartz φ q).const_mul C
  have hInt : Integrable (fun x : ℝ => φ x * f x) :=
    hW.mono' (φ.continuous.mul hf).aestronglyMeasurable (Eventually.of_forall fun x => by
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_left (hBound x) (norm_nonneg _)).trans_eq (by ring))
  have hIntC : Integrable (fun x : ℝ => φ x * conj (f x)) :=
    hW.mono' (φ.continuous.mul (Complex.continuous_conj.comp hf)).aestronglyMeasurable
      (Eventually.of_forall fun x => by
        rw [norm_mul, Complex.norm_conj]
        exact (mul_le_mul_of_nonneg_left (hBound x) (norm_nonneg _)).trans_eq (by ring))
  have hConj : complexConjugateTemperedDistribution V φ = ∫ x : ℝ, φ x * conj (f x) := by
    rw [complexConjugateTemperedDistribution_apply, hRep, ← integral_conj]
    apply integral_congr_ae
    filter_upwards with x
    simp [map_mul]
  change (1 / 2 : ℂ) * (V φ + complexConjugateTemperedDistribution V φ) = _
  rw [hRep, hConj, ← integral_add hInt hIntC, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  rw [Complex.re_eq_add_conj]
  ring

/-- A nonzero value-only atomic tempered source with a centered Fourier
gap supplies a nonzero real component on the same carrier and a
real-valued continuous polynomial-growth primitive with the same gap. -/
theorem exists_real_atomic_polynomialGrowth_primitive_with_centered_gap
    (S : LocallyFiniteCarrier) (T : TemperedDistribution ℝ ℂ) (hT : T ≠ 0)
    (hAtomic : AtomicOnCarrier S T) (R : ℝ) (hR : 0 < R)
    (hGap : VanishesOnInterval (𝓕 T) R) :
    ∃ c : ℂ, (c = 1 ∨ c = -Complex.I) ∧
      let U := realPartTemperedDistribution (c • T)
      U ≠ 0 ∧ AtomicOnCarrier S U ∧ VanishesOnInterval (𝓕 U) R ∧
        complexConjugateTemperedDistribution U = U ∧
        ∃ q : ℕ, ∀ m : ℕ, q + 2 ≤ m →
          ∃ (V : TemperedDistribution ℝ ℂ) (f : ℝ → ℝ),
            ((lineDerivOp (1 : ℝ))^[m]) V = U ∧ VanishesOnInterval (𝓕 V) R ∧
            Continuous f ∧ f ≠ 0 ∧ (∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, |f x| ≤ C * (1 + |x|) ^ q) ∧
              ∀ φ : SchwartzMap ℝ ℂ, V φ = ∫ x : ℝ, φ x * (f x : ℂ) := by
  obtain ⟨c, hc, hU⟩ := exists_realPart_smul_ne_zero hT
  have hAC : AtomicOnCarrier S (c • T) := by
    intro φ hφ
    change c * T φ = 0
    rw [hAtomic φ hφ, mul_zero]
  have hGC : VanishesOnInterval (𝓕 (c • T)) R := by
    intro φ hφ hSub
    rw [FourierTransform.fourier_smul]
    change c * (𝓕 T) φ = 0
    rw [hGap φ hφ hSub, mul_zero]
  refine ⟨c, hc, hU, hAC.realPartTemperedDistribution,
    vanishesOnInterval_fourier_realPartTemperedDistribution hGC,
    realPartTemperedDistribution_fixed _, ?_⟩
  obtain ⟨q, hPoly⟩ := exists_continuous_polynomialGrowth_primitive_with_centered_gap (c • T) R hR hGC
  refine ⟨q, fun m hm => ?_⟩
  obtain ⟨V, f, hD, hVGap, hCont, ⟨C, hC, hBound⟩, _, hRep⟩ := hPoly m hm
  let V₀ := realPartTemperedDistribution V
  let f₀ : ℝ → ℝ := fun x => (f x).re
  have hD₀ : ((lineDerivOp (1 : ℝ))^[m]) V₀ = realPartTemperedDistribution (c • T) := by
    change ((lineDerivOp (1 : ℝ))^[m]) (realPartTemperedDistribution V) =
      realPartTemperedDistribution (c • T)
    rw [iterate_lineDeriv_one_realPartTemperedDistribution, hD]
  have hRep₀ (φ : SchwartzMap ℝ ℂ) : V₀ φ = ∫ x : ℝ, φ x * (f₀ x : ℂ) :=
    realPartTemperedDistribution_apply_of_integral V f hCont q C hBound hRep φ
  refine ⟨V₀, f₀, hD₀, vanishesOnInterval_fourier_realPartTemperedDistribution hVGap,
    Complex.continuous_re.comp hCont, ?_, ⟨C, hC, fun x => (Complex.abs_re_le_norm (f x)).trans (hBound x)⟩,
    hRep₀⟩
  intro hZero
  have hV₀ : V₀ = 0 := by
    ext φ
    rw [hRep₀, hZero]
    simp
  have hIterZero (k : ℕ) : ((lineDerivOp (1 : ℝ))^[k]) (0 : TemperedDistribution ℝ ℂ) = 0 := by
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply, lineDerivOp_zero, ih]
  exact hU (by rw [← hD₀, hV₀, hIterZero])

/-- Iteration of the Schwartz line derivative in direction one gives the classical derivative. -/
theorem schwartz_iterate_lineDeriv_one_apply
    (m : ℕ) (φ : SchwartzMap ℝ ℂ) (x : ℝ) :
    (((lineDerivOp (1 : ℝ))^[m]) φ) x = iteratedDeriv m φ x := by
  induction m generalizing φ with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply, ih, iteratedDeriv_succ']
    have he : (lineDerivOp (1 : ℝ) φ : ℝ → ℂ) = deriv φ := by
      funext y
      simp [SchwartzMap.lineDerivOp_apply_eq_fderiv]
    rw [he]

private theorem tempered_iterate_lineDeriv_one_apply
    (m : ℕ) (V : TemperedDistribution ℝ ℂ) (φ : SchwartzMap ℝ ℂ) :
    (((lineDerivOp (1 : ℝ))^[m]) V) φ =
      (-1 : ℂ) ^ m * V (((lineDerivOp (1 : ℝ))^[m]) φ) := by
  induction m generalizing φ with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply', TemperedDistribution.lineDerivOp_apply_apply,
      map_neg, ih, Function.iterate_succ_apply, pow_succ]
    ring

/-- For a distribution fixed by conjugation, the canonical isolation
test yields a real coefficient at every carrier point. -/
theorem isolationSchwartz_apply_eq_real_of_conjugate_fixed
    (S : LocallyFiniteCarrier) (U : TemperedDistribution ℝ ℂ)
    (hU : complexConjugateTemperedDistribution U = U) (x : S.subtype) :
    U (S.isolationSchwartz x) = ((U (S.isolationSchwartz x)).re : ℂ) := by
  let ψ := S.isolationSchwartz x
  have hψ : complexConjugateSchwartz ψ = ψ := by
    ext y
    rw [complexConjugateSchwartz_apply]
    change conj ((S.isolationBump x y : ℝ) : ℂ) = ((S.isolationBump x y : ℝ) : ℂ)
    exact Complex.conj_ofReal _
  have hFix : conj (U ψ) = U ψ := by
    rw [← hψ, ← complexConjugateTemperedDistribution_apply, hU, hψ]
  have hIm : (U ψ).im = 0 := by
    have h := congrArg Complex.im hFix
    rw [Complex.conj_im] at h
    linarith
  change U ψ = ((U ψ).re : ℂ)
  exact Complex.ext (by simp) (by simp [hIm])

/-- A compact test pairs the weak derivative of the real primitive with
exactly the original finite list of carrier coefficients. -/
theorem real_atomic_primitive_compact_test_identity
    (S : LocallyFiniteCarrier) (U V : TemperedDistribution ℝ ℂ) (f : ℝ → ℝ) (m : ℕ)
    (hU : AtomicOnCarrier S U) (hFixed : complexConjugateTemperedDistribution U = U)
    (hD : ((lineDerivOp (1 : ℝ))^[m]) V = U)
    (hRep : ∀ φ : SchwartzMap ℝ ℂ, V φ = ∫ x : ℝ, φ x * (f x : ℂ))
    (φ : SchwartzMap ℝ ℂ) (hφ : HasCompactSupport φ) :
    ∃ E : Finset S.subtype, (∀ x : S.subtype, x ∉ E → φ x = 0) ∧
      (-1 : ℂ) ^ m * (∫ t : ℝ, iteratedDeriv m φ t * (f t : ℂ)) =
        ∑ x ∈ E, ((U (S.isolationSchwartz x)).re : ℂ) * φ x := by
  obtain ⟨E, hE, hSum⟩ := atomicOnCarrier_isLocallyAtomicCoefficientFamily S U hU φ hφ
  refine ⟨E, hE, ?_⟩
  calc
    (-1 : ℂ) ^ m * (∫ t : ℝ, iteratedDeriv m φ t * (f t : ℂ)) =
        (((lineDerivOp (1 : ℝ))^[m]) V) φ := by
      rw [tempered_iterate_lineDeriv_one_apply, hRep]
      congr 1
      simp only [schwartz_iterate_lineDeriv_one_apply]
    _ = U φ := by rw [hD]
    _ = _ := by
      rw [hSum]
      apply Finset.sum_congr rfl
      intro x _
      exact congrArg (fun z : ℂ => z * φ x)
        (isolationSchwartz_apply_eq_real_of_conjugate_fixed S U hFixed x)

end
end MeyerGeneralProblem
