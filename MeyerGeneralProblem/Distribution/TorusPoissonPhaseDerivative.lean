module

public import MeyerGeneralProblem.Distribution.TorusPoissonHeightDerivative
public import Mathlib.Analysis.Normed.Group.Tannery

@[expose] public section

/-!
# Directional differentiation along the Haar phase flow

Composition with the actual real phase advance acts by unit complex
characters in Haar Fourier coordinates. For a square-summable
directional derivative, the scalar difference quotients converge
in the square-summable norm by dominated convergence. This identifies
the height and real-flow derivatives of the positive Poisson field.
-/

namespace MeyerGeneralProblem

noncomputable section

open Adaptive Filter MeasureTheory Set UnitAddTorus
open scoped ComplexConjugate ENNReal NNReal Topology

/-- Use normalized Haar measure for the phase torus Fourier basis. -/
local instance poissonPhaseCircleMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

local notation:max "TorusL2(" d ")" => Lp ℂ 2 (volume : Measure (UnitAddTorus d))

/-- Composition in normalized Haar `L²` with the actual phase advance. -/
def torusL2PhaseAdvance {d : Type*} [Fintype d] (β : d → ℝ) (t : ℝ) :
    TorusL2(d) →ₗᵢ[ℂ] TorusL2(d) :=
  Lp.compMeasurePreservingₗᵢ ℂ _ (measurePreserving_unitAddTorusFlow β t)

/-- The Fourier coefficient of phase advance is multiplied by the corresponding
physical modulation character. -/
theorem mFourierCoeff_torusL2PhaseAdvance {d : Type*} [Fintype d]
    (β : d → ℝ) (t : ℝ) (f : TorusL2(d)) (n : d → ℤ) :
    mFourierCoeff (torusL2PhaseAdvance β t f) n =
      combModulationCharacter (torusDirectionalFrequency β n) t * mFourierCoeff f n := by
  let advance := unitAddTorusFlow β t
  let χ := mFourier n
  let E := combModulationCharacter (torusDirectionalFrequency β n) t
  let g (θ : UnitAddTorus d) := conj (χ θ) * f θ
  have hPres : MeasurePreserving advance volume volume :=
    measurePreserving_unitAddTorusFlow β t
  have hUnit : E * conj E = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq,
      show ‖E‖ = 1 from norm_combModulationCharacter _ _, one_pow, Complex.ofReal_one]
  have hMode (θ : UnitAddTorus d) : E * conj (χ (advance θ)) = conj (χ θ) := by
    change E * conj (mFourier n (unitAddTorusFlow β t θ)) = conj (χ θ)
    rw [mFourier_unitAddTorusFlow, map_mul, ← mul_assoc]
    exact congrArg (· * conj (χ θ)) hUnit |>.trans (one_mul _)
  have hMeas : AEStronglyMeasurable g volume :=
    (Complex.continuous_conj.comp χ.continuous).aestronglyMeasurable.mul (Lp.aestronglyMeasurable f)
  simp only [mFourierCoeff]
  change (∫ θ, mFourier (-n) θ • torusL2PhaseAdvance β t f θ) =
    E * ∫ θ, mFourier (-n) θ • f θ
  simp only [mFourier_neg, smul_eq_mul]
  change (∫ θ, conj (χ θ) * torusL2PhaseAdvance β t f θ) = E * ∫ θ, g θ
  calc
    _ = ∫ θ, E * g (advance θ) := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_compMeasurePreserving f hPres] with θ hθ
      change torusL2PhaseAdvance β t f θ = f (advance θ) at hθ
      rw [hθ, ← hMode θ, mul_assoc]
    _ = _ := by
      have hMap : AEStronglyMeasurable g (Measure.map advance volume) := by
        rwa [hPres.map_eq]
      have hIntegral := integral_map hPres.measurable.aemeasurable hMap
      rw [hPres.map_eq] at hIntegral
      rw [integral_const_mul, hIntegral]

private def phaseRate (b : ℝ) : ℂ :=
  Complex.ofReal (2 * Real.pi) * Complex.I * Complex.ofReal b

private theorem hasDerivAt_combModulationCharacter (b t : ℝ) :
    HasDerivAt (combModulationCharacter b) (combModulationCharacter b t * phaseRate b) t := by
  have hInner : HasDerivAt (fun x : ℝ => phaseRate b * (x : ℂ)) (phaseRate b) t := by
    simpa only [id_eq, Complex.ofReal_one, mul_one] using
      (hasDerivAt_id t).ofReal_comp.const_mul (phaseRate b)
  convert hInner.cexp using 1
  · funext x
    simpa only [phaseRate, Complex.ofReal_mul, Complex.ofReal_ofNat] using
      combModulationCharacter_eq_exp b x
  · simp only [combModulationCharacter_eq_exp, phaseRate, Complex.ofReal_mul, Complex.ofReal_ofNat]

private theorem combModulationCharacter_zero_time (b : ℝ) :
    combModulationCharacter b 0 = 1 := by
  simp [combModulationCharacter_eq_exp]

private theorem norm_combModulationCharacter_sub_one_le (b t : ℝ) :
    ‖combModulationCharacter b t - 1‖ ≤ ‖phaseRate b‖ * ‖t‖ := by
  simpa only [combModulationCharacter_zero_time, sub_zero] using
    (convex_univ : Convex ℝ (univ : Set ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun z _ => (hasDerivAt_combModulationCharacter b z).hasDerivWithinAt)
      (fun z _ => by rw [norm_mul, norm_combModulationCharacter, one_mul])
      (mem_univ 0) (mem_univ t)

private theorem hasDerivAt_lp_phaseAdvance {ι : Type*} (b : ι → ℝ)
    (X : ℝ → lp (fun _ : ι => ℂ) 2) (x v : lp (fun _ : ι => ℂ) 2)
    (hX : ∀ t i, X t i = combModulationCharacter (b i) t * x i)
    (hv : ∀ i, v i = phaseRate (b i) * x i) :
    HasDerivAt X v 0 := by
  have hX₀ (i : ι) : X 0 i = x i := by
    rw [hX, combModulationCharacter_zero_time, one_mul]
  let Q (t : ℝ) := t⁻¹ • (X t - X 0)
  have hQ (t : ℝ) (i : ι) :
      Q t i = t⁻¹ • ((combModulationCharacter (b i) t - 1) * x i) := by
    change t⁻¹ • (X t i - X 0 i) = _
    rw [hX, hX₀, sub_mul, one_mul]
  have hCoord (i : ι) : Tendsto (fun t => Q t i) (𝓝[≠] (0 : ℝ)) (𝓝 (v i)) := by
    have h := ((hasDerivAt_combModulationCharacter (b i) 0).mul_const (x i)).tendsto_slope_zero
    simpa only [hQ, hv, zero_add, combModulationCharacter_zero_time, one_mul, sub_mul] using h
  have hBound (t : ℝ) (ht : t ≠ 0) (i : ι) : ‖Q t i‖ ≤ ‖v i‖ := by
    rw [hQ, hv, norm_smul, norm_mul, norm_mul]
    calc
      _ ≤ ‖t⁻¹‖ * ((‖phaseRate (b i)‖ * ‖t‖) * ‖x i‖) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
          (norm_combModulationCharacter_sub_one_le (b i) t) (norm_nonneg _)) (norm_nonneg _)
      _ = _ := by
        rw [norm_inv]
        calc
          _ = (‖t‖⁻¹ * ‖t‖) * (‖phaseRate (b i)‖ * ‖x i‖) := by ring
          _ = _ := by rw [inv_mul_cancel₀ (norm_ne_zero_iff.mpr ht), one_mul]
  have hTwo : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  have hSummable : Summable (fun i => 4 * ‖v i‖ ^ (2 : ℕ)) := by
    have h := (lp.memℓp v).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    rw [hTwo] at h
    exact (by simpa only [Real.rpow_two] using h : Summable (fun i => ‖v i‖ ^ (2 : ℕ))).mul_left 4
  have hTerm (i : ι) : Tendsto (fun t => ‖Q t i - v i‖ ^ (2 : ℕ))
      (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    simpa only [sub_self, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)] using
      (((hCoord i).sub (tendsto_const_nhds (x := v i))).norm.pow 2)
  have hDom : ∀ᶠ t in 𝓝[≠] (0 : ℝ), ∀ i, ‖‖Q t i - v i‖ ^ (2 : ℕ)‖ ≤ 4 * ‖v i‖ ^ (2 : ℕ) := by
    filter_upwards [self_mem_nhdsWithin] with t ht i
    have ht' : t ≠ 0 := ht
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    calc
      _ ≤ (‖Q t i‖ + ‖v i‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le _ _) 2
      _ ≤ (‖v i‖ + ‖v i‖) ^ 2 := by
        gcongr
        exact hBound t ht' i
      _ = _ := by ring
  have hSum := tendsto_tsum_of_dominated_convergence hSummable hTerm hDom
  have hNormSq (t : ℝ) : ‖Q t - v‖ ^ (2 : ℕ) = ∑' i, ‖Q t i - v i‖ ^ (2 : ℕ) := by
    have h := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) (Q t - v)
    rw [hTwo] at h
    simpa only [Real.rpow_two, lp.coeFn_sub, Pi.sub_apply] using h
  have hSq : Tendsto (fun t => ‖Q t - v‖ ^ (2 : ℕ)) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    simpa only [← hNormSq, tsum_zero] using hSum
  have hNorm : Tendsto (fun t => ‖Q t - v‖) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    have h := Real.continuous_sqrt.continuousAt.tendsto.comp hSq
    simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using h
  apply hasDerivAt_iff_tendsto_slope_zero.mpr
  simpa only [zero_add] using (tendsto_iff_norm_sub_tendsto_zero.mpr hNorm)

/-- A square-summable Fourier directional derivative is the norm derivative
along the real torus phase advance. The frequencies may be unbounded. -/
theorem hasDerivAt_torusL2PhaseAdvance {d : Type*} [Fintype d]
    (β : d → ℝ) (f D : TorusL2(d))
    (hD : ∀ n : d → ℤ, mFourierCoeff D n =
      (Complex.ofReal (2 * Real.pi) * Complex.I * Complex.ofReal (torusDirectionalFrequency β n)) *
        mFourierCoeff f n) :
    HasDerivAt (fun t => torusL2PhaseAdvance β t f) D 0 := by
  let e := (mFourierBasis (d := d)).repr
  have h := hasDerivAt_lp_phaseAdvance (torusDirectionalFrequency β)
    (fun t => e (torusL2PhaseAdvance β t f)) (e f) (e D)
    (fun t n => by
      change (mFourierBasis (d := d)).repr (torusL2PhaseAdvance β t f) n =
        _ * (mFourierBasis (d := d)).repr f n
      rw [mFourierBasis_repr, mFourierBasis_repr, mFourierCoeff_torusL2PhaseAdvance])
    (fun n => by
      change (mFourierBasis (d := d)).repr D n =
        _ * (mFourierBasis (d := d)).repr f n
      rw [mFourierBasis_repr, mFourierBasis_repr]
      exact hD n)
  let L : lp (fun _ : d → ℤ => ℂ) 2 →L[ℝ] TorusL2(d) :=
    e.symm.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ
  have hL : HasDerivAt (fun t => e.symm (e (torusL2PhaseAdvance β t f))) (e.symm (e D)) 0 :=
    L.hasFDerivAt.comp_hasDerivAt 0 h
  simpa only [e.symm_apply_apply] using hL

/-- At any real phase time, the norm derivative is the phase advance of the
directional derivative at time zero. -/
theorem hasDerivAt_torusL2PhaseAdvance_at {d : Type*} [Fintype d]
    (β : d → ℝ) (f D : TorusL2(d))
    (hD : ∀ n : d → ℤ, mFourierCoeff D n =
      (Complex.ofReal (2 * Real.pi) * Complex.I * Complex.ofReal (torusDirectionalFrequency β n)) *
        mFourierCoeff f n) (t : ℝ) :
    HasDerivAt (fun s => torusL2PhaseAdvance β s f) (torusL2PhaseAdvance β t D) t := by
  have hAdvanceD (n : d → ℤ) : mFourierCoeff (torusL2PhaseAdvance β t D) n =
      phaseRate (torusDirectionalFrequency β n) *
        mFourierCoeff (torusL2PhaseAdvance β t f) n := by
    rw [mFourierCoeff_torusL2PhaseAdvance, mFourierCoeff_torusL2PhaseAdvance, hD]
    unfold phaseRate
    ring
  have hBase := hasDerivAt_torusL2PhaseAdvance β (torusL2PhaseAdvance β t f)
    (torusL2PhaseAdvance β t D) hAdvanceD
  have hInner : HasDerivAt (fun s : ℝ => s - t) 1 t := (hasDerivAt_id t).sub_const t
  have hShift := hBase.scomp_of_eq t hInner (sub_self t).symm
  have hAdd (b u v : ℝ) : combModulationCharacter b (u + v) =
      combModulationCharacter b u * combModulationCharacter b v := by
    simp only [combModulationCharacter, mul_add, Real.fourierChar.map_add_eq_mul, Circle.coe_mul]
  have hTranslation (s : ℝ) : torusL2PhaseAdvance β (s - t) (torusL2PhaseAdvance β t f) =
      torusL2PhaseAdvance β s f := by
    apply (mFourierBasis (d := d)).repr.injective
    ext n
    rw [mFourierBasis_repr, mFourierBasis_repr]
    simp only [mFourierCoeff_torusL2PhaseAdvance, ← mul_assoc]
    congr 1
    rw [← hAdd, sub_add_cancel]
  simpa only [Function.comp_def, id_eq, one_smul, hTranslation] using hShift

/-- The real phase derivative and height derivative of the positive Poisson
field exist in the Haar `L²` norm and satisfy the Cauchy–Riemann relation. -/
theorem exists_torusSupportPositivePoissonL2_hasDerivAt_phase_and_height
    {d : Type*} [Fintype d]
    (β : d → ℝ) (S : UnitAddTorus d → LocallyFiniteCarrier)
    (T : UnitAddTorus d → TemperedDistribution ℝ ℂ)
    (hT : ∀ θ, DistributionSupportedOn (S θ).carrier (T θ))
    (hAdvance : ∀ t θ, T (unitAddTorusFlow β t θ) = combDistributionTranslation (-t) (T θ))
    (hCont : ∀ f : SchwartzMap ℝ ℂ, HasCompactSupport (f : ℝ → ℂ) →
      Continuous (fun θ => T θ f))
    {K : ℕ} (hCount : ∀ θ r, ((S θ).carrier ∩ Ico r (r + 1)).ncard ≤ K)
    {y : ℝ} (hy : 0 < y) :
    ∃ D : TorusL2(d), ∀ t : ℝ,
      HasDerivAt (fun s =>
        torusL2PhaseAdvance β s (torusSupportPositivePoissonL2 β S T hT hCont hCount y.toNNReal))
        (torusL2PhaseAdvance β t D) t ∧
      HasDerivAt (fun z : ℝ =>
        torusL2PhaseAdvance β t (torusSupportPositivePoissonL2 β S T hT hCont hCount z.toNNReal))
        (Complex.I • torusL2PhaseAdvance β t D) y := by
  obtain ⟨D, hHeight, hCoeff⟩ :=
    exists_torusSupportPositivePoissonL2_hasDerivAt_height β S T hT hAdvance hCont hCount hy
  refine ⟨D, fun t => ⟨hasDerivAt_torusL2PhaseAdvance_at β _ D hCoeff t, ?_⟩⟩
  let A := (torusL2PhaseAdvance β t).toContinuousLinearMap.restrictScalars ℝ
  have h := A.hasFDerivAt.comp_hasDerivAt y hHeight
  change HasDerivAt (fun z : ℝ =>
    torusL2PhaseAdvance β t (torusSupportPositivePoissonL2 β S T hT hCont hCount z.toNNReal))
    (torusL2PhaseAdvance β t (Complex.I • D)) y at h
  rwa [map_smul] at h

end
end MeyerGeneralProblem
