module

public import MeyerGeneralProblem.Cardinal.Strong.AnnihilatorArrays
public import MeyerGeneralProblem.Distribution.OriginalAtomicTorusFiniteSampling
public import MeyerGeneralProblem.Distribution.TorusSchwartzOrbitSampling
public import MeyerGeneralProblem.Distribution.TorusCayleyHullAnnihilation
public import MeyerGeneralProblem.Distribution.TorusPoissonCayleyDirectionalEnergy
public import MeyerGeneralProblem.Sampling.GaussianDamping

@[expose] public section

/-!
# Exact original spectral equations from bounded-band annihilation

Bounded sampling passes the finite Fourier coefficient identities to the
true hull multiplier. Local finiteness of the original spectrum gives
exact stabilization at every output index.
-/

namespace MeyerGeneralProblem

noncomputable section

open Adaptive Distribution Filter MeasureTheory Set UnitAddTorus
open scoped FourierTransform SchwartzMap Topology

/-- At a fixed output label, bounded-band coefficients meet finitely
many original spectral entries, even when the phase module is dense. -/
theorem finite_support_band_convolution_row {G : Type*} [AddCommGroup G]
    (L : G →+ ℝ) (u r : G → ℂ) (hu : FrequencyLocallyFinite L u)
    (a b : ℝ) (hBand : ∀ j, r j ≠ 0 → L j ∈ Icc a b) (k : G) :
    (Function.support (fun j => r j * u (k - j))).Finite := by
  apply ((hu (L k - b) (L k - a)).image (fun n => k - n)).subset
  intro j hj
  have h := mul_ne_zero_iff.mp (show r j * u (k - j) ≠ 0 from hj)
  have hjI := hBand j h.1
  refine ⟨k - j, ⟨h.2, ?_⟩, by abel_nf⟩
  rw [map_sub]
  exact ⟨sub_le_sub_left hjI.2 _, sub_le_sub_left hjI.1 _⟩

/-- Every truncation beyond the finite active row gives the full row
sum exactly. -/
theorem eventually_sum_band_convolution_row_eq_tsum {G : Type*} [AddCommGroup G]
    (L : G →+ ℝ) (u r : G → ℂ) (hu : FrequencyLocallyFinite L u)
    (a b : ℝ) (hBand : ∀ j, r j ≠ 0 → L j ∈ Icc a b) (k : G) :
    ∀ᶠ s : Finset G in atTop, (∑ j ∈ s, r j * u (k - j)) = ∑' j, r j * u (k - j) := by
  classical
  have hFin := finite_support_band_convolution_row L u r hu a b hBand k
  filter_upwards [eventually_ge_atTop hFin.toFinset] with s hs
  exact (tsum_eq_sum fun j hj => by
    by_contra hj'
    exact hj (hs (hFin.mem_toFinset.mpr hj'))).symm

/-- A phase-label fibre sum is exactly the zero-extended original
Fourier entry at that label. -/
theorem tsum_originalFourierAtom_of_label_eq {d : Type*} [Fintype d] [DecidableEq d]
    (L : (d → ℤ) →+ ℝ) (hL : Function.Injective L) (B : LocallyFiniteCarrier)
    (label : B.subtype → d → ℤ) (hLabel : ∀ x : B.subtype, L (label x) = (x : ℝ))
    (μ : TemperedDistribution ℝ ℂ) (n : d → ℤ) :
    (∑' x : B.subtype, if label x = n then (𝓕 μ) (B.isolationSchwartz x) else 0) =
      originalFourierArray L B μ n := by
  classical
  by_cases h : L n ∈ B.carrier
  · let x₀ : B.subtype := ⟨L n, h⟩
    have hx₀ : label x₀ = n := hL (hLabel x₀)
    rw [tsum_eq_single x₀, ite_eq_left hx₀, originalFourierArray, extendedAtomicCoefficient, dite_eq_left h]
    intro x hx
    refine ite_eq_right ?_
    intro he
    apply hx
    apply Subtype.ext
    change (x : ℝ) = L n
    rw [← hLabel x, he]
  · rw [originalFourierArray, extendedAtomicCoefficient, dite_eq_right h]
    calc
      _ = ∑' _ : B.subtype, (0 : ℂ) := by
        apply tsum_congr
        intro x
        refine ite_eq_right ?_
        intro he
        apply h
        rw [← he, hLabel]
        exact x.property
      _ = _ := tsum_zero

/-- Use normalized Haar measure on each circle factor. -/
local instance originalRowCircleMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

local instance originalRowCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- An annihilating bounded-band hull multiplier gives the zero convolution
row at every index of the original spectral module. -/
theorem originalFourierArray_convolution_eq_zero_of_annihilating_band
    {d : Type*} [Fintype d] [DecidableEq d]
    (β : d → ℝ) (L : (d → ℤ) →+ ℝ) (hL : Function.Injective L)
    (hLfreq : ∀ n, L n = torusDirectionalFrequency β n)
    (B : LocallyFiniteCarrier) (label : B.subtype → d → ℤ)
    (hLabel : ∀ x : B.subtype, L (label x) = (x : ℝ))
    (N : ℕ) (μ : TemperedDistribution ℝ ℂ) (hν : 𝓕 μ ∈ stronglyTemperedAtomicAtExponent B N)
    (W : ℝ) (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d)))
    (hBand : ∀ n : d → ℤ, torusDirectionalFrequency β n ∉ Icc 0 W → mFourierCoeff f n = 0)
    (F : UnitAddTorus d → ℂ) (hF : Measurable F) (hRep : F =ᵐ[volume] f)
    (R : UnitAddTorus d → ℝ → ℂ)
    (hR : ∀ᵐ θ ∂volume, Continuous (R θ) ∧
      (R θ) =ᵐ[volume] fun x : ℝ => F (unitAddTorusFlow β x θ))
    (weight order : ℕ) (D : ℝ) (hD : 0 ≤ D)
    (hRect : ∀ᵐ θ ∂volume, ∀ g : SchwartzMap ℝ ℂ,
      ‖originalPhasePhysicalRecord B label N μ hν θ g‖ ≤
        D * ((Finset.Iic (weight, order)).sup (schwartzSeminormFamily ℂ ℝ ℂ)) g)
    (hKill : ∀ᵐ θ ∂volume,
      TemperedDistribution.smulLeftCLM ℂ (R θ) (originalPhasePhysicalRecord B label N μ hν θ) = 0)
    (k : d → ℤ) :
    (∑' j : d → ℤ, mFourierCoeff f j * originalFourierArray L B μ (k - j)) = 0 := by
  classical
  let g : SchwartzMap ℝ ℂ := 𝓕 GaussianDamping.gaussianBase
  let T := originalPhasePhysicalRecord B label N μ hν
  let a := mFourierCoeff f
  let u := originalFourierArray L B μ
  have hT (φ : SchwartzMap ℝ ℂ) : Continuous (fun θ => T θ φ) :=
    continuous_originalPhasePhysicalRecord_apply B label N μ hν φ
  obtain ⟨M, S, hM, hS, hActual⟩ := exists_torusBoundedBandSamplingCLM β W g weight order T hT D hD hRect
  let K : SchwartzMap ℝ ℂ := 𝓕⁻ (scaledCompactSchwartzCutoff M)
  have hZero : S f = 0 := by
    apply Lp.ext
    filter_upwards [hActual f hBand F hF hRep R hR, hKill,
      Lp.coeFn_zero (E := ℂ) (p := 2) (μ := (volume : Measure (UnitAddTorus d)))]
      with θ hθS hθKill hθ0
    have h := congrArg (fun U : TemperedDistribution ℝ ℂ => U g) hθKill
    simpa only [TemperedDistribution.smulLeftCLM_apply_apply, zero_apply, hθS, hθ0, Pi.zero_apply] using h
  let P (s : Finset (d → ℤ)) (θ : UnitAddTorus d) := ∑ n ∈ s, a n * mFourier n θ
  let p (s : Finset (d → ℤ)) : Lp ℂ 2 (volume : Measure (UnitAddTorus d)) :=
    ∑ n ∈ s, a n • mFourierLp 2 n
  have hP (s : Finset (d → ℤ)) : Continuous (P s) :=
    continuous_finsetSum _ fun n _ => continuous_const.mul (mFourier n).continuous
  have hp (s : Finset (d → ℤ)) : P s =ᵐ[volume] p s := by
    have he (n : d → ℤ) : (fun θ => a n * mFourier n θ) =ᵐ[volume]
        (a n • mFourierLp 2 n : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) :=
      ((Lp.coeFn_smul (a n) (mFourierLp 2 n)).trans
        ((coeFn_mFourierLp 2 n).fun_comp (fun z => a n * z))).symm
    have hPSum : P s = ∑ n ∈ s, fun θ => a n * mFourier n θ := by
      funext θ
      simp only [P, Finset.sum_apply]
    rw [hPSum]
    exact (eventuallyEq_sum fun n (_ : n ∈ s) => he n).trans (Lp.coeFn_finsetSum s _).symm
  have hLabelFreq (x : B.subtype) : torusDirectionalFrequency β (label x) = (x : ℝ) := by
    rw [← hLfreq, hLabel]
  have hFreq (j : d → ℤ) (hj : a j ≠ 0) : torusDirectionalFrequency β j ∈ Icc 0 W := by
    by_contra hc
    exact hj (hBand j hc)
  have hPass (j : d → ℤ) (hj : a j ≠ 0) : torusSchwartzKernelMultiplier β K j = 1 := by
    unfold torusSchwartzKernelMultiplier K
    rw [integral_neg_inverseFourier_mul_character]
    exact scaledCompactSchwartzCutoff_eq_one M
      (by rw [abs_of_nonneg (hFreq j hj).1]; exact (hFreq j hj).2.trans hM)
  have hKernel (s : Finset (d → ℤ)) (θ : UnitAddTorus d) :
      torusSchwartzOrbitPairing β K g T (P s) θ =
        ∑ j ∈ s, a j * (mFourier j θ *
          T θ (combSchwartzModulation (torusDirectionalFrequency β j) g)) := by
    rw [show torusSchwartzOrbitPairing β K g T (P s) θ = _ from
      torusSchwartzOrbitPairing_finite_sum β K g T s a θ]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : a j = 0
    · simp [hj]
    · rw [hPass j hj, mul_one, mul_assoc]
  have hCoeff (s : Finset (d → ℤ)) : mFourierCoeff (S (p s)) k =
      (𝓕⁻ g : SchwartzMap ℝ ℂ) (L k) * ∑ j ∈ s, a j * u (k - j) := by
    calc
      _ = mFourierCoeff (fun θ => ∑ j ∈ s, a j * (mFourier j θ *
          T θ (combSchwartzModulation (torusDirectionalFrequency β j) g))) k := by
        simp only [mFourierCoeff]
        apply integral_congr_ae
        filter_upwards [hS (p s) (P s) (hP s).measurable (hp s)] with θ hθ
        rw [hθ, hKernel s θ]
      _ = _ := by
        rw [show _ = _ from mFourierCoeff_originalPhasePhysicalRecord_finite_modulations
          B label β hLabelFreq N μ hν g s a k]
        simp only [tsum_originalFourierAtom_of_label_eq L hL B label hLabel μ, ← hLfreq, u]
  have hC : Continuous (fun f : Lp ℂ 2 (volume : Measure (UnitAddTorus d)) => mFourierCoeff f k) := by
    simp_rw [← mFourierBasis_repr]
    exact (lp.evalCLM ℂ (fun _ : d → ℤ => ℂ) 2 k).continuous.comp (mFourierBasis (d := d)).repr.continuous
  have hTendsto : Tendsto (fun s => mFourierCoeff (S (p s)) k) atTop (𝓝 0) := by
    have hpT : Tendsto p atTop (𝓝 f) := hasSum_mFourier_series_L2 f
    have hT := (hC.continuousAt.comp S.continuous.continuousAt).tendsto.comp hpT
    have h0 : mFourierCoeff (⇑(0 : Lp ℂ 2 (volume : Measure (UnitAddTorus d)))) k = 0 := by
      unfold mFourierCoeff
      calc
        _ = ∫ θ, mFourier (-k) θ • (0 : ℂ) := by
          apply integral_congr_ae
          filter_upwards [Lp.coeFn_zero (E := ℂ) (p := 2) (μ := (volume : Measure (UnitAddTorus d)))]
            with θ hθ
          rw [hθ, Pi.zero_apply]
        _ = _ := by simp
    simpa only [Function.comp_def, hZero, h0] using hT
  have hStab := eventually_sum_band_convolution_row_eq_tsum L u a
    (originalFourierArray_frequencyLocallyFinite L hL B μ) 0 W (fun j hj => by rw [hLfreq]; exact hFreq j hj) k
  have hFinal : Tendsto (fun s => mFourierCoeff (S (p s)) k) atTop
      (𝓝 ((𝓕⁻ g : SchwartzMap ℝ ℂ) (L k) * ∑' j : d → ℤ, a j * u (k - j))) :=
    tendsto_const_nhds.congr' (hStab.mono fun s hs => by
      change _ = mFourierCoeff (S (p s)) k
      rw [hCoeff s, hs])
  have hNonzero : (𝓕⁻ g : SchwartzMap ℝ ℂ) (L k) ≠ 0 := by
    rw [show 𝓕⁻ g = GaussianDamping.gaussianBase from FourierTransform.fourierInv_fourier_eq _,
      GaussianDamping.gaussianBase_apply, Complex.ofReal_ne_zero]
    exact Real.exp_ne_zero _
  exact (mul_eq_zero.mp (tendsto_nhds_unique hTendsto hFinal).symm).resolve_left hNonzero

/-- The original Cayley construction produces a nonzero bounded-band
sequence satisfying every original spectral equation, once the weighted
spectrum and common translated Schwartz bound are available. -/
theorem exists_bounded_band_originalFourierArray_annihilator_of_translated_schwartz_bound
    {d : Type*} [Fintype d] [DecidableEq d]
    (A B : LocallyFiniteCarrier) (β : d → ℝ) (L : (d → ℤ) →+ ℝ)
    (hL : Function.Injective L) (hLfreq : ∀ n, L n = torusDirectionalFrequency β n)
    (label : B.subtype → d → ℤ) (hLabel : ∀ x : B.subtype, L (label x) = (x : ℝ))
    (N : ℕ) (μ : TemperedDistribution ℝ ℂ) (hν : 𝓕 μ ∈ stronglyTemperedAtomicAtExponent B N)
    (hμ : DistributionSupportedOn A.carrier μ)
    {K : ℕ} (hA : ∀ r, windowCount A r 1 ≤ K)
    (q : ℕ) (hq : 0 < q) (D : ℝ) (hD : 0 ≤ D)
    (hUniform : ∀ (t : ℝ) (g : SchwartzMap ℝ ℂ),
      ‖combDistributionTranslation (-t) μ g‖ ≤
        D * ((Finset.Iic (2, q - 1)).sup (schwartzSeminormFamily ℂ ℝ ℂ)) g) :
    ∃ (W : ℝ) (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))), 0 ≤ W ∧ f ≠ 0 ∧
      (∀ n : d → ℤ, L n ∉ Icc 0 W → mFourierCoeff f n = 0) ∧
      ∀ k : d → ℤ, (∑' j : d → ℤ, mFourierCoeff f j * originalFourierArray L B μ (k - j)) = 0 := by
  have hLF (x : B.subtype) : torusDirectionalFrequency β (label x) = (x : ℝ) := by
    rw [← hLfreq, hLabel]
  have hIndep (n : d → ℤ) (hn : torusDirectionalFrequency β n = 0) : n = 0 := by
    apply hL
    rw [map_zero, hLfreq, hn]
  let T := originalPhasePhysicalRecord B label N μ hν
  let hCont := fun f : SchwartzMap ℝ ℂ => fun _ : HasCompactSupport (f : ℝ → ℂ) =>
    continuous_originalPhasePhysicalRecord_apply B label N μ hν f
  let hAdvance := fun t θ => originalPhasePhysicalRecord_advance B label β hLF N μ hν θ t
  obtain ⟨S, hS, hK, E, hE, _⟩ :=
    exists_originalPhasePhysical_directionalEnergy_le_upperUniformBeurlingDensity
      A B label β hLF hIndep N μ hν hμ hA
  have hRect (θ : UnitAddTorus d) (g : SchwartzMap ℝ ℂ) :
      ‖T θ g‖ ≤ D * ((Finset.Iic (2, q - 1)).sup (schwartzSeminormFamily ℂ ℝ ℂ)) g :=
    norm_originalPhasePhysicalRecord_le_of_translation_schwartzSeminorm_bound
      B label β hLF hIndep N μ hν 2 (q - 1) D hUniform θ g
  have hOrder : ∀ᵐ θ ∂volume, HasSchwartzSeminormBound (T θ) 2 (q - 1) :=
    Eventually.of_forall (fun θ => ⟨D, hD, hRect θ⟩)
  let W₁ := (q : ℝ) * E + 1
  have hW₁ : (q : ℝ) * E < W₁ := by dsimp [W₁]; linarith
  obtain ⟨W, p, G, R, hW, _, hNe, hBand, hG, hGRep, hHull⟩ :=
    exists_torusCayleyFiniteDifference_annihilates_hull β S T hS hCont hK hAdvance
      E W₁ hE q hq hW₁ hOrder
  let e := (mFourierBasis (d := d)).repr
  let U : lp (fun _ : d → ℤ => ℂ) 2 →L[ℂ] lp (fun _ : d → ℤ => ℂ) 2 :=
    (torusPoissonCayleyConvolution β S T hS hCont hK hAdvance : _ ≃ₗᵢ[ℂ] _)
  let r := ((U - 1) ^ q) p
  let f := e.symm r
  have hf : f ≠ 0 := by
    intro hf
    exact hNe (e.symm.injective (hf.trans e.symm.map_zero.symm))
  have hFBand (n : d → ℤ) (hn : torusDirectionalFrequency β n ∉ Icc 0 W) :
      mFourierCoeff f n = 0 := by
    rw [← mFourierBasis_repr]
    change e (e.symm r) n = 0
    rw [e.apply_symm_apply]
    exact (hBand n hn).2
  let Rreal (θ : UnitAddTorus d) (x : ℝ) := R θ (x : ℂ)
  have hRreal : ∀ᵐ θ ∂volume, Continuous (Rreal θ) ∧
      (Rreal θ) =ᵐ[volume] fun x : ℝ => G (unitAddTorusFlow β x θ) := by
    filter_upwards [hHull] with θ hθ
    exact ⟨hθ.1.continuous.comp Complex.continuous_ofReal, hθ.2.1⟩
  have hKill : ∀ᵐ θ ∂volume, TemperedDistribution.smulLeftCLM ℂ (Rreal θ) (T θ) = 0 :=
    hHull.mono (fun θ hθ => hθ.2.2.2)
  refine ⟨W, f, hW, hf, fun n hn => hFBand n (by rwa [← hLfreq]), ?_⟩
  exact originalFourierArray_convolution_eq_zero_of_annihilating_band β L hL hLfreq
    B label hLabel N μ hν W f hFBand G hG hGRep Rreal hRreal
    2 (q - 1) D hD (Eventually.of_forall hRect) hKill

end
end MeyerGeneralProblem
