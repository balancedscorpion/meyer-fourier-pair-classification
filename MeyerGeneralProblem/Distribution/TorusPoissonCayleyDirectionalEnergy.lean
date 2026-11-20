module

public import MeyerGeneralProblem.Distribution.TorusPoissonCayleyPoissonDerivative
public import MeyerGeneralProblem.Distribution.TorusPoissonCayleyPhaseBeurling

@[expose] public section

/-!
# Finite directional energy of the coherent Cayley boundary

Haar Parseval and the Poisson derivative bound control every damped
Fourier sum. Finite partial sums pass to height zero, giving the
original Beurling-density bound for the actual coherent boundary.
-/

namespace MeyerGeneralProblem

noncomputable section

open Adaptive Filter MeasureTheory Metric ProbabilityTheory Set UnitAddTorus
open scoped ComplexConjugate ENNReal FourierTransform NNReal Topology

/-- Use normalized Haar measure on each circle factor. -/
local instance cayleyEnergyCircleMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

local instance cayleyEnergyCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

local notation:max "TorusL2(" d ")" => Lp ℂ 2 (volume : Measure (UnitAddTorus d))

section CayleyDirectionalEnergy

variable {d : Type*} [Fintype d]
variable (β : d → ℝ) (S : UnitAddTorus d → LocallyFiniteCarrier)
variable (T : UnitAddTorus d → TemperedDistribution ℝ ℂ)
variable (hT : ∀ θ, DistributionSupportedOn (S θ).carrier (T θ))
variable (hCont : ∀ f : SchwartzMap ℝ ℂ, HasCompactSupport (f : ℝ → ℂ) →
  Continuous (fun θ => T θ f))
variable {K : ℕ} (hCount : ∀ θ r, ((S θ).carrier ∩ Ico r (r + 1)).ncard ≤ K)
variable (hAdvance : ∀ t θ, T (unitAddTorusFlow β t θ) = combDistributionTranslation (-t) (T θ))

/-- The actual complex derivative has a Haar L² representative at each
positive height. Its Fourier coefficient is the physical frequency
times the field coefficient and the factor 2πi. -/
theorem exists_torusPoissonCayleyFieldDerivativeL2 {z : ℂ} (hz : 0 < z.im) :
    ∃ D : TorusL2(d),
      D =ᵐ[volume] (fun θ => deriv (fun v => torusPoissonCayleyField β S T hT hCont hCount v θ) z) ∧
      ∀ n : d → ℤ, mFourierCoeff D n =
        2 * (Real.pi : ℂ) * Complex.I * (torusDirectionalFrequency β n : ℂ) *
          torusPoissonCayleyCoeff β S T hT hCont hCount hAdvance n z := by
  let F := torusPoissonCayleyField β S T hT hCont hCount
  let L (θ : UnitAddTorus d) := deriv (fun v => F v θ) z
  have hGood := ae_analyticOnNhd_norm_torusPoissonCayleyField β S T hT hCont hCount hAdvance
  have hMeas : AEStronglyMeasurable L volume := by
    apply aestronglyMeasurable_of_tendsto_ae (𝓝[≠] (0 : ℂ))
      (f := fun a θ => a⁻¹ • (F (z + a) θ - F z θ))
    · intro a
      exact ((aemeasurable_torusPoissonCayleyField β S T hT hCont hCount hAdvance (z + a)).aestronglyMeasurable.sub
        (aemeasurable_torusPoissonCayleyField β S T hT hCont hCount hAdvance z).aestronglyMeasurable).const_smul a⁻¹
    · filter_upwards [hGood] with θ hθ
      exact (hθ.1 z hz).differentiableAt.hasDerivAt.tendsto_slope_zero
  let r := z.im / 2
  have hr : 0 < r := half_pos hz
  have hClosed : closedBall z r ⊆ {w : ℂ | 0 < w.im} := by
    intro w hw
    have hDist := mem_closedBall.mp hw
    have hDiff := (le_abs_self ((z - w).im)).trans (Complex.abs_im_le_norm (z - w))
    rw [Complex.sub_im, ← dist_eq_norm, dist_comm] at hDiff
    change 0 < w.im
    dsimp only [r] at hDist
    linarith only [hz, hDiff, hDist]
  have hBound : ∀ᵐ θ ∂volume, ‖L θ‖ ≤ 1 / r := by
    filter_upwards [hGood] with θ hθ
    exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr
      (hθ.1.differentiableOn.diffContOnCl_ball hClosed) (fun w _ => hθ.2 w)
  let hMem : MemLp L 2 volume := MemLp.of_bound hMeas _ hBound
  let D := hMem.toLp L
  refine ⟨D, hMem.coeFn_toLp, ?_⟩
  intro n
  have hEq : mFourierCoeff D n = ∫ θ, mFourier (-n) θ * L θ := by
    unfold mFourierCoeff
    apply integral_congr_ae
    filter_upwards [hMem.coeFn_toLp] with θ hθ
    change D θ = L θ at hθ
    rw [hθ, smul_eq_mul]
  rw [hEq]
  exact (hasDerivAt_torusPoissonCayleyCoeff_eq_integral_deriv β S T hT hCont hCount hAdvance n hz).unique
    (hasDerivAt_torusPoissonCayleyCoeff β S T hT hCont hCount hAdvance n hz)

/-- The Fourier sum at positive height is bounded by the mean boundary
phase density. The sum is the imaginary part of the Haar pairing with
the actual derivative, divided by 2π. -/
theorem exists_hasSum_torusPoissonCayleyDirectionalEnergy_at_height (y : ℝ≥0) (hy : 0 < y) :
    let F := torusPoissonCayleyL2 β S T hT hCont hCount hAdvance (((y : ℝ) : ℂ) * Complex.I)
    ∃ E : ℝ, HasSum (fun n : d → ℤ =>
      torusDirectionalFrequency β n * ‖mFourierCoeff F n‖ ^ 2) E ∧
      E ≤ (torusPoissonCayleyMeanPhaseDensity β S T hT hCont hCount).toReal := by
  let z : ℂ := ((y : ℝ) : ℂ) * Complex.I
  have hz : 0 < z.im := by simpa [z, Complex.mul_im] using hy
  let F := torusPoissonCayleyL2 β S T hT hCont hCount hAdvance z
  obtain ⟨D, hDer, hCoeff⟩ :=
    exists_torusPoissonCayleyFieldDerivativeL2 β S T hT hCont hCount hAdvance hz
  let C := ∫ θ, conj (F θ) * D θ
  let E := (2 * Real.pi)⁻¹ * C.im
  refine ⟨E, ?_, ?_⟩
  · have hParseval := hasSum_prod_mFourierCoeff F D
    have hIm := (Complex.imCLM.hasSum hParseval).mul_left (2 * Real.pi)⁻¹
    refine hIm.congr_fun fun n => ?_
    let b := torusDirectionalFrequency β n
    let a := mFourierCoeff F n
    have hC : conj a * mFourierCoeff D n =
        (2 * (Real.pi : ℂ) * Complex.I * (b : ℂ)) * (‖a‖ ^ 2 : ℝ) := by
      have hD : mFourierCoeff D n = (2 * (Real.pi : ℂ) * Complex.I * (b : ℂ)) * a := hCoeff n
      rw [hD, show conj a * ((2 * (Real.pi : ℂ) * Complex.I * (b : ℂ)) * a) =
        (2 * (Real.pi : ℂ) * Complex.I * (b : ℂ)) * (a * conj a) by ring,
        Complex.mul_conj, Complex.normSq_eq_norm_sq]
    symm
    change (2 * Real.pi)⁻¹ * Complex.imCLM (conj a * mFourierCoeff D n) = b * ‖a‖ ^ 2
    rw [hC]
    simp only [Complex.imCLM_apply, Complex.mul_im, Complex.mul_re, Complex.I_im, Complex.I_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat, mul_zero, zero_mul,
      add_zero, zero_add, sub_zero, mul_one]
    field_simp [Real.pi_ne_zero]
  · let g := torusPoissonCayleyPhaseDensity β S T hT hCont hCount
    let W (p : UnitAddTorus d × ℝ) := cauchyPDFReal 0 y p.2 * g p.1 p.2
    let W₀ (θ : UnitAddTorus d) := ∫ t, W (θ, t)
    obtain ⟨hMass, hMean⟩ :=
      integrable_prod_and_integral_poisson_phaseDensity β S T hT hCont hCount hAdvance 0 y hy
    have hIntW : Integrable W₀ := hMass.integral_prod_left
    have hIntW₀ : (∫ θ, W₀ θ) = (torusPoissonCayleyMeanPhaseDensity β S T hT hCont hCount).toReal :=
      (integral_prod W hMass).symm.trans hMean
    have hF : ∀ᵐ θ ∂volume, ‖F θ‖ ≤ 1 := by
      filter_upwards [coeFn_torusPoissonCayleyL2 β S T hT hCont hCount hAdvance z,
        ae_analyticOnNhd_norm_torusPoissonCayleyField β S T hT hCont hCount hAdvance]
        with θ hθ hNorm
      change F θ = _ at hθ
      rw [hθ]
      exact hNorm.2 z
    have hD : ∀ᵐ θ ∂volume, ‖D θ‖ ≤ (2 * Real.pi) * W₀ θ := by
      filter_upwards [hDer, ae_norm_deriv_torusPoissonCayleyExtendedLeaf_le β S T hT hCont hCount hAdvance 0 y hy]
        with θ hθ hb
      have hU : IsOpen {v : ℂ | 0 < v.im} := isOpen_lt continuous_const Complex.continuous_im
      have hEq : torusPoissonCayleyExtendedLeaf β S T hT hCont hCount θ =ᶠ[𝓝 z]
          (fun v => torusPoissonCayleyField β S T hT hCont hCount v θ) := by
        filter_upwards [hU.mem_nhds hz] with v hv
        exact torusPoissonCayleyExtendedLeaf_eq_field β S T hT hCont hCount θ hv
      rw [hθ, ← hEq.deriv_eq]
      simpa only [Complex.ofReal_zero, zero_add, W₀, W, g, z] using hb
    have hPair : Integrable (fun θ => conj (F θ) * D θ) := by
      refine (L2.integrable_inner F D).congr (ae_of_all _ fun θ => ?_)
      exact RCLike.inner_apply' (F θ) (D θ)
    have hNorm : ‖C‖ ≤ (2 * Real.pi) * (torusPoissonCayleyMeanPhaseDensity β S T hT hCont hCount).toReal := by
      calc
        _ ≤ ∫ θ, ‖conj (F θ) * D θ‖ := norm_integral_le_integral_norm _
        _ ≤ ∫ θ, (2 * Real.pi) * W₀ θ := by
          refine integral_mono_ae hPair.norm (hIntW.const_mul _) ?_
          filter_upwards [hF, hD] with θ hf hd
          rw [norm_mul, Complex.norm_conj]
          exact (mul_le_of_le_one_left (norm_nonneg _) hf).trans hd
        _ = _ := by rw [integral_const_mul, hIntW₀]
    have hC := ((le_abs_self C.im).trans (Complex.abs_im_le_norm C)).trans hNorm
    change (2 * Real.pi)⁻¹ * C.im ≤ _
    rw [← div_eq_inv_mul]
    exact (div_le_iff₀ Real.two_pi_pos).mpr (by simpa only [mul_comm] using hC)


/-- The coherent unit boundary has finite directional Fourier energy,
bounded by the Haar mean of its positive phase density. -/
theorem exists_hasSum_torusPoissonCayleyDirectionalEnergy :
    let B := torusPoissonCayleyBoundaryL2 β S T hT hCont hCount hAdvance
    ∃ E : ℝ, HasSum (fun n : d → ℤ =>
      torusDirectionalFrequency β n * ‖mFourierCoeff B n‖ ^ 2) E ∧
      E ≤ (torusPoissonCayleyMeanPhaseDensity β S T hT hCont hCount).toReal := by
  let B := torusPoissonCayleyBoundaryL2 β S T hT hCont hCount hAdvance
  let b := torusDirectionalFrequency β
  let e (n : d → ℤ) := b n * ‖mFourierCoeff B n‖ ^ 2
  let M := (torusPoissonCayleyMeanPhaseDensity β S T hT hCont hCount).toReal
  have h0 : 0 ≤ e := by
    intro n
    by_cases hn : b n < 0
    · have hz : mFourierCoeff B n = 0 :=
        mFourierCoeff_torusPoissonCayleyBoundaryL2_eq_zero_of_neg β S T hT hCont hCount hAdvance n hn
      change 0 ≤ e n
      simp [e, hz]
    · exact mul_nonneg (le_of_not_gt hn) (sq_nonneg _)
  have hFinite (s : Finset (d → ℤ)) : (∑ n ∈ s, e n) ≤ M := by
    let A (y : ℝ) := ∑ n ∈ s, e n * Real.exp (-(4 * Real.pi * b n * y))
    have hA : Continuous A := by
      unfold A
      fun_prop
    have hAy (y : ℝ) (hy : 0 < y) : A y ≤ M := by
      let t : ℝ≥0 := y.toNNReal
      have ht : 0 < t := Real.toNNReal_pos.mpr hy
      have hty : (t : ℝ) = y := Real.coe_toNNReal _ hy.le
      obtain ⟨E, hSum, hE⟩ := exists_hasSum_torusPoissonCayleyDirectionalEnergy_at_height
        β S T hT hCont hCount hAdvance t ht
      have hCoeff (n : d → ℤ) :
          torusPoissonCayleyCoeff β S T hT hCont hCount hAdvance n ((y : ℂ) * Complex.I) =
            (Real.exp (-(2 * Real.pi * b n * y)) : ℂ) * mFourierCoeff B n :=
        torusPoissonCayleyCoeff_at_height β S T hT hCont hCount hAdvance n y hy
      have hEq (n : d → ℤ) : b n * ‖torusPoissonCayleyCoeff β S T hT hCont hCount hAdvance n
          (((t : ℝ) : ℂ) * Complex.I)‖ ^ 2 = e n * Real.exp (-(4 * Real.pi * b n * y)) := by
        rw [hty, hCoeff, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
          mul_pow, ← Real.exp_nat_mul]
        simp only [e, Nat.cast_ofNat]
        rw [show 2 * -(2 * Real.pi * b n * y) = -(4 * Real.pi * b n * y) by ring]
        ring
      have hSum' : HasSum (fun n => e n * Real.exp (-(4 * Real.pi * b n * y))) E := by
        refine hSum.congr_fun fun n => ?_
        exact (hEq n).symm
      have hLe := hSum'.summable.sum_le_tsum s
        (fun n _ => mul_nonneg (h0 n) (Real.exp_pos (-(4 * Real.pi * b n * y))).le)
      rw [hSum'.tsum_eq] at hLe
      exact hLe.trans hE
    have hAt : A 0 = ∑ n ∈ s, e n := by
      simp [A]
    have hLim : Tendsto A (𝓝[>] (0 : ℝ)) (𝓝 (∑ n ∈ s, e n)) := by
      rw [← hAt]
      exact (hA.tendsto 0).mono_left nhdsWithin_le_nhds
    have hEvent : ∀ᶠ y : ℝ in 𝓝[>] 0, A y ≤ M := by
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact hAy y hy
    exact le_of_tendsto hLim hEvent
  exact ⟨∑' n, e n, (summable_of_sum_le h0 hFinite).hasSum, Real.tsum_le_of_sum_le h0 hFinite⟩

end CayleyDirectionalEnergy

/-- For the actual weak phase family the original physical Beurling
density bounds the finite directional energy of the Cayley boundary. -/
theorem exists_originalPhasePhysical_directionalEnergy_le_upperUniformBeurlingDensity
    {d : Type*} [Fintype d] (A B : LocallyFiniteCarrier) (label : B.subtype → d → ℤ)
    (β : d → ℝ) (hLabel : ∀ x : B.subtype, torusDirectionalFrequency β (label x) = (x : ℝ))
    (hIndep : ∀ k : d → ℤ, torusDirectionalFrequency β k = 0 → k = 0)
    (N : ℕ) (μ : TemperedDistribution ℝ ℂ) (hν : 𝓕 μ ∈ stronglyTemperedAtomicAtExponent B N)
    (hμ : DistributionSupportedOn A.carrier μ)
    {K : ℕ} (hA : ∀ r, windowCount A r 1 ≤ K) :
    let T := originalPhasePhysicalRecord B label N μ hν
    let hCont := fun f : SchwartzMap ℝ ℂ => fun _ : HasCompactSupport (f : ℝ → ℂ) =>
      continuous_originalPhasePhysicalRecord_apply B label N μ hν f
    let hAdvance := fun t θ => originalPhasePhysicalRecord_advance B label β hLabel N μ hν θ t
    ∃ (S : UnitAddTorus d → LocallyFiniteCarrier)
      (hS : ∀ θ, DistributionSupportedOn (S θ).carrier (T θ))
      (hK : ∀ θ r, ((S θ).carrier ∩ Ico r (r + 1)).ncard ≤ K) (E : ℝ),
      HasSum (fun n : d → ℤ => torusDirectionalFrequency β n *
        ‖mFourierCoeff (torusPoissonCayleyBoundaryL2 β S T hS hCont hK hAdvance) n‖ ^ 2) E ∧
      ENNReal.ofReal E ≤ upperUniformBeurlingDensity A := by
  let T := originalPhasePhysicalRecord B label N μ hν
  let hCont := fun f : SchwartzMap ℝ ℂ => fun _ : HasCompactSupport (f : ℝ → ℂ) =>
    continuous_originalPhasePhysicalRecord_apply B label N μ hν f
  let hAdvance := fun t θ => originalPhasePhysicalRecord_advance B label β hLabel N μ hν θ t
  obtain ⟨S, hS, hK, hMean⟩ :=
    exists_originalPhasePhysical_meanPhaseDensity_le_upperUniformBeurlingDensity A B label β
      hLabel hIndep N μ hν hμ hA
  obtain ⟨E, hSum, hE⟩ := exists_hasSum_torusPoissonCayleyDirectionalEnergy β S T hS hCont hK hAdvance
  exact ⟨S, hS, hK, E, hSum,
    ((ENNReal.ofReal_le_ofReal hE).trans ENNReal.ofReal_toReal_le).trans hMean⟩



end
end MeyerGeneralProblem
