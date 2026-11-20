module

public import MeyerGeneralProblem.Distribution.TorusPoissonCayleyFourier
public import MeyerGeneralProblem.Distribution.TorusPoissonCayleyPhaseMean

@[expose] public section

/-!
# Poisson averaging of the coherent Cayley boundary

The actual analytic Cayley field at positive height is the Poisson
average of a single bounded measurable representative of its boundary.
-/

namespace MeyerGeneralProblem
noncomputable section
open Adaptive Filter MeasureTheory MeasureTheory.Measure ProbabilityTheory Set UnitAddTorus
open scoped ComplexConjugate ENNReal FourierTransform NNReal Topology

/-- Use normalized Haar measure on each circle factor. -/
local instance cayleySmoothCircleMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

local instance cayleySmoothCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

section

variable {d : Type*} [Fintype d]
variable (β : d → ℝ) (S : UnitAddTorus d → LocallyFiniteCarrier)
variable (T : UnitAddTorus d → TemperedDistribution ℝ ℂ)
variable (hT : ∀ θ, DistributionSupportedOn (S θ).carrier (T θ))
variable (hCont : ∀ f : SchwartzMap ℝ ℂ, HasCompactSupport (f : ℝ → ℂ) →
  Continuous (fun θ => T θ f))
variable {K : ℕ} (hCount : ∀ θ r, ((S θ).carrier ∩ Ico r (r + 1)).ncard ≤ K)
variable (hAdvance : ∀ t θ, T (unitAddTorusFlow β t θ) = combDistributionTranslation (-t) (T θ))

/-- There is a Borel representative of the unit boundary, bounded
everywhere by one, whose Poisson averages have the actual Cayley
coefficients at every positive height. -/
private theorem exists_boundedCayleyBoundary_poisson_coefficients :
    ∃ Q : UnitAddTorus d → ℂ, Measurable Q ∧ (∀ θ, ‖Q θ‖ ≤ 1) ∧
      Q =ᵐ[volume] torusPoissonCayleyBoundaryL2 β S T hT hCont hCount hAdvance ∧
      ∀ (y : ℝ≥0), 0 < y → ∀ n : d → ℤ,
        (∫ θ, (∫ t : ℝ, (cauchyPDFReal 0 y t : ℂ) * Q (unitAddTorusFlow β t θ)) *
          conj (mFourier n θ)) =
          torusPoissonCayleyCoeff β S T hT hCont hCount hAdvance n (((y : ℝ) : ℂ) * Complex.I) := by
  let F := torusPoissonCayleyBoundaryL2 β S T hT hCont hCount hAdvance
  let hF := (Lp.aestronglyMeasurable F).aemeasurable
  let G := hF.mk F
  have hg : Measurable G := hF.measurable_mk
  let Q (θ : UnitAddTorus d) := if ‖G θ‖ ≤ 1 then G θ else 0
  have hQ : Measurable Q := hg.ite (measurableSet_le hg.norm measurable_const) measurable_const
  have hB (θ : UnitAddTorus d) : ‖Q θ‖ ≤ 1 := by
    unfold Q
    split_ifs with h
    · exact h
    · simp
  have hAe : Q =ᵐ[volume] F := by
    filter_upwards [hF.ae_eq_mk, ae_norm_torusPoissonCayleyBoundaryL2 β S T hT hCont hCount hAdvance]
      with θ hθ hUnit
    change F θ = G θ at hθ
    change ‖F θ‖ = 1 at hUnit
    simp [Q, ← hθ, hUnit]
  refine ⟨Q, hQ, hB, hAe, ?_⟩
  intro y hy n
  let b := torusDirectionalFrequency β n
  have hNorm (θ : UnitAddTorus d) : ‖mFourier n θ‖ = 1 := by
    simp only [mFourier, ContinuousMap.coe_mk, norm_prod, fourier_apply, Circle.norm_coe,
      Finset.prod_const_one]
  have hAvg := integral_poisson_average_mul_conj (volume : Measure (UnitAddTorus d))
    (unitAddTorusFlow β) (continuous_unitAddTorusFlow β).measurable
    (measurePreserving_unitAddTorusFlow β) Q (mFourier n) hQ (mFourier n).continuous.measurable
    hB hNorm b (mFourier_unitAddTorusFlow β n) hy
  rw [hAvg]
  have hC : (∫ θ, Q θ * conj (mFourier n θ)) = mFourierCoeff F n := by
    simp only [mFourierCoeff, mFourier_neg, smul_eq_mul]
    apply integral_congr_ae
    filter_upwards [hAe] with θ hθ
    rw [hθ, mul_comm]
  rw [hC, torusPoissonCayleyCoeff_at_height β S T hT hCont hCount hAdvance n (y : ℝ) (by exact_mod_cast hy)]
  by_cases hn : b < 0
  · have hz := mFourierCoeff_torusPoissonCayleyBoundaryL2_eq_zero_of_neg β S T hT hCont hCount hAdvance n hn
    change mFourierCoeff F n = 0 at hz
    have hz' : mFourierCoeff (torusPoissonCayleyBoundaryL2 β S T hT hCont hCount hAdvance) n = 0 := hz
    simp only [hz, hz', mul_zero]
  · have hb : |b| = b := abs_of_nonneg (le_of_not_gt hn)
    rw [hb]
    congr 3
    dsimp [b]
    ring


/-- The actual Cayley field at positive height is the Poisson average
along the phase flow of a single bounded Borel boundary representative. -/
theorem exists_boundedCayleyBoundary_poisson_field :
    ∃ Q : UnitAddTorus d → ℂ, Measurable Q ∧ (∀ θ, ‖Q θ‖ ≤ 1) ∧
      Q =ᵐ[volume] torusPoissonCayleyBoundaryL2 β S T hT hCont hCount hAdvance ∧
      ∀ (y : ℝ≥0), 0 < y →
        (fun θ => ∫ t : ℝ, (cauchyPDFReal 0 y t : ℂ) * Q (unitAddTorusFlow β t θ)) =ᵐ[volume]
          torusPoissonCayleyField β S T hT hCont hCount (((y : ℝ) : ℂ) * Complex.I) := by
  obtain ⟨Q, hQ, hB, hEq, hFourier⟩ := exists_boundedCayleyBoundary_poisson_coefficients
    β S T hT hCont hCount hAdvance
  refine ⟨Q, hQ, hB, hEq, ?_⟩
  intro y hy
  let P (t : ℝ) := cauchyPDFReal 0 y t
  let f (θ : UnitAddTorus d) := ∫ t : ℝ, (P t : ℂ) * Q (unitAddTorusFlow β t θ)
  have hP : Integrable P := integrable_cauchyPDFReal 0 (γ := y)
  have hP0 (t : ℝ) : 0 ≤ P t := (cauchyPDF_pos 0 hy.ne' t).le
  have hMeasG : Measurable (fun p : UnitAddTorus d × ℝ =>
      (P p.2 : ℂ) * Q (unitAddTorusFlow β p.2 p.1)) :=
    (Complex.continuous_ofReal.measurable.comp ((measurable_cauchyPDFReal 0 y).comp measurable_snd)).mul
      (hQ.comp ((continuous_unitAddTorusFlow β).measurable.comp measurable_swap))
  have hMeas : StronglyMeasurable f := hMeasG.stronglyMeasurable.integral_prod_right'
  have hBound (θ : UnitAddTorus d) : ‖f θ‖ ≤ 1 := by
    let G (t : ℝ) := (P t : ℂ) * Q (unitAddTorusFlow β t θ)
    have hPoint (t : ℝ) : ‖G t‖ ≤ P t := by
      rw [show G t = (P t : ℂ) * Q (unitAddTorusFlow β t θ) from rfl,
        norm_mul, Complex.norm_real, Real.norm_of_nonneg (hP0 t)]
      exact mul_le_of_le_one_right (hP0 t) (hB _)
    have hInt : Integrable G := hP.mono'
      (hMeasG.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable (ae_of_all _ hPoint)
    calc
      ‖f θ‖ ≤ ∫ t, ‖G t‖ := norm_integral_le_integral_norm G
      _ ≤ ∫ t, P t := integral_mono hInt.norm hP hPoint
      _ = 1 := integral_cauchyPDFReal_eq_one 0 hy.ne'
  have hMem : MemLp f 2 (volume : Measure (UnitAddTorus d)) :=
    MemLp.of_bound hMeas.aestronglyMeasurable 1 (ae_of_all _ hBound)
  let U := hMem.toLp f
  let z := (((y : ℝ) : ℂ) * Complex.I)
  have hU : U = torusPoissonCayleyL2 β S T hT hCont hCount hAdvance z := by
    apply (mFourierBasis (d := d)).repr.injective
    ext n
    rw [mFourierBasis_repr, mFourierBasis_repr]
    change mFourierCoeff U n = torusPoissonCayleyCoeff β S T hT hCont hCount hAdvance n z
    have hF : mFourierCoeff U n = ∫ θ, f θ * conj (mFourier n θ) := by
      simp only [mFourierCoeff, mFourier_neg, smul_eq_mul]
      apply integral_congr_ae
      filter_upwards [hMem.coeFn_toLp] with θ hθ
      change U θ = f θ at hθ
      rw [hθ, mul_comm]
    rw [hF]
    exact hFourier y hy n
  change f =ᵐ[volume] torusPoissonCayleyField β S T hT hCont hCount z
  have hRep : U =ᵐ[volume] torusPoissonCayleyField β S T hT hCont hCount z := by
    rw [hU]
    exact coeFn_torusPoissonCayleyL2 β S T hT hCont hCount hAdvance z
  exact hMem.coeFn_toLp.symm.trans hRep


/-- A Borel representative of the coherent boundary gives the actual
real Cayley path under the flow, for almost every phase and almost
every real time on that path. -/
theorem ae_ae_boundedCayleyBoundary_phaseAdvance_eq_realLeaf
    (Q : UnitAddTorus d → ℂ) (hQ : Measurable Q)
    (hEq : Q =ᵐ[volume] torusPoissonCayleyBoundaryL2 β S T hT hCont hCount hAdvance) :
    ∀ᵐ θ : UnitAddTorus d ∂volume, ∀ᵐ x : ℝ ∂volume,
      Q (unitAddTorusFlow β x θ) =
        torusPoissonCayleyExtendedLeaf β S T hT hCont hCount θ (x : ℂ) := by
  let μ := (volume : Measure (UnitAddTorus d))
  let ν := (volume : Measure ℝ)
  let F (θ : UnitAddTorus d) (x : ℝ) :=
    torusPoissonCayleyExtendedLeaf β S T hT hCont hCount θ (x : ℂ)
  let f (p : UnitAddTorus d × ℝ) := F p.1 p.2
  let q (p : UnitAddTorus d × ℝ) := Q (unitAddTorusFlow β p.2 p.1)
  have hf : AEMeasurable f (μ.prod ν) :=
    aemeasurable_prod_torusPoissonCayleyExtendedLeaf_real β S T hT hCont hCount hAdvance
  have hq : Measurable q :=
    hQ.comp ((continuous_unitAddTorusFlow β).measurable.comp measurable_swap)
  have hBoundary : Q =ᵐ[μ] torusPoissonCayleyBoundary β S T hT hCont hCount := by
    refine hEq.trans ?_
    unfold torusPoissonCayleyBoundaryL2
    exact MemLp.coeFn_toLp _
  have hSlice (x : ℝ) : ∀ᵐ θ ∂μ, q (θ, x) = f (θ, x) := by
    let hPres := measurePreserving_unitAddTorusFlow β x
    filter_upwards [hPres.quasiMeasurePreserving.ae_eq_comp hBoundary,
      ae_torusPoissonCayleyExtendedLeaf_real_phaseAdvance β S T hT hCont hCount hAdvance x]
      with θ hθ hCov
    have hReal := hCov 0
    rw [Complex.ofReal_zero, zero_add, torusPoissonCayleyExtendedLeaf_zero] at hReal
    exact hθ.trans hReal
  let g := hf.mk f
  have hg : Measurable g := hf.measurable_mk
  have hSwap : MeasurePreserving Prod.swap (ν.prod μ) (μ.prod ν) := Measure.measurePreserving_swap
  have hRepSwap : (fun p : ℝ × UnitAddTorus d => f (p.2, p.1)) =ᵐ[ν.prod μ]
      fun p : ℝ × UnitAddTorus d => g (p.2, p.1) :=
    hSwap.quasiMeasurePreserving.ae_eq_comp hf.ae_eq_mk
  have hRepX := Measure.ae_ae_eq_curry_of_prod hRepSwap
  have hX : ∀ᵐ x ∂ν, ∀ᵐ θ ∂μ, q (θ, x) = g (θ, x) := by
    filter_upwards [hRepX] with x hx
    exact EventuallyEq.trans (hSlice x) hx
  have hComm := (Measure.ae_ae_comm (μ := μ) (ν := ν)
    (measurableSet_eq_fun hq hg)).mpr hX
  have hRep := Measure.ae_ae_eq_curry_of_prod hf.ae_eq_mk
  filter_upwards [hComm, hRep] with θ hEqQ hEqF
  exact EventuallyEq.trans hEqQ hEqF.symm


include hAdvance in
/-- At every fixed horizontal coordinate and positive height, the
actual analytic leaf is the Poisson integral of its actual real
Cayley path on a full-measure set of phases. -/
theorem ae_poisson_integral_torusPoissonCayleyExtendedLeaf (x : ℝ) (y : ℝ≥0) (hy : 0 < y) :
    ∀ᵐ θ : UnitAddTorus d ∂volume,
      (∫ t : ℝ, (cauchyPDFReal x y t : ℂ) *
        torusPoissonCayleyExtendedLeaf β S T hT hCont hCount θ (t : ℂ)) =
      torusPoissonCayleyExtendedLeaf β S T hT hCont hCount θ ((x : ℂ) + ((y : ℝ) : ℂ) * Complex.I) := by
  obtain ⟨Q, hQ, _, hEq, hField⟩ := exists_boundedCayleyBoundary_poisson_field
    β S T hT hCont hCount hAdvance
  have hSlice := ae_ae_boundedCayleyBoundary_phaseAdvance_eq_realLeaf
    β S T hT hCont hCount hAdvance Q hQ hEq
  let F := torusPoissonCayleyExtendedLeaf β S T hT hCont hCount
  let z : ℂ := ((y : ℝ) : ℂ) * Complex.I
  have hPos : 0 < z.im := by simpa [z, Complex.mul_im] using hy
  have h0 : ∀ᵐ θ : UnitAddTorus d ∂volume,
      (∫ t : ℝ, (cauchyPDFReal 0 y t : ℂ) * F θ (t : ℂ)) = F θ z := by
    filter_upwards [hSlice, hField y hy] with θ hMatch hVal
    calc
      _ = ∫ t : ℝ, (cauchyPDFReal 0 y t : ℂ) * Q (unitAddTorusFlow β t θ) := by
        apply integral_congr_ae
        filter_upwards [hMatch] with t ht
        rw [ht]
      _ = _ := hVal.trans (torusPoissonCayleyExtendedLeaf_eq_field β S T hT hCont hCount θ hPos).symm
  let hPres := measurePreserving_unitAddTorusFlow β x
  have hX : ∀ᵐ θ : UnitAddTorus d ∂volume,
      (∫ t : ℝ, (cauchyPDFReal 0 y t : ℂ) * F (unitAddTorusFlow β x θ) (t : ℂ)) =
        F (unitAddTorusFlow β x θ) z := hPres.quasiMeasurePreserving.ae h0
  filter_upwards [hX, ae_torusPoissonCayleyExtendedLeaf_real_phaseAdvance β S T hT hCont hCount hAdvance x,
    ae_forall_torusPositivePoissonLeaf_phaseAdvance β S T hT hCont hCount hAdvance x]
    with θ hθ hRe hUpper
  have hPos' : 0 < ((x : ℂ) + z).im := by simpa using hPos
  change (∫ t : ℝ, (cauchyPDFReal x y t : ℂ) * F θ (t : ℂ)) = F θ ((x : ℂ) + z)
  calc
    _ = ∫ t : ℝ, (cauchyPDFReal 0 y t : ℂ) * F (unitAddTorusFlow β x θ) (t : ℂ) := by
      rw [← integral_add_right_eq_self
        (fun t : ℝ => (cauchyPDFReal x y t : ℂ) * F θ (t : ℂ)) x]
      apply integral_congr_ae
      filter_upwards with t
      have hP : cauchyPDFReal x y (t + x) = cauchyPDFReal 0 y t := by
        simp only [cauchyPDFReal_def, add_sub_cancel_right, sub_zero]
      rw [hP]
      exact congrArg ((cauchyPDFReal 0 y t : ℂ) * ·) (hRe t).symm
    _ = F (unitAddTorusFlow β x θ) z := hθ
    _ = _ := by
      have hEq := hUpper z hPos
      rw [add_comm z (x : ℂ)] at hEq
      change torusPoissonCayleyExtendedLeaf β S T hT hCont hCount (unitAddTorusFlow β x θ) z =
        torusPoissonCayleyExtendedLeaf β S T hT hCont hCount θ ((x : ℂ) + z)
      rw [torusPoissonCayleyExtendedLeaf_eq_field β S T hT hCont hCount _ hPos,
        torusPoissonCayleyExtendedLeaf_eq_field β S T hT hCont hCount _ hPos']
      simpa only [torusPoissonCayleyField, ite_eq_left hPos, ite_eq_left hPos'] using
        congrArg supportPoissonCayley hEq

end

end
end MeyerGeneralProblem
