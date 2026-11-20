module

public import MeyerGeneralProblem.Distribution.L2ExponentialDamping

@[expose] public section

/-!
# Positive-height derivative of the positive-frequency Poisson field

Starting at half the reference height gives a uniform positive
time margin for the Fourier multiplier. The resulting norm derivative
is `i` times the directional Fourier derivative of the positive field.
-/

namespace MeyerGeneralProblem

noncomputable section

open Adaptive Filter MeasureTheory Set UnitAddTorus
open scoped NNReal Topology

/-- Use normalized Haar measure for the phase torus Fourier basis. -/
local instance poissonHeightCircleMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

local notation:max "TorusL2(" d ")" => Lp ℂ 2 (volume : Measure (UnitAddTorus d))

/-- The positive Poisson field has the norm derivative in the height
variable. The derivative is `i • D`, with `D` having precisely the
directional derivative coefficients `2π i (n · β)`. -/
theorem exists_torusSupportPositivePoissonL2_hasDerivAt_height {d : Type*} [Fintype d]
    (β : d → ℝ) (S : UnitAddTorus d → LocallyFiniteCarrier)
    (T : UnitAddTorus d → TemperedDistribution ℝ ℂ)
    (hT : ∀ θ, DistributionSupportedOn (S θ).carrier (T θ))
    (hAdvance : ∀ t θ, T (unitAddTorusFlow β t θ) = combDistributionTranslation (-t) (T θ))
    (hCont : ∀ f : SchwartzMap ℝ ℂ, HasCompactSupport (f : ℝ → ℂ) →
      Continuous (fun θ => T θ f))
    {K : ℕ} (hCount : ∀ θ r, ((S θ).carrier ∩ Ico r (r + 1)).ncard ≤ K)
    {y : ℝ} (hy : 0 < y) :
    ∃ D : TorusL2(d),
      HasDerivAt (fun t : ℝ => torusSupportPositivePoissonL2 β S T hT hCont hCount t.toNNReal)
        (Complex.I • D) y ∧
      ∀ n : d → ℤ, mFourierCoeff D n =
        (Complex.ofReal (2 * Real.pi) * Complex.I * Complex.ofReal (torusDirectionalFrequency β n)) *
          mFourierCoeff (torusSupportPositivePoissonL2 β S T hT hCont hCount y.toNNReal) n := by
  let e := (mFourierBasis (d := d)).repr
  let G (z : ℝ) := torusSupportPositivePoissonL2 β S T hT hCont hCount z.toNNReal
  let a := y / 2
  have ha : 0 < a := half_pos hy
  have hay : a < y := half_lt_self hy
  let rate (n : d → ℤ) := 2 * Real.pi * |torusDirectionalFrequency β n|
  have hRate (n : d → ℤ) : 0 ≤ rate n := mul_nonneg Real.two_pi_pos.le (abs_nonneg _)
  let x := e (G a)
  have hG (z : ℝ) (hz : a < z) : G z = e.symm (lpExponentialDamping rate hRate (z - a) x) := by
    let s := (z - a).toNNReal
    have hs : 0 < s := Real.toNNReal_pos.mpr (sub_pos.mpr hz)
    have hsCoe : (s : ℝ) = z - a := Real.coe_toNNReal _ (sub_nonneg.mpr hz.le)
    have hSum : s + a.toNNReal = z.toNNReal := by
      apply NNReal.eq
      rw [NNReal.coe_add, hsCoe, Real.coe_toNNReal _ ha.le, Real.coe_toNNReal _ (ha.trans hz).le]
      ring
    apply e.injective
    ext n
    rw [LinearIsometryEquiv.apply_symm_apply, lpExponentialDamping_apply,
      max_eq_left (sub_nonneg.mpr hz.le)]
    change (mFourierBasis (d := d)).repr (G z) n =
      Complex.ofReal (Real.exp (-rate n * (z - a))) * (mFourierBasis (d := d)).repr (G a) n
    rw [mFourierBasis_repr, mFourierBasis_repr]
    have h := mFourierCoeff_torusSupportPositivePoissonL2_add β S T hT hAdvance hCont hCount
      hs (Real.toNNReal_pos.mpr ha) n
    rw [hSum, hsCoe] at h
    refine h.trans ?_
    congr 2
    dsimp only [rate]
    ring
  obtain ⟨v, hv, hvCoeff⟩ := exists_lpExponentialDamping_hasDerivAt rate hRate x (sub_pos.mpr hay)
  have hShift : HasDerivAt (fun z : ℝ => lpExponentialDamping rate hRate (z - a) x) v y := by
    change HasDerivAt ((fun t : ℝ => lpExponentialDamping rate hRate t x) ∘ (fun z : ℝ => z - a)) v y
    simpa only [id_eq, one_smul] using hv.scomp y ((hasDerivAt_id y).sub_const a)
  let L : lp (fun _ : d → ℤ => ℂ) 2 →L[ℝ] TorusL2(d) :=
    e.symm.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ
  have hLift : HasDerivAt (fun z : ℝ => e.symm (lpExponentialDamping rate hRate (z - a) x))
      (e.symm v) y :=
    L.hasFDerivAt.comp_hasDerivAt y hShift
  have hEq : G =ᶠ[𝓝 y] fun z => e.symm (lpExponentialDamping rate hRate (z - a) x) := by
    filter_upwards [Ioi_mem_nhds hay] with z hz
    exact hG z hz
  let D := (-Complex.I) • e.symm v
  have hD : Complex.I • D = e.symm v := by
    unfold D
    rw [smul_smul, mul_neg, Complex.I_mul_I, neg_neg, one_smul]
  refine ⟨D, ?_, ?_⟩
  · rw [hD]
    exact hLift.congr_of_eventuallyEq hEq
  · intro n
    have hCoeffD : mFourierCoeff D n = -Complex.I * v n := by
      change mFourierCoeff ((-Complex.I) • e.symm v : TorusL2(d)) n = _
      rw [← mFourierBasis_repr, map_smul]
      change -Complex.I * e (e.symm v) n = _
      rw [e.apply_symm_apply]
    have hCoeffG : mFourierCoeff (G y) n =
        Complex.ofReal (Real.exp (-rate n * (y - a))) * x n := by
      rw [hG y hay, ← mFourierBasis_repr]
      change e (e.symm (lpExponentialDamping rate hRate (y - a) x)) n = _
      rw [e.apply_symm_apply, lpExponentialDamping_apply, max_eq_left (sub_nonneg.mpr hay.le)]
    change mFourierCoeff D n =
      _ * mFourierCoeff (G y) n
    rw [hCoeffD, hCoeffG, hvCoeff]
    rcases lt_or_ge (torusDirectionalFrequency β n) 0 with hb | hb
    · have hx : x n = 0 := by
        change (mFourierBasis (d := d)).repr (G a) n = 0
        rw [mFourierBasis_repr]
        exact mFourierCoeff_torusSupportPositivePoissonL2_eq_zero_of_neg
          β S T hT hCont hCount _ n hb
      simp [hx]
    · simp only [rate, abs_of_nonneg hb, Complex.ofReal_mul, Complex.ofReal_neg]
      ring

end
end MeyerGeneralProblem
